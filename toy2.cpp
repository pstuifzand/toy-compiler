#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/IR/IRPrintingPasses.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/ExecutionEngine/JIT.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/Module.h"
#include "llvm/PassManager.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/LinkAllPasses.h"
#include <iostream>
#include <cctype>
#include <cstdio>
#include <unordered_map>
#include <string>
#include <vector>
#include <algorithm>
#include "toy2.hpp"
#include "marpa-cpp/marpa.hpp"
#include "symbol_table.h"
#include "error.h"

#include "tree.hpp"

using namespace llvm;

const char* AstTypesNames[] = {
    "Error",
    "Number",
    "Variable",
    "Binary",
    "Call",
    "Comma",
    "Param",
    "Params",
    "Prototype",
    "Function",
    "Type",
    "Struct",
    "StructMember",
};

const char* BuiltInTypeNames[] = {
    "Unknown Type",
    "int8",
    "int16",
    "int32",
    "int64",
    "uint8",
    "uint16",
    "uint32",
    "uint64",
    "float32",
    "float64",
};

std::ostream& operator<<(std::ostream& os, TypeCode c) {

    if (!(c>= TypeCode::Unknown_Type && c < TypeCode::MaxBuiltIn)) {
        //os << "WRONG TYPE(" << int(c) << ")";
        if (c == TypeCode(100))
            os << "Vec2";
        return os;
    }
    os << BuiltInTypeNames[int(c)];
    return os;
}

struct eq_cstring {
    bool operator()(const char* a, const char* b) {
        return strcmp(a, b) == 0;
    }
};

TypeCode BuiltInToTypecode(const char* type_name)
{
    if (strcmp("double", type_name) == 0) type_name = "float64";
    if (strcmp("Vec2", type_name) == 0) return TypeCode(100);
    auto first = std::begin(BuiltInTypeNames);
    auto last  = std::end(BuiltInTypeNames);
    auto it = find(first, last, type_name, eq_cstring());
    if (it != last) {
        int count = std::distance(first, it);
        return TypeCode(count);
    }
    std::cerr << "Unknown type: " << type_name << "\n";
    return TypeCode::Unknown_Type;
}

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
  tok_eof        = -1,

  // commands
  tok_def        = -2,
  tok_extern     = -3,

  // primary
  tok_identifier = -4,
  tok_number     = -5,
  tok_integer    = -6,
  tok_struct     = -7,
  tok_type       = -8,
};

static std::string IdentifierStr;  // Filled in if tok_identifier
static double      NumVal;         // Filled in if tok_number
static int32_t     IntVal;         // Filled in if tok_integer

inline int isident(int c) { return isalnum(c) || c == '_'; }

int line = 1;

static int mygetchar() {
    int c = getchar();
    if (c == '\n') ++line;
    return c;
}

/// gettok - Return the next token from standard input.
static int gettok() {
  static int LastChar = ' ';

  // Skip any whitespace.
  while (isspace(LastChar))
    LastChar = mygetchar();

  if (isalpha(LastChar)) { // identifier: [a-zA-Z][a-zA-Z0-9]*
    IdentifierStr = LastChar;
    while (isident((LastChar = mygetchar())))
      IdentifierStr += LastChar;

    if (IdentifierStr == "def") return tok_def;
    if (IdentifierStr == "func") return tok_def;
    if (IdentifierStr == "type") return tok_type;
    if (IdentifierStr == "struct") return tok_struct;
    if (IdentifierStr == "extern") return tok_extern;
    return tok_identifier;
  }

  if (isdigit(LastChar) || LastChar == '.') {   // Number: [0-9.]+
    std::string NumStr;
    do {
      NumStr += LastChar;
      LastChar = mygetchar();
    } while (isdigit(LastChar) || LastChar == '.');

    if (find(NumStr.begin(), NumStr.end(), '.') == NumStr.end()) {
        IntVal = std::stoi(NumStr);
        return tok_integer;
    }
    else {
        NumVal = strtod(NumStr.c_str(), 0);
        return tok_number;
    }
    //return tok_number;
  }

  if (LastChar == '#') {
    // Comment until end of line.
    do LastChar = mygetchar();
    while (LastChar != EOF && LastChar != '\n' && LastChar != '\r');
    
    if (LastChar != EOF)
      return gettok();
  }
  
  // Check for end of file.  Don't eat the EOF.
  if (LastChar == EOF)
    return tok_eof;

  // Otherwise, just return the character as its ascii value.
  int ThisChar = LastChar;
  LastChar = mygetchar();
  return ThisChar;
}

//===----------------------------------------------------------------------===//
// Parser
//===----------------------------------------------------------------------===//

/// CurTok/getNextToken - Provide a simple token buffer.  CurTok is the current
/// token the parser is looking at.  getNextToken reads another token from the
/// lexer and updates CurTok with its results.
static int CurTok;
static int getNextToken() {
  CurTok = gettok();
  return CurTok;
}

static void Match(int c) {
    if (CurTok != c) {
        printf("%d: Expected %c\n", line, c);
        exit(1);
    }
    getNextToken();
}

/// BinopPrecedence - This holds the precedence for each binary operator that is
/// defined.
static std::map<char, int> BinopPrecedence;

/// GetTokPrecedence - Get the precedence of the pending binary operator token.
static int GetTokPrecedence() {
  if (!isascii(CurTok))
    return -1;
  
  // Make sure it's a declared binop.
  int TokPrec = BinopPrecedence[CurTok];
  if (TokPrec <= 0) return -1;
  return TokPrec;
}

/// Error* - These are little helper functions for error handling.
tree<ast_node> Error(const char *Str) {
    printf("Error: %d: \"%c\" %s\n", line, CurTok, Str);
    ast_node n{AstType::Error};
    tree<ast_node> err{n};
    return err;
}

static tree<ast_node> ParseExpression();

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static tree<ast_node> ParseIdentifierExpr() {
    typedef tree_coordinate<ast_node> C;
    typedef tree_node_construct<ast_node> Cons;

    std::string IdName = IdentifierStr;

    ast_node identifier{IdName};
    getNextToken(); // consume the name

    tree<ast_node> id = tree<ast_node>{identifier};
    if (CurTok != '(') return id;

    // Call.
    getNextToken();  // eat (

    ast_node comma{AstType::Comma};

    tree<ast_node> args;

    Cons construct_node;

    if (CurTok != ')') {
        C it;

        if (empty(args)) {
            args = tree<ast_node>(comma);
            it = begin(args);
        }

        while (1) {
            tree<ast_node> arg = ParseExpression();

            sink(it) = comma;
            insert_left(it, begin(arg));
            //set_right_successor(it, ....); // empty

            if (CurTok == ')') break;

            if (CurTok != ',')
                return Error("Expected ')' or ',' in argument list");

            set_right_successor(it, construct_node(comma));
            it = right_successor(it);

            getNextToken();
        }
    }

    // Eat the ')'.
    getNextToken();

    ast_node op{AstType::Call};
    op.Name = IdName;

    return tree<ast_node>(op, id, args);
}

/// numberexpr ::= number
static tree<ast_node> ParseNumberExpr() {
    ast_node number{NumVal};
    getNextToken(); // consume the number
    return tree<ast_node>{number};
}

/// numberexpr ::= int
static tree<ast_node> ParseIntegerExpr() {
    ast_node number{IntVal};
    getNextToken(); // consume the number
    return tree<ast_node>{number};
}

/// parenexpr ::= '(' expression ')'
static tree<ast_node> ParseParenExpr() {
    getNextToken();  // eat (.

    tree<ast_node> V = ParseExpression();

    if (CurTok != ')')
        return Error("expected ')'");
    getNextToken();  // eat ).
    return V;
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static tree<ast_node> ParsePrimary() {
    switch (CurTok) {
    default: return Error("unknown token when expecting an expression");
    case tok_identifier: return ParseIdentifierExpr();
    case tok_number:     return ParseNumberExpr();
    case tok_integer:    return ParseIntegerExpr();
    case '(':            return ParseParenExpr();
    }
}

int isop(int c)
{
    return c == '+'
        || c == '-'
        || c == '*'
        || c == '/'
        || c == '<';
}

/// binoprhs
///   ::= ('+' primary)*
static tree<ast_node> ParseBinOpRHS(int ExprPrec, tree<ast_node> lhs) {
    while (1) {
        int TokPrec = GetTokPrecedence();

        // If this is a binop that binds at least as tightly as the current binop,
        // consume it, otherwise we are done.
        if (TokPrec < ExprPrec)
            return lhs;

        // Okay, we know this is a binop.
        int BinOp = CurTok;

        if (!isop(BinOp))
            return lhs;

        getNextToken();  // eat binop

        // Parse the primary expression after the binary operator.
        tree<ast_node> rhs = ParsePrimary();

        int NextPrec = GetTokPrecedence();

        if (TokPrec < NextPrec) {
            rhs = ParseBinOpRHS(TokPrec+1, rhs);
            if (empty(rhs)) {
                printf("%d: ERROR\n", line);
                return rhs;
            }
        }

        ast_node op;
        op.Type = AstType::Binary;
        op.Op   = BinOp;
        lhs = tree<ast_node>(op, lhs, rhs);
    }

    return lhs;
}

/// expression
///   ::= primary binoprhs
///
static tree<ast_node> ParseExpression() {
    tree<ast_node> LHS = ParsePrimary();
    return ParseBinOpRHS(0, LHS);
}

/// prototype
///   ::= id '(' id* ')'
static tree<ast_node> ParsePrototype() {
    //  if (CurTok != tok_identifier)
    //    return ErrorP("Expected function name in prototype");

    std::string FnName = IdentifierStr;
    getNextToken();

    //  if (CurTok != '(')
    //    return ErrorP("Expected '(' in prototype");

    Match('(');
    std::vector<std::string> ArgNames;
    std::vector<TypeCode>    TypeCodes;
    while (CurTok != ')') {
        if (CurTok != tok_identifier) Error("need parameter name");
        ArgNames.push_back(IdentifierStr);
        getNextToken();

        // TODO parse a type
        if (CurTok == tok_identifier) {
            std::cerr << "Type parsed: " << IdentifierStr << "\n";
            TypeCodes.push_back(BuiltInToTypecode(IdentifierStr.c_str()));
            getNextToken();
        } else {
            // default type is double
            TypeCodes.push_back(TypeCode::Float64);
        }

        if (CurTok != ',') break;
        getNextToken();
    }
    Match(')');

    // parse return type?
    std::string return_type = "float64";

    if (CurTok == tok_identifier) {
        return_type = IdentifierStr;
        getNextToken();
    }

    ast_node proto;
    proto.Type = AstType::Prototype;
    proto.Name = FnName;
    proto.Args = ArgNames;
    proto.TypeCodes = TypeCodes;
    proto.TCode = BuiltInToTypecode(return_type.c_str());
    return tree<ast_node>{proto};
}

/// definition ::= 'type' prototype expression
static tree<ast_node> ParseTypeDef() {
    getNextToken();  // eat token "type".

    if (CurTok != tok_identifier) {
        // TODO error
    }

    std::string struct_name = IdentifierStr;
    //std::cerr << "parser: struct name=[" << struct_name << "]\n";
    getNextToken(); // eat identifier

    if (CurTok != tok_struct) {
        // TODO error
    }
    getNextToken(); // eat struct

    Match('{');

    std::vector<std::string> ArgNames;
    std::vector<TypeCode>    TypeCodes;

    while (CurTok != '}') {
        if (CurTok != tok_identifier) Error("need identifier name");
        ArgNames.push_back(IdentifierStr);
        //std::cerr << "Identifier parsed: " << IdentifierStr << "\n";
        getNextToken();

        // TODO parse a type
        if (CurTok == tok_identifier) {
            //std::cerr << "Type parsed: " << IdentifierStr << "\n";
            TypeCodes.push_back(BuiltInToTypecode(IdentifierStr.c_str()));
            getNextToken();
        } else {
            Error("need type name");
        }
        Match(';');
    }

    Match('}');

    ast_node ast{AstType::Struct};
    ast.Name = struct_name;
    ast.Args = ArgNames;
    ast.TypeCodes = TypeCodes;
    return ast;
}

/// definition ::= 'def' prototype expression
static tree<ast_node> ParseDefinition() {
    getNextToken();  // eat def.
    ast_node top;
    top.Type = AstType::Function;
    top.TCode = TypeCode::Unknown_Type;

    tree<ast_node> proto = ParsePrototype();
    if (CurTok != '{') {
        printf("%d: ERROR missing {\n",line);
        return tree<ast_node>();
    }
    getNextToken(); // '{'
    tree<ast_node> expression;
    if (CurTok != '}') {
        expression = ParseExpression();
        if (CurTok == ';') getNextToken();
    }

    if (CurTok != '}') {
        printf("%d: ERROR missing }\n",line);
        return tree<ast_node>();
    }
    getNextToken(); // '}'
    tree<ast_node> ast{top, proto, expression};
    return ast;
}

/*
/// toplevelexpr ::= expression
static FunctionAST *ParseTopLevelExpr() {
  if (ExprAST *E = ParseExpression()) {
    // Make an anonymous proto.
    PrototypeAST *Proto = new PrototypeAST("", std::vector<std::string>());
    return new FunctionAST(Proto, E);
  }
  return 0;
}
*/

/*
/// external ::= 'extern' prototype
static PrototypeAST *ParseExtern() {
  getNextToken();  // eat extern.
  return ParsePrototype();
}
*/

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

static Module *TheModule;
static IRBuilder<> Builder(getGlobalContext());
static FunctionPassManager* TheFPM;

static std::unordered_map<std::string, Value*>   NamedValues;
static std::unordered_map<std::string, TypeCode> NamedTypes;
static std::unordered_map<std::string, Type*>    UserTypes;
static std::unordered_map<TypeCode, Type*>       CodedTypes;

Type* ConvertType(TypeCode type_code)
{
    // TODO uitbreiden
    if (type_code == TypeCode::Float64) {
        return Type::getDoubleTy(getGlobalContext());
    } else if (type_code == TypeCode::Float32) {
        return Type::getFloatTy(getGlobalContext());
    } else if (type_code == TypeCode::Int64) {
        return Type::getInt64Ty(getGlobalContext());
    } else if (type_code == TypeCode::Int32) {
        return Type::getInt32Ty(getGlobalContext());
    } else if (type_code == TypeCode::Int16) {
        return Type::getInt16Ty(getGlobalContext());
    } else if (type_code == TypeCode::Int8) {
        return Type::getInt8Ty(getGlobalContext());
    }

    auto it = CodedTypes.find(type_code);
    if (it != CodedTypes.end()) {
        return it->second;
    }

    // TODO error
    return Type::getDoubleTy(getGlobalContext());
}

template <class C>
Function* CodegenPrototype(C proto)
{
    const ast_node& n = source(proto);

    // Make the function type:  double(double,double) etc.
    size_t len = n.Args.size();
    size_t i = 0;

    std::vector<Type*> params(n.Args.size());
    while (i < len) {
        Type* type = ConvertType(n.TypeCodes[i]);
        params[i] = type;
        ++i;
    }

    Type* return_type = ConvertType(n.TCode);

    FunctionType* FT = FunctionType::get(return_type, params, false);

    Function* F = Function::Create(FT, Function::ExternalLinkage, n.Name, TheModule);

    // If F conflicted, there was already something named 'Name'.  If it has a
    // body, don't allow redefinition or reextern.
    if (F->getName() != n.Name) {
        // Delete the one we just made and get the existing one.
        F->eraseFromParent();
        F = TheModule->getFunction(n.Name);

        // If F already has a body, reject this.
        if (!F->empty()) {
            //ErrorF("redefinition of function");
            return 0;
        }

        // If F took a different number of args, reject.
        if (F->arg_size() != n.Args.size()) {
            //ErrorF("redefinition of function with different # args");
            return 0;
        }
    }

    // Set names for all arguments.
    unsigned Idx = 0;
    for (Function::arg_iterator AI = F->arg_begin(); Idx != n.Args.size();
            ++AI, ++Idx) {
        AI->setName(n.Args[Idx]);

        // Add arguments to variable symbol table.
        NamedValues[n.Args[Idx]] = AI;
        NamedTypes[n.Args[Idx]]  = n.TypeCodes[Idx];
    }

    return F;
}

Value* create_uint_value(uint64_t v, TypeCode type)
{
    switch (type) {
        case TypeCode::UInt64:
            return ConstantInt::get(Type::getInt64Ty(getGlobalContext()), v);
        case TypeCode::UInt32:
            return ConstantInt::get(Type::getInt32Ty(getGlobalContext()), v);
        case TypeCode::UInt16:
            return ConstantInt::get(Type::getInt16Ty(getGlobalContext()), v);
        case TypeCode::UInt8:
            return ConstantInt::get(Type::getInt8Ty(getGlobalContext()), v);
        default:
            printf("Unknown unsigned-int type %s\n", BuiltInTypeNames[int(type)]);
            return 0;
    }
}
Value* create_int_value(int64_t v, TypeCode type)
{
    switch (type) {
        case TypeCode::Int64:
            return ConstantInt::getSigned(Type::getInt64Ty(getGlobalContext()), v);
        case TypeCode::Int32:
            return ConstantInt::getSigned(Type::getInt32Ty(getGlobalContext()), v);
        case TypeCode::Int16:
            return ConstantInt::getSigned(Type::getInt16Ty(getGlobalContext()), v);
        case TypeCode::Int8:
            return ConstantInt::getSigned(Type::getInt8Ty(getGlobalContext()), v);
        default:
            printf("Unknown signed-int type %s\n", BuiltInTypeNames[int(type)]);
            return 0;
    }
}

template <class C>
Value* CodegenBody(C body) {
    const ast_node& n = source(body);
    if (n.Type == AstType::Number) {
        if (n.TCode == TypeCode::Int32) {
            return create_int_value(n.IVal, n.TCode);
        } else {
            return ConstantFP::get(getGlobalContext(), APFloat(n.Val));
        }
    } else if (n.Type == AstType::Variable) {
        // Look this variable up in the function.
        Value *V = NamedValues[n.Name];
        return V;
    } else if (n.Type == AstType::Binary) {
        C lhs = left_successor(body);
        C rhs = right_successor(body);

        Value* L = CodegenBody(lhs);
        Value* R = CodegenBody(rhs);

        if (L == 0 || R == 0) return 0;

        if (n.TCode == TypeCode::Int32) {
            switch (n.Op) {
                case '+': return Builder.CreateAdd(L, R, "addtmp");
                case '-': return Builder.CreateSub(L, R, "subtmp");
                case '*': return Builder.CreateMul(L, R, "multmp");
                case '/': return Builder.CreateSDiv(L, R, "divtmp");
                case '<':
                        L = Builder.CreateICmpULT(L, R, "cmptmp");
                        // Convert bool 0/1 to double 0.0 or 1.0
                        return Builder.CreateUIToFP(L, Type::getDoubleTy(getGlobalContext()),
                                "booltmp");
                //default: return ErrorV("invalid binary operator");
            }
        }
        else {
            switch (n.Op) {
                case '+': return Builder.CreateFAdd(L, R, "addtmp");
                case '-': return Builder.CreateFSub(L, R, "subtmp");
                case '*': return Builder.CreateFMul(L, R, "multmp");
                case '/': return Builder.CreateFDiv(L, R, "divtmp");
                case '<':
                        L = Builder.CreateFCmpULT(L, R, "cmptmp");
                        // Convert bool 0/1 to double 0.0 or 1.0
                        return Builder.CreateUIToFP(L, Type::getDoubleTy(getGlobalContext()),
                                "booltmp");
                //default: return ErrorV("invalid binary operator");
            }
        } 

    } else if (n.Type == AstType::Call) {
        C args = right_successor(body);

        const ast_node& name = source(left_successor(body));

        // Look up the name in the global module table.
        Function *CalleeF = TheModule->getFunction(name.Name);
        if (CalleeF == 0)
            return 0;
            //return ErrorV("Unknown function referenced");
        
        // If argument mismatch error.
        //if (CalleeF->arg_size() != Args.size())
            //return 0;
            //return ErrorV("Incorrect # arguments passed");

        std::vector<Value*> ArgsV;

        C it = args;
        while (!empty(it)) {
            //std::cerr << "test...\n";
            Value* v = CodegenBody(left_successor(it));
            ArgsV.push_back(v);
            it = right_successor(it);
        }
        
        return Builder.CreateCall(CalleeF, ArgsV, "calltmp");

    }
    return 0;
}

template <class C>
void CodegenFunction(C proto, C body) {
    NamedValues.clear();
    NamedTypes.clear();

    Function *TheFunction = CodegenPrototype(proto);

    BasicBlock *BB = BasicBlock::Create(getGlobalContext(), "entry", TheFunction);
    Builder.SetInsertPoint(BB);

    if (Value* RetVal = CodegenBody(body)) {
        // Finish off the function.
        Builder.CreateRet(RetVal);
        // Validate the generated code, checking for consistency.
        verifyFunction(*TheFunction);

        TheFPM->run(*TheFunction);
    }
}

template <class C>
StructType* CodegenTypeDef(C type) {
    const ast_node& n = source(type);
    assert(n.Type == AstType::Struct);

    std::vector<Type*> params(n.TypeCodes.size());
    std::transform(std::begin(n.TypeCodes), std::end(n.TypeCodes), std::begin(params), ConvertType);

    StructType* T = StructType::create(params, n.Name);
    UserTypes[n.Name] = T;
    CodedTypes[TypeCode(100)] = T;
    return T;
}

template <class C>
struct printer {
    void operator()(visit v, C c, int depth) {
        const int depth_mul = 4;
        if (v == pre) {
            std::string indent(size_t(depth*depth_mul), ' ');
            const ast_node& n = source(c);
            std::cerr << indent << "Node: " << AstTypesNames[int(n.Type)] << "\n";
            std::cerr << indent << "Type: " << n.TCode << "\n";
            if (n.Type == AstType::Variable || n.Type == AstType::Param) {
                std::cerr << indent << "Name: " << n.Name << "\n";
            } else if (n.Type == AstType::Number) {
                std::cerr << indent << "Val: " << n.Val << "\n";
            } else if (n.Type == AstType::Struct) {
                std::cerr << indent << "Name: " << n.Name << "\n";
                std::string indent(size_t((depth+2)*depth_mul), ' ');
                for (int i = 0; i < n.Args.size(); ++i) {
                    std::cerr << indent << "Name: " << n.Args[i] << "\n";
                    std::cerr << indent << "Type: " << n.TypeCodes[i] << "\n";
                }
            } else if (n.Type == AstType::Binary) {
                std::cerr << indent << "Op: " << n.Op << "\n";
            }
            std::cerr << "\n";
        }
    }
};

template <class C>
struct type_inference {
    void operator()(visit v, C c, int depth) {
        const ast_node& n = source(c);

        if (v == post && n.Type == AstType::Function) {
            C l = left_successor(c);
            // move prototype typename up to function
            sink(c).TCode = source(l).TCode;
        }
        else if (v == pre && n.Type == AstType::Prototype) {
            size_t len = n.Args.size();
            size_t i = 0;
            while (i < len) {
                NamedTypes[n.Args[i]] = n.TypeCodes[i];
                ++i;
            }
        }
        else if (v == post && n.Type == AstType::Variable) {
            sink(c).TCode = NamedTypes[n.Name];
        }
        else if (v == post && n.Type == AstType::Binary) {
            C l = left_successor(c);
            C r = right_successor(c);
            if (source(l).TCode == source(r).TCode) {
                sink(c).TCode = source(l).TCode;
            } else {
                if (source(l).TCode == TypeCode::Int32 
                 && source(r).TCode == TypeCode::Float64) {
                    sink(l).TCode = TypeCode::Float64;
                    sink(l).Val = source(l).IVal;
                    sink(c).TCode = TypeCode::Float64;
                } else if (source(l).TCode == TypeCode::Float64
                        && source(r).TCode == TypeCode::Int32) {
                    sink(r).TCode = TypeCode::Float64;
                    sink(r).Val = source(r).IVal;
                    sink(c).TCode = TypeCode::Float64;
                } 
            }
        }
    }
};

template <class C>
void TypeInference(C root) {
    std::cerr << "========================\n";
    traverse(root, type_inference<C>());
}

template <class C>
void Show(C root) {
    traverse(root, printer<C>());
}

template <class C>
void Codegen(C root) {
    const ast_node& n = source(root);

    for (auto& c : NamedTypes) {
        std::cerr << c.first << " => " << c.second << "\n";
    }

    if (n.Type == AstType::Function) {
        C proto = left_successor(root);
        C body  = right_successor(root);
        TypeInference(root);
        CodegenFunction(proto, body);
    }
}

//===----------------------------------------------------------------------===//
// Top-Level parsing and JIT Driver
//===----------------------------------------------------------------------===//

static void HandleDefinition() {
    using C = tree_coordinate<ast_node>;
    tree<ast_node> ast = ParseDefinition();
    C root = begin(ast);
    Codegen(root);
    //Show(root);
}

static void HandleTypeDef() {
    using C = tree_coordinate<ast_node>;
    tree<ast_node> ast_struct = ParseTypeDef();
    //Show(begin(ast_struct));
    Type* type = CodegenTypeDef(begin(ast_struct));
}

/*
static void HandleExtern() {
  if (PrototypeAST *P = ParseExtern()) {
    if (Function *F = P->Codegen()) {
      //F->dump();
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}

static void HandleTopLevelExpression() {
  // Evaluate a top-level expression into an anonymous function.
  if (FunctionAST *F = ParseTopLevelExpr()) {
    if (Function *LF = F->Codegen()) {
      //fprintf(stderr, "Read top-level expression:");
      //LF->dump();
    }
  } else {
    // Skip token for error recovery.
    getNextToken();
  }
}
*/

/// top ::= definition | external | expression | ';'
static void MainLoop() {
    while (1) {
        switch (CurTok) {
            case tok_eof:  return;
            case tok_def:  HandleDefinition(); break;
            case tok_type: HandleTypeDef(); break;
    //    case tok_extern: HandleExtern(); break;
    //    default:         HandleTopLevelExpression(); break;
            default: std::cout << CurTok << "\n";
                     if (CurTok == tok_identifier) {
                         std::cout << IdentifierStr << "\n";
                     }
        }
    }
}

static int MarpaParser() {
    using rule = marpa::grammar::rule_id;

    marpa::grammar g;

    marpa::grammar::symbol_id R_top   = g.new_symbol();
    marpa::grammar::symbol_id R_top_0 = g.new_symbol();

    marpa::grammar::symbol_id R_definition = g.new_symbol();
    marpa::grammar::symbol_id R_typedef    = g.new_symbol();
    marpa::grammar::symbol_id R_funcdef    = g.new_symbol();
    marpa::grammar::symbol_id R_expression = g.new_symbol();

    marpa::grammar::symbol_id R_function  = g.new_symbol();
    marpa::grammar::symbol_id R_prototype = g.new_symbol();
    marpa::grammar::symbol_id R_body      = g.new_symbol();
    marpa::grammar::symbol_id R_params    = g.new_symbol();
    marpa::grammar::symbol_id R_param     = g.new_symbol();

    marpa::grammar::symbol_id R_identifierexpr = g.new_symbol();
    marpa::grammar::symbol_id R_numberexpr = g.new_symbol();
    marpa::grammar::symbol_id R_parenexpr  = g.new_symbol();

    marpa::grammar::symbol_id R_term   = g.new_symbol();
    marpa::grammar::symbol_id R_factor = g.new_symbol();

    // [a-z]+
    marpa::grammar::symbol_id T_id   = g.new_symbol();
    // [0-9]+
    marpa::grammar::symbol_id T_num  = g.new_symbol();
    // left/right parent ()
    marpa::grammar::symbol_id T_lp   = g.new_symbol();
    marpa::grammar::symbol_id T_rp   = g.new_symbol();
    // left/right curly {}
    marpa::grammar::symbol_id T_lc   = g.new_symbol();
    marpa::grammar::symbol_id T_rc   = g.new_symbol();
    // 'type'
    marpa::grammar::symbol_id T_type = g.new_symbol();
    // 'struct'
    marpa::grammar::symbol_id T_struct = g.new_symbol();
    // 'func'
    marpa::grammar::symbol_id T_func = g.new_symbol();
    // 'def'
    marpa::grammar::symbol_id T_def  = g.new_symbol();

    // operators
    marpa::grammar::symbol_id T_assign = g.new_symbol();
    marpa::grammar::symbol_id T_plus = g.new_symbol();
    marpa::grammar::symbol_id T_min  = g.new_symbol();
    marpa::grammar::symbol_id T_mul  = g.new_symbol();
    marpa::grammar::symbol_id T_div  = g.new_symbol();
    marpa::grammar::symbol_id T_mod  = g.new_symbol();

    marpa::grammar::symbol_id T_semicolon = g.new_symbol();
    marpa::grammar::symbol_id T_comma = g.new_symbol();

    g.start_symbol(R_top);

    // top   ::= top_0+ ';'
    // top_0 ::= definition
    // top_0 ::= typedef
    rule rule_id_top   = g.new_sequence(R_top, R_top_0, -1, 1, 0);
    rule rule_id_top_0_0 = g.add_rule(R_top_0, { R_definition });
    rule rule_id_top_0_1 = g.add_rule(R_top_0, { R_funcdef });

    // funcdef ::= func id prototype id body
    rule rule_id_funcdef   = g.add_rule(R_funcdef, { T_func, T_id, R_prototype, T_id, R_body });
    // prototype ::= "(" params ")"
    rule rule_id_prototype = g.add_rule(R_prototype, { T_lp, R_params, T_rp });
    // params ::= param* ","
    rule rule_id_params    = g.new_sequence(R_params, R_param, T_comma, 0, 0);
    // param   ::= id id
    rule rule_id_param     = g.add_rule(R_param, { T_id, T_id });
    // body   ::= "{" "}"
    rule rule_id_body_0 = g.add_rule(R_body, { T_lc, T_rc });
    rule rule_id_body_1 = g.add_rule(R_body, { T_lc, R_expression, T_rc });

    rule rule_id_expression_0 = g.add_rule(R_expression, { R_term });
    rule rule_id_expression_1 = g.add_rule(R_expression, { R_expression, T_plus, R_term });
    rule rule_id_expression_2 = g.add_rule(R_expression, { R_expression, T_min,  R_term });

    rule rule_id_term_0       = g.add_rule(R_term,       { R_factor });
    rule rule_id_term_1       = g.add_rule(R_term,       { R_term, T_mul, R_factor });
    rule rule_id_term_2       = g.add_rule(R_term,       { R_term, T_div, R_factor });
    rule rule_id_term_3       = g.add_rule(R_term,       { R_term, T_mod, R_factor });

    rule rule_id_factor_0     = g.add_rule(R_factor,     { T_num });
    rule rule_id_factor_1     = g.add_rule(R_factor,     { T_id });
    //rule rule_id_factor_2     = g.add_rule(R_factor,     { T_id });

    if (g.precompute() < 0) {}

    marpa::recognizer r{g};

    indexed_table<std::string> identifiers;
    indexed_table<double>      numbers;

    while (1) {
        int t = CurTok;
        /*
        std::cout << t << char(t) << "\n";
        if (t == tok_identifier) {
            std::cout << "id: " << IdentifierStr << "\n";
        }
        */
        if (t == tok_eof) break;
        else if (t == tok_def) {
            r.read(T_func, 1, 1);
        }
        else if (t == tok_extern) {
            std::cerr << "extern token found - not implemented\n";
            return 1;
        }
        else if (t == tok_identifier) {
            int x = identifiers.add(IdentifierStr);
            r.read(T_id, x, 1);
        }
        else if (t == tok_number) {
            int x = numbers.add(NumVal);
            r.read(T_num, x, 1);
        }
        else if (t == tok_integer) {
            int x = IntVal;
            r.read(T_num, x, 1);
        }
        else if (t == tok_struct) {
            r.read(T_struct, 1, 1);
        }
        else if (t == tok_type) {
            r.read(T_type, 1, 1);
        }
        else if (t == '(') r.read(T_lp, 1, 1);
        else if (t == ')') r.read(T_rp, 1, 1);
        else if (t == '{') r.read(T_lc, 1, 1);
        else if (t == '}') r.read(T_rc, 1, 1);
        else if (t == '=') r.read(T_assign, 1, 1);
        else if (t == '+') r.read(T_plus, 1, 1);
        else if (t == '-') r.read(T_min, 1, 1);
        else if (t == '*') r.read(T_mul, 1, 1);
        else if (t == '/') r.read(T_div, 1, 1);
        else if (t == '%') r.read(T_mod, 1, 1);
        else if (t == ';') r.read(T_semicolon, 1, 1);
        else if (t == ',') r.read(T_comma, 1, 1);
        else {
            std::cerr << "Unknown token\n";
        }

        getNextToken();
    }

    marpa::bocage b{r, r.latest_earley_set()};
    if (g.error() != MARPA_ERR_NONE) {
        std::cerr << marpa_errors[g.error()] << "\n";
        return 1;
    }

    marpa::order o{b};
    marpa::tree t{o};

    /* Evaluate trees */
    while (t.next() >= 0) {
        marpa::value v{t};
        g.set_valued_rules(v);

        std::vector<int> stack;
        stack.resize(128);

        std::vector<tree<ast_node>> tree_stack;
        tree_stack.resize(128);

        for (;;) {
            marpa::value::step_type type = v.step();

            switch (type) {
                case MARPA_STEP_INITIAL:
                    //stack.resize(1);
                    break;
                case MARPA_STEP_TOKEN: {
                    //stack.resize(std::max((std::vector<int>::size_type)v.result()+1, stack.size()));
                    stack[v.result()] = v.token_value();
                    break;
                }
                case MARPA_STEP_RULE: {
                    marpa::grammar::rule_id rule = v.rule();
                    //stack.resize(std::max((std::vector<int>::size_type)v.result()+1, stack.size()));

                    if (rule == rule_id_top) {}
                    else if (rule == rule_id_top_0_0) {}
                    else if (rule == rule_id_top_0_1) {}
                    else if (rule == rule_id_funcdef) {
                        using Tree = tree<ast_node>;
                        using C = tree_coordinate<ast_node>;
                        std::cerr << "func definition\n";

                        int name_value = stack[v.arg_0() + 1];
                        //int proto_value = stack[v.arg_0() + 2];
                        int ret_type_value = stack[v.arg_0() + 3];
                        //int body_value = stack[v.arg_0() + 4];

                        std::string name = identifiers[name_value];
                        std::string type = identifiers[ret_type_value];

                        std::cerr << "func def " << name << " ret type " << type << "\n";
                        Tree proto = tree_stack[v.arg_0()+2];
                        Tree body  = tree_stack[v.arg_0()+4];
                        std::cerr << "func body\n";
                        Show(begin(body));
                        std::cerr << "end of body\n";

                        ast_node f{AstType::Function};
                        ast_node prototype{AstType::Prototype};

                        prototype.Name = name;
                        prototype.TCode = BuiltInToTypecode(type.c_str());

                        std::vector<std::string> ArgNames;
                        std::vector<TypeCode>    TypeCodes;

                        C it = begin(proto);
                        while (!empty(it)) {
                            ast_node param = source(it);
                            ArgNames.push_back(param.Name);
                            TypeCodes.push_back(param.TCode);
                            it = right_successor(it);
                        }

                        prototype.Args = ArgNames;
                        prototype.TypeCodes = TypeCodes;

                        Tree p{prototype};
                        Tree func_def{f, p, body};

                        C root = begin(func_def);
                        Show(root);
                        Codegen(root);

                        tree_stack[v.result()] = func_def;

                    }
                    else if (rule == rule_id_prototype) {
                        std::cerr << "prototype\n";
                        tree_stack[v.result()] = tree_stack[v.arg_0()+1];
                    }
                    else if (rule == rule_id_params) {
                        using C = tree_coordinate<ast_node>;
                        using Tree = tree<ast_node>;
                        using Cons = tree_node_construct<ast_node>;

                        Cons construct_node;

                        std::cerr << "params\n";

                        ast_node comma{AstType::Comma};

                        Tree params{comma};
                        C it = begin(params);

                        auto first = tree_stack.begin() + v.arg_0();
                        auto last  = tree_stack.begin() + v.arg_n()+1;

                        while (first != last) {
                            sink(it) = source(begin(*first));
                            ////insert_left(it, begin(*first));

                            ++first;

                            if (first == last) break;

                            set_right_successor(it, construct_node(comma));
                            it = right_successor(it);

                            ++first;
                        }

                        Show(begin(params));

                        tree_stack[v.result()] = params;
                    }
                    else if (rule == rule_id_param) {
                        int id_value   = stack[v.arg_0()];
                        int type_value = stack[v.arg_0()+1];

                        std::string id   = identifiers[id_value];
                        std::string type = identifiers[type_value];

                        ast_node param{AstType::Param};
                        param.TCode = BuiltInToTypecode(type.c_str());
                        param.Name  = id;
                        std::cerr << "param id = " << id << ", type = " << type << "\n";
                        tree_stack[v.result()] = tree<ast_node>(param);
                    }
                    else if (rule == rule_id_body_0) {
                        std::cerr << "body 0\n";
                        tree_stack[v.result()] = tree<ast_node>();
                    }
                    else if (rule == rule_id_body_1) {
                        std::cerr << "body 1\n";
                        tree_stack[v.result()] = tree_stack[v.arg_0()+1];
                    }
                    else if (rule == rule_id_expression_0) {
                        std::cerr << "expression 0\n";
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                    else if (rule == rule_id_expression_1) { // expr ::= expr + term
                        std::cerr << "expression 1\n";
                        using Tree = tree<ast_node>;
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '+';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_expression_2) { // expr ::= expr - term
                        std::cerr << "expression 2\n";
                        using Tree = tree<ast_node>;
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '-';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_term_0) {
                        std::cerr << "term 0\n";
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                    else if (rule == rule_id_term_1) { // term ::= term * factor
                        std::cerr << "term 1\n";
                        using Tree = tree<ast_node>;
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '*';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_term_2) { // term ::= term / factor
                        std::cerr << "term 1\n";
                        using Tree = tree<ast_node>;
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '/';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_term_3) { // term ::= term % factor
                        std::cerr << "term 1\n";
                        using Tree = tree<ast_node>;
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '%';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_factor_0) {
                        using Tree = tree<ast_node>;
                        std::cerr << "factor 0\n";
                        double val = numbers[stack[v.arg_0()]];
                        Tree x{ast_node{val}};
                        tree_stack[v.result()] = x;
                    }
                    else if (rule == rule_id_factor_1) {
                        using Tree = tree<ast_node>;
                        std::cerr << "factor 1\n";
                        std::string val = identifiers[stack[v.arg_0()]];
                        Tree x{ast_node{val}};
                        tree_stack[v.result()] = x;
                    }
                }
                case MARPA_STEP_NULLING_SYMBOL: {
                    int res    = v.result();
                    // put some value here
                    stack[res] = v.token_value(); 
                    break;
                }
                case MARPA_STEP_INACTIVE:
                    goto END;
            }
        }
        END: ;
    }
    return 0;
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main(int argc, char** argv) {
    InitializeNativeTarget();
    InitializeNativeTargetAsmPrinter();
    //InitializeNatureTargetAsmParser();
    //
    ForcePassLinking::ForcePassLinking();

    LLVMContext &Context = getGlobalContext();

    // Install standard binary operators.
    // 1 is lowest precedence.
    BinopPrecedence['<'] = 10;
    BinopPrecedence['+'] = 20;
    BinopPrecedence['-'] = 20;
    BinopPrecedence['*'] = 40;  // highest.
    BinopPrecedence['/'] = 40;  // highest.

    // Prime the first token.
    getNextToken();

    // Make the module, which holds all the code.
    TheModule = new Module("test.toy", Context);

    // Now we going to create JIT
    std::string errStr;

    ExecutionEngine *engine =
        EngineBuilder(std::move(TheModule))
        .setErrorStr(&errStr)
        .setUseMCJIT(true)
        //.setEngineKind(EngineKind::JIT)
        .create();

    if (!engine) {
        errs() << argv[0] << ": Failed to construct ExecutionEngine: " << errStr
            << "\n";
        return 1;
    }

    FunctionPassManager OurFPM(TheModule);

    //OurFPM.add(new DataLayoutPass());

    // Set up the optimizer pipeline.  Start with registering info about how the
    // target lays out data structures.
    // OurFPM.add(new DataLayout(*TheExecutionEngine->getDataLayout()));
    // Provide basic AliasAnalysis support for GVN.
    OurFPM.add(createBasicAliasAnalysisPass());
    // Promote allocas to registers.
    OurFPM.add(createPromoteMemoryToRegisterPass());
    // Do simple "peephole" optimizations and bit-twiddling optzns.
    OurFPM.add(createInstructionCombiningPass());
    // Reassociate expressions.
    OurFPM.add(createReassociatePass());
    // Eliminate Common SubExpressions.
    OurFPM.add(createGVNPass());
    // Simplify the control flow graph (deleting unreachable blocks, etc).
    OurFPM.add(createCFGSimplificationPass());

    OurFPM.doInitialization();

    // Set the global so the code gen can use this.
    TheFPM = &OurFPM;

    // Run the main "interpreter loop" now.
    //MainLoop();
    int ret = MarpaParser();
    if (ret) {
        return ret;
    }

    // For each function in the module
    Module::iterator it;
    Module::iterator end = TheModule->end();
    for (it = TheModule->begin(); it != end; ++it) {
      // Run the FPM on this function
      TheFPM->run(*it);
    }

    verifyModule(*TheModule, &outs());

    /*
    typedef double (*test_add_1_times_2)(double t);
    test_add_1_times_2 fptr = (test_add_1_times_2)engine->getPointerToFunction(
            TheModule->getFunction("test_add_1_times_2"));
    std::cerr << fptr(10.0) << "\n";
    */

    // Print out all of the generated code.
    raw_fd_ostream out{1, false, false};
    TheModule->print(out, 0);

    delete TheModule;

    return 0;
}
