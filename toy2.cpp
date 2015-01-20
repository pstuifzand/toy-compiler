#include "llvm/ADT/Triple.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/SectionMemoryManager.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/PassManager.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Transforms/Scalar.h"
#include <iostream>
#include <cctype>
#include <cstdio>
#include <unordered_map>
#include <string>
#include <vector>
#include <algorithm>

#include "tree.hpp"

using namespace llvm;

enum class NodeType {
    Error,
    Number,
    Variable,
    Binary,
    Call,
    Comma,
    Prototype,
    Function,
};

const char* NodeTypesNames[] = {
    "Error",
    "Number",
    "Variable",
    "Binary",
    "Call",
    "Comma",
    "Prototype",
    "Function",
};

enum class TypeCode {
    Unknown_Type,
    Int8,
    Int16,
    Int32,
    Int64,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Float32,
    Float64,
    MaxBuiltIn,
};

const char* BuiltInTypeNames[] = {
    "Unknown Type",
    "Int8",
    "Int16",
    "Int32",
    "Int64",
    "UInt8",
    "UInt16",
    "UInt32",
    "UInt64",
    "Float32",
    "Float64",
};

struct less_cstring {
    bool operator()(const char* a, const char* b) {
        return strcmp(a, b) < 0;
    }
};

template <class I, class P>
I find(I first, I last, const char* x, P pred)
{
    while (first != last && !pred(x, *first)) {
        ++first;
    }
    return first;
}

TypeCode BuiltInToTypecode(const char* type_name)
{
    auto first = std::begin(BuiltInTypeNames);
    auto last  = std::end(BuiltInTypeNames);
    auto it = find(first, last, type_name, less_cstring());
    if (it != last) {
        int count = std::distance(first, it);
        return TypeCode(count);
    }
    return TypeCode(0);
}

struct node {
    NodeType Type;
    double   Val;
    int      IVal;
    char     Op;
    std::string Name;
    std::string Typename;
    std::vector<std::string> Args;
    std::vector<std::string> Types;
};

//===----------------------------------------------------------------------===//
// Lexer
//===----------------------------------------------------------------------===//

// The lexer returns tokens [0-255] if it is an unknown character, otherwise one
// of these for known things.
enum Token {
  tok_eof = -1,

  // commands
  tok_def = -2,
  tok_extern = -3,

  // primary
  tok_identifier = -4,
  tok_number = -5,
  tok_integer = -6,
};

static std::string IdentifierStr;  // Filled in if tok_identifier
static double      NumVal;         // Filled in if tok_number
static int32_t     IntVal;

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
tree<node> Error(const char *Str) {
    printf("Error: %d: \"%c\" %s\n", line, CurTok, Str);
    node n;
    n.Type = NodeType::Error;
    tree<node> err{n};
    return err;
}

static tree<node> ParseExpression();

/// identifierexpr
///   ::= identifier
///   ::= identifier '(' expression* ')'
static tree<node> ParseIdentifierExpr() {
    typedef tree_coordinate<node> C;
    typedef tree_node_construct<node> Cons;

    std::string IdName = IdentifierStr;

    node identifier;
    identifier.Type = NodeType::Variable;
    identifier.Name = IdName;
    getNextToken(); // consume the number

    tree<node> id = tree<node>{identifier};
    if (CurTok != '(') return id;

    // Call.
    getNextToken();  // eat (

    node comma;
    comma.Type = NodeType::Comma;

    tree<node> args;

    Cons construct_node;

    if (CurTok != ')') {
        node comma;
        comma.Type = NodeType::Comma;

        C it;

        if (empty(args)) {
            args = tree<node>(comma);
            it = begin(args);
        }

        while (1) {
            tree<node> arg = ParseExpression();

            sink(it) = comma;
            set_left_successor(it, bifurcate_copy<C, Cons>(begin(arg)));
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

    node op;
    op.Type = NodeType::Call;
    op.Name = IdName;

    return tree<node>(op, id, args);
}

/// numberexpr ::= number
static tree<node> ParseNumberExpr() {
    node number;
    number.Type = NodeType::Number;
    number.Val = NumVal;
    number.Typename = "float64";
    getNextToken(); // consume the number
    return tree<node>{number};
}

/// numberexpr ::= int
static tree<node> ParseIntegerExpr() {
    node number;
    number.Type = NodeType::Number;
    number.IVal = IntVal;
    number.Typename = "i32";
    getNextToken(); // consume the number
    return tree<node>{number};
}

/// parenexpr ::= '(' expression ')'
static tree<node> ParseParenExpr() {
    getNextToken();  // eat (.

    tree<node> V = ParseExpression();

    if (CurTok != ')')
        return Error("expected ')'");
    getNextToken();  // eat ).
    return V;
}

/// primary
///   ::= identifierexpr
///   ::= numberexpr
///   ::= parenexpr
static tree<node> ParsePrimary() {
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
static tree<node> ParseBinOpRHS(int ExprPrec, tree<node> lhs) {
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
        tree<node> rhs = ParsePrimary();

        int NextPrec = GetTokPrecedence();

        if (TokPrec < NextPrec) {
            rhs = ParseBinOpRHS(TokPrec+1, rhs);
            if (empty(rhs)) {
                printf("%d: ERRROR\n", line);
                return rhs;
            }
        }

        node op;
        op.Type = NodeType::Binary;
        op.Op   = BinOp;
        lhs = tree<node>(op, lhs, rhs);
    }

    return lhs;
}

/// expression
///   ::= primary binoprhs
///
static tree<node> ParseExpression() {
    tree<node> LHS = ParsePrimary();
    return ParseBinOpRHS(0, LHS);
}

/// prototype
///   ::= id '(' id* ')'
static tree<node> ParsePrototype() {
    //  if (CurTok != tok_identifier)
    //    return ErrorP("Expected function name in prototype");

    std::string FnName = IdentifierStr;
    getNextToken();

    //  if (CurTok != '(')
    //    return ErrorP("Expected '(' in prototype");

    Match('(');
    std::vector<std::string> ArgNames;
    std::vector<std::string> TypeNames;
    while (CurTok != ')') {
        if (CurTok != tok_identifier) Error("need parameter name");
        ArgNames.push_back(IdentifierStr);
        getNextToken();
        if (CurTok == tok_identifier) {
            TypeNames.push_back(IdentifierStr);
            getNextToken();
        } else {
            // default type is double
            TypeNames.push_back("float64");
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

    node proto;
    proto.Type = NodeType::Prototype;
    proto.Name = FnName;
    proto.Args = ArgNames;
    proto.Types = TypeNames;
    proto.Typename = return_type;
    return tree<node>{proto};
}

/// definition ::= 'def' prototype expression
static tree<node> ParseDefinition() {
    getNextToken();  // eat def.
    node top;
    top.Type = NodeType::Function;
    tree<node> proto = ParsePrototype();
    if (CurTok != '{') {
        printf("%d: ERROR missing {\n",line);
        return tree<node>();
    }
    getNextToken(); // '{'
    tree<node> expression = ParseExpression();
    if (CurTok == ';') getNextToken();

    if (CurTok != '}') {
        printf("%d: ERROR missing }\n",line);
        return tree<node>();
    }
    getNextToken(); // '}'
    tree<node> ast{top, proto, expression};
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
static std::unordered_map<std::string, Value*> NamedValues;
static std::unordered_map<std::string, std::string> NamedTypes;
static FunctionPassManager* TheFPM;

Type* ConvertType(const std::string& type_name)
{
    if (type_name == "double" || type_name == "float64") {
        return Type::getDoubleTy(getGlobalContext());
    } else if (type_name == "i32") {
        return Type::getInt32Ty(getGlobalContext());
    }
    return Type::getDoubleTy(getGlobalContext());
}

template <class C>
Function* CodegenProto(C proto)
{
    const node& n = source(proto);

    // Make the function type:  double(double,double) etc.
    size_t len = n.Args.size();
    size_t i = 0;

    std::vector<Type*> params(n.Args.size());
    while (i < len) {
        Type* type = ConvertType(n.Types[i]);
        params[i] = type;
        ++i;
    }

    Type* return_type = ConvertType(n.Typename);

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
        NamedTypes[n.Args[Idx]]  = n.Types[Idx];
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
            printf("Unknown signed-int type %s\n", BuiltInTypeNames[int(type)]);
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
    const node& n = source(body);
    if (n.Type == NodeType::Number) {
        if (n.Typename == "i32") {
            return create_int_value(n.IVal, TypeCode::Int32);
        } else {
            return ConstantFP::get(getGlobalContext(), APFloat(n.Val));
        }
    } else if (n.Type == NodeType::Variable) {
        // Look this variable up in the function.
        Value *V = NamedValues[n.Name];
        return V;
    } else if (n.Type == NodeType::Binary) {
        C lhs = left_successor(body);
        C rhs = right_successor(body);

        Value* L = CodegenBody(lhs);
        Value* R = CodegenBody(rhs);

        if (L == 0 || R == 0) return 0;

        if (n.Typename == "i32") {
            switch (n.Op) {
                case '+': return Builder.CreateAdd(L, R, "addtmp");
                case '-': return Builder.CreateSub(L, R, "subtmp");
                case '*': return Builder.CreateMul(L, R, "multmp");
                case '/': return Builder.CreateSDiv(L, R, "divtmp");
                case '<':
                        L = Builder.CreateFCmpULT(L, R, "cmptmp");
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

    } else if (n.Type == NodeType::Call) {
        C args = right_successor(body);

        const node& name = source(left_successor(body));

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
            std::cout << "test...\n";
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

    Function *TheFunction = CodegenProto(proto);

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
struct type_inference {
    void operator()(visit v, C c) {
        const node& n = source(c);

        if (v == pre) {
            std::cout << "Pre[\n";
            std::cout << "  Node: " << NodeTypesNames[int(source(c).Type)] << "\n";
            std::cout << "  Type: " << source(c).Typename << "\n";
            if (n.Type == NodeType::Variable) {
                std::cout << "  Name: " << source(c).Name << "\n";
            }
            std::cout << "]\n";
        }

        if (v == post && n.Type == NodeType::Function) {
            C l = left_successor(c);
            // move prototype typename up to function
            sink(c).Typename = source(l).Typename;
        }
        else if (v == pre && n.Type == NodeType::Prototype) {
            size_t len = n.Args.size();
            size_t i = 0;
            while (i < len) {
                NamedTypes[n.Args[i]] = n.Types[i];
                ++i;
            }
        }
        else if (v == post && n.Type == NodeType::Variable) {
            sink(c).Typename = NamedTypes[n.Name];
        }
        else if (v == post && n.Type == NodeType::Binary) {
            C l = left_successor(c);
            C r = right_successor(c);
            if (source(l).Typename == source(r).Typename) {
                std::cout << "Changing type from " << source(c).Typename << " to " << source(l).Typename << "\n";
                sink(c).Typename = source(l).Typename;
            } else {
                if (source(l).Typename == "i32" && source(r).Typename == "float64") {
                    std::cout << "Changing type from " << source(l).Typename << " to " << source(r).Typename << "\n";
                    sink(l).Typename = "float64";
                    sink(l).Val = source(l).IVal;
                    sink(c).Typename = "float64";
                } else if (source(l).Typename == "float64" && source(r).Typename == "i32") {
                    std::cout << "Changing type from " << source(r).Typename << " to " << source(l).Typename << "\n";
                    sink(r).Typename = "float64";
                    sink(r).Val = source(r).IVal;
                    sink(c).Typename = "float64";
                } 
            }
        }

        if (v == post) {
            std::cout << "Post[\n";
            std::cout << "  Node: " << NodeTypesNames[int(source(c).Type)] << "\n";
            std::cout << "  Type: " << source(c).Typename << "\n";
            if (n.Type == NodeType::Variable) {
                std::cout << "  Name: " << source(c).Name << "\n";
            }
            std::cout << "]\n";
        }
    }
};

template <class C>
void TypeInference(C root) {
    traverse(root, type_inference<C>());
}

template <class C>
void Codegen(C root) {
    const node& n = source(root);

    for (auto& c : NamedTypes) {
        std::cout << c.first << " => " << c.second << "\n";
    }

    if (n.Type == NodeType::Function) {
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
    using C = tree_coordinate<node>;

    tree<node> ast = ParseDefinition();

    C root = begin(ast);
    Codegen(root);
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
            case tok_eof:    return;
            case tok_def:    HandleDefinition(); break;
    //    case tok_extern: HandleExtern(); break;
    //    default:         HandleTopLevelExpression(); break;
        }
    }
}

//===----------------------------------------------------------------------===//
// Main driver code.
//===----------------------------------------------------------------------===//

int main() {
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

    FunctionPassManager OurFPM(TheModule);

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
    MainLoop();

    // For each function in the module
    Module::iterator it;
    Module::iterator end = TheModule->end();
    for (it = TheModule->begin(); it != end; ++it) {
      // Run the FPM on this function
      TheFPM->run(*it);
    }

  // Print out all of the generated code.
  TheModule->dump();

  return 0;
}
