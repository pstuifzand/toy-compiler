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

#include "codegen.hpp"
#include "eop-code/eop.h"
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
    "If",
    "Else",
    "Stmt",
    "Return",
    "Assignment",
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
    "void",
};

llvm::Type* convert_type(TypeCode type_code)
{
    // TODO uitbreiden
    if (type_code == TypeCode::Float64) {
        return llvm::Type::getDoubleTy(llvm::getGlobalContext());
    } else if (type_code == TypeCode::Float32) {
        return llvm::Type::getFloatTy(llvm::getGlobalContext());
    } else if (type_code == TypeCode::Int64) {
        return llvm::Type::getInt64Ty(llvm::getGlobalContext());
    } else if (type_code == TypeCode::Int32) {
        return llvm::Type::getInt32Ty(llvm::getGlobalContext());
    } else if (type_code == TypeCode::Int16) {
        return llvm::Type::getInt16Ty(llvm::getGlobalContext());
    } else if (type_code == TypeCode::Int8) {
        return llvm::Type::getInt8Ty(llvm::getGlobalContext());
    } else if (type_code == TypeCode::Void) {
        return llvm::Type::getVoidTy(llvm::getGlobalContext());
    }

    // TODO error
    return llvm::Type::getDoubleTy(llvm::getGlobalContext());
}

llvm::Value* create_uint_value(uint64_t v, TypeCode type)
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

llvm::Value* create_int_value(int64_t v, TypeCode type)
{
    switch (type) {
        case TypeCode::Int64:
            return llvm::ConstantInt::getSigned(llvm::Type::getInt64Ty(llvm::getGlobalContext()), v);
        case TypeCode::Int32:
            return llvm::ConstantInt::getSigned(llvm::Type::getInt32Ty(llvm::getGlobalContext()), v);
        case TypeCode::Int16:
            return llvm::ConstantInt::getSigned(llvm::Type::getInt16Ty(llvm::getGlobalContext()), v);
        case TypeCode::Int8:
            return llvm::ConstantInt::getSigned(llvm::Type::getInt8Ty(llvm::getGlobalContext()), v);
        default:
            printf("Unknown signed-int type %s\n", BuiltInTypeNames[int(type)]);
            return 0;
    }
}

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

  tok_if         = -9,

  tok_return     = -10,

  tok_false      = -11,
  tok_true       = -12,

  tok_else       = -13,
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

    if (IdentifierStr == "def")    return tok_def;
    if (IdentifierStr == "func")   return tok_def;
    if (IdentifierStr == "type")   return tok_type;
    if (IdentifierStr == "struct") return tok_struct;
    if (IdentifierStr == "extern") return tok_extern;
    if (IdentifierStr == "if")     return tok_if;
    if (IdentifierStr == "else")   return tok_else;
    if (IdentifierStr == "return") return tok_return;
    if (IdentifierStr == "false")  return tok_false;
    if (IdentifierStr == "true")   return tok_true;
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
            } else if (n.Type == AstType::Number && n.TCode == TypeCode::Float64) {
                std::cerr << indent << "Val: " << n.Val << "\n";
            } else if (n.Type == AstType::Number && n.TCode == TypeCode::Int32) {
                std::cerr << indent << "IVal: " << n.IVal << "\n";
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
void Show(C root) {
    traverse(root, printer<C>());
}

//===----------------------------------------------------------------------===//
// Top-Level parsing and JIT Driver
//===----------------------------------------------------------------------===//

/// top ::= definition | external | expression | ';'

static int MarpaParser(llvm::Module* TheModule, llvm::FunctionPassManager* TheFPM) {
    using rule = marpa::grammar::rule_id;

    marpa::grammar g;

    marpa::grammar::symbol_id R_top   = g.new_symbol();
    marpa::grammar::symbol_id R_top_0 = g.new_symbol();

    marpa::grammar::symbol_id R_definition = g.new_symbol();
    marpa::grammar::symbol_id R_typedef    = g.new_symbol();
    marpa::grammar::symbol_id R_funcdef    = g.new_symbol();
    marpa::grammar::symbol_id R_expression = g.new_symbol();
    marpa::grammar::symbol_id R_semiopt   = g.new_symbol();

    marpa::grammar::symbol_id R_function  = g.new_symbol();
    marpa::grammar::symbol_id R_prototype = g.new_symbol();
    marpa::grammar::symbol_id R_body      = g.new_symbol();
    marpa::grammar::symbol_id R_params    = g.new_symbol();
    marpa::grammar::symbol_id R_param     = g.new_symbol();

    marpa::grammar::symbol_id R_args    = g.new_symbol();
    marpa::grammar::symbol_id R_arg     = g.new_symbol();

    marpa::grammar::symbol_id R_identifierexpr = g.new_symbol();
    marpa::grammar::symbol_id R_numberexpr = g.new_symbol();
    marpa::grammar::symbol_id R_parenexpr  = g.new_symbol();

    marpa::grammar::symbol_id R_term   = g.new_symbol();
    marpa::grammar::symbol_id R_factor = g.new_symbol();

    marpa::grammar::symbol_id R_compound          = g.new_symbol();
    marpa::grammar::symbol_id R_statements        = g.new_symbol();
    marpa::grammar::symbol_id R_statement         = g.new_symbol();

    marpa::grammar::symbol_id R_simple_statement  = g.new_symbol();
    marpa::grammar::symbol_id R_assignment        = g.new_symbol();
    marpa::grammar::symbol_id R_control_statement = g.new_symbol();

    marpa::grammar::symbol_id R_conditional       = g.new_symbol();
    marpa::grammar::symbol_id T_return            = g.new_symbol();

    marpa::grammar::symbol_id T_if     = g.new_symbol();
    marpa::grammar::symbol_id T_else   = g.new_symbol();

    // [a-z]+
    marpa::grammar::symbol_id T_id   = g.new_symbol();
    // [0-9]+
    marpa::grammar::symbol_id T_num  = g.new_symbol();
    marpa::grammar::symbol_id T_int  = g.new_symbol();
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

    marpa::grammar::symbol_id T_false = g.new_symbol();
    marpa::grammar::symbol_id T_true  = g.new_symbol();

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
    
    rule rule_id_body       = g.add_rule(R_body, { R_compound });
    rule rule_id_compound   = g.add_rule(R_compound, { T_lc, R_statements, T_rc });
    rule rule_id_statements = g.new_sequence(R_statements, R_statement, -1, 0, 0);

    rule rule_id_statement_0 = g.add_rule(R_statement, { R_simple_statement });
    rule rule_id_statement_1 = g.add_rule(R_statement, { R_control_statement });
    rule rule_id_statement_2 = g.add_rule(R_statement, { R_compound });
    rule rule_id_statement_3 = g.add_rule(R_statement, { R_assignment });

    rule rule_id_simple_statement    = g.add_rule(R_simple_statement, { R_expression, T_semicolon });
    rule rule_id_control_statement_0 = g.add_rule(R_control_statement, { R_conditional });
    rule rule_id_control_statement_1 = g.add_rule(R_control_statement, { T_return, R_expression, T_semicolon });
    rule rule_id_conditional_0       = g.add_rule(R_conditional, { T_if, T_lp, R_expression, T_rp, R_statement });
    rule rule_id_conditional_1       = g.add_rule(R_conditional, { T_if, T_lp, R_expression, T_rp, R_statement, T_else, R_statement });
    rule rule_id_assignment          = g.add_rule(R_assignment,  { R_expression, T_assign, R_expression, T_semicolon });

    rule rule_id_expression_0 = g.add_rule(R_expression, { R_term });
    rule rule_id_expression_1 = g.add_rule(R_expression, { R_expression, T_plus, R_term });
    rule rule_id_expression_2 = g.add_rule(R_expression, { R_expression, T_min,  R_term });

    rule rule_id_term_0       = g.add_rule(R_term,       { R_factor });
    rule rule_id_term_1       = g.add_rule(R_term,       { R_term, T_mul, R_factor });
    rule rule_id_term_2       = g.add_rule(R_term,       { R_term, T_div, R_factor });
    rule rule_id_term_3       = g.add_rule(R_term,       { R_term, T_mod, R_factor });

    rule rule_id_factor_0     = g.add_rule(R_factor,     { T_num });
    rule rule_id_factor_1     = g.add_rule(R_factor,     { T_int });
    rule rule_id_factor_2     = g.add_rule(R_factor,     { T_id });
    rule rule_id_factor_3     = g.add_rule(R_factor,     { T_id, T_lp, R_args, T_rp });
    rule rule_id_factor_4     = g.add_rule(R_factor,     { T_lp, R_expression, T_rp });
    rule rule_id_factor_5     = g.add_rule(R_factor,     { T_false });
    rule rule_id_factor_6     = g.add_rule(R_factor,     { T_true });

    rule rule_id_args         = g.new_sequence(R_args, R_arg, T_comma, 0, 0);
    rule rule_id_arg          = g.add_rule(R_arg, { R_expression });

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
            r.read(T_func, 1, 1, line);
        }
        else if (t == tok_extern) {
            std::cerr << "extern token found - not implemented\n";
            return 1;
        }
        else if (t == tok_identifier) {
            int x = identifiers.add(IdentifierStr);
            r.read(T_id, x, 1, line);
        }
        else if (t == tok_number) {
            int x = numbers.add(NumVal);
            r.read(T_num, x, 1, line);
        }
        else if (t == tok_integer) {
            int x = IntVal;
            r.read(T_int, x, 1, line);
        }
        else if (t == tok_struct) {
            r.read(T_struct, 1, 1, line);
        }
        else if (t == tok_type) {
            r.read(T_type, 1, 1, line);
        }
        else if (t == tok_if) {
            r.read(T_if, 1, 1, line);
        }
        else if (t == tok_else) {
            r.read(T_else, 1, 1, line);
        }
        else if (t == tok_return) {
            r.read(T_return, 1, 1, line);
        }
        else if (t == '(') r.read(T_lp, 1, 1, line);
        else if (t == ')') r.read(T_rp, 1, 1, line);
        else if (t == '{') r.read(T_lc, 1, 1, line);
        else if (t == '}') r.read(T_rc, 1, 1, line);
        else if (t == '=') r.read(T_assign, 1, 1, line);
        else if (t == '+') r.read(T_plus, 1, 1, line);
        else if (t == '-') r.read(T_min, 1, 1, line);
        else if (t == '*') r.read(T_mul, 1, 1, line);
        else if (t == '/') r.read(T_div, 1, 1, line);
        else if (t == '%') r.read(T_mod, 1, 1, line);
        else if (t == ';') r.read(T_semicolon, 1, 1, line);
        else if (t == ',') r.read(T_comma, 1, 1, line);
        //else if (t == '<') r.read(T_lt, 1, 1, line);
        //else if (t == '>') r.read(T_gt, 1, 1, line);
        else if (t == tok_false) r.read(T_false, 1, 1, line);
        else if (t == tok_true) r.read(T_true, 1, 1, line);
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

    using C = tree_coordinate<ast_node>;
    using Tree = tree<ast_node>;
    using Cons = tree_node_construct<ast_node>;

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
                        int name_value = stack[v.arg_0() + 1];
                        std::string name = identifiers[name_value];

                        Tree proto = tree_stack[v.arg_0()+2];

                        int ret_type_value = stack[v.arg_0() + 3];
                        std::string type = identifiers[ret_type_value];

                        Tree body  = tree_stack[v.arg_0()+4];

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
                        codegen(TheModule, TheFPM, root);
                        tree_stack[v.result()] = func_def;
                    }
                    else if (rule == rule_id_prototype) {
                        tree_stack[v.result()] = tree_stack[v.arg_0()+1];
                    }
                    else if (rule == rule_id_params) {

                        Cons construct_node;

                        ast_node comma{AstType::Comma};

                        Tree params{comma};
                        C it = begin(params);

                        auto first = tree_stack.begin() + v.arg_0();
                        auto last  = tree_stack.begin() + v.arg_n()+1;

                        while (first != last) {
                            sink(it) = source(begin(*first));
                            //insert_left(it, begin(*first));

                            ++first;

                            if (first == last) break;

                            set_right_successor(it, construct_node(comma));
                            it = right_successor(it);

                            ++first;
                        }
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
                        tree_stack[v.result()] = tree<ast_node>(param);
                    }
                    else if (rule == rule_id_body) {
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                    else if (rule == rule_id_compound) {
                        tree_stack[v.result()] = tree_stack[v.arg_0()+1];
                    }
                    else if (rule == rule_id_statements) {
                        // sequence
                        Cons construct_node;

                        ast_node stmt{AstType::Stmt};

                        Tree statements{stmt};
                        C it = begin(statements);

                        auto first = tree_stack.begin() + v.arg_0();
                        auto last  = tree_stack.begin() + v.arg_n()+1;

                        while (first != last) {
                            //sink(it) = source(begin(*first));
                            insert_left(it, begin(*first));
                            ++first;

                            if (first == last) break;
                            set_right_successor(it, construct_node(stmt));
                            it = right_successor(it);
                        }
                        tree_stack[v.result()] = statements;
                    }
                    else if (rule == rule_id_statement_0) {
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                    else if (rule == rule_id_statement_1) {
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                    else if (rule == rule_id_statement_2) {
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                    else if (rule == rule_id_statement_3) {
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                    else if (rule == rule_id_simple_statement) {
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                    else if (rule == rule_id_control_statement_0) {
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                    else if (rule == rule_id_control_statement_1) { // 'return' expr ';'
                        Tree expr = tree_stack[v.arg_0()+1];
                        Tree empty;
                        ast_node return_node{AstType::Return};
                        Tree return_tree{return_node, expr, empty};
                        tree_stack[v.result()] = return_tree;
                    }
                    else if (rule == rule_id_conditional_0) { // if '(' expr ')' stmt
                        Tree& cond  = tree_stack[v.arg_0()+2];
                        Tree& stmts = tree_stack[v.arg_0()+4];
                        ast_node if_node{AstType::If};
                        Tree if_tree{if_node, cond, stmts};
                        tree_stack[v.result()] = if_tree;
                    }
                    else if (rule == rule_id_conditional_1) { // if '(' expr ')' stmt 'else' stmt
                        Tree& cond  = tree_stack[v.arg_0()+2];
                        Tree& if_block = tree_stack[v.arg_0()+4];
                        Tree& else_block = tree_stack[v.arg_0()+6];
                        ast_node if_node{AstType::If};
                        ast_node else_node{AstType::Else};
                        Tree else_tree{else_node, if_block, else_block};
                        Tree if_tree{if_node, cond, else_tree};
                        tree_stack[v.result()] = if_tree;
                    }
                    else if (rule == rule_id_assignment) { // expr '=' expr
                        Tree& var_block = tree_stack[v.arg_0()];
                        Tree& val_block = tree_stack[v.arg_0()+2];
                        ast_node assign_node{AstType::Assignment};
                        Tree assign_tree{assign_node, var_block, val_block};
                        tree_stack[v.result()] = assign_tree;
                    }
                    else if (rule == rule_id_expression_0) {
                        Tree expr = tree_stack[v.arg_0()];
                        tree_stack[v.result()] = expr;
                    }
                    else if (rule == rule_id_expression_1) { // expr ::= expr + term
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '+';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_expression_2) { // expr ::= expr - term
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '-';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_term_0) {
                        Tree expr = tree_stack[v.arg_0()];
                        tree_stack[v.result()] = expr;
                    }
                    else if (rule == rule_id_term_1) { // term ::= term * factor
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '*';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_term_2) { // term ::= term / factor
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '/';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_term_3) { // term ::= term % factor
                        Tree l = tree_stack[v.arg_0()];
                        Tree r = tree_stack[v.arg_0()+2];
                        ast_node binop{AstType::Binary};
                        binop.Op = '%';
                        Tree op{binop, l, r};
                        tree_stack[v.result()] = op;
                    }
                    else if (rule == rule_id_factor_0) {
                        double val = numbers[stack[v.arg_0()]];
                        ast_node n{val};
                        Tree x{n};
                        tree_stack[v.result()] = x;
                    }
                    else if (rule == rule_id_factor_1) {
                        int val = stack[v.arg_0()];
                        ast_node n{val};
                        Tree x{n};
                        tree_stack[v.result()] = x;
                    }
                    else if (rule == rule_id_factor_2) {
                        std::string val = identifiers[stack[v.arg_0()]];
                        ast_node n{val};
                        Tree x{n};
                        tree_stack[v.result()] = x;
                    }
                    else if (rule == rule_id_factor_3) {
                        Cons construct_node;
                        std::string val = identifiers[stack[v.arg_0()]];
                        ast_node id{val};

                        Tree args = tree_stack[v.arg_0()+2];

                        ast_node call{AstType::Call};
                        call.Name = val;
                        Tree x{call, id, args};
                        tree_stack[v.result()] = x;
                    }
                    else if (rule == rule_id_factor_4) {
                        Tree r = tree_stack[v.arg_0()+1];
                        tree_stack[v.result()] = r;
                    }
                    else if (rule == rule_id_factor_5) { // false
                        Tree x{ast_node{0}};
                        tree_stack[v.result()] = x;
                    }
                    else if (rule == rule_id_factor_6) { // true
                        Tree x{ast_node{1}};
                        tree_stack[v.result()] = x;
                    }
                    else if (rule == rule_id_args) {
                        Cons construct_node;
                        ast_node comma{AstType::Comma};

                        Tree args{comma};
                        C it = begin(args);

                        auto first = tree_stack.begin() + v.arg_0();
                        auto last  = tree_stack.begin() + v.arg_n()+1;

                        while (first != last) {
                            insert_left(it, begin(*first));
                            ++first;
                            if (first == last) break;
                            set_right_successor(it, construct_node(comma));
                            it = right_successor(it);
                            ++first;
                        }

                        tree_stack[v.result()] = args;
                    }
                    else if (rule == rule_id_arg) {
                        Tree x = tree_stack[v.arg_0()];
                        tree_stack[v.result()] = tree_stack[v.arg_0()];
                    }
                }
                case MARPA_STEP_NULLING_SYMBOL: {
                    using Tree = tree<ast_node>;
                    int res    = v.result();
                    // put some value here
                    stack[res] = 0;
                    //Tree x{};
                    //tree_stack[res] = x;
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

    // Prime the first token.
    getNextToken();

    // Make the module, which holds all the code.
    llvm::Module* TheModule = new Module("test.toy", Context);

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
    //
    /*

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

    */
    OurFPM.doInitialization();

    // Set the global so the code gen can use this.
    llvm::FunctionPassManager* TheFPM = &OurFPM;

    // Run the main "interpreter loop" now.
    //MainLoop();
    int ret = MarpaParser(TheModule, TheFPM);
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
