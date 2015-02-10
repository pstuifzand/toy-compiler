#ifndef TOY2_HPP
#define TOY2_HPP

enum class AstType {
    Error,
    Number,
    Variable,
    Binary,
    Call,
    Comma,
    Param,
    Params,
    Prototype,
    Function,
    Type,
    Struct,
    StructMember,
    If,
    Else,
    Stmt,
    Return,
    Assignment,
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
    Void,
    MaxBuiltIn,
};

namespace std {
    template <> struct hash<TypeCode>
    {
        size_t operator()(TypeCode x) const
        {
            return hash<int>()(int(x));
        }
    };
}

template <class I, class P>
I find(I first, I last, const char* x, P pred)
{
    while (first != last && !pred(x, *first)) {
        ++first;
    }
    return first;
}

struct ast_node {
    AstType     Type;
    double      Val;
    int32_t     IVal;
    char        Op;
    std::string Name;

    TypeCode    TCode;
    std::vector<std::string> Args;
    std::vector<TypeCode>    TypeCodes;

    ast_node() : TCode(TypeCode::Unknown_Type) {}
    ast_node(AstType type) : Type(type), TCode(TypeCode::Unknown_Type) {}
    ast_node(int32_t x) : Type(AstType::Number), IVal(x), TCode(TypeCode::Int32) {}
    ast_node(double x) : Type(AstType::Number), Val(x), TCode(TypeCode::Float64) {}
    ast_node(std::string x) : Type(AstType::Variable), Name(x), TCode(TypeCode::Unknown_Type) {}
};

#endif

