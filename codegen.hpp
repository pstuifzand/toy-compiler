#ifndef CODEGEN_HPP
#define CODEGEN_HPP

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
#include "llvm/IR/Verifier.h"
#include "llvm/IR/Module.h"
#include "llvm/PassManager.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/LinkAllPasses.h"

#include "eop-code/eop.h"

//===----------------------------------------------------------------------===//
// Code Generation
//===----------------------------------------------------------------------===//

typedef std::unordered_map<std::string, llvm::AllocaInst*> NamedValuesMap;
typedef std::unordered_map<std::string, TypeCode>          NamedTypesMap;
//typedef std::unordered_map<std::string, llvm::Type*>  UserTypesMap;
//typedef std::unordered_map<TypeCode, llvm::Type*>     CodedTypesMap;

llvm::Type* convert_type(TypeCode type_code);
llvm::Value* create_uint_value(uint64_t v, TypeCode type);
llvm::Value* create_int_value(int64_t v, TypeCode type);

// Set names for all arguments.
template <class I, class I2>
void set_argument_names(I f0, I l0, I2 f1) {
    while (f0 != l0) {
        f1->setName(*f0);
        ++f0;
        ++f1;
    }
}

template <class C>
llvm::Function*
codegen_prototype(llvm::Module* module, NamedValuesMap& named_values, C proto) {
    using namespace llvm;
    using namespace std;

    const ast_node& n = source(proto);

    // Make the function type:  double(double,double) etc.
    vector<Type*> params(n.Args.size());
    transform(begin(n.TypeCodes), end(n.TypeCodes),
              begin(params), convert_type);

    Type* return_type = convert_type(n.TCode);

    FunctionType* ft = FunctionType::get(return_type, params, false);

    Function* f = Function::Create(ft, Function::ExternalLinkage, n.Name, module);

    // If F conflicted, there was already something named 'Name'.  If it has a
    // body, don't allow redefinition or reextern.
    if (f->getName() != n.Name) {
        // Delete the one we just made and get the existing one.
        f->eraseFromParent();
        f = module->getFunction(n.Name);

        // If F already has a body, reject this.
        if (!f->empty()) {
            //ErrorF("redefinition of function");
            return 0;
        }

        // If f took a different number of args, reject.
        if (f->arg_size() != n.Args.size()) {
            //ErrorF("redefinition of function with different # args");
            return 0;
        }
    }

    set_argument_names(begin(n.Args), end(n.Args), f->arg_begin());

    return f;
}

llvm::Value*
create_float_value(double x) {
    using namespace llvm;
    return ConstantFP::get(getGlobalContext(), APFloat(x));
}

template <class B, class C>
static llvm::Value*
codegen_expression(llvm::Module* module, llvm::Function* function, B& builder, NamedValuesMap& named_values, C body) {
    using namespace llvm;

    const ast_node& n = source(body);

    if (n.Type == AstType::Number) {
        if (n.TCode == TypeCode::Int32) {
            return create_int_value(n.IVal, n.TCode);
        } else {
            return create_float_value(n.Val);
        }
    } else if (n.Type == AstType::Variable) {
        // Look this variable up in the function.
        Value* V = named_values[n.Name];
        if (V == 0) return 0;
        return builder.CreateLoad(V, n.Name.c_str());
    } else if (n.Type == AstType::Binary) {
        C lhs = left_successor(body);
        C rhs = right_successor(body);

        Value* L = codegen_expression(module, function, builder, named_values, lhs);
        Value* R = codegen_expression(module, function, builder, named_values, rhs);

        if (L == 0 || R == 0) return 0;


        // TODO check type of L and R

        if (n.TCode == TypeCode::Int32) {
            switch (n.Op) {
                case '+': return builder.CreateAdd(L, R, "addtmp");
                case '-': return builder.CreateSub(L, R, "subtmp");
                case '*': return builder.CreateMul(L, R, "multmp");
                case '/': return builder.CreateSDiv(L, R, "divtmp");
                case '<':
                        L = builder.CreateICmpULT(L, R, "cmptmp");
                        // Convert bool 0/1 to double 0.0 or 1.0
                        return builder.CreateUIToFP(L, Type::getDoubleTy(getGlobalContext()),
                                "booltmp");
                //default: return ErrorV("invalid binary operator");
            }
        }
        else {
            switch (n.Op) {
                case '+': return builder.CreateFAdd(L, R, "addtmp");
                case '-': return builder.CreateFSub(L, R, "subtmp");
                case '*': return builder.CreateFMul(L, R, "multmp");
                case '/': return builder.CreateFDiv(L, R, "divtmp");
                case '<':
                        L = builder.CreateFCmpULT(L, R, "cmptmp");
                        // Convert bool 0/1 to double 0.0 or 1.0
                        return builder.CreateUIToFP(L, Type::getDoubleTy(getGlobalContext()),
                                "booltmp");
                //default: return ErrorV("invalid binary operator");
            }
        } 

    } else if (n.Type == AstType::Call) {
        C args = right_successor(body);

        const ast_node& name = source(left_successor(body));

        // Look up the name in the global module table.
        Function *CalleeF = module->getFunction(name.Name);
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
            Value* v = codegen_expression(module, function, builder, named_values, left_successor(it));
            ArgsV.push_back(v);
            it = right_successor(it);
        }
        
        return builder.CreateCall(CalleeF, ArgsV, "calltmp");
    }
    return 0;
}

template <class B, class C>
static void codegen_stmts(llvm::Module* module, llvm::Function* function, B& builder, NamedValuesMap& named_values, C stmts);

template <class B, class C>
static void
codegen_stmt(llvm::Module* module, llvm::Function* function, B& builder, NamedValuesMap& named_values, C stmt) {
    const ast_node& n = source(stmt);
    if (n.Type == AstType::Return) {
        C lhs = left_successor(stmt);
        llvm::Value* RetVal = codegen_expression(module, function, builder, named_values, lhs);

        // Finish off the function.
        llvm::BasicBlock* ret_block = llvm::BasicBlock::Create(llvm::getGlobalContext(), "ret", function);
        builder.CreateBr(ret_block);
        builder.SetInsertPoint(ret_block);
        builder.CreateRet(RetVal);
        //return ret_block;
    } else if (n.Type == AstType::If) {
        C lhs = left_successor(stmt);
        C rhs = right_successor(stmt);

        llvm::Value* cond = codegen_expression(module, function, builder, named_values, lhs);

        // check if this is a boolean type expression
        if (!cond->getType()->isIntegerTy(1))
            cond = builder.CreateICmp(llvm::CmpInst::Predicate::ICMP_NE, cond, create_int_value(0, source(lhs).TCode));

        if (source(rhs).Type == AstType::Stmt) {
            llvm::BasicBlock* if_block = llvm::BasicBlock::Create(llvm::getGlobalContext(), "if", function);
            llvm::BasicBlock* merge_block = llvm::BasicBlock::Create(llvm::getGlobalContext(), "merge", function);

            builder.CreateCondBr(cond, if_block, merge_block);
            builder.SetInsertPoint(if_block);
            codegen_stmt(module, function, builder, named_values, rhs);
            builder.CreateBr(merge_block);
            if_block = builder.GetInsertBlock();
            builder.SetInsertPoint(merge_block);
        } else if (source(rhs).Type == AstType::Else) {
            C if_stmts = left_successor(rhs);
            C else_stmts = right_successor(rhs);

            llvm::BasicBlock* then_block = llvm::BasicBlock::Create(llvm::getGlobalContext(), "if", function);
            llvm::BasicBlock* else_block = llvm::BasicBlock::Create(llvm::getGlobalContext(), "else", function);
            llvm::BasicBlock* merge_block = llvm::BasicBlock::Create(llvm::getGlobalContext(), "merge", function);

            builder.CreateCondBr(cond, then_block, else_block);
            builder.SetInsertPoint(then_block);
            codegen_stmt(module, function, builder, named_values, if_stmts);
                builder.CreateBr(merge_block);
            then_block = builder.GetInsertBlock();
            builder.SetInsertPoint(else_block);
            codegen_stmt(module, function, builder, named_values, else_stmts);
                builder.CreateBr(merge_block);
            else_block = builder.GetInsertBlock();
            builder.SetInsertPoint(merge_block);
        }
    } else if (n.Type == AstType::Assignment) {
        C lhs = left_successor(stmt);
        C rhs = right_successor(stmt);

        llvm::Value* Val = codegen_expression(module, function, builder, named_values, rhs);
        llvm::Value* Variable = named_values[source(lhs).Name];

        builder.CreateStore(Val, Variable);
        
    } else if (n.Type == AstType::Stmt) {
        codegen_stmts(module, function, builder, named_values, stmt);
    } else {
        std::cerr << "Unknown statement type\n";
    }
}

template <class C, class Op>
void
tree_foreach(C c, Op op) {
    while (!empty(c)) {
        op(left_successor(c));
        c = right_successor(c);
    }
}

template <class B, class C>
static void
codegen_stmts(llvm::Module* module, llvm::Function* function, B& builder, NamedValuesMap& named_values, C stmts) {
    tree_foreach<C>(stmts, [&](C stmt) { codegen_stmt(module, function, builder, named_values, stmt); });
}

/// create_entry_block_alloca - Create an alloca instruction in the entry block of
/// the function.  This is used for mutable variables etc.
static llvm::AllocaInst*
create_entry_block_alloca(llvm::Function* function, const std::string& var_name, llvm::Type* type) {
    llvm::IRBuilder<> TmpB(&function->getEntryBlock(), function->getEntryBlock().begin());
    return TmpB.CreateAlloca(type, 0, var_name.c_str());
}

template <class B, class C>
static void 
create_argument_allocas(llvm::Function *function, B& builder, NamedValuesMap& named_values, C proto) {
    const ast_node& ast = source(proto);

    llvm::Function::arg_iterator it = function->arg_begin();

    for (unsigned i = 0, e = ast.Args.size(); i != e; ++i, ++it) {
        // Create an alloca for this variable.
        llvm::Type* type = convert_type(ast.TypeCodes[i]);
        llvm::AllocaInst *alloca = create_entry_block_alloca(function, ast.Args[i], type);

        // Store the initial value into the alloca.
        builder.CreateStore(it, alloca);

        // Add arguments to variable symbol table.
        named_values[ast.Args[i]] = alloca;
    }
}

template <class C>
static llvm::Function*
codegen_function(llvm::Module* module, C proto, C body) {
    using namespace llvm;

    IRBuilder<> builder(getGlobalContext());

    NamedValuesMap named_values;

    Function *function = codegen_prototype(module, named_values, proto);

    BasicBlock *BB = BasicBlock::Create(llvm::getGlobalContext(), "entry", function);
    builder.SetInsertPoint(BB);

    create_argument_allocas(function, builder, named_values, proto);

    if (!empty(body)) {
        codegen_stmts(module, function, builder, named_values, body);
    } else {
        builder.CreateRetVoid();
    }

    // Validate the generated code, checking for consistency.
    verifyFunction(*function);
    return function;
}

template <class C>
static llvm::StructType*
codegen_typedef(C type) {
    using namespace llvm;
    const ast_node& n = source(type);
    assert(n.Type == AstType::Struct);

    std::vector<Type*> params(n.TypeCodes.size());
    std::transform(std::begin(n.TypeCodes), std::end(n.TypeCodes), std::begin(params), convert_type);

    StructType* T = StructType::create(params, n.Name);
    return T;
}

template <class C>
struct type_inference {
    NamedTypesMap variable_types;

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
                variable_types[n.Args[i]] = n.TypeCodes[i];
                ++i;
            }
        }
        else if (v == post && n.Type == AstType::Variable) {
            sink(c).TCode = variable_types[n.Name];
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
void inference_types(C root) {
    traverse(root, type_inference<C>());
}

template <class C>
void codegen(llvm::Module* module, llvm::FunctionPassManager* fpm, C root) {
    const ast_node& n = source(root);

    if (n.Type == AstType::Function) {
        C proto = left_successor(root);
        C body  = right_successor(root);
        inference_types(root);
        llvm::Function* function = codegen_function(module, proto, body);
        fpm->run(*function);
    }
}

#endif

