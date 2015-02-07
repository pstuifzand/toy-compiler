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

typedef std::unordered_map<std::string, llvm::Value*> NamedValuesMap;
typedef std::unordered_map<std::string, TypeCode>     NamedTypesMap;
//typedef std::unordered_map<std::string, llvm::Type*>  UserTypesMap;
//typedef std::unordered_map<TypeCode, llvm::Type*>     CodedTypesMap;

llvm::Type* ConvertType(TypeCode type_code);
llvm::Value* create_uint_value(uint64_t v, TypeCode type);
llvm::Value* create_int_value(int64_t v, TypeCode type);

template <class C>
llvm::Function* CodegenPrototype(
        llvm::Module* TheModule,
        NamedValuesMap& NamedValues,
        C proto) {

    using namespace llvm;

    const ast_node& n = source(proto);

    // Make the function type:  double(double,double) etc.
    size_t len = n.Args.size();
    size_t i = 0;

    std::vector<llvm::Type*> params(n.Args.size());
    while (i < len) {
        llvm::Type* type = ConvertType(n.TypeCodes[i]);
        params[i] = type;
        ++i;
    }

    llvm::Type* return_type = ConvertType(n.TCode);

    llvm::FunctionType* FT = llvm::FunctionType::get(return_type, params, false);

    llvm::Function* F = Function::Create(FT, Function::ExternalLinkage, n.Name, TheModule);

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
    }

    return F;
}

template <class B, class C>
llvm::Value* CodegenBody(
        llvm::Module* TheModule,
        B& Builder,
        NamedValuesMap& NamedValues,
        C body) {

    using namespace llvm;

    const ast_node& n = source(body);
    if (n.Type == AstType::Number) {
        if (n.TCode == TypeCode::Int32) {
            return create_int_value(n.IVal, n.TCode);
        } else {
            return ConstantFP::get(getGlobalContext(), APFloat(n.Val));
        }
    } else if (n.Type == AstType::Variable) {
        // Look this variable up in the function.
        Value* V = NamedValues[n.Name];
        return V;
    } else if (n.Type == AstType::Binary) {
        C lhs = left_successor(body);
        C rhs = right_successor(body);

        Value* L = CodegenBody(TheModule, Builder, NamedValues, lhs);
        Value* R = CodegenBody(TheModule, Builder, NamedValues, rhs);

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
            Value* v = CodegenBody(TheModule, Builder, NamedValues, left_successor(it));
            ArgsV.push_back(v);
            it = right_successor(it);
        }
        
        return Builder.CreateCall(CalleeF, ArgsV, "calltmp");

    }
    return 0;
}

template <class C>
llvm::Function* CodegenFunction(llvm::Module* TheModule, C proto, C body) {
    using namespace llvm;

    llvm::IRBuilder<> Builder(llvm::getGlobalContext());

    NamedValuesMap NamedValues;

    Function *TheFunction = CodegenPrototype(TheModule, NamedValues, proto);

    BasicBlock *BB = BasicBlock::Create(llvm::getGlobalContext(), "entry", TheFunction);
    Builder.SetInsertPoint(BB);

    if (Value* RetVal = CodegenBody(TheModule, Builder, NamedValues, body)) {
        // Finish off the function.
        Builder.CreateRet(RetVal);
        // Validate the generated code, checking for consistency.
        verifyFunction(*TheFunction);

        return TheFunction;
    }
    return 0;
}

template <class C>
llvm::StructType* CodegenTypeDef(C type) {
    using namespace llvm;
    const ast_node& n = source(type);
    assert(n.Type == AstType::Struct);

    std::vector<Type*> params(n.TypeCodes.size());
    std::transform(std::begin(n.TypeCodes), std::end(n.TypeCodes), std::begin(params), ConvertType);

    StructType* T = StructType::create(params, n.Name);
    return T;
}

template <class C>
struct type_inference {
    NamedTypesMap NamedTypes;

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
    traverse(root, type_inference<C>());
}

template <class C>
void Codegen(llvm::Module* TheModule, llvm::FunctionPassManager* TheFPM, C root) {
    const ast_node& n = source(root);

    if (n.Type == AstType::Function) {
        C proto = left_successor(root);
        C body  = right_successor(root);
        TypeInference(root);
        llvm::Function* TheFunction = CodegenFunction(TheModule, proto, body);
        TheFPM->run(*TheFunction);
    }
}

#endif

