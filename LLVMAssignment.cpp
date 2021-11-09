//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Utils.h>

#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/CFG.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>

#include <sstream>


using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }
/* In LLVM 5.0, when  -O0 passed to clang , the functions generated with clang will
 * have optnone attribute which would lead to some transform passes disabled, like mem2reg.
 */
struct EnableFunctionOptPass: public FunctionPass {
    static char ID;
    EnableFunctionOptPass():FunctionPass(ID){}
    bool runOnFunction(Function & F) override{
        if(F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID=0;

#ifdef DEBUG_PRINT
// Name unnamed values for debug purpose
struct NameAnonymousValuePass : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  NameAnonymousValuePass() : ModulePass(ID) {}

  bool runOnModule(Module &M) override {
    for (Function &F : M) {
      processFunction(F);
    }
    return false;
  }

private:
  unsigned int mNumber = 0;

  void checkAndNameValue(Value &v) {
    if (!v.hasName() && !v.getType()->isVoidTy()) {
      v.setName("name" + std::to_string(mNumber++));
    }
  }

  void processFunction(Function &F) {
    for (Argument &A : F.args()) {
      checkAndNameValue(A);
    }
    for (BasicBlock &BB : F) {
      for (Instruction &I : BB.getInstList()) {
        checkAndNameValue(I);
      }
    }
  }
};

char NameAnonymousValuePass::ID=0;
#endif

// Returns true if a new use is inserted
template <typename KT, typename VT>
bool insertRecordToMap(std::map<KT, std::set<VT>> &map, KT key, VT value) {
  auto it = map.find(key);
  if (it == map.end()) {
    std::set<VT> s = {value};
    map.insert(std::make_pair(key, s));
  }
  else {
    return it->second.insert(value).second;
  }
  return true;
}

///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 2
///Updated 11/10/2017 by fargo: make all functions
///processed by mem2reg before this pass.
struct FuncPtrPass : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  FuncPtrPass() : ModulePass(ID) {}

  
  bool runOnModule(Module &M) override {
    processModule(M);
    dumpResult();
    return false;
  }

private:
  using MapType = std::map<Value*, std::set<Function*>>;
  MapType mUseMap; // variable -> {possible functions}
  std::map<unsigned int, std::set<Function*>> mCallMap; // line number -> {possible functions}

  void copyUse(MapType &dstmap, Value *dst, MapType &srcmap, Value *src) {
    if (Function *f = dyn_cast<Function>(src)) {
      insertRecordToMap(dstmap, dst, f);
      return;
    }
    auto it = srcmap.find(src);
    if (it != srcmap.end()) {
      for (Function *f : it->second) {
        insertRecordToMap(dstmap, dst, f);
      }
    }
  }

  void mergeToGlobalMap(MapType &map) {
    for (auto it : map) {
      for (Function *f : it.second) {
        insertRecordToMap(mUseMap, it.first, f);
      }
    }
  }

  void processModule(Module &M) {
    for (Function &F : M) {
      if (!F.getName().startswith("llvm.dbg")) {
        processFunction(F, nullptr, mUseMap);
      }
    }
  }

  void processFunction(Function &F, CallInst *parentCall, MapType &parentMap) {
    if (F.isDeclaration()) return;
  
    std::vector<BasicBlock*> stackBB = {&F.getEntryBlock()};
    std::vector<MapType> stackMap = {{}};
    std::vector<std::vector<BasicBlock*>> stackPath = {{}};

    // handle arguments
    if (parentCall) {
      for (unsigned int i = 0; i < parentCall->getNumArgOperands(); i++) {
        Value *arg = parentCall->getArgOperand(i);
        if (arg->getType()->isPointerTy()) {
          copyUse(stackMap.back(), F.getArg(i), parentMap, arg);
        }
      }
    }

    while (!stackBB.empty()) {
      BasicBlock *bb = stackBB.back();
      MapType map = stackMap.back();
      std::vector<BasicBlock*> path = stackPath.back();
      stackBB.pop_back();
      stackMap.pop_back();
      stackPath.pop_back();

      if (std::find(path.begin(), path.end(), bb) != path.end()) {
        continue;
      }

      for (Instruction &I : *bb) {
        if (PHINode *phi = dyn_cast<PHINode>(&I)) {
          if (phi->getType()->isPointerTy()) {
            copyUse(map, phi, map, phi->getIncomingValueForBlock(path.back()));
          }
        }

        else if (CallInst *call = dyn_cast<CallInst>(&I)) {
          Value *callee = call->getCalledOperand();
          if (!callee->getName().startswith("llvm.dbg")) {
            if (Function *f = dyn_cast<Function>(callee)) {
              insertRecordToMap(mCallMap, I.getDebugLoc().getLine(), f);
              processFunction(*f, call, map);
            }
            else {
              auto it = map.find(callee);
              if (it != map.end()) {
                for (Function *f : it->second) {
                  insertRecordToMap(mCallMap, I.getDebugLoc().getLine(), f);
                  processFunction(*f, call, map);
                }
              }
            }
          }
        }

        else if (ReturnInst *ret = dyn_cast<ReturnInst>(&I)) {
          if (parentCall) {
            Value *v = ret->getReturnValue();
            if (v->getType()->isPointerTy()) {
              copyUse(parentMap, parentCall, map, v);
            }
          }
        }

        // kill branch with constant condition
        else if (BranchInst *br = dyn_cast<BranchInst>(&I)) {
          BasicBlock* kill = nullptr;
          if (br->isConditional()) {
            Value *cond = br->getCondition();
            if (ConstantInt *ci = dyn_cast<ConstantInt>(cond)) {
              kill = br->getSuccessor(ci->isZero() ? 0 : 1);
            }else if(CmpInst *cmpInst = dyn_cast<CmpInst>(cond)){
	        if (cmpInst->getNumOperands() == 2) {
                    Value *firstOperand = cmpInst->getOperand(0);
                    Value *secondOperand = cmpInst->getOperand(1);
                    ConstantInt *CI = dyn_cast<ConstantInt>(secondOperand);
		    ConstantInt *CI2 = dyn_cast<ConstantInt>(firstOperand);
                    if (CI && CI2){
			    int64_t t1 = CI2->getSExtValue();
			    int64_t t2 = CI->getSExtValue();
			    switch(cmpInst->getPredicate()){
				case CmpInst::Predicate::ICMP_SGT: kill = br->getSuccessor(t1 > t2 ? 1 : 0); break;
				case CmpInst::Predicate::ICMP_SGE: kill = br->getSuccessor(t1 >= t2 ? 1 : 0); break;
				case CmpInst::Predicate::ICMP_SLT: kill = br->getSuccessor(t1 < t2 ? 1 : 0); break;
				case CmpInst::Predicate::ICMP_SLE: kill = br->getSuccessor(t1 <= t2 ? 1 : 0); break;
			    }
		    }	
                }
	    }
          }
	  for (BasicBlock *succ : br->successors()) {
            if (succ != kill) {
              std::vector<BasicBlock*> newpath = path;
              newpath.push_back(bb);
              stackBB.push_back(succ);
              stackMap.push_back(map);
              stackPath.push_back(newpath);
            }
          }
          break;
        }
      }

      mergeToGlobalMap(map);
    }
  }

  void dumpResult() {
    for (auto it : mCallMap) {
      errs() << it.first << " : ";
      bool first = true;
      for (Function *f : it.second) {
        if (first) {
          first = false;
        }
        else {
          errs() << ", ";
        }
        errs() << f->getName();
      }
      errs() << '\n';
    }
  }
};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");

static cl::opt<std::string>
InputFilename(cl::Positional,
              cl::desc("<filename>.bc"),
              cl::init(""));


int main(int argc, char **argv) {
   LLVMContext &Context = getGlobalContext();
   SMDiagnostic Err;
   // Parse the command line to read the Inputfilename
   cl::ParseCommandLineOptions(argc, argv,
                              "FuncPtrPass \n My first LLVM too which does not do much.\n");


   // Load the input module
   std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
   if (!M) {
      Err.print(argv[0], errs());
      return 1;
   }

   llvm::legacy::PassManager Passes;
   	
   ///Remove functions' optnone attribute in LLVM5.0
   Passes.add(new EnableFunctionOptPass());
   ///Transform it to SSA
   Passes.add(llvm::createPromoteMemoryToRegisterPass());

   /// Your pass to print Function and Call Instructions
   Passes.add(new FuncPtrPass());
   Passes.run(*M.get());
}
