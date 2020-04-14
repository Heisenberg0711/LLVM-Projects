#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <iterator>


using namespace llvm;
using namespace std;

namespace {
struct CountFunc : public FunctionPass {
  static char ID;

  CountFunc() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    static std::map<const char*,int>  Count;

    for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; I++) {

        Count[I->getOpcodeName()] += 1;
    }

    for (auto iter:Count) {
        errs() << iter.first << "\t" << iter.second << "\n";
    }

    return false;
  }
};
}

char CountFunc::ID = 0;
static RegisterPass<CountFunc> X("cse231-csi", "CountFunc Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
