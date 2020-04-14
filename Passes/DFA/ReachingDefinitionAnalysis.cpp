#include "231DFA.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include <set>

using namespace std;
using namespace llvm;


class ReachingInfo : public Info{
public:
  set<unsigned> info;

  ReachingInfo() {}

  ReachingInfo(const set<unsigned>& a)
  {
    info = a;
  }

  static bool equals(ReachingInfo *a, ReachingInfo *b) {
    return a->info == b->info;
  }

  static ReachingInfo* join(ReachingInfo* info1, ReachingInfo* info2, ReachingInfo* result)
  {
    std::set<unsigned>::iterator itr1 = info1->info.begin();
    std::set<unsigned>::iterator itr2 = info2->info.begin();

    while (itr1 != info1->info.end())
    {
      result->info.insert(*itr1);
      itr1++;
    }

    while (itr2 != info2->info.end())
    {
      result->info.insert(*itr2);
      itr2++;
    }

    return result;
  }

  static void TwoJoin(ReachingInfo* info1, ReachingInfo* result)
  {
    std::set<unsigned>::iterator itr = info1->info.begin();
    while (itr != info1->info.end()) {
      result->info.insert(*itr);
      itr++;
    }

  }

  void print()
  {
			for (auto itr = info.begin(); itr != info.end(); ++itr) {
				errs() << *itr << '|';
			}

			errs() << '\n';
	}

};


class ReachingDefinitionAnalysis : public DataFlowAnalysis<ReachingInfo, true> {
private:
  typedef pair<unsigned, unsigned> Edge;

  set<string> RetOpCode =
  { "alloca", "load", "store",
    "getelementptr", "icmp", "fcmp", "select"
  };

  set<string> NonRetOpCode = {"br", "switch"};

public:
  //Constructor
  ReachingDefinitionAnalysis(ReachingInfo & bottom, ReachingInfo & initialState):
    DataFlowAnalysis(bottom, initialState) {}

  void flowfunction(Instruction * I,
                    vector<unsigned> & IncomingEdges,
                    vector<unsigned> & OutgoingEdges,
                    vector<ReachingInfo *> & Infos)
  {
    //Initialize the new ReachingInfo object
    ReachingInfo* newInfo = new ReachingInfo();

    string curr_op = I->getOpcodeName();
    int category;
    //If operation is binary or return, then it is category 1
    if (I->isBinaryOp() || RetOpCode.find(curr_op) != RetOpCode.end()) category = 1;
    else if (NonRetOpCode.find(curr_op) != NonRetOpCode.end()) category = 2;
    else if (curr_op == "phi") category = 3;

    unsigned instruction_idx = getInstrToIndex()[I];

    for (auto InEdge : IncomingEdges){
      ReachingInfo::TwoJoin(getEdgeToInfo()[Edge(InEdge, instruction_idx)], newInfo);
    }

    if (category == 1) {
      newInfo->info.insert(instruction_idx);
    }

    else if (category == 3) {
      BasicBlock *block = I->getParent();
      for (auto itr = block->begin(); itr != block->end(); itr++) {
          if (isa<PHINode>(cast<Instruction>(itr)))
              newInfo->info.insert(getInstrToIndex()[cast<Instruction>(itr)]);
      }
    }

    for (unsigned i = 0; i < OutgoingEdges.size(); i++) {
        Infos.push_back(newInfo);
    }

  }
};

namespace {
struct ReachingDefinitionAnalysisPass : public FunctionPass {
    static char ID;
    ReachingDefinitionAnalysisPass() : FunctionPass(ID){}

    bool runOnFunction(Function &F) override
    {
        ReachingInfo bottom, initialState;
        ReachingDefinitionAnalysis rda(bottom, initialState);

        rda.runWorklistAlgorithm(&F);
        rda.print();

        return false;
    }
};
}

char ReachingDefinitionAnalysisPass::ID = 0;
static RegisterPass<ReachingDefinitionAnalysisPass> X("cse231-reaching",
                                                      "Reaching Definition Analysis",
                                                      false,
                                                      false);
