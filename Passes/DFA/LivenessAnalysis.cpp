#include "231DFA.h"
#include "llvm/Pass.h"


using namespace llvm;
using namespace std;

class LivenessInfo: public Info {
    
    public:
    set<unsigned> info;

    LivenessInfo () {}

    LivenessInfo(const set<unsigned>& a) {
        info = a;
    }

    static bool equals(LivenessInfo *a, LivenessInfo *b) {
        return a->info == b->info;
    }

    static LivenessInfo* join(LivenessInfo* info1, LivenessInfo* info2, LivenessInfo* result) {
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


    static LivenessInfo* diffRemove (LivenessInfo* info1, LivenessInfo* info2, LivenessInfo* result) {
        set<unsigned> set1 = info1->info;    // Deep copy of info1's info set
        std::set<unsigned>::iterator itr2 = info2->info.begin();

        while (itr2 != info2->info.end()) {
			set1.erase(*itr2);
			itr2++;
        }

        result->info = set1;
        return result;
    }

    void print() {
        for (auto itr = info.begin(); itr != info.end(); ++itr) {
            errs() << *itr << '|';
        }

        errs() << '\n';
	}

};


class LivenessAnalysis : public DataFlowAnalysis<LivenessInfo, false> {
    private:
        typedef pair<unsigned, unsigned> Edge;

        set<string> RetOpCode =
        { "alloca", "load", "getelementptr", "icmp", "fcmp", "select"
        };

        set<string> NonRetOpCode = {"br", "switch", "store"};

    public:
        LivenessAnalysis(LivenessInfo & bottom, LivenessInfo & initialState) : 
			DataFlowAnalysis(bottom, initialState) {}
        

        void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges,
									       std::vector<unsigned> & OutgoingEdges,
									       std::vector<LivenessInfo *> & Infos) {
        
            //Initialize the new LivenessInfo object
            
            LivenessInfo* LiveInfo = new LivenessInfo();
            
            
            //Get current opCodeName and then decide its category
            string curr_op = I->getOpcodeName();
            
            int category;
            
            
            //If operation is binary or return, then it is category 1
            if (I->isBinaryOp() || RetOpCode.find(curr_op) != RetOpCode.end()) category = 1;
            else if (NonRetOpCode.find(curr_op) != NonRetOpCode.end()) category = 2;
            else if (curr_op == "phi") category = 3;

            
            map<Instruction *, unsigned> instrToIndex = getInstrToIndex();
			map<unsigned, Instruction *> indexToInstr = getIndexToInstr();
            map<Edge, LivenessInfo *> edgeToInfo = getEdgeToInfo();
            
            //Get index of current IR instruction 
            unsigned instruction_idx = instrToIndex[I];

            //Create a set to store all operands for current instruction
            set<unsigned> all_operands;


            for (unsigned i = 0; i < I->getNumOperands(); ++i) {
				Instruction *instr = (Instruction *) I->getOperand(i);

				if (instrToIndex.find(instr) != instrToIndex.end()) {
					all_operands.insert(instrToIndex[instr]);
                }
			}

            //Incoming edges
			for (unsigned i = 0; i < IncomingEdges.size(); ++i) {
				Edge e = make_pair(IncomingEdges[i], instruction_idx);
				LivenessInfo::join(LiveInfo, edgeToInfo[e], LiveInfo);
			}

            //If instruction has a return value
            if (category == 1) {
                //Create a set to represent the current IR instruction index
                set<unsigned> temp;
                temp.insert(instruction_idx);

                //Create two LiveInfo object to use the join and remove function
                LivenessInfo* OperandLiveInfo = new LivenessInfo(all_operands);
                LivenessInfo* IndexLiveInfo = new LivenessInfo(temp);

                LivenessInfo::join(LiveInfo, OperandLiveInfo, LiveInfo);
                LivenessInfo::diffRemove(LiveInfo, IndexLiveInfo, LiveInfo);
                
                //Pass the LiveInfo to Infos vector
                for (unsigned i = 0; i < OutgoingEdges.size(); i++) {
                    Infos.push_back(LiveInfo);
                }
            }

            //If instruction does not have a return value
            else if (category == 2) {
                LivenessInfo* OperandLiveInfo = new LivenessInfo(all_operands);
                LivenessInfo::join(LiveInfo, OperandLiveInfo, LiveInfo);

                for (unsigned i = 0; i < OutgoingEdges.size(); i++) {
                    Infos.push_back(LiveInfo);
                }
            }

            //Handle phi nodes
            else {
                set<unsigned> IdxBeforeFirstNonPhi;
                Instruction * NonPhi = I->getParent()->getFirstNonPHI();
                unsigned NonPhiIdx = instrToIndex[NonPhi];

                for (unsigned i = instruction_idx; i < NonPhiIdx; ++i) {
                    IdxBeforeFirstNonPhi.insert(i);
                }

                LivenessInfo* NonPhiIdxInfo = new LivenessInfo(IdxBeforeFirstNonPhi); 
                LivenessInfo::diffRemove(LiveInfo, NonPhiIdxInfo, LiveInfo);

                //For each different ougoing edge, we need to decide which edges from phi nodes to put in
                for (unsigned out_idx = 0; out_idx < OutgoingEdges.size(); out_idx++) {
                    LivenessInfo* k_info = new LivenessInfo();
                    set<unsigned> k_operand;

                    for (unsigned i = instruction_idx; i < NonPhiIdx; i++) {

                        for (unsigned j = 0; j < indexToInstr[i]->getNumOperands(); j++) {
                            Instruction * instr = (Instruction *) indexToInstr[i]->getOperand(j);

                            if (instrToIndex.find(instr) != instrToIndex.end()) {
                                continue;
                            }

                            if (instr->getParent() == indexToInstr[OutgoingEdges[out_idx]]->getParent()) {
								k_operand.insert(instrToIndex[instr]);
								break;
							}

                        }
                    }
                    LivenessInfo* k_operandInfo = new LivenessInfo(k_operand);
                    LivenessInfo::join(LiveInfo, k_operandInfo, k_info);
                    Infos.push_back(k_info);
                }

            }
   
        }
};


namespace {
    struct LivenessAnalysisPass : public FunctionPass {
        static char ID;
        LivenessAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override
        {
            LivenessInfo bottom, initialState;
            LivenessAnalysis rda(bottom, initialState);

            rda.runWorklistAlgorithm(&F);
            rda.print();

            return false;
        }
    };
}

char LivenessAnalysisPass::ID = 0;
static RegisterPass<LivenessAnalysisPass> X("cse231-liveness",
                                            "Liveness Analysis",
                                            false,
                                            false);

