#include "231DFA.h"
#include "llvm/Pass.h"

using namespace std;
using namespace llvm;

class MayPointToInfo: public Info {
    public:
        map<pair<char, unsigned>, set<unsigned>> PointToMap;

        MayPointToInfo () {}

        MayPointToInfo(map<pair<char, unsigned>, set<unsigned>> OtherMap) {
            PointToMap = OtherMap;
        }

        static bool equals(MayPointToInfo* info1, MayPointToInfo* info2) {
            return info1->PointToMap == info2->PointToMap;
        }

        //Add info2 to info1
        static MayPointToInfo* join(MayPointToInfo* info1, MayPointToInfo* info2) {
            map<pair<char, unsigned>, set<unsigned>>::iterator itr2 = info2->PointToMap.begin();

            while (itr2 != info2->PointToMap.end()) {
                info1->PointToMap[make_pair(itr2->first.first, itr2->first.second)].
                insert(itr2->second.begin(), itr2->second.end());
                itr2 ++;
            }

            return info1;
        }


        set<unsigned> getMemory(pair<char, unsigned> key) {
		    return PointToMap[key];
	    }


        void addMemToMap(int typeMR, unsigned instrIdx, unsigned MemIdx) {
            char type;
            if (typeMR == 1) {type = 'R';} else {type = 'M';}
            PointToMap[make_pair(type, instrIdx)].insert(MemIdx);
        }


        void print() {
			for (auto it = PointToMap.begin(); it != PointToMap.end(); it++) {
				if (it->second.size() == 0)
					continue;

				errs() << (char) toupper(it->first.first) << it->first.second << "->(";

				for (auto m = it->second.begin(); m != it->second.end(); m++) {
					errs() << "M" << *m << "/";
				}
				errs() << ")|";
			}
			errs() << "\n";
		}

};


class MayPointToAnalysis: public DataFlowAnalysis<MayPointToInfo, true> {
    private:
        typedef pair<unsigned, unsigned> Edge;

    public:
        //Constructor
        MayPointToAnalysis(MayPointToInfo& bottom, MayPointToInfo& initialState) :
            DataFlowAnalysis(bottom, initialState) {}
        

        void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges,
									       std::vector<unsigned> & OutgoingEdges,
									       std::vector<MayPointToInfo *> & Infos) {

            //Construct a new Maypoin
            MayPointToInfo* MayInfo = new MayPointToInfo();

            //Get index of current IR instruction 
            unsigned instruction_idx = getIndexFromInstr(I);


            //Add incoming edges to MayInfo
            for (unsigned i = 0; i < IncomingEdges.size(); ++i) {
				Edge e = make_pair(IncomingEdges[i], instruction_idx);
				MayPointToInfo::join(MayInfo, getInfoFromEdge(e));
			}

            if (isa<AllocaInst>(I)) { MayInfo->addMemToMap(1, instruction_idx, instruction_idx);}

            else if (isa<BitCastInst>(I)) {
                unsigned Rv = getIndexFromInstr((Instruction*) I->getOperand(0));
                set<unsigned> RvInSet = MayInfo->getMemory(make_pair('R', Rv));

                for (auto it = RvInSet.begin(); it != RvInSet.end(); it++) {
                    MayInfo->addMemToMap(1, instruction_idx, *it);
                }
            }

            else if (isa<GetElementPtrInst>(I)) {
                unsigned Rv = getIndexFromInstr((Instruction*) cast<GetElementPtrInst>(I)->getPointerOperand());
                set<unsigned> RvInSet = MayInfo->getMemory(make_pair('R', Rv));

                for (auto it = RvInSet.begin(); it != RvInSet.end(); it++) {
                    MayInfo->addMemToMap(1, instruction_idx, *it);
                }
            }

            else if (isa<LoadInst>(I)) {
                if (I->getType()->isPointerTy()) {
                    unsigned Rp = getIndexFromInstr((Instruction *) cast<LoadInst>(I)->getPointerOperand());
                    set<unsigned> RpX = MayInfo->getMemory(make_pair('R', Rp));
                    
                    set<unsigned> RpY;

                    for (auto itr = RpX.begin(); itr != RpX.end(); itr++) {
                        set<unsigned> temp = MayInfo->getMemory(make_pair('M', *itr));
                        RpY.insert(temp.begin(), temp.end());
                    }

                    for (auto it = RpY.begin(); it != RpY.end(); it++) {
                        MayInfo->addMemToMap(1, instruction_idx, *it);
                    }
                }
            }

            else if (isa<StoreInst>(I)) {
                unsigned Rv = getIndexFromInstr((Instruction *) cast<StoreInst>(I)->getValueOperand());
			    unsigned Rp = getIndexFromInstr((Instruction *) cast<StoreInst>(I)->getPointerOperand());

                set<unsigned> RvInSet = MayInfo->getMemory(make_pair('R', Rv));
                set<unsigned> RpInSet = MayInfo->getMemory(make_pair('R', Rp));

                for (auto i = RvInSet.begin(); i != RvInSet.end(); i++) {
                    for (auto j = RpInSet.begin(); j != RpInSet.end(); i++) {
                        MayInfo->addMemToMap(2, *j, *i);
                    }
                }
            }

            else if (isa<SelectInst>(I)) {
                unsigned R1 = getIndexFromInstr((Instruction*) cast<SelectInst>(I)->getTrueValue());
                unsigned R2 = getIndexFromInstr((Instruction*) cast<SelectInst>(I)->getFalseValue());

                set<unsigned> R1Set = MayInfo->getMemory(make_pair('R', R1));
                set<unsigned> R2Set = MayInfo->getMemory(make_pair('R', R2));

                for (auto it1 = R1Set.begin(); it1 != R1Set.end(); it1++) {
                    MayInfo->addMemToMap(1, instruction_idx, *it1);
                }

                for (auto it2 = R2Set.begin(); it2 != R2Set.end(); it2++) {
                    MayInfo->addMemToMap(1, instruction_idx, *it2);
                }
            }

            else if (isa<PHINode>(I)) {
                unsigned NonPhiIdx = getIndexFromInstr(I->getParent()->getFirstNonPHI());

                for (unsigned i = instruction_idx; i < NonPhiIdx; i++) {
                    Instruction* temp = getInstrFromIndex(i);

                    for (unsigned j = 0; j < temp->getNumOperands(); j++) {
                        unsigned Rv = getIndexFromInstr((Instruction*) temp->getOperand(j));
                        set<unsigned> s = MayInfo->getMemory(make_pair('R', Rv));

                        for (auto it = s.begin(); it != s.end(); it++) {
                            MayInfo->addMemToMap(1, i, *it);
                        }
                    }
                }
            }

            for (unsigned i = 0; i < OutgoingEdges.size(); i++) Infos.push_back(MayInfo);

        }

};


namespace {
    struct MayPointToAnalysisPass : public FunctionPass {
        static char ID;
        MayPointToAnalysisPass() : FunctionPass(ID) {}

        bool runOnFunction(Function &F) override {
        MayPointToInfo bottom;
        MayPointToInfo initialState;
        MayPointToAnalysis rda(bottom, initialState);

        rda.runWorklistAlgorithm(&F);
        rda.print();

        return false;
        }
    };
}

char MayPointToAnalysisPass::ID = 0;
static RegisterPass<MayPointToAnalysisPass> X("cse231-maypointto", 
                                              "Maypointto analysis on DFA CFG", 
                                              false, false);
