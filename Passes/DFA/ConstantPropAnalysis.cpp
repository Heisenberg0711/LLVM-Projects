#include "231DFA.h"
#include "llvm/Pass.h"
#include "llvm/IR/ConstantFolder.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"

using namespace std;
using namespace llvm;

struct Const {
    unsigned state; 
    Constant* value;
    Const () {}
    Const (unsigned st, Constant* v) {
        state = st;
        value = v;
    }
};

bool operator == (const Const& lhs, const Const& rhs) {
    return lhs.state == rhs.state && lhs.value == rhs.value;
}

typedef std::map<Value*, struct Const> ConstPropContent;


class ConstPropInfo: public Info {
    private:
        ConstPropContent ConstPropMap;

    public:
        ConstPropInfo() {}

        ConstPropInfo(ConstPropContent& otherMap) {
            ConstPropMap = otherMap;
        }

        static bool equals (ConstPropInfo* info1, ConstPropInfo* info2) {
            return info1->ConstPropMap == info2->ConstPropMap;
        }


        static void join(ConstPropInfo * info1, ConstPropInfo * info2, ConstPropInfo * output){

                for( auto kv : info2->ConstPropMap){
                    Value* key = kv.first;

                    if ( info1->ConstPropMap[key].state == 2 || info2->ConstPropMap[key].state == 2){ 
                        output->setTop(key);
                    }
                    else if( info1->ConstPropMap[key].value && info2->ConstPropMap[key].value && 
                    info1->ConstPropMap[key].value != info2->ConstPropMap[key].value){
                        output->setTop(key);
                    }
                    else if( info1->ConstPropMap[key].state == 1) {
                        output->setConst(key, info1->ConstPropMap[key].value);
                    }
                    else if( info2->ConstPropMap[key].state == 1) {
                        output->setConst(key, info2->ConstPropMap[key].value);
                    }
                    else{
                        output->setBottom(key);
                    }
                }
        } 

        ConstPropContent getInfo() {
            return ConstPropMap;
        }

        void setTop (Value* v) {
            Const* newConst = new Const(2, NULL);
            ConstPropMap[v] = *newConst;
        }

        void setBottom (Value* v) {
            Const* newConst = new Const(0, NULL);
            ConstPropMap[v] = *newConst;
        }

        void setConst(Value* v, Constant* c) {
            Const* newConst = new Const(1, c);
            ConstPropMap[v] = *newConst;
        }

        Constant* getConstant(Value* v) {
            auto it = getInfo().find(v);
            if (it != getInfo().end()) {
                return it->second.value;
            } else {
                return NULL;
            }
        }

        void print() {
            for (auto it = ConstPropMap.begin(); it != ConstPropMap.end(); it++) {
                Value* val = it->first;
                Const thisConst = it->second;
                unsigned state = thisConst.state;
                Constant* value = thisConst.value;
                
                GlobalVariable* global = dyn_cast<GlobalVariable>(val);

                if (global) {
                    if (state == 1) {
                        errs() << global->getName().str() << '=' << *value << "|";
                    }
                    if (state == 2) {
                        errs() << global->getName().str() << "=⊤|";
                    }
                    if (state == 0) {
                        errs() << global->getName().str() << "=⊥|";
                    }
                }
            }
            errs()<<"\n";
        }

};

template <class Info, bool Direction>
class ConstPropAnalysis: public DataFlowAnalysis<ConstPropInfo, true> {
    private:
		typedef std::pair<unsigned, unsigned> Edge;
    
    public:
        ConstantFolder FOLDER;

        ConstPropAnalysis(ConstPropInfo& bottom, ConstPropInfo& initialState):
            DataFlowAnalysis(bottom, initialState) {}
        
        void flowfunction(Instruction * I, std::vector<unsigned> & IncomingEdges,
									       std::vector<unsigned> & OutgoingEdges,
									       std::vector<ConstPropInfo *> & Infos) {


            //Construct a new ConstPropInfo 
            ConstPropInfo* ConstInfo = new ConstPropInfo();
            
            //Get index of current IR instruction 
            unsigned instr_idx = getIndexFromInstr(I);

            //Add incoming edges to MayInfo
            for (unsigned i = 0; i < IncomingEdges.size(); ++i) {
				Edge e = make_pair(IncomingEdges[i], instr_idx);
				ConstPropInfo::join(ConstInfo, getInfoFromEdge(e), ConstInfo);
			}

            // Binary case
            if (BinaryOperator* bin_op = dyn_cast<BinaryOperator>(I)) {

                Value* x = I->getOperand(0);
                Value* y = I->getOperand(1);

                Constant* cons_x = dyn_cast<Constant>(x);
                Constant* cons_y = dyn_cast<Constant>(y);

                if (!cons_x) {
                    cons_x = ConstInfo->getConstant(x);
                }

                if (!cons_y) {
                    cons_y = ConstInfo->getConstant(y);
                }

                if (cons_x && cons_y) {
                    ConstInfo->setConst(I, FOLDER.CreateBinOp(bin_op->getOpcode(), cons_x, cons_y));
                } else {
                    ConstInfo->setTop(I);
                }
            }

            // Unary Case
            else if (UnaryOperator* un_op = dyn_cast<UnaryOperator>(I)) {

                Value* x = I->getOperand(0);

                Constant* cons_x = dyn_cast<Constant>(x);

                if (!cons_x) {
                    cons_x = ConstInfo->getConstant(x);
                }

                if (cons_x) {
                    ConstInfo->setConst(I, FOLDER.CreateUnOp(un_op->getOpcode(), cons_x));
                } else {
                    ConstInfo->setTop(I);
                }
            }

            // Load
            else if (isa<LoadInst>(I)) {

                Value* x = cast<LoadInst>(I)->getPointerOperand();
                Constant* cons_x = dyn_cast<Constant>(x);
                
                if (!cons_x) {
                    cons_x = ConstInfo->getConstant(x);
                }

                if (cons_x) {
                    ConstInfo->setConst(I, cons_x);
                } else {
                    ConstInfo->setTop(I);
                }

            }

            // store
            else if (isa<StoreInst>(I)) {
                Value* val = cast<StoreInst>(I)->getValueOperand();
                Value* ptr = cast<StoreInst>(I)->getPointerOperand();

                if (val->getType()->isPointerTy()) 
                {
                    ConstInfo->setTop(val);
                }
                
                Constant* cons_x = dyn_cast<Constant>(val);
                
                if (!cons_x) {
                    cons_x = ConstInfo->getConstant(ptr);
                }

                if (cons_x) {
                    ConstInfo->setConst(ptr, cons_x);
                } else {
                    ConstInfo->setTop(ptr);
                }
            }

            // icmp 
            else if (isa<ICmpInst>(I)) {
                auto pred = cast<ICmpInst>(I)->getPredicate();
                Value* x = cast<ICmpInst>(I)->getOperand(0);
                Value* y = cast<ICmpInst>(I)->getOperand(1);

                Constant* cons_x = dyn_cast<Constant>(x);
                Constant* cons_y = dyn_cast<Constant>(y);

                if (!cons_x) {
                    cons_x = ConstInfo->getConstant(x);
                }

                if (!cons_y) {
                    cons_y = ConstInfo->getConstant(y);
                }

                if (cons_x && cons_y) {
                    ConstInfo->setConst(I, FOLDER.CreateICmp(pred, cons_x, cons_y));
                } else {
                    //in the map, with key I set top
                    ConstInfo->setTop(I);
                }
            }
            
            // fcmp
            else if (isa<FCmpInst>(I)) {
                auto pred = cast<FCmpInst>(I)->getPredicate();
                Value* x = cast<FCmpInst>(I)->getOperand(0);
                Value* y = cast<FCmpInst>(I)->getOperand(1);

                Constant* cons_x = dyn_cast<Constant>(x);
                Constant* cons_y = dyn_cast<Constant>(y);

                if (!cons_x) {
                    cons_x = ConstInfo->getConstant(x);
                }

                if (!cons_y) {
                    cons_y = ConstInfo->getConstant(y);
                }

                if (cons_x && cons_y) {
                    ConstInfo->setConst(I, FOLDER.CreateFCmp(pred, cons_x, cons_y));
                } else {
                    ConstInfo->setTop(I);
                }
            }

            //PHI-Node
            else if (isa<PHINode>(I)) {
                Value* val = cast<PHINode>(I)->hasConstantValue();

                if(val){
                    Constant* const_val = dyn_cast<Constant>(val);
                    if(!const_val){
                        const_val = ConstInfo->getConstant(val);
                    }
                    if(const_val){
                        ConstInfo->setConst(I, const_val);
                    }
                }
                else{
                    ConstInfo->setTop(I);
                }
            }

            //Select 
            else if (isa<SelectInst>(I)) {
                Value* op1 = cast<SelectInst>(I)->getTrueValue();
                Value* op2 = cast<SelectInst>(I)->getFalseValue();
                Value* cond = cast<SelectInst>(I)->getCondition();

                Constant* cons_op1 = dyn_cast<Constant>(op1);
                Constant* cons_op2 = dyn_cast<Constant>(op2);
                Constant* cons_cond = dyn_cast<Constant>(cond);

                if (!cons_op1){
                    cons_op1 = ConstInfo->getConstant(op1);
                }
                if (!cons_op2){
                    cons_op2 = ConstInfo->getConstant(op2);
                }
                if (!cons_cond){
                    cons_cond = ConstInfo->getConstant(cond);
                }

                if (cons_op1 && cons_op2 && cons_cond) {
                    ConstInfo->setConst(I, FOLDER.CreateSelect(cons_cond, cons_op1, cons_op2));
                }
                else if (cons_op1 && cons_op2 && cons_op1 == cons_op2) {
                    ConstInfo->setConst(I, cons_op1);
                }
                else {
                    ConstInfo->setTop(I);
                }
            }

            //Add info to edges
            for (unsigned i = 0; i < OutgoingEdges.size(); i++) Infos.push_back(ConstInfo);
        }
};


namespace {
    struct ConstPropAnalysisPass : public CallGraphSCCPass
    {   
        
        static char ID;
        ConstPropAnalysisPass() : CallGraphSCCPass(ID) {}
        bool doInitialization(CallGraph& CG) override { 
            return false;
        }

        bool runOnSCC(CallGraphSCC& SCC) override {return false;}

        bool doFinalization(CallGraph& CG) override {
            for (Function& F : CG.getModule().functions()) {
                ConstPropInfo Top, Bottom;

                for (GlobalVariable& glob : CG.getModule().getGlobalList()) {
                    Top.setTop(&glob);
                }

                for (GlobalVariable& glob : CG.getModule().getGlobalList()) {
                    Bottom.setBottom(&glob);
                }

                ConstPropAnalysis<ConstPropInfo, true> CPA(Bottom, Top);
                CPA.runWorklistAlgorithm(&F);
                CPA.print();
            }
            return false;
        }

    };
}

char ConstPropAnalysisPass::ID = 0;
static RegisterPass<ConstPropAnalysisPass> X("cse231-constprop", 
                                            "ConstPropAnalysisPass", 
                                            false, 
                                            false);
