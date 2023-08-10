#include "SVF-FE/LLVMUtil.h"
#include "Graphs/SVFG.h"
#include "WPA/Andersen.h"
#include "SABER/LeakChecker.h"
#include "SVF-FE/SVFIRBuilder.h"
#include "WPA/Steensgaard.h"
#include "Util/Options.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/Path.h"

#include <fstream>
#include <memory>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <sstream>
#include <sys/resource.h>
#include <iomanip>

#include "include/Util.hpp"

using namespace llvm;
using namespace SVF;

// Command line parameters.
cl::list<std::string> InputFilenames(
    cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<unsigned> VerboseLevel(
    "verbose-level", cl::desc("Print information at which verbose level"),
    cl::init(0));

class FieldSenSteens: public Steensgaard{

public:
    unordered_map<NodeID, unordered_set<NodeID>> Real2Formal;
    unordered_set<NodeID> repnodes;
     

    FieldSenSteens(SVFIR* _pag, GlobalContext *GCtx) : Steensgaard(_pag){
        // Set up the indirect calls to callee edges from MLTA
        for(const auto callinst : GCtx->Callees){
            const auto argsize = callinst.first->arg_size();
            for(const auto callee : callinst.second){
                if(argsize == callee->arg_size()){
                    for(unsigned int i = 0; i < argsize; i++){
                        if( _pag->hasValueNode(callinst.first->getArgOperand(i)->stripPointerCasts())
                            && _pag->hasValueNode(callee->getArg(i))
                        ){
                            const auto real = _pag->getValueNode(callinst.first->getArgOperand(i)->stripPointerCasts());
                            const auto formal = _pag->getValueNode(callee->getArg(i));
                            Real2Formal[real].insert(formal);
                        }
                    }
                }
            }
        }
    }

    void solveWorklist() override
    {

        processAllAddr();

        // Keep solving until workList is empty.
        while (!isWorklistEmpty())
        {
            NodeID nodeId = popFromWorklist();
            ConstraintNode* node = consCG->getConstraintNode(nodeId);

            /// foreach o \in pts(p)
            for(NodeID o : getPts(nodeId))
            {
                /// *p = q : EC(o) == EC(q)
                for (ConstraintEdge* edge : node->getStoreInEdges())
                {
                    ecUnion(edge->getSrcID(), o);
                }
                // r = *p : EC(r) == EC(o)
                for (ConstraintEdge* edge : node->getLoadOutEdges())
                {
                    ecUnion(o, edge->getDstID());
                }
            }

            /// q = p : EC(q) == EC(p)
            for (ConstraintEdge* edge : node->getCopyOutEdges())
            {
                ecUnion(edge->getSrcID(),edge->getDstID());
            }

            /// Indirect call, same as copy out
            for (auto dstNode : Real2Formal[node->getId()]){
                ecUnion(node->getId(), dstNode);
            }

            /// q = &p->f : EC(q) == EC(p)
            for (ConstraintEdge* edge : node->getGepOutEdges())
            {
                // Handled Normal Geps, make it field-sensitive
                if(const auto gepEdge = SVFUtil::dyn_cast<NormalGepCGEdge>(edge)){
                    processGepPts(gepEdge);
                }else{
                    // Conservatively lose field-sensitivity
                    ecUnion(edge->getSrcID(),edge->getDstID());
                }
            }
        }
    }

};

GlobalContext GlobalCtx;

int main(int argc, char **argv) {

	// Print a stack trace if we signal out.
	sys::PrintStackTraceOnErrorSignal(argv[0]);
	PrettyStackTraceProgram X(argc, argv);

	llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

	cl::ParseCommandLineOptions(argc, argv, "global analysis\n");
	SMDiagnostic Err;

	// Loading modules
	OP << "Total " << InputFilenames.size() << " file(s)\n";

	SVFModule* svfModule = nullptr;

	for (unsigned i = 0; i < InputFilenames.size(); ++i) {

		LLVMContext *LLVMCtx = new LLVMContext();
		std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);

		if (M == NULL) {
			OP << argv[0] << ": error loading file '"
				<< InputFilenames[i] << "'\n";
			continue;
		}

		Module *Module = M.release();
		StringRef MName = StringRef(strdup(InputFilenames[i].data()));
		GlobalCtx.Modules.push_back(std::make_pair(Module, MName));
		GlobalCtx.ModuleMaps[Module] = InputFilenames[i];

		svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(*Module);
		svfModule->buildSymbolTableInfo();

	}

    // Build PAG
	SVFIRBuilder builder;
	SVFIR* pag = builder.build(svfModule);
    errs() << "pag built!\n";

	// Build indirect callgraph
	addSVFAddrFuncs(&GlobalCtx, svfModule, pag);
	ENABLE_MLTA = MLTA;
	CallGraphPass CGPass(&GlobalCtx);
	CGPass.run(GlobalCtx.Modules);

    auto steens = FieldSenSteens(pag, &GlobalCtx);
    steens.analyze();

    // Check results
    // steens.getPts(NodeID id);

	return 0;
}