//===-- Analyzer.cc - the kernel-analysis framework-------------===//
//
// It constructs a global call-graph based on multi-layer type
// analysis.
//
//===-----------------------------------------------------------===//
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

#include "mlta/Analyzer.h"
#include "mlta/CallGraph.h"
#include "mlta/Config.h"
#include "include/Unias.hpp"
#include "include/Util.hpp"

using namespace llvm;
using namespace SVF;

// Command line parameters.
cl::list<std::string> InputFilenames(
    cl::Positional, cl::OneOrMore, cl::desc("<input bitcode files>"));

cl::opt<unsigned> VerboseLevel(
    "verbose-level", cl::desc("Print information at which verbose level"),
    cl::init(0));


static llvm::cl::opt<std::string> InputScopename("InputScopename",
    llvm::cl::desc("<input scope file>"), llvm::cl::init(""));

static llvm::cl::opt<std::string> OutputFileName("OutputFileName",
    llvm::cl::desc("OutputFileName"), llvm::cl::init(""));

unordered_set<string> wholeScopeString;
unordered_set<GlobalVariable*> wholeScopeSet;
GlobalContext GlobalCtx;

unordered_map<const StructType*, unordered_map<u32_t, unordered_set<PAGEdge*>>> typebasedShortcuts;
unordered_map<const StructType*, unordered_set<PAGEdge*>> fdinsensitiveShortcuts;
unordered_map<const StructType*, unordered_set<PAGEdge*>> castSites;


void processGEPedges(SVFIR* pag){
    errs() << pag->getSVFStmtSet(SVFStmt::Gep).size() << "\n";
    for(auto edge : pag->getSVFStmtSet(SVFStmt::Gep)){
        auto gepedge = dyn_cast<GepStmt>(edge);
        if(edge->getSrcNode()->getType()){
            if(auto sttype = ifPointToStruct(edge->getSrcNode()->getType())){
                if(gepedge->isVariantFieldGep() || !gepedge->isConstantOffset()){
                    // field-insensitive
                    fdinsensitiveShortcuts[sttype].insert(edge);
                }else{
                    typebasedShortcuts[sttype][gepedge->accumulateConstantOffset()].insert(edge);
                }
            }
        }
    }
}

void processCastSites(SVFIR* pag){
    for(auto edge : pag->getSVFStmtSet(SVFStmt::Copy)){
        if(edge->getSrcNode()->getType() != edge->getDstNode()->getType()){
            if(edge->getSrcNode()->getType()){
                if(auto sttype = ifPointToStruct(edge->getSrcNode()->getType())){
                    castSites[sttype].insert(edge);
                }
            }
            if(edge->getDstNode()->getType()){
                if(auto sttype = ifPointToStruct(edge->getDstNode()->getType())){
                    castSites[sttype].insert(edge);
                }
            }   
            
        }
    }
}

void getCurrentScope(SVFModule* svfmod){
    ifstream fin(InputScopename);
    string tmp;
    while(!fin.eof()){
        fin >> tmp;
        wholeScopeString.insert(tmp);
    }
    for(auto ii = svfmod->global_begin(), ie = svfmod->global_end(); ii != ie; ii++){
        if(wholeScopeString.find((*ii)->getName().str()) != wholeScopeString.end()){
            wholeScopeSet.insert(*ii);
        }
    }
    errs() << "Current Scope Size: " << wholeScopeSet.size() << "\n";
}

unordered_map<NodeID, unordered_map<int, bool>> GVtoNonProtect;

bool checkIfProtectable(PAGNode* pagnode){
    for(auto edge : pagnode->getIncomingEdges(PAGEdge::Store)){
        if(auto inst = dyn_cast<Instruction>(edge->getValue())){
            if(auto func = inst->getFunction()){
                if(func->getSection().str() != ".init.text"
                 && func->getSection().str() != ".exit.text"
                 && NewInitFuncstr.find(func->getName().str()) == NewInitFuncstr.end()){
                    return false;
                }
            }
        }
    }
    return true;
}

unordered_map<NodeID, unordered_set<NodeID>> Real2Formal;
unordered_map<NodeID, unordered_set<NodeID>> Formal2Real;
unordered_map<NodeID, unordered_set<NodeID>> Ret2Call;
unordered_map<NodeID, unordered_set<NodeID>> Call2Ret;

void setupFuncs(SVFIR* _pag, GlobalContext *GCtx){
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
                        Formal2Real[formal].insert(real);
                        for(auto &bb : *callee){
                            for(auto &inst : bb){
                                if(auto retinst = dyn_cast<ReturnInst>(&inst)){
                                    if(retinst->getNumOperands() != 0 && callee->getReturnType()->isPointerTy()){
                                        const auto retval = _pag->getValueNode(retinst->getReturnValue());
                                        Ret2Call[retval].insert(_pag->getValueNode(callinst.first));
                                        Call2Ret[_pag->getValueNode(callinst.first)].insert(retval);
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    errs() << "Real2Formal " << Real2Formal.size() << "\n";
    errs() << "Formal2Real " << Formal2Real.size() << "\n";
    errs() << "Ret2Call " << Ret2Call.size() << "\n";
    errs() << "Call2Ret " << Call2Ret.size() << "\n";
}


u32_t IterateStruct(const StructType* st, bool& contain, vector<u32_t> &offset, vector<vector<u32_t>> &offsetset);
u32_t IterateArray(const ArrayType* ar, bool& contain, vector<u32_t> &offset, vector<vector<u32_t>> &offsetset){
    u32_t ret = 0;
    auto elementType = ar->getElementType();
    auto elementNum = ar->getNumElements();
        if(elementType->isArrayTy()){
            ret += IterateArray(dyn_cast<ArrayType>(elementType), contain, offset, offsetset);
        }
        else if (elementType->isStructTy()){
            ret += IterateStruct(dyn_cast<StructType>(elementType), contain, offset, offsetset);
        }
        else if(elementType->isSingleValueType()){
            ret++;
            
        }else{
            assert(true && "impossible");
        }
    return ret;
}

u32_t IterateStruct(const StructType* st, bool& contain, vector<u32_t> &offset, vector<vector<u32_t>> &offsetset){
    auto fdNum = st->getStructNumElements();
    u32_t ret = 0;
    for(u32_t fd = 0; fd < fdNum; fd++){
        auto fdtype = st->getStructElementType(fd);
        if(fdtype->isArrayTy()){
            offset.push_back(fd);
            ret += IterateArray(dyn_cast<ArrayType>(fdtype), contain, offset, offsetset);
            offset.pop_back();
        }
        else if(fdtype->isStructTy()){
            // if(!contain){
                offset.push_back(fd);
            // }
            ret += IterateStruct(dyn_cast<StructType>(fdtype), contain, offset, offsetset);
            // if(!contain){
                offset.pop_back();
            // }
        }else if(fdtype->isSingleValueType()){
            ret++;
            while(fdtype->isPointerTy()){
                fdtype = fdtype->getPointerElementType();
            }
            if(auto sttype = dyn_cast<StructType>(fdtype)){
            }
        }
    }
    return ret;
}

void performAnalysis(GlobalVariable* gv, SVFIR* pag){
    unordered_set<NodeID> globalAliases;
    Unias unias;
    unias.Formal2Real = &Formal2Real;
    unias.Real2Formal = &Real2Formal;
    unias.Ret2Call = &Ret2Call;
    unias.Call2Ret = &Call2Ret;
    unias.typebasedShortcuts = &typebasedShortcuts;
    unias.fdinsensitiveShortcuts = &fdinsensitiveShortcuts;
    unias.castSites = &castSites;
    unias.pag = pag;
    PNwithOffset firstLayer(0 ,true);
    unias.AnalysisStack.push(firstLayer);
    // find the variable you want to query on the graph
    auto pgnode = pag->getGNode(pag->getValueNode(gv));
    // Production `flows-to` is false, `I-Alias` is true
    // For global variables, we use `flows-to`
    unias.ComputeAlias(pgnode, false, 0);
    // Aliases will be unias.Aliases, it's a field sensitive map
    // where Aliases[0] shows the aliases of field indice 0
}


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
    Module *mod = nullptr;

	for (unsigned i = 0; i < InputFilenames.size(); ++i) {

		LLVMContext *LLVMCtx = new LLVMContext();
		std::unique_ptr<Module> M = parseIRFile(InputFilenames[i], Err, *LLVMCtx);

		if (M == NULL) {
			OP << argv[0] << ": error loading file '"
				<< InputFilenames[i] << "'\n";
			continue;
		}

		mod = M.release();
		StringRef MName = StringRef(strdup(InputFilenames[i].data()));
		GlobalCtx.Modules.push_back(std::make_pair(mod, MName));
		GlobalCtx.ModuleMaps[mod] = InputFilenames[i];

		svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(*mod);
		svfModule->buildSymbolTableInfo();

	}

	SVFIRBuilder builder;
	SVFIR* pag = builder.build(svfModule);
    errs() << "pag built!\n";

    addSVFAddrFuncs(&GlobalCtx, svfModule, pag);
	ENABLE_MLTA = MLTA;
	CallGraphPass CGPass(&GlobalCtx);
	CGPass.run(GlobalCtx.Modules);
    setupFuncs(pag, &GlobalCtx);

    processGEPedges(pag);
    processCastSites(pag);

    errs() << "shortcuts setup! " << "\n";

    auto gv = getSpecificGV(svfModule);

    performAnalysis(gv, pag);
    
	return 0;
}

