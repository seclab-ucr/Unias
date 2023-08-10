#ifndef UNIAS_UTIL_H
#define UNIAS_UTIL_H
#include <string>
#include <fstream>
#include "SVF-FE/LLVMUtil.h"
#include "SVF-FE/SVFIRBuilder.h"
#include "../mlta/Analyzer.h"
#include "../mlta/CallGraph.h"
#include "../mlta/Config.h"

using namespace SVF;
using namespace llvm;
using namespace std;

static llvm::cl::opt<std::string> SpecificGV("SpecificGV",
    llvm::cl::desc("specific the gv"), llvm::cl::init(""));

static llvm::cl::opt<std::string> InputNewInitFuncs("InputNewInitFuncs",
    llvm::cl::desc("Input the new init functions"), llvm::cl::init(""));

cl::opt<int> MLTA(
    "mlta",
  cl::desc("Multi-layer type analysis for refining indirect-call \
    targets"),
  cl::NotHidden, cl::init(2));

unordered_set<string> NewInitFuncstr;

void getNewInitFuncs(llvm::Module * module){
    ifstream fin(InputNewInitFuncs);
    string tmp;
    while(!fin.eof()){
        fin >> tmp;
        NewInitFuncstr.insert(tmp);
    }
    fin.close();
}

string printVal(const Value* val){
	string tmp;
    raw_string_ostream rso(tmp);
    val->print(rso);
    if(rso.str().length() > 500){
        return "too long";
    }else{
        return rso.str();
    }
}

string printType(const Type* val){
	string tmp;
    raw_string_ostream rso(tmp);
    val->print(rso);
    if(rso.str().length() > 200){
        return "too long";
    }else{
        return rso.str();
    }
}

string getRealName(string str){
    if(str.find("struct.") != string::npos){
        size_t nd = str.rfind("."), t = 0;
        if(nd != string::npos){
            string suffix = str.substr(nd + 1);
            try{
                stoi(suffix, &t, 10);
            }catch(...){
                t = 0;
            }
            if(t >= suffix.size()){
                str.erase(nd);
            }
        }
        return str;
    }else{
        return "";
    }
}

GlobalVariable* getSpecificGV(SVFModule* svfmod){
    for(auto ii = svfmod->global_begin(), ie = svfmod->global_end(); ii != ie; ii++){
        if((*ii)->getName().str() == SpecificGV){
            return *ii;
        }
    }
    return nullptr;
}

bool checkIfFuncPtrFd(GlobalVariable* gv, int fd){
    Type* realType = nullptr;
    if(gv->getType()->getPointerElementType()->isStructTy()){
        realType = gv->getType()->getPointerElementType();
    }else if(gv->getType()->getPointerElementType()->isArrayTy()
        && gv->getType()->getPointerElementType()->getArrayElementType()->isStructTy()){
        realType = gv->getType()->getPointerElementType()->getArrayElementType();
    }else if(gv->getType()->getPointerElementType()->isFunctionTy()){
        return true;
    }else {
        return false;
    }
    int i = 0;
    for (auto fdType : SymbolTableInfo::SymbolInfo()->getStructInfoIter(realType)->second->getFlattenFieldTypes()){
        if(fd == i){
            if(fdType->isPointerTy() && fdType->getPointerElementType()->isFunctionTy()){
                return true;
            }
        }
        i++;
    }
    return false;
}

void addSVFAddrFuncs(GlobalContext *GCtx, SVFModule* svfModule, SVFIR* pag){
	for(auto F : *svfModule){
		auto funcnode = dyn_cast<PAGNode>(pag->getGNode(pag->getValueNode(F->getLLVMFun())));
		if(funcnode->hasOutgoingEdge()){
			GCtx->SVFAddressTakenFuncs.insert(F->getLLVMFun());
		}
	}
}

void checkVars(SVFIR* pag){
    auto num = pag->getPAGNodeNum();
    for(u32_t i = 0; i < num; i++){
        if(SVFUtil::isa<DummyValVar>(pag->getGNode(i))){
            errs() << "dummy val: " << i << "\n";
        }
        if(SVFUtil::isa<DummyObjVar>(pag->getGNode(i))){
            errs() << "dummy obj: " << i << "\n";
        }
    }
}

StructType* ifPointToStruct(const Type* tp){
    if(tp->isPointerTy() && (tp->getNumContainedTypes() > 0)){
        return dyn_cast<StructType>(tp->getNonOpaquePointerElementType());
    }
    return nullptr;
}
#endif