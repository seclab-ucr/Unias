#ifndef HAGVA_HYBRIDALGORITHM_H
#define HAGVA_HYBRIDALGORITHM_H
#include "SVF-FE/SVFIRBuilder.h"
#include <functional>
#include <set>
#include <queue>
#include <unordered_set>
#include "Util.hpp"

using namespace SVF;
using namespace std;
using namespace llvm;

class PNwithOffset{
public:
    // const PAGNode* pagnode;
    s64_t offset;
    bool isVariant = false;
    bool curFlow;
    PNwithOffset(s64_t os, bool cf) : offset(os), curFlow(cf){

    }
};

using typeStack = stack<PNwithOffset>;

class Unias{
public:
    unordered_set<PAGEdge*> visitedEdges;
    unordered_set<PAGNode*> visitedNodes;
    typeStack AnalysisStack;
    map<s64_t, unordered_set<PAGNode*>> Aliases;
    unordered_map<NodeID, unordered_set<NodeID>> *Real2Formal;
    unordered_map<NodeID, unordered_set<NodeID>> *Formal2Real;
    unordered_map<NodeID, unordered_set<NodeID>> *Ret2Call;
    unordered_map<NodeID, unordered_set<NodeID>> *Call2Ret;
    unordered_map<const StructType*, unordered_map<u32_t, unordered_set<PAGEdge*>>> *typebasedShortcuts;
    unordered_map<const StructType*, unordered_set<PAGEdge*>> *fdinsensitiveShortcuts;
    unordered_map<const StructType*, unordered_set<PAGEdge*>> *castSites;
    SVFIR *pag;
    bool taked = false;

    bool ifValidForShortcut(PAGEdge* edge, u32_t threshold){
        if(edge->getSrcNode()->getType()){
            if(auto sttype = ifPointToStruct(edge->getSrcNode()->getType())){
                auto offset = dyn_cast<GepStmt>(edge)->accumulateConstantOffset();
                if((*typebasedShortcuts)[sttype][offset].size() + (*fdinsensitiveShortcuts)[sttype].size() + (*castSites)[sttype].size() < threshold){
                    return true;
                }
            }
        }
        return false;
    }

    void Prop(PAGNode* nxt, PAGEdge* eg, bool state, int depth){
        if(visitedEdges.size() > 15){
            return;
        }
        if(eg && !visitedEdges.insert(eg).second){
            return;
        }
        if(eg == nullptr && !visitedNodes.insert(nxt).second){
            return;
        }
        ComputeAlias(nxt, state, depth);

        if(eg == nullptr){
            visitedNodes.erase(nxt);
        }else{
            visitedEdges.erase(eg);
        }
    }

    void ComputeAlias(PAGNode* cur, bool state, int depth){
        if(cur->getId() < 10){
            return;
        }
        if(AnalysisStack.size() == 1){
            Aliases[AnalysisStack.top().offset].insert(cur);
        }
        
        for(auto edge : cur->getOutgoingEdges(PAGEdge::Load)){
            if(AnalysisStack.size() > 1){
                auto &topItem = AnalysisStack.top();
                // if(topItem.curFlow == false && (topItem.isVariant || topItem.offset == 0)){
                if(topItem.isVariant || topItem.offset == 0){
                    AnalysisStack.pop();
                    Prop(edge->getDstNode(), edge, false, depth);
                    AnalysisStack.push(topItem);
                }
            }
        }

        if(state){
            for(auto edge : cur->getIncomingEdges(PAGEdge::Store)){
                if(AnalysisStack.size() > 1){
                    auto &topItem = AnalysisStack.top();
                    if(topItem.curFlow == true && (topItem.isVariant || topItem.offset == 0)){
                        AnalysisStack.pop();
                        Prop(edge->getSrcNode(), edge, true, depth);
                        AnalysisStack.push(topItem);
                    }
                }
            }
        }

        for(auto edge : cur->getOutEdges()){
            switch(edge->getEdgeKind()){
                case PAGEdge::Copy:
                case PAGEdge::Ret:
                case PAGEdge::Call:{
                    // if(AnalysisStack.size() == 1){
                    //     Aliases.insert(dstNode);
                    // }
                    Prop(edge->getDstNode(), edge, false, depth);
                    break;
                }
                default:{
                    break;
                }
            }
        }

        for(auto formal : (*Real2Formal)[cur->getId()]){
            Prop(pag->getGNode(formal), nullptr, false, depth);
        }

        for(auto callinst : (*Ret2Call)[cur->getId()]){
            Prop(pag->getGNode(callinst), nullptr, false, depth);
        }

        if(state){
            for(auto real : (*Formal2Real)[cur->getId()]){
                Prop(pag->getGNode(real), nullptr, true, depth);
            }
        }

        if(state){
            for(auto ret : (*Call2Ret)[cur->getId()]){
                Prop(pag->getGNode(ret), nullptr, true, depth);
            }
        }

        if(state){
            for(auto edge : cur->getInEdges()){
                switch (edge->getEdgeKind()){
                    case PAGEdge::Copy:
                    case PAGEdge::Ret:
                    case PAGEdge::Call:{
                        Prop(edge->getSrcNode(), edge, true, depth);
                        break;
                    }
                    default:{
                        break;
                    }
                }
            }
        }

        for(auto edge : cur->getOutgoingEdges(PAGEdge::Store)){
            auto dstNode = edge->getDstNode();
            PNwithOffset newTypeInfo(0, false);
            AnalysisStack.push(newTypeInfo);
            Prop(dstNode, edge, true, depth);
            AnalysisStack.pop();
        }

        if(state){
            for(auto edge : cur->getIncomingEdges(PAGEdge::Load)){
                auto srcNode = edge->getSrcNode();
                PNwithOffset newTypeInfo(0, true);
                AnalysisStack.push(newTypeInfo);
                Prop(srcNode, edge, true, depth);
                AnalysisStack.pop();
            }
        }

        if(state){
            for(auto edge : cur->getIncomingEdges(PAGEdge::Gep)){
                if(!AnalysisStack.empty()){
                    auto &topItem = AnalysisStack.top();
                    if(!topItem.isVariant){
                        auto gepedge = dyn_cast<GepStmt>(edge);
                        if(gepedge->isVariantFieldGep() || !gepedge->isConstantOffset()){
                            topItem.isVariant = true;
                            Prop(edge->getSrcNode(), edge, true, depth);
                        }else{
                            // Consider taking shortcut?
                            if(!taked && ifValidForShortcut(edge, 50)){
                                taked = true;
                                auto sttype = ifPointToStruct(edge->getSrcNode()->getType());
                                for(auto dstShort : (*typebasedShortcuts)[sttype][gepedge->accumulateConstantOffset()]){
                                    Prop(dstShort->getDstNode(), dstShort, false, depth);
                                }
                                for(auto dstShort : (*fdinsensitiveShortcuts)[sttype]){
                                    Prop(dstShort->getDstNode(), dstShort, false, depth);
                                }
                                for(auto dstCast : (*castSites)[sttype]){
                                    if(dstCast->getSrcNode()->getType() == sttype){
                                        // Cast To
                                        topItem.offset -= gepedge->accumulateConstantOffset();
                                        Prop(dstCast->getDstNode(), dstCast, false, depth);
                                        topItem.offset += gepedge->accumulateConstantOffset();
                                    }else{
                                        // Cast From
                                        topItem.offset -= gepedge->accumulateConstantOffset();
                                        Prop(dstCast->getSrcNode(), dstCast, true, depth);
                                        topItem.offset += gepedge->accumulateConstantOffset();
                                    }
                                }
                                taked = false;
                            }else{
                                topItem.offset -= gepedge->accumulateConstantOffset();
                                Prop(edge->getSrcNode(), edge, true, depth);
                                topItem.offset += gepedge->accumulateConstantOffset();
                            }

                        }
                    }
                }
            }
        }

        for(auto edge : cur->getOutgoingEdges(PAGEdge::Gep)){
            if(!AnalysisStack.empty()){
                auto &topItem = AnalysisStack.top();
                if(!topItem.isVariant){
                    auto gepedge = dyn_cast<GepStmt>(edge);
                    if(gepedge->isVariantFieldGep() || !gepedge->isConstantOffset()){
                        topItem.isVariant = true;
                        Prop(edge->getDstNode(), edge, true, depth);
                    }else{
                        topItem.offset += gepedge->accumulateConstantOffset();
                        Prop(edge->getDstNode(), edge, true, depth);
                        topItem.offset -= gepedge->accumulateConstantOffset();
                    }
                }else{
                    Prop(edge->getDstNode(), edge, true, depth);
                }
            }
        }
    }
};

#endif