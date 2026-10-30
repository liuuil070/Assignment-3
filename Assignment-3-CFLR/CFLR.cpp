/**
 * CFLR.cpp
 * @author kisslune 
 */

#include "A4Header.h"

using namespace SVF;
using namespace llvm;
using namespace std;

int main(int argc, char **argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVFIRBuilder builder;
    auto pag = builder.build();
    pag->dump();

    CFLR solver;
    solver.buildGraph(pag);
    // TODO: complete this method
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    // TODO: complete this function. The implementations of graph and worklist are provided.
    //  You need to:
    //  1. implement the grammar production rules into code;
    //  2. implement the dynamic-programming CFL-reachability algorithm.
    //  You may need to add your new methods to 'CFLRGraph' and 'CFLR'.
    if (!graph)
        return;

    // PT runs from a pointer to an object; PTBar is its inverse.
    // PT -> AddrBar | CopyBar PT | LoadBar LV | PTBar SV
    // LV -> PT PT; SV -> StoreBar PT.
    // Include the reversed production for every rule.
    const pair<EdgeLabel, EdgeLabel> unaryRules[] = {
        {PT, AddrBar}, {PTBar, Addr}
    };
    struct BinaryRule
    {
        EdgeLabel lhs;
        EdgeLabel first;
        EdgeLabel second;
    };
    const BinaryRule binaryRules[] = {
        {PT, CopyBar, PT}, {PTBar, PTBar, Copy},
        {PT, LoadBar, LV}, {PTBar, LVBar, Load},
        {LV, PT, PT}, {LVBar, PTBar, PTBar},
        {PT, PTBar, SV}, {PTBar, SVBar, PT},
        {SV, StoreBar, PT}, {SVBar, PTBar, Store}
    };

    // The supplied graph omits GEP edges. Project newly discovered objects
    // onto the fields accessed by their pointers without merging distinct fields.
    auto* pag = SVFIR::getPAG();
    unordered_map<unsigned, vector<const GepStmt*>> fieldAccesses;
    for (const auto* stmt : pag->getSVFStmtSet(SVFStmt::Gep))
    {
        const auto* gep = SVFUtil::cast<GepStmt>(stmt);
        fieldAccesses[gep->getRHSVarID()].push_back(gep);
    }

    workList.clear();
    for (const auto& node : graph->getSuccessorMap())
        for (const auto& label : node.second)
            for (unsigned dst : label.second)
                workList.push(CFLREdge(node.first, dst, label.first));

    while (!workList.empty())
    {
        const CFLREdge edge = workList.pop();
        vector<CFLREdge> derived;
        if (edge.label == PT)
        {
            auto accesses = fieldAccesses.find(edge.src);
            if (accesses != fieldAccesses.end())
            {
                const auto* object = pag->getBaseObject(edge.dst);
                for (const auto* gep : accesses->second)
                {
                    set<unsigned> fields;
                    if (pag->isBlkObjOrConstantObj(edge.dst) || object->isFieldInsensitive())
                        fields.insert(edge.dst);
                    else if (gep->isVariantFieldGep())
                    {
                        // An unknown offset may select any field in this object.
                        fields.insert(object->getId());
                        for (unsigned offset = 0; offset < object->getMaxFieldOffsetLimit(); ++offset)
                            fields.insert(pag->getGepObjVar(object, offset));
                    }
                    else
                        fields.insert(pag->getGepObjVar(edge.dst, gep->getConstantStructFldIdx()));

                    for (unsigned field : fields)
                    {
                        derived.emplace_back(gep->getLHSVarID(), field, PT);
                        derived.emplace_back(field, gep->getLHSVarID(), PTBar);
                    }
                }
            }
        }
        for (const auto& rule : unaryRules)
            if (edge.label == rule.second)
                derived.emplace_back(edge.src, edge.dst, rule.first);

        for (const auto& rule : binaryRules)
        {
            // Use the new edge as the first symbol: X -> Y Z.
            if (edge.label == rule.first)
            {
                const auto& successors = graph->getSuccessorMap();
                auto node = successors.find(edge.dst);
                if (node != successors.end())
                {
                    auto label = node->second.find(rule.second);
                    if (label != node->second.end())
                        for (unsigned dst : label->second)
                            derived.emplace_back(edge.src, dst, rule.lhs);
                }
            }

            // Also use it as the second symbol: X -> Z Y.
            if (edge.label == rule.second)
            {
                const auto& predecessors = graph->getPredecessorMap();
                auto node = predecessors.find(edge.src);
                if (node != predecessors.end())
                {
                    auto label = node->second.find(rule.first);
                    if (label != node->second.end())
                        for (unsigned src : label->second)
                            derived.emplace_back(src, edge.dst, rule.lhs);
                }
            }
        }

        // Insert after traversal: unordered-map/set growth can invalidate iterators.
        for (const CFLREdge& next : derived)
        {
            if (!graph->hasEdge(next.src, next.dst, next.label))
            {
                graph->addEdge(next.src, next.dst, next.label);
                workList.push(next);
            }
        }
    }
}
