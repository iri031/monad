/**
 * kildall.hpp
 * 
 * This file contains the implementation of the Kildall algorithm for dataflow analysis.
 * Inspired by https://compcert.org/doc/html/compcert.backend.Kildall.html
 */

// Standard library includes
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <functional>
#include <iostream>
#include <limits>
#include <optional>
#include <utility>
#include <variant>

// Boost includes
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/integer.hpp>
#include "sparse_map.hpp"
#include "evm.hpp"

using NodeID = uint16_t;

template<typename L>
struct Semilattice {
    // L is the value type

    // lub: Modifies 'a' in place to be the least upper bound of 'a' and 'b' if false is returned, a must be unchanged.
    static bool lub(L& a, const L& b);

    // beq: L x L -> bool (equality)
    static bool beq(const L& a, const L& b); // should not be needed anymore as now lub returns a bool

    // bot: L (bottom element)
    static L bot();

    static void print(std::ostream& os, const L& value);
};


// NodeSet interface
template<typename NS>
struct NodeSet {
    // NS is the type of the node set

    // Add a node to the set
    static void add(NodeID n, NS& s);

    // Pick and remove a node from the set
    // Returns an optional node
    static NodeID pick(NS& s);

    // Create an empty node set
    static void clear(NS& s);

    // Check if the node set is empty
    static bool is_empty(const NS& s);

    // Check if a node is in the set
    // static bool contains(const NS& s, int n);

    static void print(std::ostream& os, const NS& value);
};

template<size_t Cutoff>
struct Successors {
    FixedSizeArray<NodeID, Cutoff+1> succs;
    bool includeAllJumpDests{false};
};

#define DEBUG_KILDALL 1 
// DataflowSolver class template
template<typename L, typename NS, typename Semilattice, typename NodeSet, uint16_t MAX_BYTECODESIZE, uint16_t MAX_BBLOCKS, size_t Cutoff>
class DataflowSolver {
public:

    using TransfSuccessors = std::function<void(const ParsedBytecode<MAX_BYTECODESIZE, MAX_BBLOCKS>&, NodeID, L&, Successors<Cutoff>&)>;
    using PrintStateFunction = std::function<void(const ParsedBytecode<MAX_BYTECODESIZE, MAX_BBLOCKS>&, const SparseMap<L, MAX_BYTECODESIZE, MAX_BBLOCKS>&)>;

    // Constructor
    DataflowSolver(const TransfSuccessors& transfSuccessors, const PrintStateFunction& printStateFunction)
        : transfSuccessors(transfSuccessors), printStateFunction(printStateFunction) {}

    // Compute the fixpoint starting from the entry node and initial value
    const SparseMap<L, MAX_BYTECODESIZE, MAX_BBLOCKS> & fixpoint(NodeID entryNode, const L& entryValue) {
        initialize_state(entryNode, entryValue);
        fixpoint_from();
        return state.aval;
    }

    // State structure
    struct State {
        SparseMap<L, MAX_BYTECODESIZE, MAX_BBLOCKS> aval;  // Mapping from nodes to L
        NS worklist;            // Set of nodes to process
    };

    State state;  // Class member instead of parameter
    TransfSuccessors transfSuccessors;
    ParsedBytecode<MAX_BYTECODESIZE, MAX_BBLOCKS> parsedBytecode;
    size_t steps{0};

private:
    void printState(std::ostream& os, const State& state) {
        os << "State {\n  Abstract Values:\n";
        
        // Print abstract values map
        for (const auto& [node, value] : state.aval) {
        os << "    Node " << node << ": ";
        Semilattice::print(os, value);
            os << "\n";
        }
        
        // Print worklist using NodeSet's print function
        os << "  Worklist: ";
        NodeSet::print(os, state.worklist);
        os << "\n}";
    }   

    // Initialize the starting state
    void initialize_state(NodeID enode, const L& eval) {
        state.aval.clear();  // Reset the map
        state.aval.insert(enode, eval);
        NodeSet::clear(state.worklist);
        NodeSet::add(enode, state.worklist);
    }

    // Main fixpoint computation
    void fixpoint_from() {
        steps = 0;
        while (!NodeSet::is_empty(state.worklist)) {
            steps++;
#if DEBUG_KILDALL
            std::cout << "Steps: " << steps << std::flush;
#endif
            step();
        }
        std::cout << "\rCompleted in " << steps << " steps." << std::endl;
    }

    // Perform one iteration step
    void step() {
#if DEBUG_KILDALL
        //std::cout << "\nInitial State:\n";
        //printStateFunction(parsedBytecode, state.aval);
        std::cout << "worklist: ";
        NodeSet::print(std::cout, state.worklist);
        std::cout << "\n";
#endif

        NodeID n = NodeSet::pick(state.worklist);

#if DEBUG_KILDALL
        std::cout << "\nProcessing node " << n << "\n";
#endif

        L val = abstr_value_clone(n);
#if DEBUG_KILDALL
        std::cout << "\nAbstract value for node " << n << ":\n";
        Semilattice::print(std::cout, val);
        std::cout << "\n";
#endif

        Successors<Cutoff> succs;
        transfSuccessors(parsedBytecode, n, val, succs);
        propagate_succ_list(val, succs);
#if DEBUG_KILDALL
        std::cout << "\nSuccessors of node " << n << ": ";
        for (int i=0; i<succs.succs.size; i++) {
            std::cout << succs.succs[i] << ":";
            Semilattice::print(std::cout, state.aval.get(succs.succs[i]));
            std::cout << "\n" << std::flush;
        }
        std::cout << "\n";
#endif

        
#if DEBUG_KILDALL
        std::cout << "\n----------------------------------------\n";
#endif
    }
    // Get the abstract value for a node, defaulting to bottom if not present
    L abstr_value_clone(NodeID n) const {
        return state.aval.get(n);
    }


    const SparseMap<L, MAX_BYTECODESIZE, MAX_BBLOCKS>& get_solns() const {
        return state.aval;
    }

    // Propagate the value to a successor node
    void propagate_succ(const L& out, NodeID n) {
        if (n==21851) {
            std::cout << "propagating " << " to " << n << "\n";
            Semilattice::print(std::cout, out);
            std::cout << "\n";
        }
        if (!state.aval.exists(n)) {
            state.aval.insert(n, out);
            NodeSet::add(n, state.worklist);
        } else {
            L &oldl = state.aval.get(n);
            bool changed = Semilattice::lub(oldl, out);
            if (changed) {
                //state.aval[n] = newl; modified in-place
                NodeSet::add(n, state.worklist);
            }
        }
    }

    // Propagate the value to a list of successor nodes
    void propagate_succ_list(const L& out, const Successors<Cutoff>& succs) {
        // Iterate over successors in reverse order
        for (int i=succs.succs.size-1; i>=0; i--) {
            propagate_succ(out, succs.succs[i]);
        }
        if (succs.includeAllJumpDests) {
            #if DEBUG_KILDALL
            std::cout << "\nIncluding all jump destinations\n";
            #endif
            for (int n =0; n < parsedBytecode.jumpDestOffsets.size; n++) {
                propagate_succ(out, parsedBytecode.jumpDestOffsets[n]);
                #if DEBUG_KILDALL
                std::cout << "Including jump destination " << parsedBytecode.jumpDestOffsets[n] << "\n";
                #endif
            }
        }
    }

    PrintStateFunction printStateFunction;  // Member variable to store the print function
};
