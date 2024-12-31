/**
 * inst_kildall.cpp
 * 
 * This file contains the instantiation of the Kildall algorithm for to statically predict the possible values
 *  (as a set of constants) of each stack element at each program point in an EVM bytecode program.
 */

#include "kildall.hpp"
#include <sys/stat.h>
#include <errno.h>
#include <memory> 
#include <unordered_set>
#include <boost/container_hash/hash.hpp>
#include "expr.hpp"
//#include "evm.hpp"

static constexpr size_t MAX_BYTECODESIZE = 24600;
static constexpr size_t MAX_BBLOCKS = 1829;


// Use the boost::multiprecision namespace
namespace mp = boost::multiprecision;

// Word256 type using Boost.Multiprecision
using Word256 = mp::uint256_t;


struct CompleteSetTag {};
//possible values of each element of the stack
template<size_t N, typename T>
struct SizedArray {
    std::array<T, N> values;
    uint8_t size=0;  // tracks actual number of elements in use

    // Reset the set to empty
    void reset() {
        size = 0;
    }

    bool empty() const {
        return size == 0;
    }

    // Add an element to the end
    // Returns true if successful, false if set is full
    bool push_back(const T& value) {
        static_assert(N <= 256, "N must be less than or equal to 256");
        assert(value<std::numeric_limits<uint32_t>::max());
        if (size >= N) {
            return false;  // Set is full
        }
        values[size++] = value;
        return true;
    }

    // Copy between differently sized FixedValueSets
    template<size_t M>
    void copyFrom(const SizedArray<M, T>& other) {
        // Caller must ensure other.size <= N
        size = other.size;
        std::copy(other.values.begin(), 
                 other.values.begin() + other.size, 
                 values.begin());
    }

    // Regular copy assignment operator
    SizedArray& operator=(const SizedArray& other) {
        if (this != &other) {  // Guard against self-assignment
            size = other.size;
            std::copy(other.values.begin(), 
                     other.values.begin() + other.size, 
                     values.begin());
        }
        return *this;
    }

    void sortAndDeduplicate() {
        if (size <= 1) return;  // Already sorted and unique if 0 or 1 elements
        
        // Sort the active portion of the array
        std::sort(values.begin(), values.begin() + size);
        
        // Remove duplicates using std::unique and update size
        auto newEnd = std::unique(values.begin(), values.begin() + size);
        size = std::distance(values.begin(), newEnd);
    }

    // Add iterator support
    const T* begin() const { return values.begin(); }
    const T* end() const { return values.begin() + size; }

    // Equality operator
    bool operator==(const SizedArray& other) const {
        if (size != other.size) return false;
        // Compare only the active elements
        for (size_t i = 0; i < size; ++i) {
            if (values[i] != other.values[i]) return false;
        }
        return true;
    }
};

static constexpr size_t Cutoff = 3;

template<size_t N> 
using FixedValueSet = SizedArray<N, uint32_t>;

class ValueSet {
private:
    FixedValueSet<Cutoff> fixedValues_;
    // Default constructor - creates an empty value set


public:
    ValueSet() {
        fixedValues_.reset();
    }

    ValueSet(uint32_t val) {
        fixedValues_.reset();
        fixedValues_.push_back(val);
    }

    void push_back(uint32_t val) {
        fixedValues_.push_back(val);
    }
    void clear_push_back(uint32_t val) {
        fixedValues_.reset();
        fixedValues_.push_back(val);
    }

    void setFixedValues(const FixedValueSet<Cutoff>& fs) {  // Declaration only
        fixedValues_.copyFrom(fs);
    }

    void reset() {
        fixedValues_.reset();
    }

    // Default constructor - empty fixed set
//    ValueSet() : isComplete_(false), fixedValues_(nullptr) {}//u
    
    // CompleteSet constructor
    void makeComplete() {
        fixedValues_.size=2;
        fixedValues_.values[0]=std::numeric_limits<uint32_t>::max();
    }

    bool isComplete() const { 
        // the array is sorted (ascending order) and deduplicated. so if there are 2 elements, the first one cannot be the max value. so we use that case to represent completeSets.
        return fixedValues_.size>1 && fixedValues_.values[0]==std::numeric_limits<uint32_t>::max(); }
    
    const FixedValueSet<Cutoff>& getFixedValues() const {
        assert(!isComplete());// cannot get fixed values from CompleteSet
        return fixedValues_;
    }

    uint32_t getFixedValue(size_t index) const {
        assert(!isComplete());// cannot get fixed values from CompleteSet
        assert(index<fixedValues_.size);
        return fixedValues_.values[index];
    }

    void canonicalize() {
        assert(!isComplete());
        fixedValues_.sortAndDeduplicate();
    }
    
    size_t size() const {
        return fixedValues_.size;
    }

    // Modified Equality Operator
    bool operator==(const ValueSet& other) const {
        if (isComplete() != other.isComplete()) {
            return false;
        }
        if (isComplete()) {
            return true;  // All complete sets are equal
        }

        return getFixedValues() == other.getFixedValues();
    }

private:
    //explicit ValueSet(bool complete) : isComplete_(complete), fixedValues_() {}
};

const ValueSet emptyValueSett;
ValueSet singleton0;
ValueSet singleton1;
ValueSet s01;
static ExpressionPool epool;

void resetFactory() {
    epool.reset();
    singleton0=ValueSet(epool.e0);
    singleton1=ValueSet(epool.e1);
    assert(epool.e0< epool.e1);
    s01=ValueSet(epool.e0);
    s01.push_back(epool.e1);
}


// ValueSet itself is a semilattice with the inverse of \subseteq as the partial order.
// later, we will lift the lattice operations to StackValues, the stack of ValueSets at each program point.
struct ValueSetSemilattice {

    template<size_t BufferSize>
    static void canonicalizeTo(FixedValueSet<BufferSize> & vals, ValueSet & to) {
        vals.sortAndDeduplicate();
        
        if (vals.size > Cutoff) {
            to.makeComplete();
        } else {
            FixedValueSet<Cutoff> smallerSet;
            smallerSet.copyFrom(vals);
            to.setFixedValues(smallerSet);  // Creates new fixed set
            //to.getFixedValues().copyFrom(vals);
        }
    }

//    static ValueSet<Cutoff> botValueSet() {
//        // Return empty FixedValueSet
//        return FixedValueSet<Cutoff>{std::array<Word256, Cutoff>{}, 0};
//    }

    // TODO: run a test where this uses stdlib sort/dedup ops instead of doing this custom complex merging
    static bool lubValueSet(ValueSet& a, const ValueSet& b) {
        if (b.isComplete() && !a.isComplete()) {
            a.makeComplete();
            return true;
        }
        if (a.isComplete()) {
            return false;
        }

        const auto& va = a.getFixedValues();
        const auto& vb = b.getFixedValues();

        // Quick check: if b is empty, no modification needed
        if (vb.size == 0) {
            return false;
        }

        bool modified = false;
        FixedValueSet<Cutoff> merged;
        merged.reset();

        size_t i = 0, j = 0;
        while (i < va.size && j < vb.size) {
            if (va.values[i] < vb.values[j]) {
                if (!merged.push_back(va.values[i++])) {
                    a.makeComplete();
                    return true;
                }
            } else if (vb.values[j] < va.values[i]) {
                if (!merged.push_back(vb.values[j++])) {
                    a.makeComplete();
                    return true;
                }
                modified = true;
            } else {
                if (!merged.push_back(va.values[i])) {
                    a.makeComplete();
                    return true;
                }
                i++; j++;
            }
        }

        // Add remaining elements from va
        while (i < va.size) {
            if (!merged.push_back(va.values[i++])) {
                a.makeComplete();
                return true;
            }
        }

        // Add remaining elements from vb
        while (j < vb.size) {
            if (!merged.push_back(vb.values[j++])) {
                a.makeComplete();
                return true;
            }
            modified = true;
        }

        if (modified) {
            a.setFixedValues(merged);
        }
        return modified;
    }

    // Helper function to compare two ValueSets for equality
    static bool beqValueSet(const ValueSet& a, const ValueSet& b) {
        return a==b;
    }
};

// emlements of StackValues are the semilattice elements in the intended instantiation of the kildall algorithm. 
// below struct Semilattice<StackValues> defines the semilattice operations.    
struct StackValues {
    static constexpr size_t MaxSize = 1024;
    std::array<ValueSet, MaxSize> values;
    size_t head = 0;
    size_t size = 0;

    // Default constructor
    StackValues() = default;

    // Copy constructor with size-based optimization
    StackValues(const StackValues& other) : head(other.head), size(other.size) {
        if (size >= MaxSize * 0.9) {  // Arbitrary threshold, could be tuned
            // For nearly full stacks, just copy everything
            values = other.values;
        } else {
            // For sparse stacks, only copy active elements
            for (size_t i = 0; i < size; ++i) {
                size_t src_idx = (other.head + MaxSize - i - 1) % MaxSize;
                size_t dst_idx = (head + MaxSize - i - 1) % MaxSize;
                values[dst_idx] = other.values[src_idx];
            }
        }
    }

    // Copy assignment operator with the same optimization
    StackValues& operator=(const StackValues& other) {
        if (this != &other) {
            head = other.head;
            size = other.size;
            
            if (size >= MaxSize * 0.9) {
                values = other.values;
            } else {
                for (size_t i = 0; i < size; ++i) {
                    size_t src_idx = (other.head + MaxSize - i - 1) % MaxSize;
                    size_t dst_idx = (head + MaxSize - i - 1) % MaxSize;
                    values[dst_idx] = other.values[src_idx];
                }
            }
        }
        return *this;
    }

    // Push operation
    ValueSet& push() {  // No longer takes a value parameter
        size_t new_head = head;
        head = (head + 1) % MaxSize;
        if (size < MaxSize) {
            ++size;
        }
        // If the stack is full, the oldest value is overwritten
        // s:StackValues is an assertion that at a particular program point, the stack is a prefix of s. So, even if the stack is full, we cannot be sure this is an overflow situation because the actual stack may be a prefix. 
        // the overflow case doesnt matter because the program will terminate anyway and we want a sound (not necessarily complete) upperbound on the set of possible stack values

        return values[new_head];  // Return reference to the cell that can be modified
    }

    // Push to end variant - adds item to the bottom of the stack
    void push_to_end(const ValueSet& value) {
        assert (size < MaxSize);
        
        // Calculate the index where the new item should go
        size_t tail = (head + MaxSize - size -1) % MaxSize;
        
        values[tail] = value;
        ++size;
    }

    // Pop operation
    void pop() {
        if (size > 0) {
            head = (head + MaxSize - 1) % MaxSize;
            --size;
            // Optional: Clear the popped value
            //values[head] = ValueSet{};
        } else {
            // Handle underflow if necessary
        }
    }

    void clear() {
        head = 0;
        size = 0;
    }

    ValueSet& operator[](size_t index) {
        assert(index < size && "StackValues index out of range");
        size_t idx = (head + MaxSize - index - 1) % MaxSize;
        return values[idx];
    }

    const ValueSet& operator[](size_t index) const {
        assert(index < size && "StackValues index out of range");
        size_t idx = (head + MaxSize - index - 1) % MaxSize;
        return values[idx];
    }
};


// Helper function to print ValueSet
void printValueSet(std::ostream& os, const ValueSet& vs) {
    if (vs.isComplete()) {
        os << "*";  // Top element (complete set)
    } else {
        const auto& fixed_set = vs.getFixedValues();
        if (fixed_set.size == 1) {
            epool.printExpression(os, fixed_set.values[0]);  // Single value without braces
        } else {
            os << "{";
            for (size_t i = 0; i < fixed_set.size; ++i) {
                if (i > 0) os << ",";
                epool.printExpression(os, fixed_set.values[i]);
            }
            os << "}";
        }
    }
}

template<>
struct Semilattice<StackValues> {

// Specialization of Semilattice print function for StackValues
    static void print(std::ostream& os, const StackValues& stack) {
        os<<"[";
//        os << "Stack[size=" << stack.size << "] {\n";
        if (stack.size==0) {
            os << "]";
            return;
        }
        printValueSet(os, stack[0]);
        int dupCount=0;

        for (size_t i = 1; i < stack.size; ++i) {
            if (stack[i]==stack[i-1]) {
                ++dupCount;
            } else {
                if (dupCount>0) {
                    os << "x" << 1+dupCount;
                    dupCount=0;
                }
                os << ",";
                printValueSet(os, stack[i]);
            }
        }
        if (dupCount>0) {
            os << "x" << 1+dupCount;
        }
        os << "]";
    }

    // Modifies 'a' in place to be the least upper bound of 'a' and 'b'
    static bool lub(StackValues& a, const StackValues& b) {
#if DEBUG_KILDALL
        std::cout << "\nLUB Operation:";
        std::cout << "\nInput a: [";
        print(std::cout, a);
        std::cout << "\nInput b: [";
        print(std::cout, b);
#endif
        
        bool changed = false;
        size_t maxSize = std::min(std::max(a.size, b.size), StackValues::MaxSize);
        
        for (size_t i = 0; i < maxSize; ++i) {
            if (i >= a.size) {
                a.push_to_end(b[i]);  // Take b's value directly
                changed = true;
            } else if (i >= b.size) {
                continue;
            } else if (ValueSetSemilattice::lubValueSet(a[i], b[i])) {
                changed = true;
            }
        }
        
#if DEBUG_KILDALL
        std::cout << "\nResult: [";
        print(std::cout, a);
        std::cout << "\nChanged: " << (changed ? "true" : "false") << "\n";
#endif
        
        return changed;
    }

    // Equality check
    static bool beq(const StackValues& a, const StackValues& b) {
        if (a.size != b.size) {
            return false;
        }
        for (size_t i = 0; i < a.size; ++i) {
            if (!ValueSetSemilattice::beqValueSet(a[i], b[i])) {
                return false;
            }
        }
        return true;
    }

    // Bottom element of the semilattice
    static StackValues bot() {
        // Return an empty stack
        return StackValues();
    }

};

/** the next step is to define transferSucc which is the transfer (add successor) function needed to instantiate the kildall algorithm. */

void transferTerm(const Terminator& term, StackValues& stack) {
    // Visitor struct to handle the different terminator variants
    struct TerminatorVisitor {
        StackValues& stack;

        void operator()(TerminatorType termType) {
            switch (termType) {
                case TerminatorType::Jump:
                    // Pop one value off the stack
                    if (stack.size >= 1) {
                        stack.pop();
                    }
                    break;
                case TerminatorType::Stop:
                case TerminatorType::Return:
                case TerminatorType::Revert:
                case TerminatorType::SelfDestruct:
                    // Empty the stack
                    stack.clear();
                    break;
                default:
                    assert(false);
            }
        }

        void operator()(const Jumpi& jumpi) {
            // Pop two values off the stack
            if (stack.size >= 2) {
                stack.pop();
                stack.pop();
            }
        }

        void operator()(const Jumpdest& jumpdest) {
            // Stack remains unchanged
        }

        void operator()(const InvalidInstruction& invalid) {
            // Empty the stack
            stack.clear();
        }
    };

    // Create the visitor and apply it to the terminator
    TerminatorVisitor visitor{stack};
    std::visit(visitor, term);
}

static FixedValueSet<Cutoff*Cutoff*Cutoff> buffer;
// Helper functions for binary, unary, and ternary operations

// result and a may be the same set. this impl reads a fully before writing to result.
void binOpPairwise(const ValueSet& a, const ValueSet& b, const std::function<std::optional<uint32_t>(const uint32_t&, const uint32_t&)>& op, ValueSet & result) {
    if (a.isComplete() || b.isComplete()) {
        result.makeComplete();
        return;
    }
    buffer.reset();
    const auto& va = a.getFixedValues();
    const auto& vb = b.getFixedValues();
    for (const uint32_t& x : va) {
        for (const uint32_t& y : vb) {
            auto res = op(x, y);
            if (!res) {
                result.makeComplete();
                return;
            }
            buffer.push_back(*res);
        }
    }
    ValueSetSemilattice::canonicalizeTo(buffer, result);
}

// result and a may be the same set. this impl reads a fully before writing to result. we can optimize it by not copying to the buffer at all.
void unaryOp(const ValueSet& a, const std::function<std::optional<uint32_t>(const uint32_t&)>& op, ValueSet & result) {
    if (a.isComplete()) {
        result.makeComplete();
        return;
    }
    const auto& va = a.getFixedValues();
    buffer.reset();
    for (const uint32_t& x : va) {
        auto res = op(x);
        if (!res) {
            result.makeComplete();
            return;
        }
        buffer.push_back(*res);
    }
    ValueSetSemilattice::canonicalizeTo(buffer, result);
}

ValueSet valueSetOfBools(const bool included[2]) {
    if (included[0] && included[1]) {
        return s01;
    }
    if (included[0]) {
        return singleton0;
    }
    if (included[1]) {
        return singleton1;
    }
    return emptyValueSett;
}


void unaryCmpOp(const ValueSet& a, const std::function<std::optional<bool>(const uint32_t&)>& op, ValueSet & result) {
    if (a.isComplete()) {
        result=ValueSet(s01);
        return;
    }
    const auto& va = a.getFixedValues();
    bool included[2] = {false, false};

    for (const uint32_t& x : va) {
        auto res = op(x);
        if (res) {
            included[*res ? 1 : 0] = true;
        }
        else {
            result=ValueSet(s01);
            return;
        }
    }
    result=valueSetOfBools(included);// only 2 words (16 bytes) so this copying is ok
}


void ternaryOp(const ValueSet& a, const ValueSet& b, const ValueSet& c, const std::function<std::optional<uint32_t>(const uint32_t&, const uint32_t&, const uint32_t&)>& op, ValueSet & result) {
    if (a.isComplete() || b.isComplete() || c.isComplete()) {
        result.makeComplete();
        return;
    }
    const auto& va = a.getFixedValues();
    const auto& vb = b.getFixedValues();
    const auto& vc = c.getFixedValues();
    buffer.reset();
    for (const uint32_t& x : va) {
        for (const uint32_t& y : vb) {
            for (const uint32_t& z : vc) {
                auto res = op(x, y, z);
                if (!res) {
                    result.makeComplete();
                    return;
                }
                buffer.push_back(*res);
            }
        }
    }
    ValueSetSemilattice::canonicalizeTo(buffer, result);
}

// Define cmpOpPairwise function
void cmpOpPairwise(
    const ValueSet& valSet1,
    const ValueSet& valSet2,
    const std::function<std::optional<bool>(const uint32_t&, const uint32_t&)>& cmpOp, 
    ValueSet & result
) {
    bool included[2] = {false, false};

    if (valSet1.isComplete() ||
        valSet2.isComplete()) {
        // If any of the inputs are unknown, the result can be 0 or 1
        included[0] = true;
        included[1] = true;
    } else {
        const auto& vals1 = valSet1.getFixedValues();
        const auto& vals2 = valSet2.getFixedValues();

        for (const uint32_t& x : vals1) {
            for (const uint32_t& y : vals2) {
                auto cmpResult = cmpOp(x, y);
                if (!cmpResult) {
                    result=ValueSet(s01);
                    return;
                }
                included[*cmpResult ? 1 : 0] = true;
            }
        }
    }

    static_assert(Cutoff>=2);
    // resultSet is ordered, so array will contain {0,1} in ascending order if both present. no canonicalization needed as there are only two values
    result=valueSetOfBools(included);
}

// Function that takes an ExpressionPool and a binary operation on Word256
// Returns a function that operates on indices and returns int64_t (index of expression node)
// Returns -1 to indicate unknown value
std::function<std::optional<uint32_t>(uint32_t, uint32_t)> liftBinOp(
    std::function<Word256(const Word256&, const Word256&)> op) {

    return [op](uint32_t idx1, uint32_t idx2) -> std::optional<uint32_t> {
        std::optional<Word256> w1 = epool.getConstMaybe(idx1);
        std::optional<Word256> w2 = epool.getConstMaybe(idx2);
        if (!w1 || !w2) {
            return std::nullopt;
        }
        Word256 result = op(*w1, *w2);
        uint32_t resultIdx = epool.createConst(result);
        return resultIdx;
    };
}

std::function<std::optional<uint32_t>(uint32_t, uint32_t)> binOpExpr(ExpressionNode::Type binOpType,
    std::function<Word256(const Word256&, const Word256&)> constOp) {

    return [constOp, binOpType](uint32_t idx1, uint32_t idx2) -> std::optional<uint32_t> {
        std::optional<Word256> w1 = epool.getConstMaybe(idx1);
        std::optional<Word256> w2 = epool.getConstMaybe(idx2);
        if (w1 && w2) {
            Word256 result = constOp(*w1, *w2);
            uint32_t resultIdx = epool.createConst(result);
            return resultIdx;
        }
        auto resultIdx = epool.createBinaryOp(binOpType, idx1, idx2);
        return resultIdx;

        // if (epool.exprTooDeep(idx1) || epool.exprTooDeep(idx2))
        //return std::nullopt;
    };
}

std::function<std::optional<uint32_t>(uint32_t)> unOpExpr(ExpressionNode::Type unOpType,
    std::function<Word256(const Word256&)> constOp) {

    return [constOp, unOpType](uint32_t idx) -> std::optional<uint32_t> {
        std::optional<Word256> w = epool.getConstMaybe(idx);
        if (w) {
            Word256 result = constOp(*w);
            uint32_t resultIdx = epool.createConst(result);
            return resultIdx;
        }
        auto resultIdx = epool.createUnaryOp(unOpType, idx);
        return resultIdx;
    };
}

std::function<std::optional<uint32_t>(uint32_t, uint32_t, uint32_t)> liftTernaryOp(
    std::function<Word256(const Word256&, const Word256&, const Word256&)> op) {

    return [op](uint32_t idx1, uint32_t idx2, uint32_t idx3) -> std::optional<uint32_t> {
        std::optional<Word256> w1 = epool.getConstMaybe(idx1);
        std::optional<Word256> w2 = epool.getConstMaybe(idx2);
        std::optional<Word256> w3 = epool.getConstMaybe(idx3);
        if (!w1 || !w2 || !w3) {
            return std::nullopt;
        }
        Word256 result = op(*w1, *w2, *w3);
        uint32_t resultIdx = epool.createConst(result);
        return resultIdx;
    };
}

std::function<std::optional<bool>(uint32_t, uint32_t)> liftCmpBinOp(
    std::function<bool(const Word256&, const Word256&)> op) {

    return [op](uint32_t idx1, uint32_t idx2) -> std::optional<bool> {
        std::optional<Word256> w1 = epool.getConstMaybe(idx1);
        std::optional<Word256> w2 = epool.getConstMaybe(idx2);
        if (!w1 || !w2) {
            return std::nullopt;
        }
        return op(*w1, *w2);
    };
}

std::function<std::optional<bool>(uint32_t)> liftCmpUnop(
    std::function<bool(const Word256&)> op) {

    return [op](uint32_t idx) -> std::optional<bool> {
        std::optional<Word256> w = epool.getConstMaybe(idx);
        if (!w) {
            return std::nullopt;
        }
        return op(*w);
    };
}

std::function<std::optional<uint32_t>(uint32_t)> liftUnOp(
    std::function<Word256(const Word256&)> op) {

    return [op](uint32_t idx) -> std::optional<uint32_t> {
        std::optional<Word256> w = epool.getConstMaybe(idx);
        if (!w) {
            return std::nullopt;
        }
        Word256 result = op(*w);
        uint32_t resultIdx = epool.createConst(result);
        return resultIdx;
    };
}

// Visitor struct to handle the different instruction variants
struct InstructionVisitor {
    StackValues& stack;
    bool underflow;

    InstructionVisitor(StackValues& s) : stack(s), underflow(false) {}

    void binaryOperation(const std::function<std::optional<uint32_t>(const uint32_t&, const uint32_t&)>& op) {
        if (stack.size >= 2) {
            ValueSet & val1 = stack[1]; // Second from top
            const ValueSet& val0 = stack[0]; // Top of stack
            ValueSet result;

            // Compute result
            binOpPairwise(val0, val1, op, result);

            stack[1]=result;
            // Pop two elements and push result
            stack.pop();
        } else {
            // Handle stack underflow
            handleUnderflow();
        }
    }

    void cmpOperation(const std::function<std::optional<bool>(const uint32_t&, const uint32_t&)>& op) {
        if (stack.size >= 2) {
            ValueSet& val1 = stack[1]; // Second from top
            const ValueSet& val0 = stack[0]; // Top of stack
            ValueSet result;

            // Compute result
            cmpOpPairwise(val0, val1, op, result);
            stack[1]=result;

            // Pop two elements and push result
            stack.pop();
        } else {
            // Handle stack underflow
            handleUnderflow();
        }
    }

    void unaryCmpOperation(const std::function<std::optional<bool>(const uint32_t&)>& op) {
        if (stack.size >= 1) {
            ValueSet& val0 = stack[0]; // Top of stack
            ValueSet result;

            // Compute result
            unaryCmpOp(val0, op, result);
            stack[0]=result;

            // Pop one element and push result
        } else {
            // Handle stack underflow
            handleUnderflow();
        }
    }
    // Function to perform unary operation
    void unaryOperation(const std::function<std::optional<uint32_t>(const uint32_t&)>& op) {
        if (stack.size >= 1) {
            ValueSet& val0 = stack[0]; // Top of stack
            ValueSet result;

            // Compute result
            unaryOp(val0, op, result);
            stack[0]=result;

            // Pop one element and push result
        } else {
            // Handle stack underflow
            handleUnderflow();
        }
    }

    // Function to perform ternary operation
    void ternaryOperation(const std::function<std::optional<uint32_t>(const uint32_t&, const uint32_t&, const uint32_t&)>& op) {
        if (stack.size >= 3) {
            ValueSet& val2 = stack[2]; // Third from top
            const ValueSet& val1 = stack[1]; // Second from top
            const ValueSet& val0 = stack[0]; // Top of stack
            ValueSet result;
            // Compute result
            ternaryOp(val0, val1, val2, op, result);
            stack[2]=result;

            // Pop three elements and push result
            stack.pop();
            stack.pop();
        } else {
            // Handle stack underflow
            handleUnderflow();
        }
    }

    // Function to handle stack underflow
    void handleUnderflow() {
        underflow = true;
        //stack.clear();
        //stack.push(CompleteSetTag{});
    }

void operator()(InstructionType instrType) {
        switch (instrType) {
            // Arithmetic Operations
            case InstructionType::Add:
                binaryOperation(binOpExpr(ExpressionNode::Type::Add, [](const Word256& x, const Word256& y) { return x + y; }));
                break;
            case InstructionType::Sub:
                binaryOperation(binOpExpr(ExpressionNode::Type::Sub, [](const Word256& x, const Word256& y) { return x - y; }));
                break;
            case InstructionType::Mul:
                binaryOperation(binOpExpr(ExpressionNode::Type::Mul, [](const Word256& x, const Word256& y) { return x * y; }));
                break;
            case InstructionType::Div:
                binaryOperation(binOpExpr(ExpressionNode::Type::Div, [](const Word256& x, const Word256& y) { return y != 0 ? x / y : 0; }));
                break;
            case InstructionType::Sdiv:
                binaryOperation(liftBinOp([](const Word256& x, const Word256& y) {
                    mp::int256_t sx = mp::int256_t(x);
                    mp::int256_t sy = mp::int256_t(y);
                    mp::int256_t res = (sy != 0) ? sx / sy : 0;
                    return Word256(res);
                }));
                break;
            case InstructionType::Mod:
                binaryOperation(binOpExpr(ExpressionNode::Type::Mod, [](const Word256& x, const Word256& y) { return y != 0 ? x % y : 0; }));
                break;
            case InstructionType::Smod:
                binaryOperation(liftBinOp([](const Word256& x, const Word256& y) {
                    mp::int256_t sx = mp::int256_t(x);
                    mp::int256_t sy = mp::int256_t(y);
                    mp::int256_t res = (sy != 0) ? sx % sy : 0;
                    return Word256(res);
                }));
                break;
            case InstructionType::Addmod:
                ternaryOperation(liftTernaryOp([](const Word256& x, const Word256& y, const Word256& m) { return m != 0 ? (x + y) % m : 0; }));
                break;
            case InstructionType::Mulmod:
                ternaryOperation(liftTernaryOp([](const Word256& x, const Word256& y, const Word256& m) { return m != 0 ? (x * y) % m : 0; }));
                break;
            case InstructionType::Exp:
                binaryOperation(binOpExpr(ExpressionNode::Type::Exp, [](const Word256& x, const Word256& y) {
                    return mp::pow(x, y.convert_to<unsigned>());
                }));
                break;
            case InstructionType::Signextend:
                binaryOperation(liftBinOp([](const Word256& x, const Word256& y) {
                    if (x < 32) {
                        size_t bitIndex = 8 * x.convert_to<size_t>() + 7;
                        Word256 mask = (Word256(1) << bitIndex) - 1;
                        Word256 signBit = Word256(1) << bitIndex;
                        if ((y & signBit) != 0) {
                            return y | (~mask);
                        } else {
                            return y & mask;
                        }
                    } else {
                        return y;
                    }
                }));
                break;

            // Comparison & Bitwise Logic Operations
            case InstructionType::Lt:
                cmpOperation(liftCmpBinOp([](const Word256& x, const Word256& y) { return x < y; }));
                break;
            case InstructionType::Gt:
                cmpOperation(liftCmpBinOp([](const Word256& x, const Word256& y) { return x > y; }));
                break;
            case InstructionType::Slt:
                cmpOperation(liftCmpBinOp([](const Word256& x, const Word256& y) {
                    mp::int256_t sx = mp::int256_t(x);
                    mp::int256_t sy = mp::int256_t(y);
                    return sx < sy;
                }));
                break;
            case InstructionType::Sgt:
                cmpOperation(liftCmpBinOp([](const Word256& x, const Word256& y) {
                    mp::int256_t sx = mp::int256_t(x);
                    mp::int256_t sy = mp::int256_t(y);
                    return sx > sy;
                }));
                break;
            case InstructionType::Eq:
                cmpOperation(liftCmpBinOp([](const Word256& x, const Word256& y) { return x == y; }));
                break;
            case InstructionType::Iszero:
                unaryCmpOperation(liftCmpUnop([](const Word256& x) { return x == 0; }));
                break;
            case InstructionType::And:
                binaryOperation(binOpExpr(ExpressionNode::Type::And, [](const Word256& x, const Word256& y) { return x & y; }));
                break;
            case InstructionType::Or:
                binaryOperation(binOpExpr(ExpressionNode::Type::Or, [](const Word256& x, const Word256& y) { return x | y; }));
                break;
            case InstructionType::Xor:
                binaryOperation(binOpExpr(ExpressionNode::Type::Xor, [](const Word256& x, const Word256& y) { return x ^ y; }));
                break;
            case InstructionType::Not:
                unaryOperation(unOpExpr(ExpressionNode::Type::Not, [](const Word256& x) { return ~x; }));
                break;
            case InstructionType::Byte://TODO: make expression node if not constant
                binaryOperation(liftBinOp([](const Word256& x, const Word256& y) {
                    if (x >= 32) {
                        return Word256(0);
                    } else {
                        size_t byteIndex = 31 - x.convert_to<size_t>();
                        Word256 byteValue = (y >> (byteIndex * 8)) & 0xFF;
                        return byteValue;
                    }
                }));
                break;
            case InstructionType::Shl:
                binaryOperation(binOpExpr(ExpressionNode::Type::Shl, [](const Word256& x, const Word256& y) { 
                    return y << x.convert_to<unsigned>(); 
                }));
                break;
            case InstructionType::Shr:
                binaryOperation(binOpExpr(ExpressionNode::Type::Shr, [](const Word256& x, const Word256& y) { 
                    return y >> x.convert_to<unsigned>(); 
                }));
                break;
            case InstructionType::Sar:// TODO: make expression node if not constant
                binaryOperation(liftBinOp([](const Word256& x, const Word256& y) {
                    mp::int256_t sy = mp::int256_t(y);
                    mp::int256_t res = sy >> x.convert_to<unsigned>();
                    return Word256(res);
                }));
                break;

            // SHA3 (Keccak-256)
            case InstructionType::SHA3:
                if (stack.size >= 2) {
                    stack[1].makeComplete(); // TODO: implement it as a unary operation
                    stack.pop(); // offset
                } else {
                    handleUnderflow();
                }
                break;

            // Environmental Information
            case InstructionType::Address:
                stack.push().clear_push_back(epool.createAddress());
                break;
            case InstructionType::Callvalue:
                stack.push().clear_push_back(epool.createCallvalue());
                break;
            case InstructionType::Gasprice:
            case InstructionType::Chainid:
            case InstructionType::Selfbalance:
                stack.push().clear_push_back(epool.createSelfbalance());
                break;
            case InstructionType::Basefee:
            // Block Information
            case InstructionType::Timestamp:
            case InstructionType::Number:
            case InstructionType::Difficulty:// no match in evmone
            case InstructionType::Gaslimit:
            case InstructionType::Blobbasefee:
                // Pushes a value onto the stack
                stack.push().makeComplete();
                break;
            case InstructionType::Caller:
                stack.push().clear_push_back(epool.createCaller());
                break;
            case InstructionType::Coinbase:
                stack.push().clear_push_back(epool.createCoinbase());
                break;
            case InstructionType::Origin:
                stack.push().clear_push_back(epool.createOrigin());
                break;
            case InstructionType::Pop:
                if (stack.size >= 1) {
                    stack.pop();
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Mstore:
            case InstructionType::Mstore8:
                if (stack.size >= 2) {
                    stack.pop(); // value
                    stack.pop(); // address
                    // No value is pushed onto the stack
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::SStore:
                if (stack.size >= 2) {
                    stack.pop(); // value
                    stack.pop(); // key
                    // No value is pushed onto the stack
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Sload:
                if (stack.size >= 1) {
                    ValueSet oldTop=stack[0];// make a copy of the old top of the stack
                    if (!oldTop.isComplete()) {// else nothing to do as the answer is also the complete set
                        stack[0].reset();
                        for (size_t i=0; i<oldTop.size(); i++) {
                            uint32_t nodeIndex=oldTop.getFixedValue(i);
                            stack[0].push_back(epool.createSload(nodeIndex));
                        }
                        stack[0].canonicalize();
                    }
                    else{
                        stack[0]=ValueSet(epool.createSload(epool.createAny()));
                    }
                } else {
                    handleUnderflow();
                }                    
                break;
            case InstructionType::Mload:
                if (stack.size >= 1) {
                    ValueSet oldTop=stack[0];// make a copy of the old top of the stack
                    if (!oldTop.isComplete()) {// else nothing to do as the answer is also the complete set
                        stack[0].reset();
                        for (size_t i=0; i<oldTop.size(); i++) {
                            uint32_t nodeIndex=oldTop.getFixedValue(i);
                            stack[0].push_back(epool.createMload(nodeIndex));
                        }
                        stack[0].canonicalize();
                    }
                    else{
                        stack[0]=ValueSet(epool.createMload(epool.createAny()));
                    }
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Tload:
                if (stack.size >= 1) {
                    stack[0].makeComplete(); // key
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Tstore:
                if (stack.size >= 2) {
                    stack.pop(); // value
                    stack.pop(); // key
                    // No value is pushed onto the stack
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Msize:
            case InstructionType::Gas:
                stack.push().makeComplete();
                break;
            case InstructionType::Mcopy:
                if (stack.size >= 3) {
                    stack.pop(); // length
                    stack.pop(); // source offset
                    stack.pop(); // destination offset
                    // No stack changes
                } else {
                    handleUnderflow();
                }
                break;

            // System Operations
            case InstructionType::Create:
                if (stack.size >= 3) {
                    stack[2]=ValueSet(epool.createCreate());
                    stack.pop(); // offset
                    stack.pop(); // size
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Create2:
                if (stack.size >= 4) {
                    stack[3].makeComplete(); // value or salt
                    stack.pop(); // offset
                    stack.pop(); // size
                    stack.pop(); // size
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Call:
            case InstructionType::Callcode:
                if (stack.size >= 7) {
                    stack[6]=s01;
                    for (size_t i=0; i<6; ++i) {
                        stack.pop();
                    }
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Delegatecall:
            case InstructionType::Staticcall:
                if (stack.size >= 6) {
                    stack[5]=s01;
                    for (size_t i=0; i<5; ++i) {
                        stack.pop();
                    }
                } else {
                    handleUnderflow();
                }
                break;

            // Other Operations
            case InstructionType::Calldatasize:
                stack.push().clear_push_back(epool.createCallDataSize());
                break;
            case InstructionType::Codesize:
            case InstructionType::Returndatasize:
                stack.push().clear_push_back(epool.createReturndataSize());
                break;
            case InstructionType::Balance:
                if (stack.size >= 1) {
                    stack[0].makeComplete();
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Extcodesize:
            case InstructionType::Extcodehash:
            case InstructionType::Blockhash:
            case InstructionType::Blobhash:
                if (stack.size >= 1) {
                    stack[0].makeComplete(); // index or address
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Calldataload:
                if (stack.size >= 1) {
                    ValueSet oldTop=stack[0];// make a copy of the old top of the stack
                    if (!oldTop.isComplete()) {// else nothing to do as the answer is also the complete set
                        stack[0].reset();
                        for (size_t i=0; i<oldTop.size(); i++) {
                            stack[0].push_back(epool.createCallData(oldTop.getFixedValue(i)));
                        }
                        stack[0].canonicalize();
                    }
                    else{
                        stack[0]=ValueSet(epool.createCallData(epool.createAny()));
                    }
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Calldatacopy:
            case InstructionType::Codecopy:
            case InstructionType::Returndatacopy:
                if (stack.size >= 3) {
                    stack.pop(); // length
                    stack.pop(); // source offset
                    stack.pop(); // destination offset
                    // No stack changes
                } else {
                    handleUnderflow();
                }
                break;
            case InstructionType::Extcodecopy:
                if (stack.size >= 4) {
                    stack.pop(); // length
                    stack.pop(); // source offset
                    stack.pop(); // destination offset
                    stack.pop(); // address
                    // No stack changes
                } else {
                    handleUnderflow();
                }
                break;

            default:
                assert(false);
        }
    }
	
    void operator()(const Swap& swap) {
        uint8_t n = swap.n;
        assert(n >= 1 && n <= 16);
        size_t idx_n = n;
        if (stack.size > idx_n) {
            std::swap(stack[0], stack[idx_n]);
        } else {
            handleUnderflow();
        }
    }

    void operator()(const Dup& dup) {
        uint8_t n = dup.n;
        assert(n >= 1 && n <= 16);
        size_t idx_n = n - 1;
        if (stack.size > idx_n) {
            stack.push()=stack[idx_n];
        } else {
            handleUnderflow();
        }
    }

    void operator()(const Push& push) {
        ValueSet & newHead= stack.push();
        newHead.reset();
        newHead.push_back(epool.createConst(push.w));
    }

    void operator()(const PC& pc) {
        stack.push().clear_push_back(epool.createSmallConst(static_cast<uint64_t>(pc.offset)));
    }

    void operator()(const Log& log) {
        uint8_t n = log.n;
        size_t itemsToPop = n + 2;
        if (stack.size >= itemsToPop) {
            for (size_t i = 0; i < itemsToPop; ++i) {
                stack.pop();
            }
        } else {
            handleUnderflow();
        }
    }
};

// The transferInstr function
bool transferInstr(const Instruction& instr, StackValues& stack) {
    InstructionVisitor visitor{stack};
    std::visit(visitor, instr);
    return visitor.underflow;
}



const ValueSet& nthElemAll(size_t index, const StackValues& stack) {
    if (index < stack.size) {
        return stack[index];
    } else {
        return emptyValueSett;
    }
}

void jumpSuccessors(const std::bitset<MAX_BYTECODESIZE> &jumpDests, const ValueSet& valSet, Successors<Cutoff> & succs) {
    #if DEBUG_KILDALL
    std::cout << "jumpSuccessors: ";
    printValueSet(std::cout, valSet);
    std::cout << "\n";
    #endif
    if (valSet.isComplete()) {
        succs.includeAllJumpDests=true;
    } else {
        const auto& vals = valSet.getFixedValues();
        for (const uint32_t& nodeIndex : vals) {
            ExpressionNode::Type type = epool.getType(nodeIndex);
            if (type == ExpressionNode::Type::SmallConst) {
                NodeID offset = 1+epool.getSmallConst(nodeIndex);   
                if (offset < MAX_BYTECODESIZE && jumpDests.test(offset))
                    succs.succs.push_back(offset);
            }
            else if (type != ExpressionNode::Type::Const) { // in case of a big constant, it is an invalid jump destination, so ignore it as that thread of execution will fail here
                succs.includeAllJumpDests=true;// there is a non-constant node in the jump dests
                #if DEBUG_KILDALL
                std::cout << "Including all jump destinations due to non-constant jump destination\n";
                #endif
                return;
            }
        }
    }
}

void transferSuccTerm(
    const std::bitset<MAX_BYTECODESIZE> &jumpDests,
    const Terminator& term,
    StackValues& stack,
    Successors<Cutoff> & succs
) {
    // Visitor struct to handle different terminator variants
    struct TerminatorVisitor {
        StackValues& stack;
        const std::bitset<MAX_BYTECODESIZE> &jumpDests;
        Successors<Cutoff> & succs;

        // Constructor
        TerminatorVisitor(StackValues& s, const std::bitset<MAX_BYTECODESIZE> &jumpDests_, Successors<Cutoff> & succs_)
            : stack(s), jumpDests(jumpDests_), succs(succs_) {}

        void operator()(TerminatorType termType) {
            switch (termType) {
                case TerminatorType::Stop:
                case TerminatorType::Return:// pops 2 in evm but does that matter?
                case TerminatorType::Revert://pop 2 in evm but does that matter?
                case TerminatorType::SelfDestruct:// pops 1 in evm but does that matter?
                    // stack.clear(); no successors. so this value is not used anyway
                    // Execution stops; no successors
                    return;
                case TerminatorType::Jump:
                    if (stack.size >= 1) {
                        const ValueSet& dest = nthElemAll(0, stack);
                        stack.pop();// shuld pop be the last operation?
                        jumpSuccessors(jumpDests, dest, succs);
                    } else {
                        // Stack underflow; no successors
                        return;
                    }
                    break;
                default:
                    assert(false);
            }
        }

        void operator()(const Jumpi& jumpi) {
            if (stack.size >= 2) {
                const ValueSet& dest = nthElemAll(0, stack);
                const ValueSet& condition = nthElemAll(1, stack);
                stack.pop();
                stack.pop();

                ByteOffset nextAddr = jumpi.offset; // the current parser already ensures that jumpi.offset  is 1+ the addr at which this opcode lives

                if (condition.isComplete()) {
                    // Condition is unknown
                    jumpSuccessors(jumpDests, dest, succs);
                    succs.succs.push_back(nextAddr);
                } else {
                    const auto& condVals = condition.getFixedValues();
                    if (condVals.empty()) {
                        // Unreachable so far
                        return;
                    } else {
                        bool allZero = std::all_of(condVals.begin(), condVals.end(), [](const uint32_t& val) {
                            std::optional<uint64_t> sc = epool.getSmallConstMaybe(val);
                            return sc.has_value() && sc.value() == 0;
                        });
                        bool allNonZero = std::all_of(condVals.begin(), condVals.end(), [](const uint32_t& val) {
                            std::optional<uint64_t> sc = epool.getSmallConstMaybe(val);
                            return sc.has_value() && sc.value() != 0;
                        });
                        if (allZero) {
                            // Condition always false; only next instruction is possible
                            succs.succs.push_back(nextAddr);
                        } else if (allNonZero) {
                            // Condition always true; only jump destinations are possible
                            jumpSuccessors(jumpDests, dest, succs);
                        } else {
                            // Condition can be true or false; include both possibilities
                            jumpSuccessors(jumpDests, dest, succs);
                            succs.succs.push_back(nextAddr);
                        }
                    }
                }
            } else {
                // Stack underflow; no successors
                return;
            }
        }

        void operator()(const Jumpdest& jumpdest) {
            // Execution continues to the next instruction
            ByteOffset nextAddr = jumpdest.offset + 1; // Assuming instruction size is 1
            succs.succs.push_back(nextAddr);
        }

        void operator()(const InvalidInstruction& invalid) {
            // Execution stops
            return;
        }
    };

    // Create the visitor and apply it to the terminator
    TerminatorVisitor visitor{stack, jumpDests, succs};
    std::visit(visitor, term);

    return;
}


// The transferSucc function
void transferSucc(
    const ParsedBytecode<MAX_BYTECODESIZE, MAX_BBLOCKS>& parsedBytecode,
    NodeID startOffset,
    StackValues& inSoln,
    Successors<Cutoff> & succs
) {
    // Start reading from the given offset
    NodeID currentOffset = startOffset;
    InsTerm insTerm;
    bool underflow = false;
    // Process instructions until we hit a terminator
    while (!underflow && currentOffset < parsedBytecode.bytes.size) {
        parseOpcode<MAX_BYTECODESIZE>(insTerm, parsedBytecode.bytes, currentOffset);
        
        if (std::holds_alternative<Instruction>(insTerm)) {
            // Regular instruction - apply transfer function
            underflow = transferInstr(std::get<Instruction>(insTerm), inSoln);
        } 
        else if (std::holds_alternative<Terminator>(insTerm)) {
            // Found terminator - compute successors and apply transfer
            const auto& term = std::get<Terminator>(insTerm);
            transferSuccTerm(parsedBytecode.jumpDests, term, inSoln, succs);
            break;  // Exit after processing terminator
        }
    }
}


#define KILDALL_LIFO 1  // Set to 1 for LIFO, 0 for FIFO

struct NodeSetType {
    
    std::bitset<MAX_BYTECODESIZE> set;      // For fast membership checking
    NodeID queue[MAX_BBLOCKS];         // Fixed-size array for stack
    uint16_t size = 0;              // Current size of stack

    bool push_back(NodeID n) {
        assert(n < MAX_BYTECODESIZE && "NodeID out of bounds");
        if (!set.test(n)) {
            assert(size < MAX_BBLOCKS && "Stack overflow");
            queue[size] = n;
            size++;
            set.set(n);
            return true;
        }
        return false;
    }

    NodeID back() const {
        assert(size > 0 && "Stack empty");
        return queue[size - 1];
    }

    NodeID pop_back() {
        assert(size > 0 && "Stack underflow");
        NodeID node = queue[size-1];
        set.reset(node);
        size--;
        return node;
    }

    bool empty() const {
        return size == 0;
    }
};

template<>
struct NodeSet<NodeSetType> {
    static void print(std::ostream& os, const NodeSetType& s) {
        os << "{";
        bool first = true;
        for (uint16_t i = 0; i < s.size; ++i) {
            if (!first) os << ", ";
            os << s.queue[i];
            first = false;
        }
        os << "}";
    }    

    static void add(NodeID n, NodeSetType& s) {
        s.push_back(n);
    }

    static NodeID pick(NodeSetType& s) {
        assert(!s.empty() && "NodeSet empty");// TODO: switch to release builds after testing

        return s.pop_back();    // Get last element (LIFO)
    }

    static void clear(NodeSetType& s) {
        s.size = 0;
    }

    static bool is_empty(const NodeSetType& s) {
        return s.empty();
    }
};




// Function to calculate the size of an instruction in bytes
struct InstructionSizeVisitor {
    size_t operator()(const InstructionType&) const {
        // All basic instructions have a size of 1 byte
        return 1;
    }

    size_t operator()(const Push& pushInstr) const {
        // PUSHn instruction has size 1 + n
        return 1 + pushInstr.n;
    }

    size_t operator()(const Dup&) const {
        return 1;
    }

    size_t operator()(const Swap&) const {
        return 1;
    }

    size_t operator()(const Log&) const {
        return 1;
    }

    size_t operator()(const PC&) const {
        return 1;
    }
};

// Function to calculate the size of an instruction in bytes
size_t instrSize(const Instruction& instr) {
    return std::visit(InstructionSizeVisitor{}, instr);
}


std::unordered_set<uint32_t> calleeExprsIndices;
std::unordered_set<uint32_t> delegateCallExprsIndices;
std::unordered_set<uint32_t> allCalleeExprIndices;

struct Counts {
    uint16_t occurrencesCount=0;
    uint16_t predictedCount=0;
    uint16_t reachableCount=0;
    bool allReachablePredicted() {
        return reachableCount==predictedCount;
    }
    void reset() {
        occurrencesCount=0;
        predictedCount=0;
        reachableCount=0;
    }
};

Counts callCounts;
Counts delegateCallCounts;
Counts createCounts;

static Predictions predictions;

// Define `fineGrainedSolns` to print solutions for every program point in all basic blocks
void fineGrainedSolns(const ParsedBytecode<MAX_BYTECODESIZE, MAX_BBLOCKS>& parsedBytecode, const SparseMap<StackValues, MAX_BYTECODESIZE, MAX_BBLOCKS>& solns) {
    std::cout << "\noffset:instr:stackvalsB4"<<std::endl;
    calleeExprsIndices.clear();
    delegateCallExprsIndices.clear();
    callCounts.reset();
    delegateCallCounts.reset();
    createCounts.reset();

    NodeID currentOffset = 0;
    bool prevSolnAvailable = false;
    StackValues prevInstrSoln;
    bool printSoln=false;
    bool isCall=false;
    // Process instructions in order
    InsTerm prevInsTerm;// because soln is avaulable for 0, the first iteration will not use this value. future iterations will set this value
    while (currentOffset < parsedBytecode.bytes.size) {
        NodeID oldOffset=currentOffset;
        InsTerm thisOffsetIns;
        isCall=parsedBytecode.bytes[currentOffset]==0xF1;//call opcode
        bool isCreate=parsedBytecode.bytes[currentOffset]==0xF0 || parsedBytecode.bytes[currentOffset]==0xF5;//create/create2 opcode
        bool isDelegateCall=parsedBytecode.bytes[currentOffset]==0xF4 || parsedBytecode.bytes[currentOffset]==0xF2;//delegatecall/callcode opcode
        printSoln=true;//make it true if we want to print all instructions
        parseOpcode<MAX_BYTECODESIZE>(thisOffsetIns, parsedBytecode.bytes, currentOffset);//increments currentOffset by size of instruction
        if (solns.exists(oldOffset)) {
            // Use solution directly from solver
            prevInstrSoln = solns.get(oldOffset);
            prevSolnAvailable = true;
            if (printSoln) {
                std::cout << "\n" << oldOffset << ":";
                printInsTerm(thisOffsetIns);
                std::cout << ":";
                Semilattice<StackValues>::print(std::cout, prevInstrSoln);
            }
        } 
        else if (prevSolnAvailable) {
            // Compute solution by applying transfer function to previous solution
            if (std::holds_alternative<Instruction>(prevInsTerm)) {
                const Instruction & instr = std::get<Instruction>(prevInsTerm);
                bool underflow = transferInstr(instr, prevInstrSoln);
                if (printSoln) {
                    std::cout << "\n" << oldOffset << ":";
                }
                if (underflow) {
                    prevSolnAvailable = false;
                    if (printSoln) {
                        std::cout << " (underflow)";
                    }
                }
                else {
                    if (printSoln) {
                        printInsTerm(thisOffsetIns);
                        std::cout << ":";
                        Semilattice<StackValues>::print(std::cout, prevInstrSoln);
                    }
                }
            }
            else if (std::holds_alternative<Terminator>(prevInsTerm)) {
                const Terminator & term = std::get<Terminator>(prevInsTerm);    
                transferTerm(term, prevInstrSoln);
                prevSolnAvailable = false;
                if (printSoln) {
                    std::cout << "\n" << oldOffset << ":";
                    printInsTerm(thisOffsetIns);
                    std::cout << ":";
                    Semilattice<StackValues>::print(std::cout, prevInstrSoln);
                }
            }
        }
        else
            prevSolnAvailable = false;

        if (isCall) {
            callCounts.occurrencesCount++;
            if (prevSolnAvailable && prevInstrSoln.size>6)
            {
                callCounts.reachableCount++;
                const ValueSet& calleeSoln=prevInstrSoln[1];
                if (!calleeSoln.isComplete()) {
                    callCounts.predictedCount++;
                    for (size_t i=0; i<calleeSoln.size(); i++) {
                        uint32_t nodeIndex=calleeSoln.getFixedValue(i);
                        calleeExprsIndices.insert(nodeIndex);
                    }
                }
            }
        }

        if (isDelegateCall) {
            delegateCallCounts.occurrencesCount++;
            if (prevSolnAvailable && prevInstrSoln.size>6)
            {
                delegateCallCounts.reachableCount++;
                const ValueSet& calleeSoln=prevInstrSoln[1];
                if (!calleeSoln.isComplete()) {
                    delegateCallCounts.predictedCount++;
                    for (size_t i=0; i<calleeSoln.size(); i++) {
                        uint32_t nodeIndex=calleeSoln.getFixedValue(i);
                        delegateCallExprsIndices.insert(nodeIndex);
                    }
                }
            }
        }

        if (isCreate) {
            createCounts.occurrencesCount++;
            if (prevSolnAvailable && prevInstrSoln.size>2) {
                createCounts.reachableCount++;
            }
        }
        prevInsTerm=thisOffsetIns;

    }
    std::cout<<"\ncallCount,callPredCount,callReachableCount, calleeExprs, calleeExprsIndices:"<<callCounts.occurrencesCount<<","<<callCounts.predictedCount<<","<<callCounts.reachableCount<<",";
    for (uint32_t nodeIndex : calleeExprsIndices) {
        epool.printExpression(std::cout, nodeIndex);
        std::cout << ";";
    }
    std::cout<<std::endl;

    std::cout<<"\ndelegateCallCount,delegateCallPredCount,delegateCallReachableCount, delegateCallExprs, delegateCallExprsIndices:"<<delegateCallCounts.occurrencesCount<<","<<delegateCallCounts.predictedCount<<","<<delegateCallCounts.reachableCount<<",";
    for (uint32_t nodeIndex : delegateCallExprsIndices) {
        epool.printExpression(std::cout, nodeIndex);
        std::cout << ";";
    }
    std::cout<<std::endl;

    std::cout<<"\ncreateCount,createReachableCount:"<<createCounts.occurrencesCount<<","<<createCounts.reachableCount<<std::endl;
}


//static SparseMap<StackValues, MAX_INSTRUCTIONS, MAX_BBLOCKS> blocks;

//    solver([](ParsedBytecode<MAX_INSTRUCTIONS, MAX_BBLOCKS>& parsedBytecode, NodeID node, StackValues& state, Successors & succs) {
  //      transferSucc(parsedBytecode, node, state, succs);
    //});
static DataflowSolver<StackValues, NodeSetType, Semilattice<StackValues>, 
    NodeSet<NodeSetType>, MAX_BYTECODESIZE, MAX_BBLOCKS, Cutoff> 
        solver(transferSucc,fineGrainedSolns);

int main() {
    //epool.deserialize("epool.bin");
    //epool.printToFile("epoolDeserialized.txt");
    //return 0;

    std::ifstream contractList("contracts.txt");
    if (!contractList) {
        std::cerr << "Error: Unable to open contracts.txt" << std::endl;
        return 1;
    }

    std::string inputDir;
    if (!std::getline(contractList, inputDir)) {
        std::cerr << "Error: contracts.txt is empty. first line should be input directory" << std::endl;
        return 1;
    }
    // Read output directory from first line
    std::string outputDir;
    if (!std::getline(contractList, outputDir)) {
        std::cerr << "Error: only one line in contracts.txt. second line should be output directory" << std::endl;
        return 1;
    }

    struct stat st; 
    if (stat(outputDir.c_str(), &st) == -1) {
        if (mkdir(outputDir.c_str(), 0755) == -1) {
            std::cerr << "Failed to create directory " << outputDir << ": " << strerror(errno) << std::endl;
            exit(1);  // Or return an error code if this is in a function that can return
        }
    }
    std::string filename;
    resetFactory();
    size_t procFiles=0;
    while (std::getline(contractList, filename)) {
        // Construct input and output paths
        std::string inputPath = inputDir + "/" + filename;
        std::string outputPath = outputDir + "/" + filename;

//        std::cout << "opening " << filename << std::endl;
        readBytecode<MAX_BYTECODESIZE, MAX_BBLOCKS>(solver.parsedBytecode, inputPath);
        // solver.parsedBytecode.print();
//        std::cout << "Parsed " << filename << std::endl;


        // Run solver
        NodeID entryPoint = 0;
        // Write results to output file
        std::ofstream outFile(outputPath);
        // Redirect cout to file temporarily
        auto cout_buf = std::cout.rdbuf(outFile.rdbuf());
        
        const SparseMap<StackValues, MAX_BYTECODESIZE, MAX_BBLOCKS>& result = solver.fixpoint(entryPoint, StackValues());

        if (!outFile) {
            std::cerr << "Error: Unable to open output file for " << filename << std::endl;
            continue;
        }
        outFile<<solver.steps<<std::endl;


        // Print results
        fineGrainedSolns(solver.parsedBytecode, result);
        allCalleeExprIndices = calleeExprsIndices;
        allCalleeExprIndices.insert(delegateCallExprsIndices.begin(), delegateCallExprsIndices.end());
        bool allCallesSupported=epool.allConstants(allCalleeExprIndices);
        bool predictionSuccess=allCallesSupported && createCounts.reachableCount==0;// in future, we can supporte create/create2 by computing the address of the created contract. for create2, we just need a prediction for the salt argument. for create, we to add nonce expressions in addition to stack elements.
        if (allCallesSupported) {
            ::evmc::bytes32 hash=hex_to_bytes32(filename);
            auto it = predictions.emplace(hash, Prediction{}).first; // Insert or find the entry in the map

            for (uint32_t nodeIndex : calleeExprsIndices) {
                it->second.callees.push_back(epool.getConstant(nodeIndex)); // Push back to the callee vector
            }   

            for (uint32_t nodeIndex : delegateCallExprsIndices) {
                it->second.delegateCallees.push_back(epool.getConstant(nodeIndex)); // Push back to the delegate callee vector
            }
        }   


        // Restore cout
        std::cout.rdbuf(cout_buf);

        std::cout << "Processed " << procFiles++ << ":"  << filename << " in " << solver.steps << " steps" << std::endl;
    }
    epool.serialize("epool.bin");
    epool.printToFile("epool.txt");
    serializePredictions(predictions, "predictions.bin");

    return 0;
}
