#include <iostream>
#include <vector>
#include <unordered_map>
#include <functional>
#include <cassert>
#include <boost/multiprecision/cpp_int.hpp>
#include <optional>
#include <fstream>
#include <unordered_set>
#include <evmc/evmc.hpp>
#include <algorithm>
#include <boost/algorithm/hex.hpp>
#include <set>
#include <intx/intx.hpp>
#undef UINT128_MAX
#include <monad/core/block.hpp>
namespace mp = boost::multiprecision;
using Word256 = mp::uint256_t;

// Forward declaration
struct ExpressionNode;

// Equality function and hash function will be updated accordingly

// ExpressionPool class declaration
class ExpressionPool;

// ConstantPool class to manage unique constants
class ConstantPool {
public:
    std::vector<Word256> constants;
    std::unordered_map<Word256, uint32_t> constantMap;

    uint32_t getConstantIndex(const Word256& w) {
        auto it = constantMap.find(w);
        if (it != constantMap.end()) {
            return it->second;
        }
        auto size = constants.size();
        uint32_t index = static_cast<uint32_t>(size);
        constants.push_back(w);
        constantMap[w] = index;
        return index;
    }

    const Word256& getConstant(uint32_t index) const {
        return constants[index];
    }

    void reset() {
        constants.clear();
        constantMap.clear();
    }
};

// ExpressionNode struct
struct ExpressionNode {
    enum class Type : uint8_t {
        Const, // constantIndex
        SmallConst, // smallConst

        CallData, // offset
        CallDataSize,
        Caller,
        Address,
        Coinbase,
        Origin,
        Create,// newly created contract
        ReturndataSize,
        Selfbalance,
        Callvalue,

        Sload, // exprIndex
        Mload, // exprIndex
        // binary ops:
        Add,
        Mul,
        Sub,
        Shl,
        Shr,
        And,
        Or,
        Xor,
        Div,
        Mod,
        Exp,

        // unary ops:
        Not,

        Any
    };

    Type type;

    union {
        uint32_t constantIndex;               // For Const
        uint32_t exprIndex;                   // For mload, sload, unary ops, calldata
        struct { uint32_t leftIndex, rightIndex; } binaryOp; // For binary operations
        uint64_t smallConst;// if we change this to uint32_t, we can save 4 bytes per node
    };

    ExpressionNode() : type(Type::Any) {}

    void mkConst(uint32_t constIdx) {
        type = Type::Const;
        constantIndex = constIdx;
    }

    void mkCallData(uint32_t exprIndex) {
        type = Type::CallData;
        this->exprIndex = exprIndex;
    }

    void mkSload(uint32_t exprIndex) {
        type = Type::Sload;
        this->exprIndex = exprIndex;
    }

    void mkMload(uint32_t exprIndex) {
        type = Type::Mload;
        this->exprIndex = exprIndex;
    }

    void mkBinaryOp(Type op, uint32_t leftIndex, uint32_t rightIndex) {
        assert(op == Type::Add || op == Type::Mul || op == Type::Sub || op == Type::Shl || op == Type::Shr || op == Type::And || op == Type::Or || op == Type::Xor || op == Type::Div || op == Type::Mod || op == Type::Exp);
        type = op;
        binaryOp.leftIndex = leftIndex;
        binaryOp.rightIndex = rightIndex;
    }

    void mkUnaryOp(Type op, uint32_t exprIndex) {
        assert(op == Type::Not);
        type = op;
        this->exprIndex = exprIndex;
    }

    void mkSmallConst(uint64_t val) {
        type = Type::SmallConst;
        smallConst = val;
    }

    void mkCaller() {
        type = Type::Caller;
    }

    void mkCoinbase() {
        type = Type::Coinbase;
    }

    void mkOrigin() {
        type = Type::Origin;
    }

    void mkReturndataSize() {
        type = Type::ReturndataSize;
    }

    void mkCallDataSize() {
        type = Type::CallDataSize;
    }

    void mkAddress() {
        type = Type::Address;
    }
    void mkCreate(){
        type = Type::Create;
    }
    void mkSelfbalance(){
        type = Type::Selfbalance;
    }
    void mkCallvalue(){
        type = Type::Callvalue;
    }

    // Copy constructor
    ExpressionNode(const ExpressionNode& other) : type(other.type) {
        switch (type) {
            case Type::Const:
                constantIndex = other.constantIndex;
                break;
            case Type::CallData:
                exprIndex = other.exprIndex;
                break;
            case Type::Sload:
            case Type::Mload:
            case Type::Not:
                exprIndex = other.exprIndex;
                break;
            case Type::Add:
            case Type::Mul:
            case Type::Sub:
            case Type::Shl:
            case Type::Shr:
            case Type::And:
            case Type::Or:
            case Type::Xor:
            case Type::Div:
            case Type::Mod:
            case Type::Exp:
                binaryOp = other.binaryOp;
                break;
            case Type::Caller:
            case Type::Coinbase:
            case Type::Origin:
            case Type::CallDataSize:
            case Type::Address:
            case Type::Create:
            case Type::ReturndataSize:
            case Type::Selfbalance:
            case Type::Callvalue:
            case Type::Any:
                // No additional data
                break;
            case Type::SmallConst:
                smallConst = other.smallConst;
                break;
            default:
                assert(false);
        }
    }

    // Copy assignment operator
    inline ExpressionNode& operator=(const ExpressionNode& other) {
        if (this != &other) {
            // Destroy existing union member
            this->~ExpressionNode();
            // Placement new copy constructor
            new (this) ExpressionNode(other);
        }
        return *this;
    }

    friend class ExpressionPool; // Allow ExpressionPool to access constructors
};

// Equality function
inline bool operator==(const ExpressionNode& lhs, const ExpressionNode& rhs) {
    if (lhs.type != rhs.type)
        return false;

    switch (lhs.type) {
        case ExpressionNode::Type::Const:
            return lhs.constantIndex == rhs.constantIndex;
        case ExpressionNode::Type::Caller:
        case ExpressionNode::Type::Coinbase:
        case ExpressionNode::Type::CallDataSize:
        case ExpressionNode::Type::Origin:
        case ExpressionNode::Type::Address:
        case ExpressionNode::Type::Create:
        case ExpressionNode::Type::ReturndataSize:
        case ExpressionNode::Type::Selfbalance:
        case ExpressionNode::Type::Callvalue:
        case ExpressionNode::Type::Any:
            return true; // These have no additional data
        case ExpressionNode::Type::Sload:
        case ExpressionNode::Type::Mload:
        case ExpressionNode::Type::Not:
        case ExpressionNode::Type::CallData:
            return lhs.exprIndex == rhs.exprIndex;
        case ExpressionNode::Type::Add:
        case ExpressionNode::Type::Mul:
        case ExpressionNode::Type::Sub:
        case ExpressionNode::Type::Shl:
        case ExpressionNode::Type::Shr:
        case ExpressionNode::Type::And:
        case ExpressionNode::Type::Or:
        case ExpressionNode::Type::Xor:
        case ExpressionNode::Type::Div:
        case ExpressionNode::Type::Mod:
        case ExpressionNode::Type::Exp:
            return lhs.binaryOp.leftIndex == rhs.binaryOp.leftIndex &&
                   lhs.binaryOp.rightIndex == rhs.binaryOp.rightIndex;
        case ExpressionNode::Type::SmallConst:
            return lhs.smallConst == rhs.smallConst;
        default:
            assert(false);
            return false;
    }
}

// Hash function
struct ExpressionNodeHash {
    std::size_t operator()(const ExpressionNode& node) const {
        using std::hash;
        size_t h = hash<int>()(static_cast<int>(node.type));
        switch (node.type) {
            case ExpressionNode::Type::Const:
                h ^= hash<uint32_t>()(node.constantIndex);
                break;
            case ExpressionNode::Type::CallData:
                h ^= hash<uint32_t>()(node.exprIndex);
                break;
            case ExpressionNode::Type::Caller:
            case ExpressionNode::Type::Coinbase:
            case ExpressionNode::Type::Origin:
            case ExpressionNode::Type::CallDataSize:
            case ExpressionNode::Type::Address:
            case ExpressionNode::Type::Create:
            case ExpressionNode::Type::ReturndataSize:
            case ExpressionNode::Type::Selfbalance:
            case ExpressionNode::Type::Callvalue:
            case ExpressionNode::Type::Any:
                // Nothing to add; types are already considered
                break;
            case ExpressionNode::Type::Sload:
            case ExpressionNode::Type::Mload:
            case ExpressionNode::Type::Not:
                h ^= hash<uint32_t>()(node.exprIndex);
                break;
            case ExpressionNode::Type::Add:
            case ExpressionNode::Type::Mul:
            case ExpressionNode::Type::Sub:
            case ExpressionNode::Type::Shl:
            case ExpressionNode::Type::Shr:
            case ExpressionNode::Type::And:
            case ExpressionNode::Type::Or:
            case ExpressionNode::Type::Xor:
            case ExpressionNode::Type::Div:
            case ExpressionNode::Type::Mod:
            case ExpressionNode::Type::Exp:
                h ^= hash<uint32_t>()(node.binaryOp.leftIndex);
                h ^= hash<uint32_t>()(node.binaryOp.rightIndex);
                break;
            case ExpressionNode::Type::SmallConst:
                h ^= hash<uint64_t>()(node.smallConst);
                break;
            default:
                assert(false);
        }
        return h;
    }
};

// Forward declaration of expressionCompare
int expressionCompare(const ExpressionPool& pool, uint32_t idx1, uint32_t idx2);


inline void to_uint64_array(const Word256& value, uint64_t out[4]) {
    // Extract the bits in 64-bit chunks.
    // value & 0xFFFFFFFFFFFFFFFFULL extracts the low 64 bits.
    out[0] = static_cast<uint64_t>(value & 0xFFFFFFFFFFFFFFFFULL);
    out[1] = static_cast<uint64_t>((value >> 64) & 0xFFFFFFFFFFFFFFFFULL);
    out[2] = static_cast<uint64_t>((value >> 128) & 0xFFFFFFFFFFFFFFFFULL);
    out[3] = static_cast<uint64_t>((value >> 192) & 0xFFFFFFFFFFFFFFFFULL);
}

inline void from_uint64_array(Word256& result, const uint64_t in[4]) {
    result = 0;
    result |= Word256(in[0]);
    result |= (Word256(in[1]) << 64);
    result |= (Word256(in[2]) << 128);
    result |= (Word256(in[3]) << 192);
}

inline void from_byte_array(Word256& result, const uint8_t in[32]) {
    result = 0;
    for (int i = 0; i < 32; ++i) {
        result |= (Word256(in[i]) << (8 * i));
    }
}

inline void from_byte_array_bigendian(Word256& result, const uint8_t in[32]) {
    result = 0;
    for (int i = 0; i < 32; ++i) {
        result |= (Word256(in[i]) << (8 * (31 - i)));
    }
}

inline void toWord256(Word256 &result, evmc::address const &address) {
    result = 0;
    for (size_t i = 0; i < 20; ++i) {
        result |= Word256(address.bytes[i]) << (8 * (19 - i));
    }
}
    // Function to serialize a Word256 constant to a file
inline void serializeConstant(std::ofstream &file, Word256 const &constant)
{
    std::array<uint64_t, 4> bits;
    to_uint64_array(constant, bits.data());

    /*
    // Debugging: Print the bits array
    std::cout << "Exported bits: ";
    for (const auto& bit : bits) {
        std::cout << std::hex << bit << " ";
    }
    std::cout << std::endl;
    // Import bits back to verify serialization
    Word256 verify;
    mp::import_bits(verify, bits.begin(), bits.end(), 64);

    // Debugging: Print the verify value
    std::cout << "Original: " << constant.str() << ", Imported: " <<
    verify.str() << std::endl;

    assert(verify == constant);
    */
    file.write(reinterpret_cast<char const *>(bits.data()), sizeof(bits));
}

// Function to deserialize a Word256 constant from a file
inline void deserializeConstant(std::ifstream &file, Word256 &constant)
{
    std::array<uint64_t, 4> bits;
    file.read(reinterpret_cast<char *>(bits.data()), sizeof(bits));
    from_uint64_array(constant, bits.data());
}

inline intx::uint256 ofBoost(const Word256& word) {
    uint64_t words[4];
    to_uint64_array(word, words);

    // Construct intx::uint256 from the uint64_t array
    intx::uint256 result{words[0], words[1], words[2], words[3]};

    // For debugging: log the Word256 and the intx::uint256 values
    ////LOG_INFO("Converting Word256 to intx::uint256");
    // //LOG_INFO("Word256:       0x{}", word.str(0, std::ios_base::hex));
    ////LOG_INFO("intx::uint256: 0x{}", intx::to_string(result, 16));

    return result;
}

inline Word256 ofIntx(const intx::uint256& word) {
    // Extract 64-bit words from intx::uint256
    uint64_t words[4];
    words[0] = word[0];  // Least significant word
    words[1] = word[1];
    words[2] = word[2];
    words[3] = word[3];  // Most significant word

    // Construct Word256 (boost::multiprecision::uint256_t) from the uint64_t array
    Word256 result;
    from_uint64_array(result, words);

    return result;
}

// Helper to convert an evmc::address into a Word256:
inline Word256 ofAddress(const evmc::address& addr)
{
    // Load the 160-bit addr bytes into a full 256-bit intx::uint256
    intx::uint256 val = intx::be::load<intx::uint256>(addr.bytes);
    // Convert intx::uint256 back to Word256
    return ofIntx(val);
}

// ExpressionPool class definition
class ExpressionPool {
public:
    ConstantPool constants; // Manages unique Word256 constants
    std::vector<ExpressionNode> nodes;
    std::unordered_map<ExpressionNode, uint32_t, ExpressionNodeHash> nodeMap;
    uint32_t e0;
    uint32_t e1;

    uint32_t addNodeToPool(ExpressionNode& node) {
        auto it = nodeMap.find(node);
        if (it != nodeMap.end())
            return it->second;

        nodes.push_back(node);
        uint32_t index = static_cast<uint32_t>(nodes.size() - 1);
        nodeMap[node] = index;
        return index;
    }

    uint32_t createSmallConst(uint64_t val) {
        ExpressionNode node;
        node.mkSmallConst(val);
        return addNodeToPool(node);
    }

    std::optional<Word256> getConstMaybe(uint32_t index) const {
        if (nodes[index].type != ExpressionNode::Type::Const && nodes[index].type != ExpressionNode::Type::SmallConst)
            return std::nullopt;
        if (nodes[index].type == ExpressionNode::Type::SmallConst)
            return Word256(nodes[index].smallConst);
        return constants.getConstant(nodes[index].constantIndex);
    }

    Word256 getConst(uint32_t index) const {
        assert(nodes[index].type == ExpressionNode::Type::Const || nodes[index].type == ExpressionNode::Type::SmallConst);
        if (nodes[index].type == ExpressionNode::Type::SmallConst)
            return Word256(nodes[index].smallConst);
        return constants.getConstant(nodes[index].constantIndex);
    }

    std::optional<uint64_t> getSmallConstMaybe(uint32_t index) const {
        if (nodes[index].type != ExpressionNode::Type::SmallConst)
            return std::nullopt;
        return nodes[index].smallConst;
    }

    bool isPrecompileAddress(uint32_t index) const {
        auto smallConst=getSmallConstMaybe(index);
        if(smallConst.has_value() && smallConst.value()<10)
            return true;
        return false;
    }

    uint64_t getSmallConst(uint32_t index) const {
        assert(nodes[index].type == ExpressionNode::Type::SmallConst);
        return nodes[index].smallConst;
    }

    template<size_t N>
    bool allConstants(const std::array<uint32_t, N>& indices, size_t size) const {
        for (size_t i=0; i<size; i++) {
            if (getType(indices[i]) != ExpressionNode::Type::Const && getType(indices[i]) != ExpressionNode::Type::SmallConst)
                return false;
        }
        return true;
    }

    bool allConstants(const std::vector<uint32_t>& indices) const {
        for (size_t i=0; i<indices.size(); i++) {
            if (getType(indices[i]) != ExpressionNode::Type::Const && getType(indices[i]) != ExpressionNode::Type::SmallConst)
                return false;
        }
        return true;
    }

    bool allConstants(const std::set<uint32_t>& indices) const {
        for (uint32_t index : indices) {
            if (getType(index) != ExpressionNode::Type::Const && getType(index) != ExpressionNode::Type::SmallConst)
                return false;
        }
        return true;
    }

    template<size_t N>
    bool allSmallConstants(const std::array<uint32_t, N>& indices, size_t size) const {
        for (size_t i=0; i<size; i++) {
            if (getType(indices[i]) != ExpressionNode::Type::SmallConst)
                return false;
        }
        return true;
    }

    ExpressionNode::Type getType(uint32_t index) const {
        return nodes[index].type;
    }

    uint32_t createConst(const Word256& w) {
        if (w <= std::numeric_limits<uint64_t>::max()) {
            return createSmallConst(static_cast<uint64_t>(w));
        }
        uint32_t constIdx = constants.getConstantIndex(w);
        ExpressionNode node;
        node.mkConst(constIdx);
        return addNodeToPool(node);
    }

    uint32_t createCallData(uint64_t offset) {
        ExpressionNode node;
        node.mkCallData(static_cast<uint32_t>(offset));
        return addNodeToPool(node);
    }

    uint32_t createCallDataSize() {
        ExpressionNode node;
        node.mkCallDataSize();
        return addNodeToPool(node);
    }

    uint32_t createSelfbalance() {
        ExpressionNode node;
        node.mkSelfbalance();
        return addNodeToPool(node);
    }

    uint32_t createCallvalue() {
        ExpressionNode node;
        node.mkCallvalue();
        return addNodeToPool(node);
    }

    uint32_t createAddress() {
        ExpressionNode node;
        node.mkAddress();
        return addNodeToPool(node);
    }

    uint32_t createReturndataSize() {
        ExpressionNode node;
        node.mkReturndataSize();
        return addNodeToPool(node);
    }

    uint32_t createCaller() {
        ExpressionNode node;
        node.mkCaller();
        return addNodeToPool(node);
    }

    uint32_t createCreate() {
        ExpressionNode node;
        node.mkCreate();
        return addNodeToPool(node);
    }

    //optimize this to pre-create in reset()
    uint32_t createCoinbase() {
        ExpressionNode node;
        node.mkCoinbase();
        return addNodeToPool(node);
    }

    uint32_t createOrigin() {
        ExpressionNode node;
        node.mkOrigin();
        return addNodeToPool(node);
    }

    uint32_t createSload(uint32_t exprIndex) {
        ExpressionNode node;
        node.mkSload(exprIndex);
        return addNodeToPool(node);
    }

    uint32_t createAny(){
        ExpressionNode node;
        return addNodeToPool(node);
    }

    uint32_t createMload(uint32_t exprIndex) {
        ExpressionNode node;
        node.mkMload(exprIndex);
        return addNodeToPool(node);
    }

private:
    uint32_t createCommutativeBinaryOp(ExpressionNode::Type op, uint32_t leftIndex, uint32_t rightIndex) {
        // Operands are already canonical and come from the pool.

        // Ensure left >= right
        if (expressionCompare(*this, leftIndex, rightIndex) < 0) {
            std::swap(leftIndex, rightIndex);
        }
        ExpressionNode node;
        node.mkBinaryOp(op, leftIndex, rightIndex);
        return addNodeToPool(node);
    }

    uint32_t createNonCommutativeBinaryOp(ExpressionNode::Type op, uint32_t leftIndex, uint32_t rightIndex) {
        // Operands are already canonical and come from the pool.

        // Construct the node
        ExpressionNode node;
        node.mkBinaryOp(op, leftIndex, rightIndex);
        return addNodeToPool(node);
    }

public:
    uint32_t createBinaryOp(ExpressionNode::Type op, uint32_t leftIndex, uint32_t rightIndex) {
        if (op == ExpressionNode::Type::And || op == ExpressionNode::Type::Or || op == ExpressionNode::Type::Xor || op == ExpressionNode::Type::Add || op == ExpressionNode::Type::Mul)
            return createCommutativeBinaryOp(op, leftIndex, rightIndex);
        return createNonCommutativeBinaryOp(op, leftIndex, rightIndex);
    }

    uint32_t createUnaryOp(ExpressionNode::Type op, uint32_t exprIndex) {
        ExpressionNode node;
        assert(op == ExpressionNode::Type::Not);
        node.mkUnaryOp(op, exprIndex);
        return addNodeToPool(node);
    }

    const ExpressionNode& getNode(uint32_t index) const {
        return nodes[index];
    }

    const Word256& getBigConstant(uint32_t constIndex) const {
        return constants.getConstant(constIndex);
    }

    void reset_core() {
        constants.reset();
        nodes.clear();
        nodeMap.clear();
    }

    void reset() {
        reset_core();
        
        e0 = createSmallConst(0);
        e1 = createSmallConst(1);
    }

    std::string stringOfBinaryOp(ExpressionNode::Type op) const {
        switch (op) {
            case ExpressionNode::Type::Add: return "+";
            case ExpressionNode::Type::Mul: return "*";
            case ExpressionNode::Type::Sub: return "-";
            case ExpressionNode::Type::Shl: return "<<";
            case ExpressionNode::Type::Shr: return ">>";
            case ExpressionNode::Type::And: return "&";
            case ExpressionNode::Type::Or: return "|";
            case ExpressionNode::Type::Xor: return "^";
            case ExpressionNode::Type::Div: return "/";
            case ExpressionNode::Type::Mod: return "%";
            case ExpressionNode::Type::Exp: return "**";
            default:
                assert(false);// not a binary op
                return "";
        }
    }

    void printExpression(std::ostream& os, uint32_t index) const {
        const ExpressionNode& node = getNode(index);
        switch (node.type) {
        case ExpressionNode::Type::Const: {
            const Word256& w = getBigConstant(node.constantIndex);
            os << w.str(16);
            break;
        }
        case ExpressionNode::Type::CallData:
            os << "callData(";
            printExpression(os, node.exprIndex);
            os << ")";
            break;
        case ExpressionNode::Type::Caller:
            os << "caller";
            break;
        case ExpressionNode::Type::Create:
            os << "create";
            break;
        case ExpressionNode::Type::CallDataSize:
            os << "CDSize";
            break;
        case ExpressionNode::Type::ReturndataSize:
            os << "RDSize";
            break;
        case ExpressionNode::Type::Address:
            os << "address";
            break;
        case ExpressionNode::Type::Coinbase:
            os << "coinbase";
            break;
        case ExpressionNode::Type::Sload: {
            os << "sload(";
            printExpression(os, node.exprIndex);
            os << ")";
            break;
        }
        case ExpressionNode::Type::Mload: {
            os << "mload(";
            printExpression(os, node.exprIndex);
            os << ")";
            break;
        }
        case ExpressionNode::Type::Add: 
        case ExpressionNode::Type::Mul:
        case ExpressionNode::Type::Sub:
        case ExpressionNode::Type::And:
        case ExpressionNode::Type::Or:
        case ExpressionNode::Type::Xor:
        case ExpressionNode::Type::Div:
        case ExpressionNode::Type::Mod:
        case ExpressionNode::Type::Exp:
        {
            os << "(";
            printExpression(os, node.binaryOp.leftIndex);
            os << stringOfBinaryOp(node.type);
            printExpression(os, node.binaryOp.rightIndex);
            os << ")";
            break;
        }
        case ExpressionNode::Type::Shl:
        case ExpressionNode::Type::Shr:
        {
            os << "(";
            printExpression(os, node.binaryOp.rightIndex);
            os << stringOfBinaryOp(node.type);
            printExpression(os, node.binaryOp.leftIndex);
            os << ")";
            break;
        }
        case ExpressionNode::Type::SmallConst:
            os << node.smallConst;
            break;
        case ExpressionNode::Type::Origin:
            os << "origin";
            break;
        case ExpressionNode::Type::Selfbalance:
            os << "selfbal";
            break;
        case ExpressionNode::Type::Callvalue:
            os << "callval";
            break;
        case ExpressionNode::Type::Not:
            os << "!";
            printExpression(os, node.exprIndex);
            break;
        case ExpressionNode::Type::Any:
            os << "*";
            break;
        default:
            assert(false);
        }
    }   

    void serialize(const std::string& filename) const {
        std::ofstream file(filename, std::ios::binary);
        if (!file) {
            throw std::runtime_error("Cannot open file for writing: " + filename);
        }

        // Write constants
        uint32_t constantsSize = static_cast<uint32_t>(constants.constants.size());
        file.write(reinterpret_cast<const char*>(&constantsSize), sizeof(constantsSize));
        for (const auto& constant : constants.constants) {
            serializeConstant(file, constant);
        }

        // Write nodes
        uint32_t nodesSize = static_cast<uint32_t>(nodes.size());
        file.write(reinterpret_cast<const char*>(&nodesSize), sizeof(nodesSize));
        for (const auto& node : nodes) {
            // Write type
            file.write(reinterpret_cast<const char*>(&node.type), sizeof(node.type));

            // Write the appropriate union member based on type
            switch (node.type) {
                case ExpressionNode::Type::Const:
                    file.write(reinterpret_cast<const char*>(&node.constantIndex), sizeof(node.constantIndex));
                    break;
                case ExpressionNode::Type::SmallConst:
                    file.write(reinterpret_cast<const char*>(&node.smallConst), sizeof(node.smallConst));
                    break;
                case ExpressionNode::Type::CallData:
                case ExpressionNode::Type::Sload:
                case ExpressionNode::Type::Mload:
                case ExpressionNode::Type::Not:
                    file.write(reinterpret_cast<const char*>(&node.exprIndex), sizeof(node.exprIndex));
                    break;
                case ExpressionNode::Type::Add:
                case ExpressionNode::Type::Mul:
                case ExpressionNode::Type::Sub:
                case ExpressionNode::Type::Shl:
                case ExpressionNode::Type::Shr:
                case ExpressionNode::Type::And:
                case ExpressionNode::Type::Or:
                case ExpressionNode::Type::Xor:
                case ExpressionNode::Type::Div:
                case ExpressionNode::Type::Mod:
                case ExpressionNode::Type::Exp:
                    file.write(reinterpret_cast<const char*>(&node.binaryOp), sizeof(node.binaryOp));
                    break;
                // Other types don't have additional data
                default:
                    break;
            }
        }

        // Write e0 and e1
        file.write(reinterpret_cast<const char*>(&e0), sizeof(e0));
        file.write(reinterpret_cast<const char*>(&e1), sizeof(e1));
    }

    void deserialize(const std::string& filename) {
        std::ifstream file(filename, std::ios::binary);
        if (!file) {
            throw std::runtime_error("Cannot open file for reading: " + filename);
        }

        // Clear current state
        reset_core();

        // Read constants
        uint32_t constantsSize;
        file.read(reinterpret_cast<char*>(&constantsSize), sizeof(constantsSize));
        for (uint32_t i = 0; i < constantsSize; i++) {
            Word256 constant;
            deserializeConstant(file, constant);
            constants.constants.push_back(constant);
            constants.constantMap[constant] = i;
        }

        // Read nodes
        uint32_t nodesSize;
        file.read(reinterpret_cast<char*>(&nodesSize), sizeof(nodesSize));
        nodes.reserve(nodesSize);
        
        for (uint32_t i = 0; i < nodesSize; i++) {
            ExpressionNode node;
            
            // Read type
            file.read(reinterpret_cast<char*>(&node.type), sizeof(node.type));

            // Read the appropriate union member based on type
            switch (node.type) {
                case ExpressionNode::Type::Const:
                    file.read(reinterpret_cast<char*>(&node.constantIndex), sizeof(node.constantIndex));
                    break;
                case ExpressionNode::Type::SmallConst:
                    file.read(reinterpret_cast<char*>(&node.smallConst), sizeof(node.smallConst));
                    break;
                case ExpressionNode::Type::CallData:
                case ExpressionNode::Type::Sload:
                case ExpressionNode::Type::Mload:
                case ExpressionNode::Type::Not:
                    file.read(reinterpret_cast<char*>(&node.exprIndex), sizeof(node.exprIndex));
                    break;
                case ExpressionNode::Type::Add:
                case ExpressionNode::Type::Mul:
                case ExpressionNode::Type::Sub:
                case ExpressionNode::Type::Shl:
                case ExpressionNode::Type::Shr:
                case ExpressionNode::Type::And:
                case ExpressionNode::Type::Or:
                case ExpressionNode::Type::Xor:
                case ExpressionNode::Type::Div:
                case ExpressionNode::Type::Mod:
                case ExpressionNode::Type::Exp:
                    file.read(reinterpret_cast<char*>(&node.binaryOp), sizeof(node.binaryOp));
                    break;
                default:
                    break;
            }

            nodes.push_back(node);
            nodeMap[node] = i;
        }

        // Read e0 and e1
        file.read(reinterpret_cast<char*>(&e0), sizeof(e0));
        file.read(reinterpret_cast<char*>(&e1), sizeof(e1));
    }

    void printToFile(const std::string& filename) const {
        // Print constants array
        std::ofstream file(filename);
        file << "Constants:\n";
        for (uint32_t i = 0; i < constants.constants.size(); i++) {
            file << i << ": " << constants.getConstant(i).str() << "\n";
        }
        file << "\nExpressions:\n";
        if (!file) {
            throw std::runtime_error("Cannot open file for writing: " + filename);
        }

        // Print each expression in the pool
        for (uint32_t i = 0; i < nodes.size(); i++) {
            printExpression(file, i);
            file << "\n";
        }
        file.close();
    }

    // \pre transaction.to.has_value()
    std::optional<Word256> interpretExpression(
        uint32_t index, monad::BlockHeader const &block_header,
        monad::Transaction const &transaction,// only transaction.data and transaction.value are used
        evmc::address const &sender, 
        evmc::address const &origin, 
        bool root_call // true iff this contract was directly called by the
                       // transaction. false for the callees of the root call
                       // and so on. for non-root calls, we do NOT have CALLDATA
                       // or CALLVALUE or .. as that would need a more complex
                       // static analysis
    ) const
    {
        ExpressionNode const &node = getNode(index);

        switch (node.type) {
        case ExpressionNode::Type::Const: {
            // Example: interpret the stored Word256 as an address
            // and return it as a 256-bit.
            return getConst(index);
        }
        case ExpressionNode::Type::CallData: {
            // return the size of the call data
            if (!root_call) {
                // For non-root calls, we do not have direct access to
                // transaction input
                return std::nullopt;
            }

            // Interpret the node's exprIndex as the offset within transaction
            // input
            auto offsetOpt = interpretExpression(
                node.exprIndex, block_header, transaction, sender, origin, root_call);
            if (!offsetOpt.has_value()) {
                return std::nullopt;
            }

            // Convert offset to a standard 64-bit size
            // If it's larger than we can handle, treat it as out-of-bounds =>
            // zero result
            Word256 offsetVal = offsetOpt.value();
            Word256 const max64{
                std::numeric_limits<uint64_t>::max()};
            if (offsetVal > max64) {
                // Entirely out of range, so we return zero
                return std::nullopt;
            }

            uint64_t offset64 = static_cast<uint64_t>(offsetVal);

            // Prepare a 32-byte buffer to hold the data slice
            uint8_t buffer[32];
            std::memset(buffer, 0, 32);

            // Copy what we can from transaction.input, zero-pad the rest
            if (offset64 < transaction.data.size()) {
                size_t bytesToCopy =
                    std::min<size_t>(32, transaction.data.size() - offset64);
                std::memcpy(buffer, &transaction.data[offset64], bytesToCopy);
            }

            Word256 dataVal;
            from_byte_array_bigendian(dataVal, buffer);
            // Convert the 32-byte buffer to intx::uint256
            // intx::uint256 dataVal = intx::be::load<intx::uint256>(buffer);

            // Convert intx::uint256 back to Word256
            return dataVal; // of
        }
        case ExpressionNode::Type::SmallConst: {
            // Interpret small constants as an address, then to Word256.
            return getConst(index);
        }
        case ExpressionNode::Type::Coinbase: {
            // block_header.beneficiary is an Address (20 bytes).
            // Convert it to Word256.
            return ofAddress(block_header.beneficiary);
        }
        case ExpressionNode::Type::Callvalue: {
            // transaction.value is an intx::uint256.
            // Convert it to Word256.
            return ofIntx(transaction.value);
        }
        case ExpressionNode::Type::Caller: {
            return ofAddress(sender);
        }
        case ExpressionNode::Type::Origin: {
            return ofAddress(origin);
        }
        case ExpressionNode::Type::Create: {
            // Incomplete placeholder. Return zero or some specialized logic.
            return std::nullopt;
        }
        case ExpressionNode::Type::Sload: {
            // Placeholder for reading from storage. Return 0.
            return std::nullopt;
        }
        case ExpressionNode::Type::Mload: {
            // Placeholder for reading from memory. Return 0.
            return std::nullopt;
        }
        case ExpressionNode::Type::Any: {
            // A wildcard or unknown expression. Return 0 or handle specially.
            return std::nullopt;
        }

        // ----------------
        // Binary operations:
        // ----------------
        case ExpressionNode::Type::Add:
        case ExpressionNode::Type::Sub:
        case ExpressionNode::Type::Mul:
        case ExpressionNode::Type::Div:
        case ExpressionNode::Type::Mod:
        case ExpressionNode::Type::And:
        case ExpressionNode::Type::Or:
        case ExpressionNode::Type::Xor:
        case ExpressionNode::Type::Exp:
        case ExpressionNode::Type::Shl:
        case ExpressionNode::Type::Shr: {
            // Recursively evaluate children as intx::uint256,
            // then combine and convert the result to Word256 at the end.
            auto lhsOpt = interpretExpression(
                node.binaryOp.leftIndex, block_header, transaction, sender, origin, root_call);
            if (!lhsOpt.has_value()) {
                return std::nullopt;
            }
            auto lhs = lhsOpt.value();
            auto rhsOpt = interpretExpression(
                node.binaryOp.rightIndex, block_header, transaction, sender, origin, root_call);
            if (!rhsOpt.has_value()) {
                return std::nullopt;
            }
            auto rhs = rhsOpt.value();

            Word256 result = 0;
            switch (node.type) {
            case ExpressionNode::Type::Add:
                result = lhs + rhs;
                break;
            case ExpressionNode::Type::Sub:
                result = lhs - rhs;
                break;
            case ExpressionNode::Type::Mul:
                result = lhs * rhs;
                break;
            case ExpressionNode::Type::Div:
                result = (rhs == 0) ? 0 : lhs / rhs;
                break;
            case ExpressionNode::Type::Mod:
                result = (rhs == 0) ? 0 : lhs % rhs;
                break;
            case ExpressionNode::Type::And:
                result = lhs & rhs;
                break;
            case ExpressionNode::Type::Or:
                result = lhs | rhs;
                break;
            case ExpressionNode::Type::Xor:
                result = lhs ^ rhs;
                break;
            case ExpressionNode::Type::Exp:
                result = boost::multiprecision::pow(lhs, rhs.convert_to<unsigned>());
                break;
            case ExpressionNode::Type::Shl:
                result = lhs << rhs.convert_to<unsigned>();
                break;
            case ExpressionNode::Type::Shr:
                result = lhs >> rhs.convert_to<unsigned>();
                break;
            default:
                result = 0;
                break;
            }
            return result;
        }

        // ----------------
        // Unary operations:
        // ----------------
        case ExpressionNode::Type::Not: {
            // Evaluate child as intx::uint256, then invert bits.
            auto valOpt = interpretExpression(node.exprIndex, block_header, transaction, sender, origin, root_call);
            if (!valOpt.has_value()) {
                return std::nullopt;
            }
            auto val = valOpt.value();
            return ~val;
        }

        // ----------------
        // Other zero-data ops:
        // ----------------
        case ExpressionNode::Type::CallDataSize: {
            return Word256(transaction.data.size());
        }
        case ExpressionNode::Type::ReturndataSize: {
            return std::nullopt;
        }
        case ExpressionNode::Type::Address: {
            if (transaction.to.has_value()) {
                return ofAddress(transaction.to.value());
            }
            return std::nullopt;
        }
        case ExpressionNode::Type::Selfbalance: {
            return std::nullopt;
        }
        default:
            MONAD_ASSERT(false);
            return std::nullopt;
        }
    }

    bool allSupported(const std::set<uint32_t>& indices) const {
        evmc::address dummyAddr;
        monad::Transaction dummy_transaction;
        dummy_transaction.to = dummyAddr;
        monad::BlockHeader dummy_block_header;
        
        
        for (uint32_t index : indices) {
            auto ie=interpretExpression(index, dummy_block_header, dummy_transaction, dummyAddr, dummyAddr, true);
            if (!ie.has_value())
                return false;
        }
        return true;
    }


};

// Implement expressionCompare
inline int expressionCompare(const ExpressionPool& pool, uint32_t idx1, uint32_t idx2) {
    if (idx1 == idx2) return 0;

    const ExpressionNode& node1 = pool.getNode(idx1);
    const ExpressionNode& node2 = pool.getNode(idx2);

    // Compare types
    if (node1.type != node2.type)
        return static_cast<int>(node1.type) - static_cast<int>(node2.type);

    // Types are equal; compare based on type
    switch (node1.type) {
        case ExpressionNode::Type::Const: {
            const Word256& w1 = pool.getBigConstant(node1.constantIndex);
            const Word256& w2 = pool.getBigConstant(node2.constantIndex);
            if (w1 < w2) return -1;
            if (w1 > w2) return 1;
            return 0;
        }
        case ExpressionNode::Type::Caller:
        case ExpressionNode::Type::Coinbase:
        case ExpressionNode::Type::Origin:
        case ExpressionNode::Type::CallDataSize:
        case ExpressionNode::Type::Address:
        case ExpressionNode::Type::Create:
        case ExpressionNode::Type::ReturndataSize:
        case ExpressionNode::Type::Any:
        case ExpressionNode::Type::Selfbalance:
        case ExpressionNode::Type::Callvalue:
            return 0; // No additional data
        case ExpressionNode::Type::Sload:
        case ExpressionNode::Type::Mload:
        case ExpressionNode::Type::Not:
        case ExpressionNode::Type::CallData:
            if (node1.exprIndex < node2.exprIndex) return -1;
            if (node1.exprIndex > node2.exprIndex) return 1;
            return 0;
        case ExpressionNode::Type::Add:
        case ExpressionNode::Type::Mul:
        case ExpressionNode::Type::Sub: 
        case ExpressionNode::Type::Shl:
        case ExpressionNode::Type::Shr:
        case ExpressionNode::Type::And:
        case ExpressionNode::Type::Or:
        case ExpressionNode::Type::Xor:
        case ExpressionNode::Type::Div:
        case ExpressionNode::Type::Mod:
        case ExpressionNode::Type::Exp:
        {
            int cmpLeft = expressionCompare(pool, node1.binaryOp.leftIndex, node2.binaryOp.leftIndex);
            if (cmpLeft != 0) return cmpLeft;
            return expressionCompare(pool, node1.binaryOp.rightIndex, node2.binaryOp.rightIndex);
        }
        case ExpressionNode::Type::SmallConst: {
            if (node1.smallConst < node2.smallConst) return -1;
            if (node1.smallConst > node2.smallConst) return 1;
            return 0;
        }
        default:
            assert(false);
            return 0;
    }
}

// Implement isCanonical for assertions
inline bool isCanonical(const ExpressionPool& pool, uint32_t idx) {
    const ExpressionNode& node = pool.getNode(idx);

    switch (node.type) {
        case ExpressionNode::Type::Const:
        case ExpressionNode::Type::Caller:
        case ExpressionNode::Type::Coinbase:
        case ExpressionNode::Type::Origin:
        case ExpressionNode::Type::SmallConst:
        case ExpressionNode::Type::CallDataSize:
        case ExpressionNode::Type::Address:
        case ExpressionNode::Type::Create:
        case ExpressionNode::Type::ReturndataSize:
        case ExpressionNode::Type::Any:
        case ExpressionNode::Type::Selfbalance:
        case ExpressionNode::Type::Callvalue:
            return true; // Base cases

        case ExpressionNode::Type::Sload:
        case ExpressionNode::Type::Mload:
        case ExpressionNode::Type::Not:
        case ExpressionNode::Type::CallData:
            return isCanonical(pool, node.exprIndex);

        case ExpressionNode::Type::Add:
        case ExpressionNode::Type::Mul: 
        case ExpressionNode::Type::And:
        case ExpressionNode::Type::Or:
        case ExpressionNode::Type::Xor:
        case ExpressionNode::Type::Div:
        case ExpressionNode::Type::Mod:
        case ExpressionNode::Type::Exp:
        {
            // Check operands are canonical
            if (!isCanonical(pool, node.binaryOp.leftIndex)) return false;
            if (!isCanonical(pool, node.binaryOp.rightIndex)) return false;

            // Ensure left >= right
            return expressionCompare(pool, node.binaryOp.leftIndex, node.binaryOp.rightIndex) >= 0;
        }

        case ExpressionNode::Type::Sub:
        case ExpressionNode::Type::Shl:
        case ExpressionNode::Type::Shr:
        {
            // Check operands are canonical
            return isCanonical(pool, node.binaryOp.leftIndex) && isCanonical(pool, node.binaryOp.rightIndex);
        }

        default:
            assert(false);
            return false;
    }
}


// Function to print expressions

/*
int main() {
    ExpressionPool pool;

    // Create constants
    auto const5 = pool.createConst(5);
    auto const10 = pool.createConst(10);
    auto const5_dup = pool.createConst(5);

    // Verify that const5 and const5_dup are the same due to hash-consing
    assert(const5 == const5_dup);

    // Create addition expressions
    auto expr1 = pool.createAdd(const5, const10); // Should create (10 + 5) after operand ordering
    auto expr2 = pool.createAdd(const10, const5); // Also (10 + 5)
    auto expr3 = pool.createAdd(const5, const5);  // Should create (5 + 5)

    // Verify that expr1 and expr2 are the same due to canonicalization
    assert(expr1 == expr2);

    // Verify that expr1 and expr3 are different
    assert(expr1 != expr3);

    // Print expressions
    Expression e1(expr1, &pool);
    Expression e3(expr3, &pool);

    std::cout << "Expression e1: ";
    printExpression(e1); // Outputs: (10 + 5)
    std::cout << std::endl;

    std::cout << "Expression e3: ";
    printExpression(e3); // Outputs: (5 + 5)
    std::cout << std::endl;

    // Verify that expressions are canonical
    assert(isCanonical(pool, expr1));
    assert(isCanonical(pool, expr3));

    std::cout << "All expressions are canonical and hash-consing works correctly." << std::endl;

    return 0;
}
*/

struct Prediction {
    std::vector<uint32_t> callees;
    std::vector<uint32_t> delegateCallees;
    std::vector<uint32_t> balanceAccounts;
};

inline void prepad_hex(std::string &s, size_t size=64) {
    if (s.size() < size) {
        s = std::string(size - s.size(), '0') + s;
    }
}

inline ::evmc::address hex_to_address(const std::string& hex_str) {
    std::string s = hex_str;
    if (s.size() >= 2 && s.compare(0, 2, "0x") == 0) {
        s = s.substr(2);
    }

    prepad_hex(s, 40);

    unsigned char bytes[20];
    boost::algorithm::unhex(s.begin(), s.end(), bytes);

    ::evmc::address addr{};
    std::copy(bytes, bytes + 20, addr.bytes);
    return addr;
}

inline void trim(std::string &s) {
    s.erase(0, s.find_first_not_of(" \n\r\t"));
    s.erase(s.find_last_not_of(" \n\r\t") + 1);
}


inline ::evmc::bytes32 hex_to_bytes32(const std::string& hex_str) {
    std::string s = hex_str;
    trim(s);

    prepad_hex(s);// this should not be needed but there is a bug in the code that generated the string (filename=code has 64 characters)
    assert(s.size() == 64);

    unsigned char bytes[32];
    boost::algorithm::unhex(s.begin(), s.end(), bytes);

    ::evmc::bytes32 hash{};
    std::copy(bytes, bytes + 32, hash.bytes);
    return hash;
}
using Predictions = std::unordered_map<::evmc::bytes32, Prediction>;


// Start Generation Here
inline void serializePredictions(const Predictions &predictions, const std::string &filename) {
    std::ofstream out(filename, std::ios::binary);
    if (!out) {
        // Could handle error silently or throw
        return;
    }

    // Write how many entries in predictions map
    size_t mapSize = predictions.size();
    out.write(reinterpret_cast<const char*>(&mapSize), sizeof(mapSize));

    // For each entry, write the key (bytes32) then the vectors
    for (auto const &kv : predictions) {
        auto const &key = kv.first;
        auto const &prediction = kv.second;

        // write key (32 bytes)
        out.write(reinterpret_cast<const char*>(key.bytes), sizeof(key.bytes));

        // write callees
        {
            size_t calleesCount = prediction.callees.size();
            out.write(reinterpret_cast<const char*>(&calleesCount), sizeof(calleesCount));
            for (auto const &callee : prediction.callees) {
                out.write(reinterpret_cast<const char*>(&callee), sizeof(callee));
            }
        }

        // write delegateCallees
        {
            size_t delegateCount = prediction.delegateCallees.size();
            out.write(reinterpret_cast<const char*>(&delegateCount), sizeof(delegateCount));
            for (auto const &dCallee : prediction.delegateCallees) {
                out.write(reinterpret_cast<const char*>(&dCallee), sizeof(dCallee));
            }
        }

        // write balance accounts
        {
            size_t balanceCount = prediction.balanceAccounts.size();
            out.write(reinterpret_cast<const char*>(&balanceCount), sizeof(balanceCount));
            for (auto const &bAccount : prediction.balanceAccounts) {
                out.write(reinterpret_cast<const char*>(&bAccount), sizeof(bAccount));
            }
        }
    }
}

inline void unserializePredictions(Predictions &predictions, const std::string &filename) {
    std::ifstream in(filename, std::ios::binary);
    if (!in) {
        throw std::runtime_error("Cannot open file for reading: " + filename);
    }

    size_t mapSize = 0;
    in.read(reinterpret_cast<char*>(&mapSize), sizeof(mapSize));

    // Clear existing predictions then reserve if possible
    predictions.clear();
    predictions.reserve(mapSize);

    for (size_t i = 0; i < mapSize; ++i) {
        ::evmc::bytes32 key{};
        in.read(reinterpret_cast<char*>(key.bytes), sizeof(key.bytes));

        Prediction pred;

        // read callees
        {
            size_t calleesCount = 0;
            in.read(reinterpret_cast<char*>(&calleesCount), sizeof(calleesCount));
            pred.callees.resize(calleesCount);
            for (size_t j = 0; j < calleesCount; ++j) {
                in.read(reinterpret_cast<char*>(&pred.callees[j]), sizeof(pred.callees[j]));
            }
        }

        // read delegateCallees
        {
            size_t delegateCount = 0;
            in.read(reinterpret_cast<char*>(&delegateCount), sizeof(delegateCount));
            pred.delegateCallees.resize(delegateCount);
            for (size_t j = 0; j < delegateCount; ++j) {
                in.read(reinterpret_cast<char*>(&pred.delegateCallees[j]), sizeof(pred.delegateCallees[j]));
            }
        }

        // read balance accounts
        {
            size_t balanceCount = 0;
            in.read(reinterpret_cast<char*>(&balanceCount), sizeof(balanceCount));
            pred.balanceAccounts.resize(balanceCount);
            for (size_t j = 0; j < balanceCount; ++j) {
                in.read(reinterpret_cast<char*>(&pred.balanceAccounts[j]), sizeof(pred.balanceAccounts[j]));
            }
        }
        predictions.emplace(key, std::move(pred));
    }
}



inline evmc::address get_address(const Word256& word) {
    auto truncated = intx::be::trunc<evmc::address>(ofBoost(word));
    return truncated;
}

inline evmc::address get_address(uint32_t index, ExpressionPool &epool) {
    Word256 word = epool.getConst(index);
    return get_address(word);
}

inline void printPredictions(const ExpressionPool& epool, const Predictions& predictions, std::string filename) {
    std::ofstream out(filename);
    out << "Predictions (" << predictions.size() << " entries):\n";
    std::map<::evmc::bytes32, Prediction> sorted_predictions(predictions.begin(), predictions.end());
    for (const auto& [key, pred] : sorted_predictions) {
        // Print key
        out << "Key: 0x";
        for (uint8_t b : key.bytes) {
            out << std::hex << std::setw(2) << std::setfill('0') << static_cast<int>(b);
        }
        out << std::dec << "\n";

        // Print callees
        out << "  Callees (" << pred.callees.size() << "):\n";
        for (const auto& callee : pred.callees) {
            epool.printExpression(out, callee);
            out << "\n";
        }

        // Print delegate callees
        out << "  Delegate Callees (" << pred.delegateCallees.size() << "):\n"; 
        for (const auto& dCallee : pred.delegateCallees) {
            epool.printExpression(out, dCallee);
            out << "\n";
        }
        out << "\n";
    }
}
