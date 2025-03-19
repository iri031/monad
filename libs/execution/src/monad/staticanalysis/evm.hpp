/**
 * evm.hpp
 * 
 * This file contains the definitions and functions needed to parse and pretty-print EVM bytecode.
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
using NodeID = uint16_t;
#include <bitset>
// Boost includes
#include <boost/multiprecision/cpp_int.hpp>
#include <boost/multiprecision/integer.hpp>

namespace mp = boost::multiprecision;

// Define EvmWord as a 256-bit unsigned integer
using EvmWord = mp::uint256_t;

// Define ByteOffset as an unsigned 64-bit integer (adjust as needed)
using ByteOffset = NodeID;

// Define Bytet as an 8-bit unsigned integer
using Bytet = uint8_t;

/* Instruction Types */

// Instructions without associated data
enum class InstructionType : uint8_t {
    Add,
    SStore,
    Pop,
    Mul,
    Sub,
    Div,
    Sdiv,
    Mod,
    Smod,
    Addmod,
    Mulmod,
    Exp,
    Signextend,
    Lt,
    Gt,
    Slt,
    Sgt,
    Eq,
    Iszero,
    And,
    Or,
    Xor,
    Not,
    Byte,
    Shl,
    Shr,
    Sar,
    SHA3,
    Address,
    Balance,
    Origin,
    Caller,
    Callvalue,
    Calldataload,
    Calldatasize,
    Calldatacopy,
    Codesize,
    Codecopy,
    Gasprice,
    Extcodesize,
    Extcodecopy,
    Returndatasize,
    Returndatacopy,
    Extcodehash,
    Blockhash,
    Coinbase,
    Timestamp,
    Number,
    Difficulty,
    Gaslimit,
    Chainid,
    Selfbalance,
    Basefee,
    Blobhash,
    Blobbasefee,
    Mload,
    Mstore,
    Mstore8,
    Sload,
    Msize,
    Gas,
    Tload,
    Tstore,
    Mcopy,
    Create,
    Call,
    Callcode,
    Delegatecall,
    Create2,
    Staticcall
};

// Instructions with associated data
struct Swap {
    uint8_t n; // Range [1, 16]
};

struct Dup {
    uint8_t n; // Range [1, 16]
};

struct Push {
    uint8_t n;  // Number of bytes in the push (e.g., 1 to 32)
    EvmWord w;  // The word to push onto the stack
};

struct PC {
    ByteOffset offset;
};

struct Log {
    uint8_t n; // Number of topics (0 to 4)
};

// Define Instruction as a variant
using Instruction = std::variant<
    InstructionType,
    Swap,
    Dup,
    Push,
    PC,
    Log
>;

/* Terminator Types */

// Terminators without associated data
enum class TerminatorType : uint8_t {
    Stop,
    Jump,
    Return,
    Revert,
    SelfDestruct
};

// Terminators with associated data
struct  Jumpi {
    ByteOffset offset;
};

struct Jumpdest {
    ByteOffset offset;
};

struct InvalidInstruction {
    Bytet b; // The invalid byte
};

// Define Terminator as a variant
using Terminator = std::variant<
    TerminatorType,
    Jumpi,
    Jumpdest,
  InvalidInstruction>;

/*
  enum class MiscTypes : uint8_t {
    JUMPI,
    JUMPDEST,
    INVALID_INSTRUCTION,
    SWAP,
    DUP,
    PUSH,
    PC,
    LOG
  };

using InstrLabel = std::variant<MiscTypes, InstructionType, TerminatorType>;
*/


// Opcode Parsing Function
using InsTerm = std::variant<Instruction, Terminator>;

template<typename T, uint16_t MAX_SIZE>
struct FixedSizeArray {
    static_assert(MAX_SIZE > 0, "MAX_SIZE must be positive");
    
    T arr[MAX_SIZE];
    uint16_t size{0};

    void push_back(const T& value) {
        assert(size < MAX_SIZE && "Array overflow");
        arr[size++] = value;
    }
    T& push_back() {
        assert(size < MAX_SIZE && "Array overflow");
        return arr[size++];
    }

    T& push_back_no_assert() {
        return arr[size++];
    }

    T& operator[](uint16_t index) {
        assert(index < size && "Index out of bounds");
        return arr[index];
    }

    const T& operator[](uint16_t index) const {
        assert(index < size && "Index out of bounds");
        return arr[index];
    }

    void clear() {
        size = 0;
    }

    bool empty() const {
        return size == 0;
    }

    uint16_t get_size() const {
        return size;
    }
};

std::string to_string(InstructionType type) {
    switch (type) {
        case InstructionType::Add: return "+";
        case InstructionType::SStore: return "SStore";
        case InstructionType::Pop: return "Pop";
        case InstructionType::Mul: return "*";
        case InstructionType::Sub: return "-";
        case InstructionType::Div: return "/";
        case InstructionType::Sdiv: return "S/";
        case InstructionType::Mod: return "Mod";
        case InstructionType::Smod: return "Smod";
        case InstructionType::Addmod: return "Addmod";
        case InstructionType::Mulmod: return "Mulmod";
        case InstructionType::Exp: return "Exp";
        case InstructionType::Signextend: return "Sgnext";
        case InstructionType::Lt: return "<";
        case InstructionType::Gt: return ">";
        case InstructionType::Slt: return "Slt";
        case InstructionType::Sgt: return "Sgt";
        case InstructionType::Eq: return "Eq";
        case InstructionType::Iszero: return "Is0";
        case InstructionType::And: return "And";
        case InstructionType::Or: return "Or";
        case InstructionType::Xor: return "Xor";
        case InstructionType::Not: return "Not";
        case InstructionType::Byte: return "Byte";
        case InstructionType::Shl: return "Shl";
        case InstructionType::Shr: return "Shr";
        case InstructionType::Sar: return "Sar";
        case InstructionType::SHA3: return "SHA3";
        case InstructionType::Address: return "Addr";
        case InstructionType::Balance: return "Bal";
        case InstructionType::Origin: return "Orig";
        case InstructionType::Caller: return "Callr";
        case InstructionType::Callvalue: return "Callval";
        case InstructionType::Calldataload: return "CDload";
        case InstructionType::Calldatasize: return "CDsize";
        case InstructionType::Calldatacopy: return "CDcopy";
        case InstructionType::Codesize: return "Csize";
        case InstructionType::Codecopy: return "Ccopy";
        case InstructionType::Gasprice: return "Gaspr";
        case InstructionType::Extcodesize: return "ECsize";
        case InstructionType::Extcodecopy: return "ECcopy";
        case InstructionType::Returndatasize: return "RDSize";
        case InstructionType::Returndatacopy: return "RDCopy";
        case InstructionType::Extcodehash: return "EChash";
        case InstructionType::Blockhash: return "Bhash";
        case InstructionType::Coinbase: return "Cbase";
        case InstructionType::Timestamp: return "TStamp";
        case InstructionType::Number: return "Number";
        case InstructionType::Difficulty: return "Diff";
        case InstructionType::Gaslimit: return "Gaslim";
        case InstructionType::Chainid: return "Chainid";
        case InstructionType::Selfbalance: return "Selfbal";
        case InstructionType::Basefee: return "BBee";
        case InstructionType::Blobhash: return "BHash";
        case InstructionType::Blobbasefee: return "BBfee";
        case InstructionType::Mload: return "Mload";
        case InstructionType::Mstore: return "Mstore";
        case InstructionType::Mstore8: return "Mstore8";
        case InstructionType::Sload: return "Sload";
        case InstructionType::Msize: return "Msize";
        case InstructionType::Gas: return "Gas";
        case InstructionType::Tload: return "Tload";
        case InstructionType::Tstore: return "Tstore";
        case InstructionType::Mcopy: return "Mcopy";
        case InstructionType::Create: return "Create";
        case InstructionType::Call: return "Call";
        case InstructionType::Callcode: return "Callcode";
        case InstructionType::Delegatecall: return "Dcall";
        case InstructionType::Create2: return "Create2";
        case InstructionType::Staticcall: return "Scall";
        default: return "InvalidIns";
    }
}

std::string to_string(TerminatorType type) {
    switch (type) {
        case TerminatorType::Stop: return "Stop";
        case TerminatorType::Jump: return "Jmp";
        case TerminatorType::Return: return "Ret";
        case TerminatorType::Revert: return "Rvt";
        case TerminatorType::SelfDestruct: return "SDst";
        default: return "Unknown TerminatorType";
    }
}

void printInstruction(const Instruction& instr, std::ostream& os = std::cout) {
    std::visit([&os](auto&& arg) {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, InstructionType>) {
            os << to_string(arg);
        } else if constexpr (std::is_same_v<T, Swap>) {
            os << "Swp" << static_cast<int>(arg.n);
        } else if constexpr (std::is_same_v<T, Dup>) {
            os << "Dup" << static_cast<int>(arg.n);
        } else if constexpr (std::is_same_v<T, Push>) {
            os << "Push" << static_cast<int>(arg.n) << " " << arg.w;
        } else if constexpr (std::is_same_v<T, PC>) {
            os << "PC" << arg.offset;
        } else if constexpr (std::is_same_v<T, Log>) {
            os << "Log" << static_cast<int>(arg.n);
        }
    }, instr);
}

// Function to print Terminator
void printTerminator(const Terminator& term, std::ostream& os = std::cout) {
    std::visit([&os](auto&& arg) {
        using T = std::decay_t<decltype(arg)>;
        if constexpr (std::is_same_v<T, TerminatorType>) {
            os << to_string(arg);
        } else if constexpr (std::is_same_v<T, Jumpi>) {
            os << "Jmpi" << arg.offset;
        } else if constexpr (std::is_same_v<T, Jumpdest>) {
            os << "Jdest" << arg.offset;
        } else if constexpr (std::is_same_v<T, InvalidInstruction>) {
            os << "Invalid:" << std::hex << static_cast<int>(arg.b) << std::dec;
        }
    }, term);
}

void printInsTerm(const InsTerm& insterm, std::ostream& os = std::cout) {
    if (std::holds_alternative<Instruction>(insterm)) {
        printInstruction(std::get<Instruction>(insterm), os);
    } else {
        printTerminator(std::get<Terminator>(insterm), os);
    }
}

template<size_t MAX_BYTECODESIZE>
void parseOpcode(
    InsTerm& parsed, const FixedSizeArray<Bytet, MAX_BYTECODESIZE>& bytes, NodeID & offset
) {
    assert(offset<bytes.size);
    Bytet opcode = bytes[offset];
    offset++;

    // Helper lambdas for instruction and terminator
    auto instr = [&](Instruction ins) {
        parsed = ins;
    };

    auto term = [&](Terminator ter) {
        parsed = ter;
    };

    switch (opcode) {
        case 0x00: term(TerminatorType::Stop); break;
        case 0x01: instr(InstructionType::Add); break;
        case 0x02: instr(InstructionType::Mul); break;
        case 0x03: instr(InstructionType::Sub); break;
        case 0x04: instr(InstructionType::Div); break;
        case 0x05: instr(InstructionType::Sdiv); break;
        case 0x06: instr(InstructionType::Mod); break;
        case 0x07: instr(InstructionType::Smod); break;
        case 0x08: instr(InstructionType::Addmod); break;
        case 0x09: instr(InstructionType::Mulmod); break;
        case 0x0A: instr(InstructionType::Exp); break;
        case 0x0B: instr(InstructionType::Signextend); break;
        case 0x10: instr(InstructionType::Lt); break;
        case 0x11: instr(InstructionType::Gt); break;
        case 0x12: instr(InstructionType::Slt); break;
        case 0x13: instr(InstructionType::Sgt); break;
        case 0x14: instr(InstructionType::Eq); break;
        case 0x15: instr(InstructionType::Iszero); break;
        case 0x16: instr(InstructionType::And); break;
        case 0x17: instr(InstructionType::Or); break;
        case 0x18: instr(InstructionType::Xor); break;
        case 0x19: instr(InstructionType::Not); break;
        case 0x1A: instr(InstructionType::Byte); break;
        case 0x1B: instr(InstructionType::Shl); break;
        case 0x1C: instr(InstructionType::Shr); break;
        case 0x1D: instr(InstructionType::Sar); break;
        case 0x20: instr(InstructionType::SHA3); break;
        case 0x30: instr(InstructionType::Address); break;
        case 0x31: instr(InstructionType::Balance); break;
        case 0x32: instr(InstructionType::Origin); break;
        case 0x33: instr(InstructionType::Caller); break;
        case 0x34: instr(InstructionType::Callvalue); break;
        case 0x35: instr(InstructionType::Calldataload); break;
        case 0x36: instr(InstructionType::Calldatasize); break;
        case 0x37: instr(InstructionType::Calldatacopy); break;
        case 0x38: instr(InstructionType::Codesize); break;
        case 0x39: instr(InstructionType::Codecopy); break;
        case 0x3A: instr(InstructionType::Gasprice); break;
        case 0x3B: instr(InstructionType::Extcodesize); break;
        case 0x3C: instr(InstructionType::Extcodecopy); break;
        case 0x3D: instr(InstructionType::Returndatasize); break;
        case 0x3E: instr(InstructionType::Returndatacopy); break;
        case 0x3F: instr(InstructionType::Extcodehash); break;
        case 0x40: instr(InstructionType::Blockhash); break;
        case 0x41: instr(InstructionType::Coinbase); break;
        case 0x42: instr(InstructionType::Timestamp); break;
        case 0x43: instr(InstructionType::Number); break;
        case 0x44: instr(InstructionType::Difficulty); break;
        case 0x45: instr(InstructionType::Gaslimit); break;
        case 0x46: instr(InstructionType::Chainid); break;
        case 0x47: instr(InstructionType::Selfbalance); break;
        case 0x48: instr(InstructionType::Basefee); break;
        case 0x49: instr(InstructionType::Blobhash); break;
        case 0x4A: instr(InstructionType::Blobbasefee); break;
        case 0x50: instr(InstructionType::Pop); break;
        case 0x51: instr(InstructionType::Mload); break;
        case 0x52: instr(InstructionType::Mstore); break;
        case 0x53: instr(InstructionType::Mstore8); break;
        case 0x54: instr(InstructionType::Sload); break;
        case 0x55: instr(InstructionType::SStore); break;
        case 0x56: term(TerminatorType::Jump); break;
        case 0x57: term(Jumpi{static_cast<uint16_t>(offset)}); break;
        case 0x58: instr(PC{static_cast<uint16_t>(offset-1)}); break;
        case 0x59: instr(InstructionType::Msize); break;
        case 0x5A: instr(InstructionType::Gas); break;
        case 0x5B: term(Jumpdest{static_cast<uint16_t>(offset-1)}); break;
        case 0x5C: instr(InstructionType::Tload); break;
        case 0x5D: instr(InstructionType::Tstore); break;
        case 0x5E: instr(InstructionType::Mcopy); break;
        case 0x5F: instr(Push{0, 0}); break;
        case 0x60 ... 0x7F: {  // PUSH1 to PUSH32
            uint8_t n = opcode - 0x5F;
            EvmWord value = 0;
            for (uint8_t i = 0; i < n; i++) {
                if (offset+1<bytes.size) {
                    value = (value << 8) | bytes[offset];
                    offset++;
                } else {
                    value = value << (8 * (n - i));
                    break;
                }
            }
            instr(Push{n, value});
            break;
        }
        case 0x80 ... 0x8F:  // DUP1 to DUP16
            instr(Dup{static_cast<uint8_t>(opcode - 0x7F)});
            break;
        case 0x90 ... 0x9F:  // SWAP1 to SWAP16
            instr(Swap{static_cast<uint8_t>(opcode - 0x8F)});
            break;
        case 0xA0 ... 0xA4:  // LOG0 to LOG4
            instr(Log{static_cast<uint8_t>(opcode - 0xA0)});
            break;
        case 0xF0: instr(InstructionType::Create); break;
        case 0xF1: instr(InstructionType::Call); break;
        case 0xF2: instr(InstructionType::Callcode); break;
        case 0xF3: term(TerminatorType::Return); break;
        case 0xF4: instr(InstructionType::Delegatecall); break;
        case 0xF5: instr(InstructionType::Create2); break;
        case 0xFA: instr(InstructionType::Staticcall); break;
        case 0xFD: term(TerminatorType::Revert); break;
        case 0xFF: term(TerminatorType::SelfDestruct); break;
        default:
            term(InvalidInstruction{opcode});
            break;
    }

}

// Update ParsedBytecode to use FixedSizeArray
template<size_t MAX_BYTECODESIZE, size_t MAX_BBLOCKS>
struct ParsedBytecode {
    FixedSizeArray<Bytet, MAX_BYTECODESIZE> bytes;//not parsed it makes the result 80x the size (sizeof Instruction=80)
    FixedSizeArray<NodeID, MAX_BBLOCKS> jumpDestOffsets; // useful when the top of the stack is unknowm just before Jump opcode
    std::bitset<MAX_BYTECODESIZE> jumpDests;      // For fast membership checking in other cases: 

    void populateJumpDests() {
        jumpDests.reset();
        for (uint16_t i = 0; i < jumpDestOffsets.size; ++i) {
            jumpDests.set(jumpDestOffsets[i]);
        }
    }

    void clear() {
        bytes.clear();
        jumpDestOffsets.clear();
    }
    void reset() {
        clear();
    }

    // Delete copy operations
    ParsedBytecode(const ParsedBytecode&) = delete;
    ParsedBytecode& operator=(const ParsedBytecode&) = delete;
    ParsedBytecode() = default;

    void print(std::ostream& os = std::cout) const {
        os << "Instructions:" << bytes.get_size() << ":\n";
        InsTerm insTerm;
        NodeID offset = 0;
        while (offset<bytes.get_size()) {
            os << offset << ":";
            parseOpcode<MAX_BYTECODESIZE>(insTerm, bytes, offset);
            if (std::holds_alternative<Instruction>(insTerm)) {
                printInstruction(std::get<Instruction>(insTerm), os);
                os << std::endl;
            } else {
                printTerminator(std::get<Terminator>(insTerm), os);
                os << std::endl;
            }
        }

        os << "JumpDest Offsets:" << jumpDestOffsets.get_size() << ":\n";
        bool first = true;
        for(uint16_t i = 0; i < jumpDestOffsets.get_size(); ++i) {
            if (!first) os << ", ";
            os << jumpDestOffsets[i];
            first = false;
        }
        os << "\n";
    }
};



template<size_t MAX_BYTECODESIZE, size_t MAX_BBLOCKS>
bool parseJumpDests(FixedSizeArray<NodeID, MAX_BBLOCKS> &jumpDestOffsets, const FixedSizeArray<Bytet, MAX_BYTECODESIZE>& bytes) {
    jumpDestOffsets.clear();
    NodeID offset = 0;
    InsTerm parsed;
    bool prevJmpi=false;
    bool isJumpdest=false;
    bool curJumpi=false;
    NodeID numNonJumpdestBB=0;
    while (offset<bytes.size) {
        Bytet current = bytes[offset];

        parseOpcode<MAX_BYTECODESIZE>(parsed, bytes, offset);
        curJumpi=false;

        // Check for JUMPDEST and record its offset
        if (std::holds_alternative<Terminator>(parsed)) {
            auto& term = std::get<Terminator>(parsed);
            isJumpdest = std::holds_alternative<Jumpdest>(term);
            if (isJumpdest) {
                if(jumpDestOffsets.get_size()>=MAX_BBLOCKS) {
                    return false;
                }
                jumpDestOffsets.push_back_no_assert(offset);
            } else if (std::holds_alternative<Jumpi>(term)) {
                curJumpi=true;
            }
        }
        if (!isJumpdest && prevJmpi) {
            numNonJumpdestBB++;// these basic blocks do not start with a jumpdest but follow a Jumpi
        }
        prevJmpi=curJumpi;

    }
    //std::cerr << "numNonJumpdestBB: " << numNonJumpdestBB << " jumpDestOffsets.get_size(): " << jumpDestOffsets.get_size() << std::endl;
    if (numNonJumpdestBB+jumpDestOffsets.get_size()>=MAX_BBLOCKS) {
        return false;
    }
    return true;
}

/**
 * returns false if the number of basic blocks is greater than MAX_BBLOCKS
 */
template<size_t MAX_BYTECODESIZE, size_t MAX_BBLOCKS>
bool readBytecode(ParsedBytecode<MAX_BYTECODESIZE, MAX_BBLOCKS>& parsedBytecode, const std::string& filename) {
    std::ifstream file(filename, std::ios::binary);
    if (!file) {
        std::cerr << "Unable to open file: " << filename << std::endl;
        exit(1);
    }

    parsedBytecode.bytes.clear();
    
    // Read file byte by byte
    char byte;
    while (file.get(byte) && parsedBytecode.bytes.get_size() < MAX_BYTECODESIZE) {
        parsedBytecode.bytes.push_back(static_cast<Bytet>(static_cast<unsigned char>(byte)));
    }

    assert (file.eof());
    // Populate jumpDests field by parsing the bytecode for JUMPDEST instructions
    if (!parseJumpDests<MAX_BYTECODESIZE, MAX_BBLOCKS>(parsedBytecode.jumpDestOffsets, parsedBytecode.bytes)) {
        return false;
    }
    parsedBytecode.populateJumpDests();
    return true;
}



