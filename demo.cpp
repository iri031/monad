#include <thread>
//#include <utility>
//#include <iostream>

using uint = unsigned int;

uint x = 0;
uint y = 0;

void foo() {
    y=x+1;
}

int a = 0;
int b = 0;
void sfoo() {
    b=a+1;
}


uint gcd(uint a, uint b) {
    while (b != 0) {
        uint temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

void gcd(const uint &a, const uint &b, uint &result) {
    result=gcd(a,b);
}


template<typename LambdaStruct>
class Thread {
    const LambdaStruct lambda;
    std::thread worker;

public:
    void fork_start() {
        worker = std::thread([this]() {
            lambda();
        });
    }

    void join() {
        if(worker.joinable())
            worker.join();
    }

    ~Thread() {
        if(worker.joinable())
            worker.join();
    }

    Thread(const Thread&) = delete;
    Thread& operator=(const Thread&) = delete;

    Thread(Thread&& other)
        : lambda(std::move(other.lambda)), worker(std::move(other.worker)) {}

    Thread& operator=(Thread&& other) {
        if (this != &other)
        {
            lambda = std::move(other.lambda);
            worker = std::move(other.worker);
        }
        return *this;
    }

    Thread(const LambdaStruct &lambda) : lambda(lambda) {}
};

void parallel_gcd_lcm(const uint &a, const uint &b, uint &gcd_result, uint &lcm_result) {
    auto gcdLambda = [&gcd_result, &a, &b]() {
           gcd(a, b, gcd_result);
       };
    Thread t1(gcdLambda);
    t1.fork_start();
    uint product=a*b;// pretend this is an expensive operation, e.g. these are 1000 bit numbers
    t1.join();
    lcm_result=product/gcd_result;
}

void parallel_gcd_lcm_wrong(const uint &a, const uint &b, uint &gcd_result, uint &lcm_result) {
    Thread t1([&gcd_result, &a, &b]() {
        gcd(a,b, gcd_result); // pretend this is an expensive operation, e.g. these are 1000 bit numbers
    });
    t1.fork_start();
    uint product=a*b;// pretend this is an expensive operation, e.g. these are 1000 bit numbers
    lcm_result=product/gcd_result;
    t1.join();
}

void gcdl (uint * nums, uint length, uint &result) {
    result=1;
    for (uint i=0; i<length; i++) {
        result=gcd(result, nums[i]);
    }
    
}

void parallel_gcdl(uint * nums, uint length, uint &result) {
    uint mid=length/2;
    uint resultl;
    auto gcdlLambda = [&nums, &mid, &resultl]() {
        gcdl(nums, mid, resultl);
    };
    Thread t1(gcdlLambda);
    t1.fork_start();
    uint resultr;
    gcdl(nums+mid, length-mid, resultr);
    t1.join();
    result=gcd(resultl, resultr);
}

struct UnoundedUInt {
    uint size;// size of the data array
    uint * data;// data[0] is the least significant 32 bit of the number, data[1] is the next most significant 32 bit, etc.

    UnoundedUInt() {
        size=0;
        data = nullptr;
    }

    UnoundedUInt(uint value) {
        size=1;
        data = new uint[1];
        data[0] = value;
    }

    // todo: implement
    UnoundedUInt(const UnoundedUInt& other){
        size = other.size;
        data = new uint[size];
        for (uint i = 0; i < size; i++) {
            data[i] = other.data[i];
        }
    }

    uint nth_word(uint n) const {
        if (size==0)
            return 0;
        else
            return data[n];
    }

    uint get_size() const {
        return size;
    }

    static uint max(uint a, uint b) {
        return a > b ? a : b;
    }

    UnoundedUInt operator+(const UnoundedUInt &other) const
    {
        // Find the larger of the two sizes
        uint maxSize = max(size, other.size);

        // Special case: if both are zero, return zero
        if (maxSize == 0) {
            return UnoundedUInt(); // Both operands are effectively 0
        }

        // Allocate space for the sum (including a possible extra carry)
        uint *sumData = new uint[maxSize + 1];

        unsigned long long carry = 0ULL;
        // Add the words from both numbers up to maxSize
        for (uint i = 0; i < maxSize; i++) {
            // Use 0 if one of the numbers has fewer words
            unsigned long long x = (i < size) ? data[i] : 0ULL;
            unsigned long long y = (i < other.size) ? other.data[i] : 0ULL;

            unsigned long long s = x + y + carry;
            sumData[i] = static_cast<uint>(s & 0xFFFFFFFFULL); // lower 32 bits
            carry = s >> 32;                                   // upper 32 bits become carry
        }

        // Check if there is a carry out after adding all words
        uint newSize = maxSize;
        if (carry != 0) {
            sumData[newSize] = static_cast<uint>(carry);
            ++newSize;
        }

        // Construct the result
        UnoundedUInt result;
        result.size = newSize;
        result.data = sumData; 
        return result;
    }

    //todo: implement
    UnoundedUInt& operator=(const UnoundedUInt& other) = delete;
};
// int main() {
//     Thread t([]() {
//         std::cout << "Hello, World!" << std::endl;
//     });
//     std::cout << "Starting thread" << std::endl;
//     t.fork_start();
//     std::cout << "Joining thread" << std::endl;
//     t.join();
//     std::cout << "Thread joined" << std::endl;
// }

