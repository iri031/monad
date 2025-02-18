#include "demo.cpp"
#include <atomic>

uint gcdl (uint * nums, uint length) {
    uint result=0;
    for (uint i=0; i<length; i++) {
        result=gcd(result, nums[i]);
    }
    return result;
}

uint parallel_gcdl(uint * nums, uint length) {
    uint mid=length/2;
    uint resultl;
    auto gcdlLambda = [&nums, &mid, &resultl]() {
        resultl=gcdl(nums, mid);
    };
    Thread t1(gcdlLambda);
    t1.start();
    uint resultr;
    resultr=gcdl(nums+mid, length-mid);
    t1.join();
    return gcd(resultl, resultr);
}



// to be verified. there may be bugs here
struct UnboundedUint {
    uint size;// size of the data array
    uint * data;// data[0] is the least significant 32 bit of the number, data[1] is the next most significant 32 bit, etc.

    UnboundedUint() {
        size=0;
        data = nullptr;
    }

    UnboundedUint(uint value) {
      if (value>0)
	{
	  size=1;
	  data = new uint[1];
	  data[0] = value;
	}
      else
	{
	  size=0;
	  data = nullptr;
	}
      
    }

    // todo: implement
    UnboundedUint(const UnboundedUint& other){
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

  // written by GPT, unverified
    UnboundedUint operator+(const UnboundedUint &other) const
    {
        // Find the larger of the two sizes
        uint maxSize = max(size, other.size);

        // Special case: if both are zero, return zero
        if (maxSize == 0) {
            return UnboundedUint(); // Both operands are effectively 0
        }

        // Allocate space for the sum. will reallocate if overflows.
        uint *sumData = new uint[maxSize];

        unsigned long long carry = 0ULL;
        // Add the words from both numbers up to maxSize
        for (uint i = 0; i < maxSize; i++) {
            // Use 0 if one of the numbers has fewer words
            unsigned long long x = (i < size) ? nth_word(i) : 0ULL;
            unsigned long long y = (i < other.size) ? other.nth_word(i) : 0ULL;

            unsigned long long s = x + y + carry;
            sumData[i] = static_cast<uint>(s & 0xFFFFFFFFULL); // lower 32 bits
            carry = s >> 32;                                   // upper 32 bits become carry
        }

        // Check if there is a carry out after adding all words
        uint newSize = maxSize;
        if (carry != 0) {
            uint *sumDataNew = new uint[newSize + 1];
            sumDataNew[newSize] = static_cast<uint>(carry);
            for (uint i = 0; i < newSize; i++) {
                sumDataNew[i] = sumData[i];
            }
            delete[] sumData;
            sumData = sumDataNew;
            ++newSize;
        }

        // Construct the result
        UnboundedUint result;
        result.size = newSize;
        result.data = sumData; 
        return result;
    }

    //todo: implement
    UnboundedUint& operator=(const UnboundedUint& other) = delete;
};

class SpinLock {
public:
    SpinLock() : locked(false) {}

    void lock() {
        while (locked.exchange(true))
            ;
    }

    void unlock() { locked.store(false); }

private:
  std::atomic<bool> locked;
};

// int main() {
//     Thread t([]() {
//         std::cout << "Hello, World!" << std::endl;
//     });
//     std::cout << "Starting thread" << std::endl;
//     t.start();
//     std::cout << "Joining thread" << std::endl;
//     t.join();
//     std::cout << "Thread joined" << std::endl;
// }

