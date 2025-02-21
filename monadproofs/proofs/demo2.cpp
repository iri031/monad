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

int z = 0;
void bar() {
    z = 1;
}

class AWrapper {
public:
    AWrapper(int value) : v(value) {}
    std::atomic<int> v;
    void setValue(int value) {
        v.store(value);
    }
    
    int getValue() {
        return v.load();
    }

    int setThenGetValue(int value) {
        setValue(value);
        // some other thread can execute setValue(value') here
        return getValue();
    }

};

/*
 
             Parent Thread                        
                  │                                     
                  │  Create Invariant:                  
                  │                                     
                  │    ┌───────────────────────────┐    
                  │    │  ∃ i: Z, a.v|-> atomicR i │    
                  │    └───────────────────────────┘    
                  │                                    
                  ├───────────────────────────────────►
                  │                (Fork Child)       Child Thread
                  │                                    │
                  │                                    │
           a.setValue(5)                               │
                  │                                    │
                  │                           a.setValue(6) 
                  │                                    │
                  │                                    │

 */
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

class CircularBuffer
{
public:
    static constexpr uint CAPACITY = 256;

    CircularBuffer()
        : head_(0), tail_(0)
    {
    }

    bool push(uint32_t value)
    {
        uint tail = tail_;
        uint nextTail = (tail + 1) % CAPACITY;

        uint head = head_;

        if (nextTail == head)
        {
            return false;
        }

        buffer_[tail] = value;

        tail_ = nextTail;
        return true;
    }
    bool pop(uint32_t &value)
    {
        uint head = head_;

        uint tail = tail_;

        if (head == tail)
        {
            return false;
        }

        value = buffer_[head];

        uint nextHead = (head + 1) % CAPACITY;

        head_ = nextHead;
        return true;
    }

    bool isEmpty() const
    {
        return head_ == tail_;
    }

    bool isFull() const
    {
        uint tail = tail_;
        uint nextTail = (tail + 1) % CAPACITY;
        uint head = head_;
        return (nextTail == head);
    }

private:
    uint head_;
    uint tail_;

    int buffer_[CAPACITY];
};

class SPSCQueue
{
public:
    static constexpr uint CAPACITY = 256;

    SPSCQueue()
        : head_(0), tail_(0)
    {
    }

    // Push a value into the buffer (from the producer thread).
    // Returns true on success, false if the buffer is full.
    bool push(uint32_t value)
    {
        // Load the current tail (relaxed, since only one producer writes to tail).
        uint tail = tail_.load(std::memory_order_seq_cst);
        // Calculate the next tail index.
        uint nextTail = (tail + 1) % CAPACITY;

        // We need to ensure we see the latest head; use acquire or stronger
        // so that we don't overwrite unconsumed data.
        uint head = head_.load(std::memory_order_acquire);

        // If next tail equals head, the buffer is full (cannot push).
        if (nextTail == head)
        {
            return false;
        }

        // Store the value into the buffer.
        buffer_[tail] = value;

        // Publish the new tail (release, so consumer sees the stored value).
        tail_.store(nextTail, std::memory_order_seq_cst);
        return true;
    }

    // Pop a value from the buffer (from the consumer thread).
    // Returns true on success, false if the buffer is empty.
    bool pop(uint32_t &value)
    {
        // Load the current head (relaxed, since only one consumer writes to head).
        uint head = head_.load(std::memory_order_seq_cst);

        // We need the latest tail so we do an acquire or stronger here
        // to ensure the read of buffer_ is valid.
        uint tail = tail_.load(std::memory_order_seq_cst);

        // If head equals tail, the buffer is empty (cannot pop).
        if (head == tail)
        {
            return false;
        }

        // Read the value from the buffer.
        value = buffer_[head];

        // Calculate the next head index.
        uint nextHead = (head + 1) % CAPACITY;

        // Publish the new head (release).
        head_.store(nextHead, std::memory_order_release);
        return true;
    }

    // Check if the buffer is empty.
    bool isEmpty() const
    {
        return head_.load(std::memory_order_acquire) ==
               tail_.load(std::memory_order_acquire);
    }

    // Check if the buffer is full.
    bool isFull() const
    {
        // nextTail == head means full
        uint tail = tail_.load(std::memory_order_acquire);
        uint nextTail = (tail + 1) % CAPACITY;
        uint head = head_.load(std::memory_order_acquire);
        return (nextTail == head);
    }

private:
    // Atomic indices for head (consumer) and tail (producer).
    // Each is only written from one thread but may be read from both.
    std::atomic<uint> head_;
    std::atomic<uint> tail_;

    // Fixed-size storage for the ring buffer.
    uint buffer_[CAPACITY];
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

