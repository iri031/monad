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

uint fold_left(uint * nums, uint length, uint (*f)(uint, uint), uint id) {
    uint result=id;
    for (uint i=0; i<length; i++) {
        result=f(result, nums[i]);
    }
    return result;
}

uint parallel_fold_left(uint * nums, uint length, uint (*f)(uint, uint), uint id) {
    uint mid=length/2;
    uint resultl;
    Thread t1([&nums, &mid, &resultl, &f, &id]() {
        resultl=fold_left(nums, mid, f, id);
    });
    t1.start();
    uint resultr;
    resultr=fold_left(nums+mid, length-mid, f, id);
    t1.join();
    return f(resultl, resultr);
}



struct Node {
    Node(Node *next, int data) : next_(next), data_(data) {}

    Node *next_;
    int data_;
};

typedef Node *List;

void
split(List ab, List &a, List &b) {
    bool which = true;
    while (ab) {
        auto temp = ab->next_;
        if (which) {
            ab->next_ = a;
            a = ab;
        } else {
            ab->next_ = b;
            b = ab;
        }
        ab = temp;
        which = !which;
    }
}

List
reverse(List l) {
    List prev = nullptr;
    List next = nullptr;
    while (l != nullptr) {
        next = l->next_;
        l->next_ = prev;
        prev = l;
        l = next;
    }
    return prev;
}

void move_cons(List &from, List &to) {
  auto t = from->next_;
  from->next_ = to;
  to = from;
  from = t;
}

// [rev_append] could be written as a tail-recursive function
// but not all compilation levels will optimize this to constant
// space.
List rev_append(List a, List rest) {
  while (a) {
    move_cons(a, rest);
  }
  return rest;
}

// this does a reverse merge, i.e. it changes the order of the list
List rev_merge(bool dir, List a, List b) {
  List result = nullptr;
  do {
    if (a) {
      if (b) {
        if (a->data_ < b->data_)
          move_cons(dir ? b : a, result);
        else
          move_cons(dir ? a : b, result);
      } else
        return rev_append(a, result);
    } else
      return rev_append(b, result);
  } while (true);
}

List merge(List a, List b) {
  if (not a) return b;
  if (not b) return a;
  if (a->data_ < b->data_) {
    a->next_ = merge(a->next_, b);
    return a;
  } else {
    b->next_ = merge(a, b->next_);
    return b;
  }
}

List merge_sort_rec(List ls) {
  if (ls && ls->next_) {
    List a = nullptr, b = nullptr;
    split(ls, a, b);
    a = merge_sort_rec(a);
    b = merge_sort_rec(b);
    return merge(a, b);
  } else
    return ls;
}

List sort(List l) {
    return merge_sort_rec(l);
}

int z = 0;
void bar() {
    z = 1;
}


std::atomic<int> u;
void setU(int value) {
    u.exchange(value);
}
int getU() {
    return u.load();
}
int setThenGetU(int value) {
    u.exchange(value);
    return u.load();
}
/*
 
             Parent Thread                        
                  │                                     
                  │  Create Invariant:                  
                  │                                     
                  │    ┌───────────────────────────┐    
                  │    │  ∃ i: Z, u |-> atomicR i │ 
                  │    └───────────────────────────┘    
                  │                                    
                  ├───────────────────────────────────►
                  │                (Fork Child)       Child Thread
                  │                                    │
                  │                                    │
                setU(5)                                │
                  │                                    │
                  │                                setU(6) 
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


#include <iostream>
#include <cassert>

void test_parallel_gcd_lcm() {
    uint a = 48;
    uint b = 18;
    uint gcd_result = 0;
    uint lcm_result = 0;

    parallel_gcd_lcm(a, b, gcd_result, lcm_result);

    assert(gcd_result == 6);
    assert(lcm_result == 144);
    std::cout << "Test parallel_gcd_lcm passed!" << std::endl;
}

void test_parallel_gcd_lcm2() {
    uint a = 48;
    uint b = 18;
    uint gcd_result = 0;

    uint lcm_result = parallel_gcd_lcm2(a, b, gcd_result);

    assert(gcd_result == 6);
    assert(lcm_result == 144);
    std::cout << "Test parallel_gcd_lcm2 passed!" << std::endl;
}


void test_parallel_fold_left() {
    uint vec[] = {48, 18, 30};
    uint init = 0;

    uint result = parallel_fold_left(vec, 3, gcd, init);

    assert(result == 6);
    std::cout << "Test parallel_fold_left passed!" << std::endl;
}

int main() {
    test_parallel_gcd_lcm();
    test_parallel_gcd_lcm2();
    test_parallel_fold_left();

    return 0;
}


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

