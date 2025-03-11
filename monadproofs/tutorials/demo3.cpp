#include <atomic>
using uint = unsigned int;
#define CAPACITY 256
class SPSCQueue
{
public:
    SPSCQueue()
        : head_(0), tail_(0)
    {
    }

    // Push a value into the buffer (from the producer thread).
    // Returns true on success, false if the buffer is full.
    bool push(int value)
    {
        uint head = head_.load();
	
        uint tail = tail_.load();
        uint nextTail = (tail + 1) % CAPACITY;


        if (nextTail == head)
        {
	  return false;// full
        }

        buffer_[tail] = value;

        tail_.store(nextTail);
        return true;
    }

    bool pop(int &value)
    {
        uint tail = tail_.load();
        uint head = head_.load();

        if (head == tail)
        {
	  return false;// empty
        }

        value = buffer_[head];

        uint nextHead = (head + 1) % CAPACITY;

        head_.store(nextHead);
        return true;
    }

    bool isEmpty() const
    {
        return head_.load() == tail_.load();
    }

    bool isFull() const
    {
        uint tail = tail_.load();
        uint nextTail = (tail + 1) % CAPACITY;
        uint head = head_.load();
        return (nextTail == head);
    }

private:
    // Atomic indices for head (consumer) and tail (producer).
    // Each is only written from one thread but may be read from both.
    std::atomic<uint> head_;
    std::atomic<uint> tail_;

    // Fixed-size storage for the ring buffer.
    int buffer_[CAPACITY];
};

#include "demo2.cpp"

// can be implemented in a lockfree way, but the specs will be the same
class MPMCQueue
{
public:
    MPMCQueue()
        : head_(0)
        , tail_(0)
    {
    }

    // Push a value into the buffer (from the producer thread).
    // Returns true on success, false if the buffer is full.
    bool push(int value)
    {
        lock.lock();
        uint nextTail = (tail_ + 1) % CAPACITY;


        if (nextTail == head_)
        {
            lock.unlock();
	        return false;// full
        }

        buffer_[tail_] = value;

        tail_ = nextTail;
        lock.unlock();
        return true;
    }

    bool pop(int &value)
    {
        lock.lock();

        if (head_ == tail_)
        {
            lock.unlock();
	        return false;// empty
        }

        value = buffer_[head_];

        uint nextHead = (head_ + 1) % CAPACITY;

        head_ = nextHead;
        lock.unlock();
        return true;
    }

    bool isEmpty()
    {
        lock.lock();
        bool result = head_ == tail_;
        lock.unlock();
        return result;
    }


private:
    SpinLock lock;
    uint head_;
    uint tail_;
    int buffer_[CAPACITY];
};


