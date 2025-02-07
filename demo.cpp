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
    const LambdaStruct & lambda;
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

    Thread(const LambdaStruct& lambda) : lambda(lambda) {}
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

