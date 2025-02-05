#include <thread>
//#include <utility>
//#include <iostream>


unsigned int x = 0;
unsigned int y = 0;

void foo() {
    y=x+1;
}



template<typename LambdaStruct>
class Thread {
    LambdaStruct lambda;
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

