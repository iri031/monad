#include <category/execution/monad/staking/fuzzer/staking_contract_machine.hpp>
#include <category/execution/monad/staking/util/test_util.hpp>

#include <evmc/evmc.hpp>

using namespace monad;
using namespace monad::staking;
using namespace monad::staking::test;
using namespace evmc::literals;

static StakingContractMachine::Transition
gen_transition(StakingContractMachine &machine)
{
    auto const p = machine.gen() % 100;
    if (p < 30) {
        if (p < 20) {
            return StakingContractMachine::Transition::syscall_reward;
        }
        return StakingContractMachine::Transition::precompile_external_reward;
    }
    return machine.gen_transition();
}

static void
run_simulation(StakingContractMachine::seed_t seed, size_t depth)
{
    MONAD_ASSERT(depth > 0);

    std::cout << "Simulation with seed " << seed << std::endl;

    auto const start_time = std::chrono::steady_clock::now();

    StakingContractMachine machine{seed};
    double success_count = 0;
    for (size_t i = 0; i < depth; ++i) {
        if (machine.transition(gen_transition(machine))) {
            ++success_count;
        }
    }

    auto const end_time = std::chrono::steady_clock::now();

    auto const success_ratio =
        success_count / static_cast<double>(depth);
    auto const time =
        static_cast<double>((end_time - start_time).count()) / 1'000'000;

    std::cout <<
        "    success ratio: " << success_ratio << '\n' <<
        "  simulation time: " << time << " ms" << std::endl;
}

int main()
{
    size_t const sim_count = 1'000;
    size_t const depth = 100;
    size_t seed = 0;

    std::cout <<
        "Running " << sim_count << " simulations\n" <<
        "  depth: " << depth << '\n' <<
        "   seed: " << seed << std::endl;

    for (size_t i = 0; i < sim_count; ++i) {
        run_simulation(seed++, depth);
    }
}
