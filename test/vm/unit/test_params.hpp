#pragma once

namespace monad::vm::compiler::test
{
    struct TestParams
    {
    public:
        bool dump_asm_on_failure = false;

        TestParams(bool dump_asm_on_failure = false)
            : dump_asm_on_failure(dump_asm_on_failure)
        {
        }
    };

    // We could use testing::AddGlobalTestEnvironment(new TestParams(...))
    // instead of using a global variable like google suggests, but that's
    // overkill for our usage, where we simply want to pass a flag to the tests.
    extern struct TestParams params;
}
