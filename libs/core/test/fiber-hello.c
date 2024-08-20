#include <assert.h>
#include <err.h>
#include <errno.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sysexits.h>

#include <monad/fiber/fiber.h>
#include <monad/fiber/fiber_util.h>

// This is the function that will run on the fiber
uintptr_t say_hello_fiber_function(uintptr_t arg)
{
    // The fiber greets you by your name, which is passed in as the fiber
    // function's argument
    char const *const name = (char const *)arg;

    // Say hello, then suspend the fiber
    printf("Hello, %s!\n", name);
    monad_fiber_yield(0);

    // When we reach here, we've been run again; we resume from the
    // suspension point of the yield immediately above. We'll say hello
    // again, then suspend again
    printf("Welcome back, %s!\n", name);
    monad_fiber_yield(0);

    // Resumed for the final time; say goodbye, then return. Returning from
    // the fiber function suspends the fiber until it is given a new function
    // to run
    printf("Farewell, %s!\n", name);
    return 0;
}

int main(int argc, char **argv)
{
    int rc;
    monad_fiber_t hello_fiber;
    monad_fiber_stack_t fiber_stack;
    char const *name;
    size_t fiber_stack_size = 1UL << 17; // A 128 KiB stack

    // This application says hello to you using a fiber; it expects your name
    // as the first (and only) positional argument
    if (argc != 2) {
        errx(EX_USAGE, "usage: %s <your-name>", argv[0]);
    }
    name = argv[1];

    // We start by allocating a stack for the fiber. You can do this manually,
    // but in this example we'll use a helper function (from fiber_util.h)
    // to call mmap(2) and set up some stack overflow guard pages
    rc = monad_fiber_alloc_stack(&fiber_stack_size, &fiber_stack);
    if (rc != 0) {
        errno = rc;
        err(1, "monad_fiber_alloc_stack failed");
    }

    // Initialize the fiber, passing in our stack
    monad_fiber_init(&hello_fiber, fiber_stack);

    // Tell the fiber what function to run; the second argument is
    // the scheduling priority, which doesn't matter in this example;
    // the last parameter is passed into the fiber function, as the
    // argument. We pass a pointer to our name
    monad_fiber_set_function(
        &hello_fiber,
        MONAD_FIBER_PRIO_HIGHEST,
        say_hello_fiber_function,
        (uintptr_t)name);

    // Run the fiber until the first suspension point; this will print
    // "Hello, <name>!", suspend the fiber function, and then our call to
    // monad_fiber_run will return. If nothing goes wrong, the return code
    // will be 0. The second parameter (which is nullptr here) allows us to
    // obtain information about why the fiber suspended; in this example we
    // don't care, so we pass nullptr
    rc = monad_fiber_run(&hello_fiber, nullptr);
    assert(rc == 0);

    // Run the fiber again, until it yields again; this will print
    // "Welcome back, <name>!" and then yield back to us once more
    rc = monad_fiber_run(&hello_fiber, nullptr);
    assert(rc == 0);

    // Run the fiber a final time. This will print "Farewell, <name>!" and then
    // the fiber function will return. The return won't look much different to
    // us than the yields above: the fiber will suspend and monad_fiber_run will
    // return 0 to us, as before. The difference is, we can't run the fiber
    // again. If, instead of passing nullptr as the second argument, we instead
    // passed a pointer to a `monad_fiber_suspend_info_t`, we could get more
    // information about the suspension. Namely, that it was a return and not a
    // yield, and we could also read the return code. However, we don't care in
    // this example.
    rc = monad_fiber_run(&hello_fiber, nullptr);
    assert(rc == 0);

    // Try to run the fiber one more time; we can't do it since the fiber
    // function returned, so this will fail and return the errno-domain error
    // code ENXIO
    rc = monad_fiber_run(&hello_fiber, nullptr);
    assert(rc == ENXIO);

    // At this point, we could reuse the fiber's resources to run the function
    // a second time. To prepare for a second run, we would reset the function:
    monad_fiber_set_function(
        &hello_fiber,
        MONAD_FIBER_PRIO_HIGHEST,
        say_hello_fiber_function,
        (uintptr_t)name);

    // However, that's enough for today. Nothing special needs to be done to
    // destroy the fiber itself, as there is no dynamic memory allocation.
    // The fiber stack though, was allocated via mmap(2) and needs to be
    // freed.
    monad_fiber_free_stack(fiber_stack);

    return 0;
}
