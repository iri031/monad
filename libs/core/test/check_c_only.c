#include <err.h>
#include <sysexits.h>

#include <monad/core/assert.h>
#include <monad/core/c_result.h>
#include <monad/util/parse_util.h>

int main(int argc, char **argv)
{
    MONAD_ASSERT(argc > 0);
    monad_c_result mcr;
    if (argc != 2) {
        errx(EX_USAGE, "usage: %s <number>", argv[0]);
    }
    mcr = monad_strtonum("-1", 1, 42);
    MONAD_ASSERT(outcome_status_code_equal_strtonum_error(
        mcr.error, MONAD_STN_TOO_SMALL));
    mcr = monad_strtonum(argv[1], 1, 42);
    if (MONAD_FAILED(mcr)) {
        monad_errc(
            EX_DATAERR, mcr.error, "monad_strtonum cannot parse `%s`", argv[1]);
    }
    return mcr.value;
}
