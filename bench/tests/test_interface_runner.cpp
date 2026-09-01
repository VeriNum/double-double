// Harness test: uses synthetic child processes to check outcome
// classification, normal-result transfer, and unexpected worker failures. It
// does not test the arithmetic library operations.

#include "interface_runner.hpp"

#include <csignal>
#include <cstdio>
#include <cstdlib>

#include <sys/wait.h>
#include <unistd.h>

namespace {

[[noreturn]] void fail(const char *message) {
    std::fprintf(stderr, "interface runner test failed: %s\n", message);
    std::exit(EXIT_FAILURE);
}

} // namespace

int main() {
    bench_eval::CollectedResults results =
        bench_eval::collect_interface_results(
            5,
            [](std::size_t index) { return index != 1; },
            [](std::size_t index) {
                if (index == 1 || index == 3) std::exit(EXIT_FAILURE);
                return bench_eval::ResultPair{
                    static_cast<double>(index), -static_cast<double>(index)};
            },
            true, "synthetic two-stage interface");

    const bench_eval::CallOutcome expected[] = {
        bench_eval::CallOutcome::returned_normally,
        bench_eval::CallOutcome::input_check_termination,
        bench_eval::CallOutcome::returned_normally,
        bench_eval::CallOutcome::post_computation_termination,
        bench_eval::CallOutcome::returned_normally
    };
    for (std::size_t i = 0; i < 5; ++i) {
        if (results.outcomes[i] != expected[i])
            fail("case was assigned the wrong outcome");
    }
    bench_eval::OutcomeCounts counts =
        bench_eval::count_outcomes(results.outcomes);
    if (counts.generated != 5 || counts.input_check != 1
        || counts.post_computation != 1 || counts.normal != 3
        || counts.first_input_check != 1
        || counts.first_post_computation != 3) {
        fail("outcome counts are incorrect");
    }
    if (results.values[4].hi != 4.0 || results.values[4].lo != -4.0)
        fail("normal result was not copied out of the child");

    pid_t input_only_test = fork();
    if (input_only_test < 0) fail("could not fork input-only test");
    if (input_only_test == 0) {
        std::freopen("/dev/null", "w", stderr);
        (void)bench_eval::collect_interface_results(
            1, [](std::size_t) { return true; },
            [](std::size_t) -> bench_eval::ResultPair {
                std::exit(EXIT_FAILURE);
            },
            false, "synthetic input-only interface");
        _Exit(0);
    }
    int input_only_status = 0;
    if (waitpid(input_only_test, &input_only_status, 0) != input_only_test
        || !WIFSIGNALED(input_only_status)
        || WTERMSIG(input_only_status) != SIGABRT) {
        fail("input-only worker failure was not treated as unexpected");
    }

    std::puts("interface runner classifications passed");
    return EXIT_SUCCESS;
}
