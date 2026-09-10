#ifndef BENCH_INTERFACE_RUNNER_HPP
#define BENCH_INTERFACE_RUNNER_HPP

#include <cerrno>
#include <cstddef>
#include <cstdio>
#include <cstdlib>
#include <vector>

#include <sys/mman.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include "input_generation.hpp"

namespace bench_eval {

enum class CallOutcome : unsigned char {
    pending = 0,
    input_check_termination = 1,
    post_computation_termination = 2,
    returned_normally = 3
};

struct CollectedResults {
    std::vector<ResultPair> values;
    std::vector<CallOutcome> outcomes;
};

struct OutcomeCounts {
    std::size_t generated = 0;
    std::size_t input_check = 0;
    std::size_t post_computation = 0;
    std::size_t normal = 0;
    std::size_t first_input_check = SIZE_MAX;
    std::size_t first_post_computation = SIZE_MAX;
};

namespace interface_runner_detail {

struct SharedSlot {
    ResultPair value;
    CallOutcome outcome;
};

inline void *shared_mapping(std::size_t bytes) {
#ifndef MAP_ANONYMOUS
#define MAP_ANONYMOUS MAP_ANON
#endif
    void *memory = mmap(nullptr, bytes, PROT_READ | PROT_WRITE,
                        MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (memory == MAP_FAILED) {
        std::perror("mmap");
        std::abort();
    }
    return memory;
}

inline int wait_for_child(pid_t child) {
    int status = 0;
    pid_t waited;
    do {
        waited = waitpid(child, &status, 0);
    } while (waited < 0 && errno == EINTR);
    if (waited != child) {
        std::perror("waitpid");
        std::abort();
    }
    return status;
}

template <class Call>
void confirm_input_check_termination(Call call, std::size_t index,
                                     const char *interface_name) {
    std::fflush(nullptr);
    pid_t child = fork();
    if (child < 0) {
        std::perror("fork");
        std::abort();
    }
    if (child == 0) {
        (void)call(index);
        _Exit(0);
    }

    int status = wait_for_child(child);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != EXIT_FAILURE) {
        std::fprintf(stderr,
                     "%s did not reject input-check case %zu as expected\n",
                     interface_name, index);
        std::abort();
    }
}

}  // namespace interface_runner_detail

// The linked predicate classifies input-check failures, and the first such
// case is replayed through the public wrapper to confirm its behavior. All
// predicate-passing cases run through that wrapper in child workers. A
// two-stage wrapper may then terminate after computing; an input-only wrapper
// may not.
template <class Precheck, class Call>
CollectedResults collect_interface_results(
        std::size_t count, Precheck precheck, Call call,
        bool allow_post_computation_termination,
        const char *interface_name,
        bool replay_input_check_rejection = true) {
    using namespace interface_runner_detail;

    if (count == 0) return CollectedResults{};

    const std::size_t slot_bytes = count * sizeof(SharedSlot);
    SharedSlot *slots =
        static_cast<SharedSlot *>(shared_mapping(slot_bytes));
    std::size_t *current =
        static_cast<std::size_t *>(shared_mapping(sizeof(std::size_t)));

    for (std::size_t i = 0; i < count; ++i) {
        slots[i].value = ResultPair{0.0, 0.0};
        slots[i].outcome = precheck(i)
            ? CallOutcome::pending
            : CallOutcome::input_check_termination;
    }

    if (replay_input_check_rejection) {
        for (std::size_t i = 0; i < count; ++i) {
            if (slots[i].outcome == CallOutcome::input_check_termination) {
                confirm_input_check_termination(call, i, interface_name);
                break;
            }
        }
    }

    std::size_t start = 0;
    while (start < count) {
        *current = SIZE_MAX;
        std::fflush(nullptr);
        pid_t child = fork();
        if (child < 0) {
            std::perror("fork");
            std::abort();
        }
        if (child == 0) {
            for (std::size_t i = start; i < count; ++i) {
                if (slots[i].outcome
                    == CallOutcome::input_check_termination) {
                    continue;
                }
                *current = i;
                __sync_synchronize();
                ResultPair value = call(i);
                slots[i].value = value;
                __sync_synchronize();
                slots[i].outcome = CallOutcome::returned_normally;
                *current = i + 1;
                __sync_synchronize();
            }
            _Exit(0);
        }

        int status = wait_for_child(child);
        if (WIFEXITED(status) && WEXITSTATUS(status) == 0) break;

        if (WIFEXITED(status) && WEXITSTATUS(status) == EXIT_FAILURE
            && allow_post_computation_termination) {
            std::size_t failed = *current;
            if (failed >= count
                || slots[failed].outcome != CallOutcome::pending) {
                std::fprintf(stderr,
                             "could not identify a %s post-computation "
                             "rejection\n", interface_name);
                std::abort();
            }
            slots[failed].outcome =
                CallOutcome::post_computation_termination;
            start = failed + 1;
            continue;
        }

        std::fprintf(stderr, "%s worker terminated unexpectedly\n",
                     interface_name);
        std::abort();
    }

    CollectedResults results;
    results.values.resize(count);
    results.outcomes.resize(count);
    for (std::size_t i = 0; i < count; ++i) {
        if (slots[i].outcome == CallOutcome::pending) {
            std::fprintf(stderr, "%s case %zu was not classified\n",
                         interface_name, i);
            std::abort();
        }
        results.values[i] = slots[i].value;
        results.outcomes[i] = slots[i].outcome;
    }

    munmap(current, sizeof(std::size_t));
    munmap(slots, slot_bytes);
    return results;
}

inline OutcomeCounts count_outcomes(
        const std::vector<CallOutcome> &outcomes) {
    OutcomeCounts counts;
    counts.generated = outcomes.size();
    for (std::size_t i = 0; i < outcomes.size(); ++i) {
        switch (outcomes[i]) {
        case CallOutcome::input_check_termination:
            ++counts.input_check;
            if (counts.first_input_check == SIZE_MAX)
                counts.first_input_check = i;
            break;
        case CallOutcome::post_computation_termination:
            ++counts.post_computation;
            if (counts.first_post_computation == SIZE_MAX)
                counts.first_post_computation = i;
            break;
        case CallOutcome::returned_normally:
            ++counts.normal;
            break;
        case CallOutcome::pending:
            std::fprintf(stderr, "encountered an unclassified interface case\n");
            std::abort();
        }
    }
    if (counts.input_check + counts.post_computation + counts.normal
        != counts.generated) {
        std::abort();
    }
    return counts;
}

}  // namespace bench_eval

#endif  // BENCH_INTERFACE_RUNNER_HPP
