CC = ccomp

SRCS1 = two_sum.c fast_2sum.c fast_2mult.c fast_2mult_guarded.c
SRCS1 += fp_utils.c dw_plus_fp_kernel.c dw_plus_fp.c dw_plus_dw_kernel.c dw_plus_dw.c
SRCS1 += dw_times_fp_kernel.c dw_times_fp.c dw_times_dw_kernel.c dw_times_dw.c
SRCS1 += dw_div_fp_kernel.c dw_div_fp.c dw_div_dw_kernel.c dw_div_dw.c
OBJS1 = ${SRCS1:.c=.o}

CHECK_TESTS = dw_times_fp_check_test dw_times_dw_check_test
CHECK_TESTS += dw_div_fp_check_test dw_div_dw_check_test

SRCS2 = dw_eps_test.c
OBJS2 = ${SRCS2:.c=.o}

SRCS3 =  ${SRCS1} 
SRCS3 += ${SRCS2}
OBJS3 =  ${SRCS3:.c=.o}

LIBS = -lm
INCLUDES = -I "./include"
CFLAGS =  ${INCLUDES}

all: build test

test: ${OBJS3}
	${CC} ${CFLAGS} -o $@ ${OBJS3} ${LIBS}

build: ${OBJS1}
	${CC} -c ${INCLUDES} -o $@ ${OBJS1} ${LIBS}

.PHONY: check-tests
check-tests: ${CHECK_TESTS}
	@set -e; for t in ${CHECK_TESTS}; do ./$$t; done

${CHECK_TESTS}: %: %.o ${OBJS1}
	${CC} ${CFLAGS} -o $@ $^ ${LIBS}

.PHONY: clean

clean:
	rm -f *.o test ${CHECK_TESTS}
