CC = ccomp
AR = ar

LIB_SRCS = two_sum_kernel.c two_sum.c fast_2sum_kernel.c fast_2sum.c fast_2mult_kernel.c fast_2mult.c
LIB_SRCS += fp_utils.c dw_plus_fp_kernel.c dw_plus_fp.c dw_plus_dw_kernel.c dw_plus_dw.c
LIB_SRCS += dw_times_fp_kernel.c dw_times_fp.c dw_times_dw_kernel.c dw_times_dw.c
LIB_SRCS += dw_div_fp_kernel.c dw_div_fp.c dw_div_dw_kernel.c dw_div_dw.c
LIB_OBJS = ${LIB_SRCS:.c=.o}
LIB = libfencedd.a
EXAMPLE = example

LIBS = -lm
INCLUDES = -I "./include"
CFLAGS =  ${INCLUDES}

all: ${LIB} ${EXAMPLE}

${LIB}: ${LIB_OBJS}
	${AR} rcs $@ $^

${EXAMPLE}: example.o ${LIB}
	${CC} ${CFLAGS} -o $@ example.o ${LIB} ${LIBS}

.PHONY: clean

clean:
	rm -f *.o ${LIB} ${EXAMPLE}
