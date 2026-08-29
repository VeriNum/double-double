CC = ccomp

SRCS1 = two_sum.c fast_2sum.c fast_2mult.c fast_2mult_guarded.c
SRCS1 += fp_utils.c dw_plus_fp_kernel.c dw_plus_fp.c dw_plus_dw_kernel.c dw_plus_dw.c
SRCS1 += dw_times_fp_kernel.c dw_times_fp.c dw_times_dw_kernel.c dw_times_dw.c
SRCS1 += dw_div_fp_kernel.c dw_div_fp.c dw_div_dw_kernel.c dw_div_dw.c
OBJS1 = ${SRCS1:.c=.o}

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

.PHONY: clean

clean:
	rm *.o test
