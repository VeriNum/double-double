CC = ccomp

SRCS1 = Fast2Mult.c Fast2Mult_test.c
OBJS1 = ${SRCS1:.c=.o}

SRCS2 = TwoSum.c TwoSum_test.c
OBJS2 = ${SRCS2:.c=.o}

SRCS3 = Fast2Sum.c 
OBJS3 = ${SRCS3:.c=.o}

SRCS4 = DWPFP.c dwp_test.c
OBJS4 = ${SRCS4:.c=.o}

LIBS = -lm
INCLUDES = -I "./include"
CFLAGS = -g -Wall ${INCLUDES}

all: test_sum test_mult build test_dw 

test_sum: ${OBJS2}
	${CC} ${CFLAGS} -o $@ ${OBJS2} ${LIBS}

test_mult: ${OBJS1}
	${CC} ${CFLAGS} -o $@ ${OBJS1} ${LIBS}

test_dwp: ${OBJS4}
	${CC} ${CFLAGS} -o $@ ${OBJS4} ${LIBS}

build: ${OBJS3}
	${CC} ${CFLAGS} -o $@ ${OBJS3} ${LIBS}


clean:
	rm *.o test_sum test_mult
