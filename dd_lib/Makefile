CC = ccomp

SRCS1 = Fast2Mult.c Fast2Mult_test.c
OBJS1 = ${SRCS1:.c=.o}

SRCS2 = TwoSum.c TwoSum_test.c
OBJS2 = ${SRCS2:.c=.o}

LIBS = -lm
INCLUDES = -I "./include"
CFLAGS = -g -Wall ${INCLUDES}

all: test_sum test_mult

test_sum: ${OBJS2}
	${CC} ${CFLAGS} -o $@ ${OBJS2} ${LIBS}

test_mult: ${OBJS1}
	${CC} ${CFLAGS} -o $@ ${OBJS1} ${LIBS}

clean:
	rm *.o test_sum test_mult
