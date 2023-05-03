CC = ccomp

SRCS1 = two_sum.c fast_2sum.c fast_2mult.c dw_plus_fp.c
OBJS1 = ${SRCS1:.c=.o}

SRCS2 = dwp_test.c
OBJS2 = ${SRCS2:.c=.o}

SRCS3 =  ${SRCS1} 
SRCS3 += ${SRCS2}
OBJS3 =  ${SRCS3:.c=.o}

LIBS = -lm
INCLUDES = -I "./include"
CFLAGS = -g -Wall ${INCLUDES}

all: build test

test: ${OBJS3}
	${CC} ${CFLAGS} -o $@ ${OBJS3} ${LIBS}

build: ${OBJS1}
	${CC} -c ${INCLUDES} -o $@ ${OBJS1} ${LIBS}

.PHONY: clean

clean:
	rm *.o test
