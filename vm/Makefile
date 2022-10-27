all: macc

%.o: CFLAGS+= -Wall -pedantic 
macc: LDLIBS +=-lgc -DTRACE=0

clean:
	rm -f *.o macc

.PHONY: clean all
