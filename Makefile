
all: src/Makefile
	make -C src bedwyr spec

src/Makefile: src/Makefile.in configure
	./configure
configure: configure.ac
	autoconf

clean:
	make -C src clean

