all: gcc7 clang

gcc7:
	gcc-7 -I. -O3 nego/baseline.c extern.c main.c types.c -o benchmark-gcc7

clang:
	clang -I. -O3 nego/baseline.c extern.c main.c types.c -o benchmark-clang

clean:
	rm benchmark-*
