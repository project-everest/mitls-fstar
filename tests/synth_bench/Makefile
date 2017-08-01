FILES = nego/baseline.c nego/const_ptr_ctxt.c nego/nego_state_by_ptr.c extern.c types.c main.c
FLAGS = -I. -O0 -fno-inline

all: gcc7 clang

gcc7:
	gcc-7 $(FLAGS) $(FILES) -o benchmark-gcc7

clang:
	clang $(GCC_FLAGS) $(FLAGS) $(FILES) -o benchmark-clang

test: all
	./benchmark-gcc7
	./benchmark-clang

clean:
	rm benchmark-*
