# Makefile makefile makefile makefile makefile makefile makefile makefile

CC= clang
ANALYZE= clang --analyze
WARNS= -W -Werror -Wall
CFLAGS= -g $(WARNS)
LFLAGS= -faddress-sanitizer -fno-omit-frame-pointer
LIBS= -lgc
SRC= src
BUILD= build

# Test sources
FCL_T= compiler-test
FCL_T_S= test.c

# Compiler sources
FCL_S= lexer.c tokenizer.c parsecomb.c debruijn.c desugarer.c bindgroup.c \
 depanalyzer2.c typechecker.c prettyprint.c transform.c

old_FCL_S= lexer.c tokenizer.c parsecomb.c debruijn.c depanalyzer.c typechecker.c \
 prettyprint.c transform.c

# Helper function
getobjs= $(addprefix $(BUILD)/,$(patsubst %.c,%.o,$(1)))

# Everything created by running 'make'
ARTIFACTS= $(wildcard $(call getobjs, $(FCL_T_S) $(FCL_S)) $(FCL_T))

all: $(FCL_T)

$(FCL_T): $(call getobjs, $(FCL_T_S) $(FCL_S))
	$(CC) $(CFLAGS) $(LFLAGS) -o $@ $^ $(LIBS)

$(BUILD):
	mkdir $(BUILD)

$(BUILD)/%.o: $(SRC)/%.c | $(BUILD)
	$(ANALYZE) $(WARNS) $<
	$(CC) $(CFLAGS) -I $(SRC) -c -o $@ $<

clean:
	$(if $(ARTIFACTS), rm $(ARTIFACTS))
	$(if $(wildcard $(BUILD)), rmdir $(BUILD))

.PHONY: all clean none
