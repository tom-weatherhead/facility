# See 'The GNU Make Manual' at
# https://www.gnu.org/software/make/manual/make.html

MAIN := facility
# all:: $(MAIN)
all: $(MAIN)

CC := gcc
RM := rm -f
# CFLAGS := -g -O2 -Wall
# CFLAGS := -fcoverage-mapping -fprofile-instr-generate -Wall
CFLAGS := -Wall
# -lc links in the standard C library.
# -lm links in the math library
LIBS := -lc
# LINK := ld
LINK := gcc

HEADERS := $(wildcard *.h)
# patsubst = Pattern substitution?
OBJECTS := $(patsubst %.c,%.o,$(wildcard *.c))

%.o: %.c $(HEADERS)
	$(CC) $(CFLAGS) -c $<
# 	$(CC) $(CFLAGS) $(CPPFLAGS) $(INCS) -o $@ -c $<

$(MAIN): $(OBJECTS)
	$(LINK) $(LIBS) -o $@ $(OBJECTS)

clean:
	@$(RM) $(MAIN) $(OBJECTS)
