include ../config.mk

BIN = llvm-reader

CXXFLAGS += \
	-DLLVM_MAJOR=`${LLC} --version | cut -d. -f1` \
	-DLLVM_MINOR=`${LLC} --version | cut -d. -f2` \
	`${LLC} --cxxflags` -fno-rtti

LDFLAGS += `${LLC} --ldflags --system-libs --libs bitreader core support`

all: ${BIN}

${BIN}: ${BIN}.o
	${CXX} $^ ${LDFLAGS} -o $@

%.o: %.cpp
	${CXX} ${CXXFLAGS} -c $^

clean:
	rm -f *.o ${BIN}

.PHONY: all clean
