C := gcc
CPP := g++

ROOT_DIR  := ./
INCL_DIR_SUFFIX  := include
SRC_DIR_SUFFIX   := src
BUILD_DIR_SUFFIX := build
BIN_DIR_SUFFIX   := bin

INCL_DIR  := $(ROOT_DIR)/$(INCL_DIR_SUFFIX)
SRC_DIR   := $(ROOT_DIR)/$(SRC_DIR_SUFFIX)
BUILD_DIR := $(ROOT_DIR)/$(BUILD_DIR_SUFFIX)
BIN_DIR   := $(ROOT_DIR)/$(BIN_DIR_SUFFIX)

TEST_DIR   := $(ROOT_DIR)/test
TEST_INCL_DIR := $(TEST_DIR)/$(INCL_DIR_SUFFIX)
TEST_SRC_DIR := $(TEST_DIR)/$(SRC_DIR_SUFFIX)
TEST_BIN_DIR := $(TEST_DIR)/$(BIN_DIR_SUFFIX)

TOOLS_DIR := $(ROOT_DIR)/tools
DOC_DIR   := $(ROOT_DIR)/doc
DATA_DIR  := $(ROOT_DIR)/data

LIBS := -lm
INCL := -I $(INCL_DIR)
LDFLAGS := -Wl,--no-undefined
# FLAGS := $(INCL) -Wall -pedantic -fopenmp -O3 -Wfatal-errors -Wshadow
FLAGS := $(INCL) -g -Wall -pedantic -O1 -Wshadow
CPPFLAGS := $(FLAGS) -std=c++14
CFLAGS   := $(FLAGS) -std=gnu99
TEST_FLAGS := -I $(TEST_INCL_DIR)

###################################################

MKDIR := mkdir -p
MKDIR_DIRS := "$(BUILD_DIR)" "$(BIN_DIR)" "$(DOC_DIR)"

FIND_FLAGS := -not -path '*/\.*' -type f -name

###################################################

## Get list of source files, make a list of executables from them (exclude core file and header files)
# ALL_SOURCES := $(wildcard $(SRC_DIR)/*)
# HEADERS := $(wildcard $(SRC_DIR)/*.h)
# CPP_SOURCES := $(wildcard $(SRC_DIR)/*.cpp)
# C_SOURCES := $(wildcard $(SRC_DIR)/*.c)
# SOURCES := $(CPP_SOURCES) $(C_SOURCES)
# potOBJECT_SOURCES := $(patsubst %.h,%.c,$(HEADERS)) $(patsubst %.h,%.cpp,$(HEADERS))
# cOBJECT_SOURCES := $(filter-out $(SOURCES), $(potOBJECT_SOURCES) )
# OBJECT_SOURCES := $(filter-out $(cOBJECT_SOURCES), $(potOBJECT_SOURCES))
# OBJECT_CPP_SOURCES := $(filter-out $(C_SOURCES), $(OBJECT_SOURCES))
# OBJECT_C_SOURCES := $(filter-out $(CPP_SOURCES), $(OBJECT_SOURCES))
# CPP_OBJECTS := $(patsubst $(SRC_DIR)/%.cpp,$(OBJ_DIR)/%.o,$(OBJECT_CPP_SOURCES))
# C_OBJECTS := $(patsubst $(SRC_DIR)/%.c,$(OBJ_DIR)/%.o,$(OBJECT_C_SOURCES))
# OBJECTS := $(CPP_OBJECTS) $(C_OBJECTS)
# CMDS := $(basename $(patsubst $(SRC_DIR)/%,$(BIN_DIR)/%, $(filter-out $(HEADERS) $(OBJECT_SOURCES), $(ALL_SOURCES)) ) )

HEADERS     := $(shell find $(INCL_DIR) $(FIND_FLAGS) *.hpp)

CPP_SOURCES := $(shell find $(SRC_DIR)  $(FIND_FLAGS) *.cpp)
C_SOURCES   := $(shell find $(SRC_DIR)  $(FIND_FLAGS) *.c)
SOURCES := $(CPP_SOURCES) $(C_SOURCES)

TEST_HEADERS := $(shell find $(TEST_INCL_DIR) $(FIND_FLAGS) *.hpp)
TEST_SOURCES := $(shell find $(TEST_SRC_DIR)  $(FIND_FLAGS) *.cpp)

CPP_OBJECTS := $(patsubst $(SRC_DIR)/%, $(BUILD_DIR)/%, $(CPP_SOURCES:.cpp=.o))
C_OBJECTS := $(patsubst $(SRC_DIR)/%, $(BUILD_DIR)/%, $(C_SOURCES:.c=.o))
OBJECTS := $(CPP_OBJECTS) $(C_OBJECTS)

TEST_CMDS := $(patsubst $(TEST_SRC_DIR)/%, $(TEST_BIN_DIR)/%, $(TEST_SOURCES:.cpp=))
CMDS := $(TEST_CMDS)

###################################################

.PHONY: init

## Compiles and links all algorithms' source files
all: init ${OBJECTS} ${CMDS}

## Debug this makefile
debug:
	@echo HEADERS ${HEADERS}
	@echo SOURCES ${SOURCES}
	@echo OBJECTS ${OBJECTS}
	@echo TEST_SOURCES ${TEST_SOURCES}
	@echo TEST_CMDS ${TEST_CMDS}
	@echo CMDS ${CMDS}
	@echo MKDIR_DIRS ${MKDIR_DIRS}

## Initialize environment if needed (first run)
init: ${MKDIR_DIRS}

${MKDIR_DIRS}:
	@for d in ${MKDIR_DIRS}; do \
		${MKDIR} "$$d"; \
	done

## Particular object files
.DUMMY: ${OBJECTS}

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.c
	${C} -c $< ${CFLAGS} -o $@

$(BUILD_DIR)/%.o: $(SRC_DIR)/%.cpp
	${CPP} -c $< ${CPPFLAGS} -o $@

## Particular executable files
$(BIN_DIR)/%: ${C_OBJECTS} $(SRC_DIR)/%.c
	${C} ${LDFLAGS} ${CFLAGS} ${LIBS} -o $@ $^

$(BIN_DIR)/%: ${OBJECTS} $(SRC_DIR)/%.cpp
	${CPP} ${LDFLAGS} ${CPPFLAGS} ${LIBS} -o $@ $^

$(TEST_BIN_DIR)/%: ${OBJECTS} $(TEST_SRC_DIR)/%.cpp
	${CPP} ${LDFLAGS} ${CPPFLAGS} ${TEST_FLAGS} ${LIBS} -o $@ $^


## Cleans object files and executables
# clean:
# rm -fr $(BUILD_DIR)/* $(BIN_DIR)/*

#####################################

build/sos.o: src/sos.cpp include/sos.hpp include/sos.tpp
build/expr/eval.o: src/expr/eval.cpp include/expr/eval.hpp \
 include/expr.hpp include/sos.hpp include/sos.tpp include/util.hpp \
 include/util.tpp include/expr.tpp include/expr/eval.tpp
build/util.o: src/util.cpp include/util.hpp include/sos.hpp \
 include/sos.tpp include/util.tpp
build/ode/euler.o: src/ode/euler.cpp include/ode/euler.hpp \
 include/ode/solver.hpp include/ode.hpp include/sos.hpp include/sos.tpp \
 include/expr.hpp include/util.hpp include/util.tpp include/expr.tpp \
 include/expr/eval.hpp include/expr/eval.tpp
build/ode/solver.o: src/ode/solver.cpp include/ode/solver.hpp \
 include/ode.hpp include/sos.hpp include/sos.tpp include/expr.hpp \
 include/util.hpp include/util.tpp include/expr.tpp include/expr/eval.hpp \
 include/expr/eval.tpp
build/ode/odeint.o: src/ode/odeint.cpp include/ode/odeint.hpp \
 include/ode/solver.hpp include/ode.hpp include/sos.hpp include/sos.tpp \
 include/expr.hpp include/util.hpp include/util.tpp include/expr.tpp \
 include/expr/eval.hpp include/expr/eval.tpp
build/expr.o: src/expr.cpp include/expr.hpp include/sos.hpp \
 include/sos.tpp include/util.hpp include/util.tpp include/expr.tpp
