C := gcc
CPP := g++

PROJ_NAME := sos

ROOT_DIR  := ./
INCL_NAME  := include
SRC_NAME   := src
BUILD_NAME := build
BIN_NAME   := bin
TEST_NAME  := test

INCL_DIR  := $(ROOT_DIR)/$(INCL_NAME)/$(PROJ_NAME)
SRC_DIR   := $(ROOT_DIR)/$(SRC_NAME)/$(PROJ_NAME)
BUILD_DIR := $(ROOT_DIR)/$(BUILD_NAME)/$(PROJ_NAME)
BIN_DIR   := $(ROOT_DIR)/$(BIN_NAME)
SRC_MAIN_DIR := $(ROOT_DIR)/$(SRC_NAME)/main
BUILD_MAIN_DIR := $(ROOT_DIR)/$(BUILD_NAME)/main

TEST_INCL_DIR := $(ROOT_DIR)/$(INCL_NAME)/$(TEST_NAME)
TEST_SRC_DIR := $(ROOT_DIR)/$(SRC_NAME)/$(TEST_NAME)
TEST_BUILD_DIR := $(ROOT_DIR)/$(BUILD_NAME)/$(TEST_NAME)
TEST_BIN_DIR := $(ROOT_DIR)/$(TEST_NAME)

TOOLS_DIR := $(ROOT_DIR)/tools
DOC_DIR   := $(ROOT_DIR)/doc
DATA_DIR  := $(ROOT_DIR)/data

LIBS := -lm -pthread
INCL := -I $(INCL_DIR)
LDFLAGS := -Wl,--no-undefined
FLAGS := $(INCL) -g -Wall -pedantic -O1 -Wshadow
# FLAGS += -Wfatal-errors
FLAGS += -DDEBUG
CPPFLAGS := $(FLAGS) -std=c++14
CFLAGS   := $(FLAGS) -std=gnu99
TEST_FLAGS := -I $(TEST_INCL_DIR)

###################################################

MKDIR := mkdir -p
MKDIR_DIRS := "$(BUILD_DIR)" "$(BIN_DIR)" "$(DOC_DIR)"

FIND_FLAGS := -not -path '*/\.*' -type f -name

###################################################

HEADERS     := $(shell find $(INCL_DIR) $(FIND_FLAGS) *.hpp)

CPP_SOURCES := $(shell find $(SRC_DIR)  $(FIND_FLAGS) *.cpp)
C_SOURCES   := $(shell find $(SRC_DIR)  $(FIND_FLAGS) *.c)
SOURCES := $(CPP_SOURCES) $(C_SOURCES)

MAIN_SOURCES := $(shell find $(SRC_MAIN_DIR)  $(FIND_FLAGS) *.cpp)

TEST_HEADERS := $(shell find $(TEST_INCL_DIR) $(FIND_FLAGS) *.hpp)
TEST_SOURCES := $(shell find $(TEST_SRC_DIR)  $(FIND_FLAGS) *.cpp)

CPP_OBJECTS := $(patsubst $(SRC_DIR)/%, $(BUILD_DIR)/%, $(CPP_SOURCES:.cpp=.o))
C_OBJECTS := $(patsubst $(SRC_DIR)/%, $(BUILD_DIR)/%, $(C_SOURCES:.c=.o))
OBJECTS := $(CPP_OBJECTS) $(C_OBJECTS)

MAIN_OBJECTS := $(patsubst $(SRC_MAIN_DIR)/%, $(BUILD_MAIN_DIR)/%, $(MAIN_SOURCES:.cpp=.o))

TEST_OBJECTS := $(patsubst $(TEST_SRC_DIR)/%, $(TEST_BUILD_DIR)/%, $(TEST_SOURCES:.cpp=.o))

TEST_CMDS := $(patsubst $(TEST_SRC_DIR)/%, $(TEST_BIN_DIR)/%, $(TEST_SOURCES:.cpp=))

CMDS := $(patsubst $(SRC_MAIN_DIR)/%, $(BIN_DIR)/%, $(MAIN_SOURCES:.cpp=))

###################################################

.PHONY: init

## Compiles and links all algorithms' source files
# all: init ${OBJECTS} ${MAIN_OBJECTS} ${TEST_OBJECTS} ${CMDS}
default: main

all: main test

main: init ${OBJECTS} ${MAIN_OBJECTS} ${CMDS}

test: init ${OBJECTS} ${TEST_OBJECTS} ${TEST_CMDS}

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

$(BUILD_MAIN_DIR)/%.o: $(SRC_MAIN_DIR)/%.cpp
	${CPP} -c $< ${CPPFLAGS} -o $@

$(TEST_BUILD_DIR)/%.o: $(TEST_SRC_DIR)/%.cpp
	${CPP} -c $< ${CPPFLAGS} ${TEST_FLAGS} -o $@

## Particular executable files
$(BIN_DIR)/%: ${OBJECTS} $(BUILD_MAIN_DIR)/%.o
	${CPP} ${LDFLAGS} ${CPPFLAGS} ${LIBS} -o $@ $^

$(TEST_BIN_DIR)/%: ${OBJECTS} $(TEST_BUILD_DIR)/%.o
	${CPP} ${LDFLAGS} ${CPPFLAGS} ${TEST_FLAGS} ${LIBS} -o $@ $^


## Cleans object files and executables
# clean:
# rm -fr $(BUILD_DIR)/* $(BIN_DIR)/*

#####################################

build/test/expr_test.o: src/test/expr_test.cpp include/test/test.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/expr.hpp include/sos/expr.tpp \
 include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp
build/test/solver_test.o: src/test/solver_test.cpp include/test/test.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/ode/solver.hpp include/sos/ode.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/ode/solver/context.hpp \
 include/sos/ode/solver/traject.hpp include/sos/ode/euler.hpp \
 include/sos/ode/odeint.hpp
build/main/applet/euler.o: src/main/applet/euler.cpp \
 include/sos/ode/solver/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util/run.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/ode/solver.hpp include/sos/ode.hpp include/sos/expr.hpp \
 include/sos/expr.tpp include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/ode/solver/context.hpp include/sos/ode/solver/traject.hpp \
 include/sos/ode/solver/run.tpp include/sos/ode/euler.hpp
build/main/applet/eval.o: src/main/applet/eval.cpp \
 include/sos/expr/eval/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util/run.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/expr/eval.hpp include/sos/expr.hpp include/sos/expr.tpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/expr/eval/run.tpp
build/main/applet/parser.o: src/main/applet/parser.cpp \
 include/sos/parser/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util/run.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/parser.hpp include/sos/smt.hpp include/sos/expr.hpp \
 include/sos/expr.tpp include/sos/ode.hpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp
build/main/applet/smt_solver.o: src/main/applet/smt_solver.cpp \
 include/sos/smt/solver/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util/run.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/smt/solver.hpp include/sos/smt.hpp include/sos/expr.hpp \
 include/sos/expr.tpp
build/main/applet/odeint.o: src/main/applet/odeint.cpp \
 include/sos/ode/solver/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util/run.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/ode/solver.hpp include/sos/ode.hpp include/sos/expr.hpp \
 include/sos/expr.tpp include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/ode/solver/context.hpp include/sos/ode/solver/traject.hpp \
 include/sos/ode/solver/run.tpp include/sos/ode/odeint.hpp
build/main/sos_odeint.o: src/main/sos_odeint.cpp \
 include/sos/solver/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util/run.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/solver.hpp include/sos/parser.hpp include/sos/smt.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/ode.hpp \
 include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/smt/solver.hpp include/sos/ode/solver.hpp \
 include/sos/ode/solver/context.hpp include/sos/ode/solver/traject.hpp \
 include/sos/solver.tpp include/sos/solver/run.tpp \
 include/sos/ode/odeint.hpp
build/sos/sos.o: src/sos/sos.cpp include/sos/sos.hpp include/sos/sos.tpp
build/sos/expr/preprocess.o: src/sos/expr/preprocess.cpp \
 include/sos/expr/preprocess.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/expr.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/expr.tpp include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp
build/sos/expr/eval.o: src/sos/expr/eval.cpp include/sos/expr/eval.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/expr.hpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/expr.tpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp
build/sos/smt.o: src/sos/smt.cpp include/sos/smt.hpp include/sos/sos.hpp \
 include/sos/sos.tpp include/sos/expr.hpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/expr.tpp
build/sos/util.o: src/sos/util.cpp include/sos/util.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.tpp
build/sos/solver.o: src/sos/solver.cpp include/sos/solver.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/parser.hpp include/sos/smt.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/ode.hpp \
 include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/smt/solver.hpp include/sos/ode/solver.hpp \
 include/sos/ode/solver/context.hpp include/sos/ode/solver/traject.hpp \
 include/sos/solver.tpp
build/sos/ode/solver/context.o: src/sos/ode/solver/context.cpp \
 include/sos/ode/solver.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/ode.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/ode/solver/context.hpp \
 include/sos/ode/solver/traject.hpp
build/sos/ode/solver/run.o: src/sos/ode/solver/run.cpp \
 include/sos/ode/solver/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util/run.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/ode/solver.hpp include/sos/ode.hpp include/sos/expr.hpp \
 include/sos/expr.tpp include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/ode/solver/context.hpp include/sos/ode/solver/traject.hpp \
 include/sos/ode/solver/run.tpp
build/sos/ode/solver/traject.o: src/sos/ode/solver/traject.cpp \
 include/sos/ode/solver.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/ode.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/ode/solver/context.hpp \
 include/sos/ode/solver/traject.hpp
build/sos/ode/euler.o: src/sos/ode/euler.cpp include/sos/ode/euler.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/ode/solver.hpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/ode.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/ode/solver/context.hpp \
 include/sos/ode/solver/traject.hpp
build/sos/ode/solver.o: src/sos/ode/solver.cpp include/sos/ode/solver.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/ode.hpp include/sos/expr.hpp \
 include/sos/expr.tpp include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/ode/solver/context.hpp include/sos/ode/solver/traject.hpp
build/sos/ode/odeint.o: src/sos/ode/odeint.cpp include/sos/ode/odeint.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/ode/solver.hpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/ode.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/ode/solver/context.hpp \
 include/sos/ode/solver/traject.hpp
build/sos/parser.o: src/sos/parser.cpp include/sos/parser.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/smt.hpp include/sos/expr.hpp \
 include/sos/expr.tpp include/sos/ode.hpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/expr/preprocess.hpp
build/sos/smt/solver/run.o: src/sos/smt/solver/run.cpp \
 include/sos/smt/solver/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util/run.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/smt/solver.hpp include/sos/smt.hpp include/sos/expr.hpp \
 include/sos/expr.tpp
build/sos/smt/solver.o: src/sos/smt/solver.cpp include/sos/smt/solver.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/smt.hpp include/sos/expr.hpp \
 include/sos/expr.tpp include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp
build/sos/util/run.o: src/sos/util/run.cpp include/sos/util/run.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp
build/sos/parser/run.o: src/sos/parser/run.cpp include/sos/parser/run.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util/run.hpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/parser.hpp \
 include/sos/smt.hpp include/sos/expr.hpp include/sos/expr.tpp \
 include/sos/ode.hpp include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp
build/sos/expr.o: src/sos/expr.cpp include/sos/expr.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/expr.tpp
