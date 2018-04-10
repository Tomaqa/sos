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

TEST_INCL_DIR := $(ROOT_DIR)/$(INCL_NAME)/$(TEST_NAME)
TEST_SRC_DIR := $(ROOT_DIR)/$(SRC_NAME)/$(TEST_NAME)
TEST_BIN_DIR := $(ROOT_DIR)/$(TEST_NAME)

TOOLS_DIR := $(ROOT_DIR)/tools
DOC_DIR   := $(ROOT_DIR)/doc
DATA_DIR  := $(ROOT_DIR)/data

LIBS := -lm
INCL := -I $(INCL_DIR)
LDFLAGS := -Wl,--no-undefined
# FLAGS := $(INCL) -Wall -pedantic -fopenmp -O3 -Wfatal-errors -Wshadow
# FLAGS := $(INCL) -g -Wall -pedantic -O1 -Wshadow
FLAGS := $(INCL) -g -Wall -pedantic -O1 -Wshadow -Wfatal-errors
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

MAIN_SOURCES := $(shell find $(SRC_MAIN_DIR)  $(FIND_FLAGS) *.cpp)

TEST_HEADERS := $(shell find $(TEST_INCL_DIR) $(FIND_FLAGS) *.hpp)
TEST_SOURCES := $(shell find $(TEST_SRC_DIR)  $(FIND_FLAGS) *.cpp)

CPP_OBJECTS := $(patsubst $(SRC_DIR)/%, $(BUILD_DIR)/%, $(CPP_SOURCES:.cpp=.o))
C_OBJECTS := $(patsubst $(SRC_DIR)/%, $(BUILD_DIR)/%, $(C_SOURCES:.c=.o))
OBJECTS := $(CPP_OBJECTS) $(C_OBJECTS)

TEST_CMDS := $(patsubst $(TEST_SRC_DIR)/%, $(TEST_BIN_DIR)/%, $(TEST_SOURCES:.cpp=))
CMDS := $(patsubst $(SRC_MAIN_DIR)/%, $(BIN_DIR)/%, $(MAIN_SOURCES:.cpp=))
CMDS += $(TEST_CMDS)

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
$(BIN_DIR)/%: ${C_OBJECTS} $(SRC_MAIN_DIR)/%.c
	${C} ${LDFLAGS} ${CFLAGS} ${LIBS} -o $@ $^

$(BIN_DIR)/%: ${OBJECTS} $(SRC_MAIN_DIR)/%.cpp
	${CPP} ${LDFLAGS} ${CPPFLAGS} ${LIBS} -o $@ $^

$(TEST_BIN_DIR)/%: ${OBJECTS} $(TEST_SRC_DIR)/%.cpp
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
 include/sos/ode/euler.hpp include/sos/ode/odeint.hpp
build/main/euler_app.o: src/main/euler_app.cpp \
 include/sos/ode/solver/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/ode/solver.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/ode.hpp include/sos/expr.hpp include/sos/expr.tpp \
 include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/ode/solver/run.tpp include/sos/ode/euler.hpp
build/main/eval_app.o: src/main/eval_app.cpp \
 include/sos/expr/eval/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/expr/eval.hpp include/sos/expr.hpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/expr.tpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/expr/eval/run.tpp
build/main/parser_app.o: src/main/parser_app.cpp \
 include/sos/parser/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/parser.hpp include/sos/expr.hpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/expr.tpp
build/sos/sos.o: src/sos/sos.cpp include/sos/sos.hpp include/sos/sos.tpp
build/sos/expr/eval.o: src/sos/expr/eval.cpp include/sos/expr/eval.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/expr.hpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/expr.tpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp
build/sos/util.o: src/sos/util.cpp include/sos/util.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.tpp
build/sos/ode/solver/context.o: src/sos/ode/solver/context.cpp \
 include/sos/ode/solver.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/ode.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/ode/solver/context.hpp
build/sos/ode/solver/run.o: src/sos/ode/solver/run.cpp \
 include/sos/ode/solver/run.hpp include/sos/sos.hpp include/sos/sos.tpp \
 include/sos/ode/solver.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/ode.hpp include/sos/expr.hpp include/sos/expr.tpp \
 include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/ode/solver/run.tpp
build/sos/ode/euler.o: src/sos/ode/euler.cpp include/sos/ode/euler.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/ode/solver.hpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/ode.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/ode/solver/context.hpp
build/sos/ode/solver.o: src/sos/ode/solver.cpp include/sos/ode/solver.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/ode.hpp include/sos/expr.hpp \
 include/sos/expr.tpp include/sos/expr/eval.hpp include/sos/expr/eval.tpp \
 include/sos/expr/eval/oper.hpp include/sos/expr/eval/oper.tpp \
 include/sos/ode/solver/context.hpp
build/sos/ode/odeint.o: src/sos/ode/odeint.cpp include/sos/ode/odeint.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/ode/solver.hpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/ode.hpp \
 include/sos/expr.hpp include/sos/expr.tpp include/sos/expr/eval.hpp \
 include/sos/expr/eval.tpp include/sos/expr/eval/oper.hpp \
 include/sos/expr/eval/oper.tpp include/sos/ode/solver/context.hpp
build/sos/parser.o: src/sos/parser.cpp include/sos/parser.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/expr.hpp \
 include/sos/util.hpp include/sos/util.tpp include/sos/expr.tpp
build/sos/parser/run.o: src/sos/parser/run.cpp include/sos/parser/run.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/parser.hpp \
 include/sos/expr.hpp include/sos/util.hpp include/sos/util.tpp \
 include/sos/expr.tpp
build/sos/expr.o: src/sos/expr.cpp include/sos/expr.hpp \
 include/sos/sos.hpp include/sos/sos.tpp include/sos/util.hpp \
 include/sos/util.tpp include/sos/expr.tpp
