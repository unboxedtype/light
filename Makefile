CWD := $(shell pwd)

all: run test

build:
	@echo ====================================
	@echo Building LHCompiler binary...
	@echo ====================================
	@echo
	@dotnet build -c Debug src/LHCompiler/ -o ./bin/LHCompiler/
	@echo
	@echo ====================================
	@echo building LHGenDes binary...
	@echo ====================================
	@echo
	@dotnet build -c Debug src/LHGenDes/ -o ./bin/LHGenDes/

install:
	@echo =================================================
	@echo Creating a symbolic link to Light compiler binary
	@echo =================================================
	ln -fs "$(CWD)/bin/LHCompiler/LHCompiler" ~/.local/bin/lc
	ln -fs "$(CWD)/bin/LHCompiler/LHCompiler" ~/.local/bin/LHCompiler
	ln -fs "$(CWD)/bin/LHCompiler/genActorMessage.fsx" ~/.local/bin/genActorMessage.fsx
	ln -fs "$(CWD)/bin/LHCompiler/serializeExpression.fsx" ~/.local/bin/serializeExpression.fsx
	@echo
	@echo Done. Execute 'lc' or 'LHCompiler' to run Light compiler.
	@echo
	@echo

clean:
	@find . -type d -name 'bin' | xargs rm -rf
	@find . -type d -name 'obj' | xargs rm -rf

test: test_tvm test_lhm test_parser test_ti test_comp

test_parser:
	@dotnet test ./tests/ParserTests

test_lhm:
	@dotnet test ./tests/LHMachineTests

test_tvm:
	@dotnet test ./tests/TVMTests

test_lht:
	@dotnet test ./tests/LHTypesTests

test_ti:
	@dotnet test ./tests/LHTypeInferTests

test_comp:
	@dotnet test ./tests/LHCompilerTests

comp:
	@dotnet build ./src/LHCompiler/