all: run test

RUNTIME=win7-x64
CONFIGURATION=Debug
UNAME_S := $(shell uname -s)
ifeq ($(UNAME_S),Linux)
	RUNTIME=linux-x64
endif
ifeq ($(UNAME_S),Darwin)
	RUNTIME=osx.10.12-x64
endif

build:
	dotnet build --configuration ${CONFIGURATION} --runtime ${RUNTIME} src/LHCompiler/
	dotnet build --configuration ${CONFIGURATION} --runtime ${RUNTIME} src/LHGenDes/

clean:
	@find . -type d -name 'bin' | xargs rm -rf
	@find . -type d -name 'obj' | xargs rm -rf

## /m:1 switch is a workaround not to
## let dotnet break the tty
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
