all: run test

build:
	@echo ====================================
	@echo Building LHCompiler binary...
	@echo ====================================
	@echo
	@dotnet build -c Debug src/LHCompiler/
	@echo
	@echo ====================================
	@echo building LHGenDes binary...
	@echo ====================================
	@echo
	@dotnet build -c Debug src/LHGenDes/

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