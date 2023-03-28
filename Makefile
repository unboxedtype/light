all: run test

clean:
	@find . -type d -name 'bin' | xargs rm -rf
	@find . -type d -name 'obj' | xargs rm -rf

## /m:1 switch is a workaround not to
## let dotnet break the tty
test: test_tvm test_lhm test_lht test_parser

test_parser:
	@dotnet test /m:1 ./tests/ParserTests

test_lhm:
	@dotnet test /m:1 ./tests/LHMachineTests

test_tvm:
	@dotnet test /m:1 ./tests/TVMTests

test_lht:
	@dotnet test /m:1 ./tests/LHTypesTests
