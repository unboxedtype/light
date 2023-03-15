all: run test

clean:
	@find . -type d -name 'bin' | xargs rm -rf
	@find . -type d -name 'obj' | xargs rm -rf

## /m:1 switch is a workaround not to
## let dotnet break the tty
test: test_gm test_tvm test_comp

test_gm:
	@dotnet test /m:1 ./tests/GMachineTests

test_lhm:
	@dotnet test /m:1 ./tests/LHMachineTests

test_tvm:
	@dotnet test /m:1 ./tests/TVMTests

test_comp:
	@dotnet test /m:1 ./tests/CompilerTests
