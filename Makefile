CWD := $(shell pwd)
INSTALLDIR := "/usr/bin/"


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
	@echo ======================================================
	@echo Creating a symbolic link to Light compiler executables
	@echo ======================================================
	sudo ln -fs "$(CWD)/bin/LHCompiler/light" $(INSTALLDIR)/light
	sudo ln -fs "$(CWD)/bin/LHCompiler/lightMessage.fsx" $(INSTALLDIR)/lightMessage.fsx
	sudo ln -fs "$(CWD)/bin/LHCompiler/lightExpr.fsx" $(INSTALLDIR)/lightExpr.fsx
	@echo
	@echo Done. Execute 'light' to run Light compiler.
	@echo
	@echo

uninstall:
	@echo =====================================================
	@echo Removing symbolic links to Light compiler executables
	@echo =====================================================
	sudo rm -f $(INSTALLDIR)/light
	sudo rm -f $(INSTALLDIR)/lightMessage.fsx
	sudo rm -f $(INSTALLDIR)/lightExpr.fsx
	@echo

clean:
	@find . -type d -name 'bin' | xargs rm -rf
	@find . -type d -name 'obj' | xargs rm -rf

test: test_tvm test_lhm test_parser test_ti test_comp test_interop

test_interop:
	@dotnet test ./tests/SDKInteropTests/

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

interpret:
	@dotnet build ./src/LHInterpret/
