all: run test

clean:
	@rm -rf ./bin/

## /m:1 switch is a workaround not to
## let dotnet break the tty
test:
	@dotnet test /m:1
