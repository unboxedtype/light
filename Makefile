all: run test

clean:
	@rm -rf ./bin/

run:
	@NO_COLOR=true dotnet run > out.fif
	@fift -v 0 ./out.fif

## /m:1 switch is a workaround not to
## let dotnet break the tty
test:
	@NO_COLOR=true dotnet test /m:1  
