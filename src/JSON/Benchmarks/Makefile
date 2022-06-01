default: build

# Benchmark.cs: Benchmark.dfy
# 	Dafny Benchmark.dfy /useRuntimeLib /noVerify /spillTargetCode:3

build: $(wildcard *.csproj) $(wildcard *.cs) Benchmark.cs
	dotnet build --configuration Release

run: build

clean:
	rm -fr Benchmark.cs obj bin
