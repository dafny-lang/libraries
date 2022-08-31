default: release

Benchmark.cs: Benchmark.dfy
	Dafny Benchmark.dfy /useRuntimeLib /noVerify /spillTargetCode:3

deps := $(wildcard *.csproj) $(wildcard *.cs) Benchmark.cs

release: $(deps)
	dotnet build -c Release

publish: $(deps)
	dotnet publish -r win-x64 -c Release --self-contained

deps:
	dotnet add package Microsoft.DotNet.ILCompiler --prerelease

run: release

clean:
	rm -fr Benchmark.cs obj bin
