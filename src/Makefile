all:
	@dune exec ./prover.exe test.gcat

interactive:
	@dune exec -- ./prover.exe -i test.gcat < interactive.gcat

clean:
	@dune clean

ci:
	$(MAKE) -C .. ci

explain:
	menhir --explain parser.mly; less parser.conflicts; rm -f parser.conflicts parser.ml parser.mli
