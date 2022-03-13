all:
	@dune exec ./prover.exe test.gcat

clean:
	@dune clean

ci:
	git ci . -m "Worked on gcat."
	git push

explain:
	menhir --explain parser.mly; less parser.conflicts; rm -f parser.conflicts parser.ml parser.mli
