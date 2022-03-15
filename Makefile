all:
	@dune build

ci:
	git ci . -m "Worked on gcat."
	git push
