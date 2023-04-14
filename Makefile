build:
	dune build

clean:
	dune clean

html:
	dune build @doc
	rm -rf html
	cp -r _build/default/theories/melocoton.html html
	chmod -R +w html
	cp extra/resources/* html
	sed -i s/charset=iso-8859-1/charset=utf-8/g html/*

.PHONY: build clean html
