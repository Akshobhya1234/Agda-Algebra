test: Everything.agda check-whitespace
	agda -i. Everything.agda

check-whitespace:
	fix-whitespace --check

Everything.agda:
	git ls-tree --full-tree -r --name-only HEAD | grep '^src/[^\.]*.agda' | sed -e 's|^src/[/]*|import |' -e 's|/|.|g' -e 's/.agda//' -e '/import Everything/d' | LC_COLLATE='C' sort > Everything.agda

clean:
	find . -name '*.agdai' -exec rm \{\} \;