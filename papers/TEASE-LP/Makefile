all:
	cd src && pdflatex main.tex && bibtex main && pdflatex main.tex

clean:
	rm src/*.log src/*.aux src/*.pdf
.PHONY: clean
