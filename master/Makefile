#all:
#	pdflatex -output-directory src src/main.tex

all:
	cd src && \
	pdflatex main.tex && \
	biber main && \
	pdflatex main.tex

rebuild:
	cd src && \
	pdflatex main.tex

.PHONY: clean
clean:
	rm src/main.aux src/main.log src/main.pdf
