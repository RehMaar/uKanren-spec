SRC='./src/'

all:
	cd $(SRC) && pdflatex main.tex && \
	biber main && \
	pdflatex main.tex &&\
	pdflatex main.tex
	
rebuild:
	cd $(SRC) && pdflatex main.tex
