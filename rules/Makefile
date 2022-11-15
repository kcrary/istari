
all : dvi

dvi : refiner.dvi refiner-db.dvi

pdf : refiner.pdf refiner-db.pdf

refiner.dvi : refiner.tex the-rules.tex
	latex refiner.tex

refiner.pdf : refiner.tex the-rules.tex
	pdflatex refiner.tex

refiner-db.dvi : refiner-db.tex the-rules-db.tex
	latex refiner-db.tex

refiner-db.pdf : refiner-db.tex the-rules-db.tex
	pdflatex refiner-db.tex

clean :
	rm *.dvi *.aux *.log
