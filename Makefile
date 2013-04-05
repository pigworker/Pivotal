default : Pivotal.pdf

Pivotal.tex : Pivotal.lagda
	lhs2TeX --agda Pivotal.lagda > Pivotal.tex

Pivotal.aux : Pivotal.tex
	latex Pivotal

Pivotal.blg : Pivotal.aux Ornament.bib
	bibtex Pivotal

Pivotal.dvi : Pivotal.tex Pivotal.blg
	latex Pivotal
	latex Pivotal

Pivotal.pdf : Pivotal.dvi
	pdflatex Pivotal
