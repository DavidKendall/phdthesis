all: main.tex
	latex main
	bibtex main
	latex main
	latex main
	latex main
	dvips -Ppdf main
	ps2pdf -dCompatibility=1.5 -dPDFSETTINGS=/prepress -dEmbedAllFonts=true main.ps
