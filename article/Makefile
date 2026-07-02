SRC = document presentation
TARGET_PDFS = $(addsuffix .pdf, $(SRC)) 

all: cleangen

cleangen: dirtygen cleanup

dirtygen: $(TARGET_PDFS)

%.pdf: %.tex
	-pdflatex $^ 
	# Another 3 recompilation to account for restructuring, table of contents and bibliography
	-pdflatex $^ 
	-pdflatex $^ 
	-pdflatex $^ 


bleach: cleanup 
	rm -f $(TARGET_PDFS) 

cleanup:
	rm -f *.aux *.log *.bbl *.blg *.nav *.snm *.toc *.out
