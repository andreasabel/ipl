# Makefile for contnorm

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { doi }'
catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex
bibliography=medium.bib
sedfile=postprocess.sed
# stylefile=latex/agda.sty
files=macros.tex
# stdlib=$(HOME)/agda/test
types19tex=types19.tex

default : types19.pdf # talkTYPES19.pdf talkTYPES19-with-notes.pdf talkTYPES19.zip

all : default ship

ship : $(destdir)/types19.pdf

$(destdir)/types19.pdf : types19.pdf
	cp -p $< $@

#$(destdir)/types19.lagda : types19.lagda
#	cp -p $< $@

pack : types19.zip

types19.zip : types19.tex types19.bbl easychair.cls macros.tex auto-types19.bib
	zip $@ $^

talkTYPES19.zip : Makefile talkTYPES19.tex talkTYPES19.pdf talkTYPES19-with-notes.tex talkTYPES19-with-notes.pdf
	zip $@ $^

# types19
##################################################################

# types19.tex : latex/types19.tex $(sedfile)
# 	sed --file=$(sedfile) < $< > $@

# latex/types19.tex : types19.lagda
#	agda --latex -i. -i$(stdlib) $<

# types19.pdf : types19.lagda
#	pdflatex $<

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
types19_aux : $(types19tex) $(files)
	$(pdflatex) $(types19tex);
	touch $@;

# then, run bibtex
types19.bbl : types19_aux auto-types19.bib
	-bibtex types19;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
types19.pdf : types19.bbl
	$(pdflatex) $(types19tex);
	$(pdflatex) $(types19tex);

# auto-types19.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-types19.bib : types19_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x types19.aux -i $(bibliography) >> $@;
endif
endif

# Templates (reverted back to simple templates)


talk% : talk%.pdf
	cp -p $? $(destdir)/;
	touch $@;

talk%.pdf : talk%.tex
	pdflatex $<;

# EOF
