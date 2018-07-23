# Makefile for IPL
# Author : Andreas Abel
# Created: 2008-05-09, 2010-03-29, 2010-11-23, 2018-05-xx

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
	  -- 'delete.field = { doi }' \
	  -- 'delete.field = { url }' \
	  -- 'delete.field = { note }' \
	  -- 'delete.field = { editor }' \
	  -- 'delete.field = { publisher }' \
	  -- 'delete.field = { pages }'

catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex
bibliography=short.bib

# stdlib=$(HOME)/agda/std-lib/src

agda=agda-2.6.0

files=nbeSum.tex Makefile macros.tex

stlcagda = \
  src/Everything.agda \
  src/Library.agda \
  src/SimpleTypes.agda \
  src/STLCDefinable.agda \
  src/NBE.agda \
  src/NotNotDefinable.agda \
  src/PeirceNotDefinable.agda \

# END stlcagda

.PHONY : all debugMake html default deploy pack

.PRECIOUS : %.dvi %.ps %.gz %.pdf %.tex

default : nbeSum.pdf

mnt=/home
deploy :
	docker run -v $(shell pwd):$(mnt) -w $(mnt) sumdoc/texlive-2017 latexmk nbeSum.tex

pack : nbeSum.zip

nbeSum.zip : nbeSum.pdf $(files) jfp1.cls harpoons.sty nbeSum.bbl jfp.bst auto-nbeSum.bib
	zip $@ $^

html : src-stlc/html/Everything.html

src-stlc/html/Everything.html : $(stlcagda)
	cd src-stlc; $(agda) --html Everything.agda

latex/%.tex : %.lagda
	$(agda) --latex $<

talkAIM27.pdf : talkAIM27.tex macros.tex
	pdflatex $<

ship : shipTalk shipHtml

shipHtml : src-stlc/html/Everything.html
	cp -pr src-stlc/html $(destdir)/aim27/stlc-definability

shipTalk : talkAIM27.pdf
	cp -p $< $(destdir)/

# nbeSum
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
nbeSum_aux : nbeSum.tex $(files)
	$(pdflatex) nbeSum.tex;
	touch $@;

# then, run bibtex
nbeSum.bbl : nbeSum_aux auto-nbeSum.bib
	-bibtex nbeSum;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
nbeSum.pdf : nbeSum.bbl
	$(pdflatex) nbeSum.tex;
	$(pdflatex) nbeSum.tex;

# auto-nbeSum.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-nbeSum.bib : nbeSum_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x nbeSum.aux -i $(bibliography) >> $@;
endif
endif

# nbeSum-long
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
nbeSum-long_aux : nbeSum-long.tex $(files)
	$(pdflatex) nbeSum-long.tex;
	touch $@;

# then, run bibtex
nbeSum-long.bbl : nbeSum-long_aux auto-nbeSum-long.bib
	-bibtex nbeSum-long;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
nbeSum-long.pdf : nbeSum-long.bbl
	$(pdflatex) nbeSum-long.tex;
	$(pdflatex) nbeSum-long.tex;

# auto-nbeSum-long.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-nbeSum-long.bib : nbeSum-long_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x nbeSum-long.aux -i $(bibliography) >> $@;
endif
endif



# Templates (reverted back to simple templates)


talk% : talk%.pdf
	cp -p $? $(destdir)/;
	touch $@;

talk%.pdf : talk%.tex
	pdflatex $<;


%.tex : %.lhs
	lhs2TeX --poly -i lhs2TeX.fmt $< > $@
# /usr/local/share/lhs2tex-1.13/

% :  %.pdf # %.dvi %.ps.gz # %.tar.gz
	cp -p $? $(destdir)/;
	touch $@;

%.dvi : %.tex
	$(latex) $<;
	-bibtex $*;
	$(latex) $<;
	$(latex) $<;

%.pdf : %.dvi
	pdflatex $*.tex;

%.ps  : %.dvi
	dvips -o $@ $<;

%.gz : %
	cat $< | gzip > $@

## does not work since $ is evaluated before %
#%.tar : %.cfg $(shell cat %.cfg)
#	echo $?


#EOF
