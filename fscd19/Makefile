# Makefile for FSCD
# Author : Andreas Abel
# Created: 2008-05-09, 2010-03-29, 2010-11-23, 2018-05-xx

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -q \
	  -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { url }' \
	  -- 'delete.field = { note }' \
	  -- 'delete.field = { pages }'

#	  -- 'delete.field = { doi }' \
#	  -- 'delete.field = { publisher }' \
#	  -- 'delete.field = { editor }' \
#

catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex -interaction=batchmode
bibliography=medium.bib

# stdlib=$(HOME)/agda/std-lib/src

agda=agda

files=fscd19.tex Makefile macros.tex abstract.txt

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

default : fscd19.pdf

mnt=/home
deploy :
	docker run -v $(shell pwd):$(mnt) -w $(mnt) sumdoc/texlive-2017 latexmk -pdf fscd19.tex

pack : fscd19.zip

fscd19.zip : fscd19.pdf $(files) jfp1.cls harpoons.sty fscd19.bbl jfp.bst auto-fscd19.bib
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

# fscd19
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
fscd19_aux : fscd19.tex $(files)
	$(pdflatex) fscd19.tex;
	touch $@;

# then, run bibtex
fscd19.bbl : fscd19_aux auto-fscd19.bib
	-bibtex fscd19;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
fscd19.pdf : fscd19.bbl
	$(pdflatex) fscd19.tex;
	$(pdflatex) fscd19.tex;

# auto-fscd19.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-fscd19.bib : fscd19_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x fscd19.aux -i $(bibliography) >> $@;
endif
endif

# fscd19-long
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
fscd19-long_aux : fscd19-long.tex $(files)
	$(pdflatex) fscd19-long.tex;
	touch $@;

# then, run bibtex
fscd19-long.bbl : fscd19-long_aux auto-fscd19-long.bib
	-bibtex fscd19-long;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
fscd19-long.pdf : fscd19-long.bbl
	$(pdflatex) fscd19-long.tex;
	$(pdflatex) fscd19-long.tex;

# auto-fscd19-long.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-fscd19-long.bib : fscd19-long_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x fscd19-long.aux -i $(bibliography) >> $@;
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
