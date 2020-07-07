# Makefile for POPL 21

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'print.use.tab = OFF' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { note }'
#	  -- 'delete.field = { editor }'
#	  -- 'delete.field = { doi }' \
catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex
bibliography=all.bib

stdlib=$(HOME)/agda/std-lib/src

files=
# acmart.cls Makefile

.PHONY : default add all pack ship debugMake html

.PRECIOUS : %.dvi %.ps %.gz %.pdf %.tex

default : popl21.pdf

all : popl21.pdf popl21-long.pdf

add : additional-material.tgz

additional-material.tgz : popl21-long.pdf
	tar czhf $@ $^

pack : popl21.zip

popl21.zip : popl21.pdf $(files) jfp1.cls harpoons.sty popl21.bbl jfp.bst auto-popl21.bib
	zip $@ $^

# latex/popl21-long.tex: latex/popl21.tex
# 	echo '\\newcommand\LONGVERSION[1]{#1}' > $@
# 	cat $< >> $@

# latex/popl21.tex : latex/%.tex : %.tex syntaxMacros.tex
# 	mkdir -p latex
# 	lhs2TeX -o $@ $<

# latex/%.tex : %.tex
# 	mkdir -p latex
# 	lhs2TeX -o $@ $

# popl21
##################################################################

clean:
	rm -rf latex
	rm -f *.pdf

# popl21.pdf: popl21.tex $(files)
# 	latexmk -f -pdf popl21.tex

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
popl21_aux : popl21.tex $(files)
	-$(pdflatex) $<;
	touch $@;

# then, run bibtex
popl21.bbl : popl21_aux auto-popl21.bib
	-bibtex popl21;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
popl21.pdf : popl21.bbl
	-$(pdflatex) popl21.tex;
	$(pdflatex) popl21.tex;

# auto-popl21.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-popl21.bib : popl21_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x popl21.aux -i $(bibliography) >> $@;
endif
endif

# popl21-long
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
popl21-long_aux : popl21-long.tex $(files)
	$(pdflatex) popl21-long.tex;
	touch $@;

# then, run bibtex
popl21-long.bbl : popl21-long_aux auto-popl21.bib
	-bibtex popl21-long;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
popl21-long.pdf : popl21-long.bbl
	$(pdflatex) popl21-long.tex;
	$(pdflatex) popl21-long.tex;

# auto-popl21-long.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-popl21-long.bib : popl21-long_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x popl21-long.aux -i $(bibliography) >> $@;
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
