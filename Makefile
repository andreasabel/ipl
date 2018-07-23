# Makefile to create docs

default :
	make -C notes

docs : default clean
	cp notes/*.pdf docs/

.PHONY: clean
clean :
	mkdir -p docs/
	rm -f docs/*.pdf

# EOF
