# Makefile to create docs

.PHONY: default deploy clean

# Make contents locally
default :
	make -C notes
	make -C src

# Main goal:
# - make contents
# - copy contents to docs folder

docs : deploy clean
	cp notes/*.pdf docs/
	cp fscd19/fscd19.pdf docs/
	cp ppdp19/ppdp19.pdf docs/
	cp -r src/html docs/
	cp -r src-focusing/html docs/html-focusing

# Make contents on travis

deploy :
	make -C ppdp19       deploy
	make -C src          deploy
	make -C src-focusing deploy
	make -C notes        deploy
	make -C fscd19       deploy

# Provide empty docs folder
clean :
	mkdir -p docs/
	rm -f docs/*.pdf
	rm -rf docs/html
	rm -rf docs/html-focusing

# EOF
