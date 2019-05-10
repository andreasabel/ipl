main=Polarized.agda

default :
	agda --html $(main)

# Mount current directory as /src in docker image
mnt=/src

deploy :
	docker run -v $(shell pwd):$(mnt) -w $(mnt) jlimperg/agda-stdlib agda --html $(main)

# deploy :
# 	docker run -v $(shell pwd):$(mnt) jlimperg/agda-stdlib agda --html --html-dir=$(mnt)/html -l standard-library -i $(mnt) $(mnt)/Everything.agda

debug :
	echo $(PWD)
	echo $(shell pwd)

# EOF
