main=NfCBPV.agda

default :
	agda --html Everything.agda

# Mount current directory as /src in docker image
mnt=/src-cbpv

deploy :
	docker run -v $(shell pwd):$(mnt) -v $(shell pwd)/../src:/src \
	   -w $(mnt) jlimperg/agda-stdlib agda --html $(main)

debug :
	echo $(PWD)
	echo $(shell pwd)

# EOF
