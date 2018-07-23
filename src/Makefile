default :
	agda --html Everything.agda

# Mount current directory as /src in docker image
mnt=/src

deploy :
	docker run -v $(PWD):$(mnt) jlimperg/agda-stdlib agda --html --html-dir=$(mnt)/html -l standard-library -i $(mnt) $(mnt)/Everything.agda

debug :
	echo $(PWD)

# EOF
