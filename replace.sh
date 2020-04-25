git ls-files | xargs -n 1 sed -i '' \
	-e 's/aMax/aMax/g' \
	-e 's/getMax/getMax/g' \
	-e 's/aMin/aMin/g' \
	-e 's/getMin/getMin/g'
