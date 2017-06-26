maple = maple
headlines := 8
reformat = tail -n +$(headlines) | cat

form:
	'$(maple)' < examples_symmetries.mpl | $(reformat) > form.txt
	'$(maple)' < examples_transformations.mpl | $(reformat) >> form.txt
	'$(maple)' < examples_2F1.mpl | $(reformat) >> form.txt

tests:
	'$(maple)' < examples_derivation.mpl
