maple = maple

form:
	'$(maple)' < examples_symmetries.mpl > form.txt
	'$(maple)' < examples_2F1.mpl >> form.txt

tests:
	'$(maple)' < examples_derivation.mpl
