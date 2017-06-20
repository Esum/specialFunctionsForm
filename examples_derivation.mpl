read "formulas.mpl":

# Formally proved derivation
Dx := proc (y) options operator, arrow; derive[Derive](y, x) end proc;

# Maple derivation
Dm := proc (y) options operator, arrow; diff(y, x) end proc;

test := proc () global expected, result; if not simplify(result = expected) then printf("False result %a <> %a.", result, expected); `quit`(1) end if end proc:

# derive cos
result := Dx(cos(x)); expected := Dm(cos(x)); test();

# derive ln
result := Dx(ln(x)); expected := Dm(ln(x)); test();

# derive exp
result := Dx(exp(x)); expected := Dm(exp(x)); test();

# more complicated examples
result := Dx(1/exp(x)); expected := Dm(exp(-x)); test();
result := Dx(cos(x^2 + 1)); expected := Dm(cos(x^2 + 1)); test();
result := Dx(ln(cos(1/x)+x^2-exp(x))); expected := Dm(ln(cos(1/x)+x^2-exp(x))); test();
result := Dx(exp(exp(exp(x)))); expected := Dm(exp(exp(exp(x)))); test();
