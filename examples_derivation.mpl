# Formally proved derivation
Dx := proc (y) options operator, arrow; derive[Derive](y, x) end proc;

# Maple derivation
Dm := proc (y) options operator, arrow; diff(y, x) end proc;

# derive cos
Dx(cos(x)), expected=Dm(cos(x));

# derive ln
Dx(ln(x)), expected=Dm(ln(x));

# derive exp
Dx(exp(x)), expected=Dm(exp(x));

# more complicated examples
Dx(1/exp(x)), expected=Dm(exp(-x));
Dx(cos(x^2 + 1)), expected=Dm(cos(x^2 + 1));
Dx(ln(cos(1/x)+x^2-exp(x))), expected=Dm(ln(cos(1/x)+x^2-exp(x)));
Dx(exp(exp(exp(x)))), expected=Dx(exp(exp(exp(x))));
