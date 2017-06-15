# cos(x+a) formulas
dsolve_symmetries((D@@2)(y)(x) + y(x), y, x, cos, [[a, b], [c, d]], [d=1, b=a], true);

# sin(x+a) formulas
dsolve_symmetries((D@@2)(y)(x) + y(x), y, x, sin, [[a, b], [c, d]], [d=1, b=a], true);

# arctan(1/x) formulas
dsolve_symmetries((x^2 + 1)*(D@@2)(y)(x) + 2*x*(D)(y)(x), y, x, arctan, [[a, b], [c, d]], [b=1, d=0, c=1], true);

# exp(a+x) formula
dsolve_symmetries(D(y)(x) - y(x), y, x, exp, [[a, b], [c, d]], [d=1], true);

# ln(a*x) formulas
dsolve_symmetries(x*(D@@2)(y)(x) + D(y)(x), y, x, lnp1, [[a, b], [c, d]], [b=a, d=1, c=1], true);

# sinh(a+x) formulas
dsolve_symmetries((D@@2)(y)(x) - y(x), y, x, sinh, [[a, b], [c, d]], [b=a, d=1], true);
