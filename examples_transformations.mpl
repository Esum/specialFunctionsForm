kernelopts(printbytes=false):
read "formulas.mpl":

dsolve_transformations((D@@2)(y)(x) + y(x), y, x, cos, [[a, b], [c, d]], [d=1, b=0], true);

dsolve_transformations((D@@2)(y)(x) + y(x), y, x, sin, [[a, b], [c, d]], [d=1, b=0], true);
