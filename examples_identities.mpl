kernelopts(printbytes=false):
read "identities.mpl": tab := subs(_x=x, _y=y, [indices(diffeqs_table, 'nolist')]):


identities((D@@2)(y)(x) + y(x), y, x, tab, 'homography');

identities((x^2 + 1)*(D@@2)(y)(x) + 2*x*(D)(y)(x), y, x, tab, 'homography');

identities(D(y)(x) - y(x), y, x, tab, 'homography');

identities(x*(D@@2)(y)(x) + D(y)(x), y, x, tab, 'homography');

identities((D@@2)(y)(x) - y(x), y, x, tab, 'homography');
