#normalize_ore
# Input:
#  ore: an ore polynomial
#  x: the commutative variable of ore
#  basis: a basis of an ideal
#  pars: the list of variables in basis
# Output: the polynomial of ore with all coefficients in normal form
#
normalize_ore := proc(ore, x, basis, pars)
    local coefs, i, Dx;
    coefs := PolynomialTools[CoefficientList](OreTools[Converters][FromOrePolyToPoly](ore, Dx), Dx);
    coefs := [seq([PolynomialTools[CoefficientList](numer(coefs[i]), x), PolynomialTools[CoefficientList](denom(coefs[i]), x)], i=1..nops(coefs))];
    for i from 1 to nops(coefs) do
        coefs[i][1] := PolynomialTools[FromCoefficientList](map(Groebner[NormalForm], coefs[i][1], basis, tdeg(op(pars))), x);
        coefs[i][2] := PolynomialTools[FromCoefficientList](coefs[i][2], x);
        coefs[i] := coefs[i][1]/coefs[i][2]
    end do;
    return OreTools[Converters][FromPolyToOrePoly](PolynomialTools[FromCoefficientList](coefs, Dx), Dx)
end proc;

#searchideal
# Input:
#  R: a sequence of Ore polynomial remainders
#  i: the index of the processed remainder in R
#  n: the length of R
#  x: the commutative variable of R[i]
#  pars: the formal parameters occuring in R
#  ineqs: parameters that must not be canceled
#  basis: a basis of an ideal
#  depth: maximum number of ideal to process
#  default: default value for the gcd
#  fgb: use FGb for Groebner basis computations
# Output: a gcd that is different from 1 if possible and a Groebner basis of the ideal that produces this gcd
#
searchideal := proc(R, i, n, x, pars, ineqs, basis, depth, default, fgb:=true)
    local j, k, i_, Ri, lcoef, b, t, prev;
    if i = n + 1 then
        return OrePoly(1), [1]
    end if;
    # try to cancel R[i] entirely first then try to cancel the j leading terms
    for j in [nops(R[i]), seq(k, k=1..nops(R[i])-1)] do
        if fgb then
            b := FGb[fgb_gbasis_elim]([op(basis), op(map(coeffs, map(collect, map(numer, [seq(op(k, R[i]), k=1..j)]), x), x)), seq(1-t[k]*op(k, ineqs), k=1..nops(ineqs))], 0, [seq(t[k], k=1..nops(ineqs))], pars);
        else
            b := Groebner[Basis]([op(basis), op(map(coeffs, map(collect, map(numer, [seq(op(k, R[i]), k=1..j)]), x), x)), seq(1-t[k]*op(k, ineqs), k=1..nops(ineqs))], lexdeg([seq(t[k], k=1..nops(ineqs))], pars));
            for j from 1 to nops(ineqs) do
                b := remove(has, b, t[j])
            end do
        end if;
        if not 1 in b then
            if j = nops(R[i]) then
                if depth = 1 or i = n then
                    i_ := i;
                    j := -1;
                    while j < 0 and i_ > 1 do
                        if i_ = 1 then
                            prev := default
                        else
                            prev := R[i_-1]
                        end if;
                        i_ := i_ - 1;
                        j := OreTools[Utility][Degree](prev);
                        while j >= 0 and {op(map(Groebner[NormalForm], [coeffs(numer(OreTools[Utility][Coefficient](prev, j)), x)], b, tdeg(op(pars))))} = {0} do
                            j := j - 1;
                        end do;
                        if j >= 0 then
                            return normalize_ore(prev, x, b, pars), b
                        end if
                    end do
                else
                    return searchideal(R, i+1, n, x, pars, ineqs, basis, depth-1, default)
                end if
            else
                return searchideal(R, i+1, n, x, pars, ineqs, b, depth, default)
            end if
        end if
    end do;
    searchideal(R, i+1, n, x, pars, ineqs, basis, depth, default)
end proc;

#gcdideal
# Input:
#  ore1, ore2: two Ore polynomials
#  x: the commutative variable of ore1 and ore2
#  ineqs: parameters in ore1 and ore2 that must not be canceled
#  depth: search depth for the ideal
#  fgb: use FGb in Groebner basis computations
# Output: a gcd that is different from 1 if possible and a Groebner basis of the ideal that produces this gcd
#
gcdideal := proc(ore1, ore2, x, ineqs:={}, basis:=[], depth:=1, fgb:=false)
    local A, pars, n, R, ideal, gcd, k, t, counter;
    A := OreTools[SetOreRing](x, 'differential');
    gcd := OreTools[GCD]['right'](ore1, ore2, A);
    if OreTools[Utility][Degree](gcd) > 0 then
        # the gcd is different from 1
        return gcd, [0]
    end if
    n, R := op(OreTools[Euclidean]['right'](ore1, ore2, A));
    pars := [op((indets({op(ore1)}, 'name') union indets({op(ore2)}, 'name')) minus {x})];
    return searchideal([seq(R[i], i=3..n)], 1, n-2, x, pars, ineqs, [], depth, ore2);
end proc;


gcdorediffeq := proc(ore1, ore2, x)
    local A, res, c1, c2;
    A := OreTools[SetOreRing](x, 'differential');
    res := OreTools[GCD]['right'](ore1, ore2, A);
    if res = OrePoly(1) then
        OreTools[ExtendedGCD]['right'](ore1, ore2, A, 'c1', 'c2');
        c1 := c1[1];
        c2 := c2[1];
        res := OreTools[Add](OreTools[Multiply](c1, ore1, A), OreTools[Multiply](c2, ore2, A));
    end if;
    return res
end proc;


#diffeqs_table
# A table indexed by differential equations with values its basis of solutions in the format
# [[e1, [e1(x0), e1'(x0), ..., e1^(n)(x0)],
#   ...
#  [en, [en(x0), en'(x0), ..., en^(n)(x0)]],
#  x0]
# where e1, ..., en is the basis of solutions of the differential equation
#
diffeqs_table[(D@@2)(_y)(_x) + _y(_x)] := [
    [sin, [_y(0)=0, D(_y)(0)=1]],
    [cos, [_y(0)=1, D(_y)(0)=0]],
    0];

diffeqs_table[(D@@2)(_y)(_x) - _y(_x)] := [
    [sinh, [_y(0)=0, D(_y)(0)=1]],
    [cosh, [_y(0)=1, D(_y)(0)=0]],
    0];

diffeqs_table[(_x^2 + 1)*(D@@2)(_y)(_x) + 2*_x*(D)(_y)(_x)] := [
    [arctan, [_y(0)=0, D(_y)(0)=1]],
    [proc (x) options operator, arrow; 1 end proc, [_y(0)=1, D(_y)(0)=0]],
    0];

diffeqs_table[(D)(_y)(_x) - _y(_x)] := [
    [exp, [_y(0)=1]],
    0];

diffeqs_table[(D@@2)(_y)(_x) + 2*_x*D(_y)(_x)] := [
    [erf, [_y(0)=0, D(_y)(0)=2/sqrt(pi)]],
    [erfc, [_y(0)=1, D(_y)(0)=-2/sqrt(pi)]],
    0];

diffeqs_table[_x*(D@@2)(_y)(_x) + (D)(_y)(_x)] := [
    [ln, [_y(1)=0, D(_y)(1)=1]],
    [proc (x) options operator, arrow; 1 end proc, [_y(1)=1, D(_y)(1)=0]],
    1];

#diffeq_symmetries
# Input:
#  LDE: linear differential equation
#  y, x: the variables of LDE
#  g: an algebraic function of x
#  deqpar: name of possible parameters of deq
#  ineqs(={}): additional constraints on g
#  fgb(=false): use FGb instead of Groebner
# Output: a groebner list of groebner basis of the symmetries and tranformation of LDE
#
diffeq_symmetries := proc (LDE, y, x, g, deq, deqpar, ineqs:={}, fgb:=false)
    local deq1, poly_deq, poly_sym, pars, Dx, sys, basis, t, i, c, symgcd, gcd, ideal;
    if type(LDE, 'set') then
        deq1 := op(remove(type, LDE, `=`));
    else
        deq1 := LDE
    end if;
    pars := [op(indets(deq, 'name') minus {y, x})];
    poly_deq := DETools[de2diffop](subs(seq(pars[i]=deqpar[i], i=1..nops(pars)), deq), y(x), [Dx, x]);
    poly_deq := collect(poly_deq/lcoeff(poly_deq, Dx), Dx);
    poly_sym := DETools[de2diffop](gfun[algebraicsubs](deq1, gfun[algfuntoalgeq](g, y(x)), y(x)), y(x), [Dx, x]);
    poly_sym := collect(poly_sym/lcoeff(poly_sym, Dx), Dx);
    gcd, ideal := gcdideal(OreTools[Converters][FromPolyToOrePoly](poly_deq, Dx), OreTools[Converters][FromPolyToOrePoly](poly_sym, Dx), x, ineqs union subs(seq(pars[i]=deqpar[i], i=1..nops(pars)), ineqs), 1);
    nops(pars), DETools[diffop2de](OreTools[Converters][FromOrePolyToPoly](gcd, Dx), y(x), [Dx, x]), ideal;
end proc;


recognize := proc(LDE, LDE2, g, y, x, ineqs, icspars, fgb:=false)
    local y2, deq, pars, ics, i, t, init_point, basis;
    deq := subs(y=y2, _x=x, LDE2);
    pars := indets(deq, 'name') minus {x, y2};
    #deq := subs(seq(op(i, pars)=deqpar[i], i=1..nops(pars)), deq);
    ics := gfun[poltodiffeq](y(x) - y2(x), [gfun[algebraicsubs](LDE, gfun[algfuntoalgeq](g, y(x)), y(x), {seq((D@@(i-1))(y)(0)=subs(x=0, (D@@(i-1))(g)(x)), i=1..2*PDETools[difforder](LDE))}), {deq, seq((D@@(i-1))(y2)(0)=icspars[i], i=1..PDETools[difforder](deq, x))}], [y(x), y2(x)], y(z));
    ics := map2(op, 2, [op(select(type, ics, `=`))]);
    if fgb then
        basis := FGb[fgb_gbasis_elim](ics, 0, [seq(1-t[i]*op(i, ineqs), i=1..nops(ineqs))], [op(indets(ics))]);
    else
        basis := Groebner[Basis](ics, lexdeg([seq(1-t[i]*op(i, ineqs), i=1..nops(ineqs))], [op(indets(ics))]));
        for i from 1 to nops(pars) do
            basis := remove(has, basis, t[i])
        end do
    end if;
    return basis;
end proc;

#getfunction
# Input:
#  x: a formal variable
#  par: formal parameter name
#  itype: type of transformation
# Output: the expression and the system of inequations asociated to itype
#
getfunction := proc(x, par, itype)
    local g, dp, dq, sys;
    if itype = 'homography' then
        g := (par[1,1]*x+par[1,2])/(par[2,1]*x+par[2,2]);
        sys := {resultant(numer(g), denom(g), x)}
    elif op(0, itype) = 'ratpoly' then
        dp := op(1, itype);
        dq := op(2, itype);
        g := par[1] * `+`(seq(par[i+1]*x^(i-1), i=1..dp), x^dp)/`+`(seq(par[i+1+dp]*x^(i-1), i=1..dq), x^dq);
        sys := {resultant(numer(g), denom(g), x), par[1]} minus {1};
    elif op(0, itype) = 'ratpolyfactor' then
        dp := op(1, itype);
        dq := op(2, itype);
        g := par[1] * `*`(seq(x - par[i+1], i=1..dp))/`*`(seq(x - par[i+1+dp], i=1..dq));
        sys := {seq(seq(par[i+1] - par[j+1+dp], j=1..dq), i=1..dp)}
    elif type(itype, 'ratpoly') then
        g := itype;
        sys := {resultant(numer(g), denom(g), x)} minus {1}
    else
        return
    end if;
    return g, sys;
end proc;

#identities
# Input:
#  LDE: linear differential equation
#  y, x: the variables of LDE
#  tab(=[]): a table of LDE
#  itype(='homography'): either 'homography', 'ratpoly'(dp, dq), 'ratpolyfactor'(dp, dq) or a rational fraction in x
#  fgb(=false): use FGb instead of Groebner
# Output:
#
identities := proc(LDE, y, x, tab:=[], itype:='homography', ineqs:={}, fgb:=false)
    local g, g2, sys, ndeqpar, ics, par, deq, rdeq, rdeq2, deqpar, icspars, gbase, sol, sol2, i, j;
    g, sys := getfunction(x, par, itype);
    if type(LDE, 'set') then
        deq := op(remove(type, LDE, `=`));
    else
        deq := LDE
    end if;
    for deq in {deq, op(tab)} do
        ndeqpar, rdeq, gbase := diffeq_symmetries(LDE, y, x, g, deq, deqpar, sys union ineqs, fgb);
        print(gbase);
        for sol in [solve(gbase, {seq(deqpar[i], i=1..ndeqpar)} union indets(LDE, 'name') union indets(g) minus {x})] do
            sol := [allvalues(sol)][1];
            g2 := subs(op(sol), g);
            rdeq2 := subs(op(sol), rdeq);
            print(deq, sol, g2);
            if resustant(numer(g2), denom(g2), x) <> 0  then
                if degree(denom(g2), x) = 0 then
                    g2 := collect(g2, x)
                end if;
                print(deq, sol, g2);
                print(gfun[poltodiffeq](rdeq2, [gfun[algebraicsubs](LDE, gfun[algfuntoalgeq](g2, y(x)), y(x), {seq((D@@(i-1))(y)(0)=subs(x=0, (D@@(i-1))(g)(x)), i=1..2*PDETools[difforder](LDE))})], [y(x)], y(x)))
                #for sol2 in solve(recognize(LDE, deq, g2, y, x, ineqs, icspars, fgb), {seq(icspars[i], i=1..PDETools[difforder](deq, x)), seq(deqpar[i], i=1..ndeqpar)}) do
                #    print(sol2)
                #end do
            end if
        end do
    end do
end proc;
