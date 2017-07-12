identities := module ()

export
    identities,
    getfunction,
    symmetries,
    gcdideal,
    recognize,
    diffeqs_table,
    formal_sol,
    `formal_sol/prettyprint`,
    testg,
    force_export,
    # module variables
    use_FGb;

local
    searchideal,
    normalize_ore,
    algeqtoseries,
    puiseux_coeffs,
    `formal_sol/nt`,
    ModulelLoad;

ModulelLoad := proc ()
    if not type(gfun, '`module`') then
        error "gfun module not loaded."
    end if;
    use_FGb := type(FGb, '`module`')
end proc;
ModulelLoad();

force_export := proc ()
    return [searchideal, normalize_ore, algeqtoseries, puiseux_coeffs, `formal_sol/nt`]
end proc;
    


#normalize_ore
# Input:
#  ore: an ore polynomial
#  x: the commutative variable of ore
#  basis: a basis of an ideal
#  pars: the list of variables in basis
# Output: the polynomial of ore with all coefficients in normal form
#
normalize_ore := proc (ore, x, basis, pars)
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
# Output: a gcd that is different from 1 if possible and a Groebner basis of the ideal that produces this gcd
#
searchideal := proc (R, i, n, x, pars, ineqs, basis, depth, default)
    local j, k, i_, Ri, lcoef, b, t, prev;
    if i = n + 1 then
        if OreTools[Utility][Degree](R[i-1]) = 0 then
            return OrePoly(1), [1]
        else
            return OreTools[MonicAssociate](R[i-1]), [0]
        end if
    end if;
    # try to cancel R[i] entirely first then try to cancel the j leading terms
    for j in [nops(R[i]), seq(k, k=1..nops(R[i])-1)] do
        if use_FGb then
            b := FGb[fgb_gbasis_elim]([op(basis), op(map(coeffs, map(collect, map(numer, [seq(op(nops(R[i]) - k + 1, R[i]), k=1..j)]), x), x)), seq(1-t[k]*op(k, ineqs), k=1..nops(ineqs))], 0, [seq(t[k], k=1..nops(ineqs))], pars);
        else
            b := Groebner[Basis]([op(basis), op(map(coeffs, map(collect, map(numer, [seq(op(nops(R[i]) - k + 1, R[i]), k=1..j)]), x), x)), seq(1-t[k]*op(k, ineqs), k=1..nops(ineqs))], lexdeg([seq(t[k], k=1..nops(ineqs))], pars));
            for j from 1 to nops(ineqs) do
                b := remove(has, b, t[j])
            end do
        end if;
        if not 1 in b then
            if j = nops(R[i]) then
                if depth = 1 or i = n then
                    i_ := i;
                    j := -1;
                    while j < 0 and i_ >= 1 do
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
# Output: a gcd that is different from 1 if possible and a Groebner basis of the ideal that produces this gcd
#
gcdideal := proc (ore1, ore2, A, ineqs:={}, basis:=[], depth:=1)
    local x, pars, n, R, ideal, gcd, k, t, counter;
    x := OreTools[Properties][GetVariable](A);
    n, R := op(OreTools[Euclidean]['right'](ore1, ore2, A));
    if n = 2 then
        return ore2, [0]
    end if;
    pars := [op((indets({op(ore1)}, 'name') union indets({op(ore2)}, 'name')) minus {x})];
    return searchideal([seq(R[i], i=3..n)], 1, n-2, x, pars, ineqs, [], depth, ore2);
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
# Output: a groebner list of groebner basis of the symmetries and tranformation of LDE
#
symmetries := proc (LDE, y, x, deq, deqpar, ineqs:={})
    local deq1, poly_deq, poly_sym, pars, Dx, sys, basis, t, i, gcd, ideal;#, ld1, ld2;
    if type(LDE, 'set') then
        deq1 := op(remove(type, LDE, `=`));
    else
        deq1 := LDE
    end if;
    pars := [op(indets(deq, 'name') minus {y, x})];
    poly_deq := DETools[de2diffop](subs(seq(pars[i]=deqpar[i], i=1..nops(pars)), deq), y(x), [Dx, x]);
    poly_deq := collect(poly_deq/lcoeff(poly_deq, Dx), Dx);
    poly_sym := DETools[de2diffop](deq1, y(x), [Dx, x]);
    poly_sym := collect(poly_sym/lcoeff(poly_sym, Dx), Dx);
    gcd, ideal := gcdideal(OreTools[Converters][FromPolyToOrePoly](poly_deq, Dx), OreTools[Converters][FromPolyToOrePoly](poly_sym, Dx), OreTools[SetOreRing](x, 'differential'), ineqs union subs(seq(pars[i]=deqpar[i], i=1..nops(pars)), ineqs), 1);
    nops(pars), DETools[diffop2de](OreTools[Converters][FromOrePolyToPoly](gcd, Dx), y(x), [Dx, x]), ideal;
end proc;


recognize := proc (LDE, LDE2, g, y, x, ineqs, icspars)
    local y2, deq, pars, ics, i, t, init_point, basis;
    deq := subs(y=y2, _x=x, LDE2);
    pars := indets(deq, 'name') minus {x, y2};
    #deq := subs(seq(op(i, pars)=deqpar[i], i=1..nops(pars)), deq);
    ics := gfun[poltodiffeq](y(x) - y2(x), [gfun[algebraicsubs](LDE, gfun[algfuntoalgeq](g, y(x)), y(x), {seq((D@@(i-1))(y)(0)=subs(x=0, (D@@(i-1))(g)(x)), i=1..2*PDETools[difforder](LDE))}), {deq, seq((D@@(i-1))(y2)(0)=icspars[i], i=1..PDETools[difforder](deq, x))}], [y(x), y2(x)], y(z));
    ics := map2(op, 2, [op(select(type, ics, `=`))]);
    if use_FGb then
        basis := FGb[fgb_gbasis_elim](ics, 0, [seq(1-t[i]*op(i, ineqs), i=1..nops(ineqs))], [op(indets(ics))]);
    else
        basis := Groebner[Basis](ics, lexdeg([seq(1-t[i]*op(i, ineqs), i=1..nops(ineqs))], [op(indets(ics))]));
        for i from 1 to nops(pars) do
            basis := remove(has, basis, t[i])
        end do
    end if;
    return basis;
end proc;

algeqtoseries := proc (pol, y, x, x0, order:=6)
    if x0 = infinity then
        return subs(x=1/x, gfun[algeqtoseries](numer(subs(x=1/x, pol)), x, y, order))
    end if;
    return subs(x=x-x0, gfun[algeqtoseries](subs(x=x+x0, pol), x, y, order))
end proc;

`formal_sol/nt` := proc (f, n)
    local a, res, g, m;
    global `DEtools/diffop/x`;
    if has(f, log(`DEtools/diffop/x`)) then
        return subs(a=log(`DEtools/diffop/x`), procname(subs(log(`DEtools/diffop/x`)=a, f), n))
    end if;
    if type(f, list) then
        return map(procname, f, n)
    end if;
    map(`DEtools/diffop/nmterms_laurent`, indets(f) intersect `DEtools/diffop/set_laurents`, n);
    g := `DEtools/diffop/subsvalueslaurents`(f);
    res := 0;
    m := n;
    while res = 0 do
        res := `algcurves/normal_tcoeff`(`algcurves/truncate`(g, m, `DEtools/diffop/x`, []), `DEtools/diffop/x`);
        m := m + 1
    end do;
    return [res, m-1];
end proc;

#puiseux_coeffs
# Input:
#  Q: a sum of terms of the form a/x^(k/l) where k >= 0
#  x: the variable of Q
# Output: A list of coefficient of a polynomial P and an integer m such that Q(x) = P(1/x^(1/m))
#
puiseux_coeffs := proc (Q, x)
    local i, j, m, P, ops;
    if Q = 0 then
        return [1, []];
    end if;
    if op(0, Q) = `*` or op(0, Q) = `^` then
        ops := [Q]
    else
        ops := [op(Q)]
    end if;
    m := 1;
    for i from 1 to nops(ops) do
        if op(0, ops[i]) = `*` then
            m := ilcm(m, denom(op([2, 2], ops[i])))
        else
            m := ilcm(m, denom(op(2, ops[i])))
        end if
    end do;
    for i from 1 to nops(ops) do
        if op(0, ops[i]) = `*` then
           ops[i] := subsop(2=x^(-numer(op([2, 2], ops[i])) * (m/denom(op([2, 2], ops[i])))), ops[i])
        else
           ops[i] := x^(-numer(op(2, ops[i])) * (m/denom(op(2, ops[i]))))
        end if
    end do;
    return m, PolynomialTools[CoefficientList](`+`(op(ops)), x)
end proc;

#formal_sol
# Input:
#  LDE: linear differential equation
#  y, x: variables of LDE
#  x0: expansion point
# Output: the list of the dominant terms of the formal solutions of LDE at x=x0 in the format
#  [[a, b, c, [d1, [d20, ...]]], [a', b', c', [d1', [d20', ...]]], ..., x=p] (where p is x-x0 or 1/x if x0 = infinity)
#  meaning that the formal solutions at x0 are
#  a * p^b * ln(p)^c * exp(... + d2i/p^(i/d1) + ...), ...
#
formal_sol := proc (LDE, y, x, x0)
    local L, Dx, a, i, j;
    L := `DEtools/de2diffop`(LDE, y(x), [Dx, x]);
    a := `DEtools/diffop/formal_sol`(`DEtools/diffop/l_p`(subs(Dx = `DEtools/diffop/DF`, x = `DEtools/diffop/x`, L), x0), `DEtools/diffop/g_ext`([L, x0]));
    a := subs(`DEtools/diffop/x`=x, [seq([`formal_sol/nt`(i[1], 1), i[2], `if`(3 < nops(i), i[4], `DEtools/diffop/x`)], i = a)]);
    a := [seq(seq([x^coeff(j[2], x, 0), i[1], int((j[2]-coeff(j[2], x, 0))/x, x), subs(x=y, j[3]) = `if`(x0 = infinity, 1/x, x-x0)], i = j[1]), j = a)];
    a := [seq(subs(x=RootOf(j[-1], y), j[1..-2]), j = a)];
    a := [seq(`DEtools/index_them`(j, [args]), j = subs(`algcurves/g_conversion2`, convert([seq(`DEtools/index_them`(j, [args]), j = a)], 'radical')))];
    for i from 1 to nops(a) do
        j := eval(subs(ln=(_ -> y), a[i][2]));
        j, a[i][2] := lcoeff(j, y), degree(j, y);
        if op(0, j) = `*` then
            if op([2, 0], j) = `^` then
                a[i][1] := a[i][1] * x^op([2, 2], j);
                j := op(1, j)
            elif op(2, j) = x then
                a[i][1] := a[i][1] * x;
                j := op(1, j)
            end if
        elif op(0, j) = `^` then
            a[i][1] := a[i][1] * x^op(2, j);
            j := 1
        elif j = x then
            a[i][1] := a[i][1] * x;
            j := 1
        end if;
        a[i][1] := evala(a[i][1]);
        if type(a[i][1], 'symbol') then
            a[i][1] := 1
        elif type(a[i][1], 'constant') then
            j, a[i][1] := j*a[i][1], 0
        else
            a[i][1] := op(2, a[i][1])
        end if;
        a[i][3] := puiseux_coeffs(evala(a[i][3]), x);
        a[i] := [allvalues([j, op(a[i])])];
    end do;
    unassign('i');
    return [seq(op(i), i=a), x = `if`(x0 = infinity, 1/x, x-x0)]
end proc;

#`formal_sol/prettyprint`
# Input:
#  LDE: linear differential equation
#  y, x: variables of LDE
#  x0: expansion point
# Output: the list of the dominant terms of the formal solutions of LDE at x=x0
#
`formal_sol/prettyprint` := proc (LDE, y, x, x0)
    local res, i, j;
    res := formal_sol(LDE, y, x, x0);
    for i from 1 to nops(res)-1 do
        res[i] := subs(res[-1], res[i][1] * x^res[i][2] * ln(x)^res[i][3] * exp(add(seq(res[i][4][2][j]/x^((j-1)/res[i][4][1]), j=1..nops(res[i][4][2])))));
    end do;
    return res[..-2];
end proc;


testg := proc (LDE, y, x, deq, g)
    local dom1, dom2, tab1, tab2, degs, deg, k, i, j, degcmp, factor1, factor2, branch, poss, t, g2, infin;
    degcmp := proc(p, q) degree(p, x) >= degree(q, x) end proc;
    if degree([PDETools[dcoeffs](deq, y(x))][1], x) <> 0 then
        dom1 := sort(map2(op, [1, 1], factors([PDETools[dcoeffs](LDE, y(x))][1])[2..]), degcmp);
        dom2 := sort(map2(op, [1, 1], factors([PDETools[dcoeffs](deq, y(x))][1])[2..]), degcmp);
        print(dom1, dom2);
        degs := map(degree, dom1, x);
        if degs <> map(degree, dom2, x) then
            return false
        end if;
        degs := {op(degs)};
        print(degs);
        for deg in degs do
            poss[deg] := {};
            tab1[deg], dom1 := selectremove((_ -> degree(_, x) = deg), dom1);
            tab2[deg], dom2 := selectremove((_ -> degree(_, x) = deg), dom2);
            for i from 1 to nops(tab1[deg]) do
                factor1 := tab1[deg][i];
                for j from 1 to nops(tab2[deg]) do
                    factor2 := tab2[deg][j];
                    for branch in `algcurves/puiseux`(g, x=RootOf(factor2, x), y, 1) do
                        poss[deg] := poss[deg] union {[i, j, numer(evala(subs(x=branch, factor1)))]};
                    end do
                end do
            end do
        end do;
    else
        degs := {}
    end if;
    infin := false;
    if infinity in `union`(op(map2(op, 2, [DETools[singularities](deq, y(x))]))) then
        infin := true;
        poss[0] := {};
        g2 := subs(x=0, numer(subs(x=1/x, g)));
        if degree(g2, y) = 0 then
            if infinity in `union`(op(map2(op, 2, [DETools[singularities](LDE, y(x))]))) then
                poss[0] := {0}
            else
                poss[0] := {1}
            end if;
        elif ldegree(g2, y) > 0 then
            if 0 in `union`(op(map2(op, 2, [DETools[singularities](LDE, y(x))]))) then
                poss[0] := {0}
            else
                poss[0] := {1}
            end if;
        else
            for factor1 in tab1[1] do
                poss[0] := poss[0] union {numer(evala(subs(x=RootOf(g2, y)), factor1))}
            end do
        end if;
    end if;
    if infin then
        return [seq(poss[k], k=degs), poss[0]]
    else
        return [seq(poss[k], k=degs)]
    end if 
end proc;

#getfunction
# Input:
#  x: a formal variable
#  par: formal parameter name
#  itype: type of transformation
# Output: the expression and the system of inequations associated to itype
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
    elif type(itype, 'radfun') then
        g := itype;
        sys := {}
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
#  ineqs(={}): parameters that must not be canceled
# Output:
#
identities := proc (LDE, y, x, tab:=[], itype:='homography', ineqs:={})
    local g, g2, sys, ndeqpar, ics, par, deqsub, deq, rdeq, rdeq2, deqpar, icspars, gbase, sol, sol2, i, j;
    g, sys := getfunction(x, par, itype);
    if type(LDE, 'set') then
        deq := op(remove(type, LDE, `=`));
    else
        deq := LDE
    end if;
    deqsub := gfun[algebraicsubs](deq, gfun[algfuntoalgeq](g, y(x)), y(x));
    for deq in {deq, op(tab)} do
        ndeqpar, rdeq, gbase := symmetries(deqsub, y, x, deq, deqpar, sys union ineqs);
        print(deq, rdeq, gbase);
        for sol in [solve(gbase, {seq(deqpar[i], i=1..ndeqpar)} union indets(LDE, 'name') union indets(g) minus {x})] do
            sol := [allvalues(sol)][1];
            g2 := subs(op(sol), g);
            rdeq2 := subs(op(sol), rdeq);
            if resustant(numer(g2), denom(g2), x) <> 0  then
                if degree(denom(g2), x) = 0 then
                    g2 := collect(g2, x)
                end if;
                if true or gfun[poltodiffeq](rdeq2, [gfun[algebraicsubs](LDE, gfun[algfuntoalgeq](g2, y(x)), y(x), {seq((D@@(i-1))(y)(0)=subs(x=0, (D@@(i-1))(g)(x)), i=1..2*PDETools[difforder](LDE))})], [y(x)], y(x)) = y(x) then
                    printf("%a(%a) satisfies:", y, g2);
                    print({deq, y(0)=subs(x=0, y(g2)), seq((D@@(i-1))(y)(0)=subs(x=0, diff(y(g2), x$(i-1))), i=2..PDETools[difforder](deq))})
                end if;
            end if
        end do
    end do
end proc;

end module;