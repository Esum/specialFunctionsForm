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
    solve_singularities,
    force_export,
    # module variables
    use_FGb;

local
    searchideal,
    normalize_ore,
    algeqtoseries,
    puiseux_coeffs,
    permutations,
    product,
    gcdlist,
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
#  depth: maximum number of ideals to process
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
    # try to cancel R[i] entirely first then try to cancel the jth leading terms
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
gcdideal := proc (ore1, ore2, A, ineqs:={}, depth:=1, basis:=[])
    local x, pars, n, R, ideal, gcd, k, t, counter;
    x := OreTools[Properties][GetVariable](A);
    n, R := op(OreTools[Euclidean]['right'](ore1, ore2, A));
    if n = 2 then
        return ore2, [0]
    end if;
    pars := [op((indets({op(ore1)}, 'name') union indets({op(ore2)}, 'name') union indets(ineqs)) minus {x})];
    return searchideal([seq(R[i], i=3..n)], 1, n-2, x, pars, ineqs, basis, depth, ore2);
end proc;

#diffeqs_table
# A table indexed by differential equations with values its basis of solutions in the format
# diffeqs_table[LDE][x0] is a table
# [[e1, [e1(x0), e1'(x0), ..., e1^(n)(x0)],
#   ...
#  [en, [en(x0), en'(x0), ..., en^(n)(x0)]]]
# where e1, ..., en is the basis of solutions of the differential equation at x0
# diffeqs_table[LDE][""] is the canonical initial point of LDE (and is an in index in diffeqs_table[LDE])
# diffeqs_table[LDE]["pars"] is the list of parameters that occur in LDE
#
diffeqs_table[(D@@2)(_y)(_x) + _y(_x)] := table([
    0 = [[sin, [_y(0)=0, D(_y)(0)=1]],
         [cos, [_y(0)=1, D(_y)(0)=0]]],
    "" = 0]);

diffeqs_table[(D@@2)(_y)(_x) - _y(_x)] := table([
    0 = [[sinh, [_y(0)=0, D(_y)(0)=1]],
         [cosh, [_y(0)=1, D(_y)(0)=0]]],
    "" = 0]);

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
#  basis(=[]): polynomials on the parameters that must be equal to 0
# Output: a groebner list of groebner basis of the symmetries and tranformation of LDE
#
symmetries := proc (LDE, y, x, deq, ineqs:={}, basis:=[])
    local deq1, poly_deq, poly_sym, pars, Dx, sys, t, i, gcd, ideal;#, ld1, ld2;
    if type(LDE, 'set') then
        deq1 := op(remove(type, LDE, `=`));
    else
        deq1 := LDE
    end if;
    poly_deq := DETools[de2diffop](deq, y(x), [Dx, x]);
    poly_deq := collect(poly_deq/lcoeff(poly_deq, Dx), Dx);
    poly_sym := DETools[de2diffop](deq1, y(x), [Dx, x]);
    poly_sym := collect(poly_sym/lcoeff(poly_sym, Dx), Dx);
    gcd, ideal := gcdideal(OreTools[Converters][FromPolyToOrePoly](poly_deq, Dx), OreTools[Converters][FromPolyToOrePoly](poly_sym, Dx), OreTools[SetOreRing](x, 'differential'), ineqs, 1, basis);
    return DETools[diffop2de](OreTools[Converters][FromOrePolyToPoly](gcd, Dx), y(x), [Dx, x]), ideal;
end proc;


#recognize
# Input:
#  LDE: a linear differential equation
#  LDE2: a linear differential equation
#  g: an algebraic function
#  y, x: the variables of LDE and LDE2
# Output: 
#
recognize := proc (LDE, LDE2, g, y, x, ineqs, icspars)
    local y2, Dx, g2, deq, res, pars, ics, ics2, order, k, i, t, partable, init_point, basis;
    if type(LDE, 'set') then
        deq := op(remove(type, LDE, `=`));
        ics := [op(select(type, LDE, `=`))];
        init_point := op([1, 1, 1], ics);
        print(deq,ics,init_point);
        # the initial point is a fixed point of g
        if eval(subs(x=init_point, g)) = init_point then
            ics2 := map(degree, map(DETools[de2diffop], subs(init_point=x, map2(op, 1, ics)), y(x), [Dx, x]), Dx);
            for k from 1 to nops(ics2) do
                if ics2[k] > 0 then
                    order := ics2[k];
                    ics2[k] := diff(y(g2(x)), x$ics2[k]);
                    ics2[k] := (D@@order)(y)(init_point) = eval(subs(x=init_point, eval(subs(g2(x)=g, ics2[k]))))
                else
                    ics2[k] := y(init_point) = op(2, ics[k])
                end if
            end do
        # try to determine the initial conditions at x=g(init_point)
        else
            return false, [1];
            deq := subs(x=_x, y=_y, deq);
            if assigned(diffeqs_table[deq][init_point]) then

            end if;
        end if;
    else
        deq := subs(x=_x, y=_y, LDE);
        if assigned(diffeqs_table[deq]) then
            for k in [indices(diffeqs_table[deq], 'nolist')] do
                if eval(subs(x=k, g)) = k then
                    init_point := k;
                    break
                end if
            end do;
        end if;
        if not assigned(init_point) then
            init_point := 0
        end if;
        ics := [y(init_point) = icspars[1], seq((D@@i)(y)(init_point) = icspars[i+1], i=1..(PDETools[difforder](deq)-1))];
        ics2 := map(degree, map(DETools[de2diffop], subs(init_point=x, map2(op, 1, ics)), y(x), [Dx, x]), Dx);
        for k from 1 to nops(ics2) do
            if ics2[k] > 0 then
                order := ics2[k];
                ics2[k] := diff(y(g2(x)), x$ics2[k]);
                ics2[k] := (D@@order)(y)(init_point) = eval(subs(x=init_point, eval(subs(g2(x)=g, ics2[k]))))
            else
                ics2[k] := y(init_point) = op(2, ics[k])
            end if
        end do
    end if;
    deq := subs(_x=x, _y=y, deq);
    res := gfun[poltodiffeq](numer(LDE2), [{gfun[algebraicsubs](deq, gfun[algfuntoalgeq](g, y(x)), y(x)), op(ics2)}], [y(x)], y(x));
    if res = y(x) then
        return true, []
    else
        return false, map2(op, 2, [op(select(type, res, `=`))])
    end if
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
        return 1, [];
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
    a := subs(x=`if`(x0 = infinity, 1/x, x), [seq(subs(x=RootOf(j[-1], y), j[1..-2]), j = a)]);
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
        a[i][3] := [puiseux_coeffs(expand(allvalues(a[i][3])), x)];
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


product := proc (l, off:=0)
    local res, i, j, k;
    res := {seq([[i], {`if`(off=0, op(i, l[1]), op(i, l[1])[off])}], i=1..nops(l[1]))};
    for k from 2 to nops(l) do
        res := {seq(seq([[op(op(i, res)[1]), j], {op(op(i, res)[2]), `if`(off=0, op(j, l[k]), op(j, l[k])[off])}], j=1..nops(l[k])), i=1..nops(res))}
    end do;
    return res
end proc;


permutations := proc (l, i:=1)
    local res, j, k, p;
    if i = nops(l) then
        return [[l[i]]]
    end if;
    res := permutations(l, i+1);
    return [seq(seq([seq(`if`(k<j, res[p][k], `if`(k=j, l[i], res[p][k-1])), k=1..nops(res[p])+1)], j=1..nops(res[p])+1), p=1..nops(res))]
end proc;

gcdlist := proc (l, i:=1)
    if nops(l) = i then
        return l[i]
    else
        return gcd(l[i], gcdlist(l, i+1))
    end if
end proc;


#solve_singularities
# Input:
#  LDE: a linear differential equation
#  y, x: the variables of LDE
#  deq: a linear differential equation in x and y
#  g: an algebraic function given as a polynomial in y and x
#  ineqs(={}): polynomial in the parameters that must no be canceled
# Output: A list of Groebner basis followed by a set of [e1(x), ...] such that the formal solutions of y(g(x)) corresponds to the formal solutions of ei(x)*deq
#
solve_singularities := proc (LDE, y, x, deq, g, ineqs:={})
    local dom1, dom2, tab1, tab2, degs, deg, LDE2, deq2, A, k, i, j, l, m, degcmp, ind, factor1, factor2, branch, poss, p, basis, sing, s, s2, fs1, fs2, tay, tay0, t, g2, pol, pol2, comp;
    degcmp := proc(p, q) degree(p, x) >= degree(q, x) end proc;
    if degree([PDETools[dcoeffs](deq, y(x))][1], x) <> 0 then
        # order factors by degree
        dom1 := sort(map2(op, 1, factors([PDETools[dcoeffs](LDE, y(x))][1])[2..][1]), degcmp);
        dom2 := sort(map2(op, 1, factors([PDETools[dcoeffs](deq, y(x))][1])[2..][1]), degcmp);
        degs := map(degree, dom1, x);
        if degs <> map(degree, dom2, x) then
            return false
        end if;
        degs := {op(degs)};
        # each singularity of deq must be send on a singularity of LDE of the same degree
        for deg in degs do
            poss[deg] := {};
            tab1[deg], dom1 := selectremove((_ -> degree(_, x) = deg), dom1);
            tab2[deg], dom2 := selectremove((_ -> degree(_, x) = deg), dom2);
            for i from 1 to nops(tab1[deg]) do
                factor1 := tab1[deg][i];
                for j from 1 to nops(tab2[deg]) do
                    factor2 := tab2[deg][j];
                    for l from 1 to deg do
                        for branch in `algcurves/puiseux`(g, x=RootOf(factor2, x, 'index'=l), y, 1) do
                            pol := numer(evala(subs(x=branch, factor1)));
                            for pol in [allvalues(pol)] do
                                pol := factors(pol);
                                if pol[1] <> 0 then
                                    for pol in pol[2] do
                                        if not pol[1] in ineqs then
                                            poss[deg] := poss[deg] union {[deg, i, j, pol[1]]}
                                        end if
                                    end do
                                else
                                    poss[deg] := poss[deg] union {[deg, i, j, 0]}
                                end if
                            end do
                        end do
                    end do
                end do
            end do
        end do;
    else
        degs := {}
    end if;
    # add infinity if it is a singularity
    if infinity in `union`(op(map2(op, 2, [DETools[singularities](deq, y(x))]))) then
        degs := degs union {0};
        poss[0] := {};
        g2 := subs(x=0, numer(subs(x=1/x, g)));
        if degree(g2, y) = 0 or subs(x=0, lcoeff(g2, y)) = 0 then
            if infinity in `union`(op(map2(op, 2, [DETools[singularities](LDE, y(x))]))) then
                poss[0] := {[0, 0, 0, 0]}
            else
                poss[0] := {[0, 0, 0, 1]}
            end if;
        elif ldegree(g2, y) > 0 then
            if 0 in `union`(op(map2(op, 2, [DETools[singularities](LDE, y(x))]))) then
                poss[0] := {[0, 0, 0, 0]}
            else
                poss[0] := {[0, 0, 0, 1]}
            end if;
        else
            for factor1 in tab1[1] do
                pol := numer(evala(subs(x=RootOf(g2, y), factor1)));
                pol := factors(pol);
                if pol[1] <> 0 then
                    for pol in pol[2] do
                        poss[0] := poss[0] union {[0, 0, 0, pol[1]]}
                    end do
                else
                    poss[0] := {[0, 0, 0, 0]};
                end if
            end do
        end if;
    end if;
    degs := [op(degs)];
    # all possible singularity injections
    poss := [op(product([seq(poss[k], k=degs)], 4))];
    sing := {};
    ind := [op(indets(LDE, 'name') union indets(deq, 'name') union indets(g, 'name') minus {x, y})];
    A := OreTools[SetOreRing](x, 'differential');
    # find all values of x such that g(x) is a singularity of LDE
    for deg in degs do
        if deg <> 0 then
            for i from 1 to nops(tab1[deg]) do
                factor1 := tab1[deg][i];
                pol := select((_ -> degcmp(_, x)) , map2(op, 1, factors(subs(y=RootOf(factor1, x), g))[2]));
                for j from 1 to nops(pol) do
                    branch := gcdlist([coeffs(pol[j], x)]);
                    if branch in ineqs then
                        factor2 := collect(normal(pol[j]/branch), x)
                    else
                        factor2 := pol[j]
                    end if;
                    try
                        sing := sing union {[[deg, i, j], RootOf(factor2, x)]}
                    catch: end try
                end do
            end do
        else
            sing := sing union {[[0, 0, 0], infinity]}
        end if
    end do;
    sing := [op(sing)];
    for i from 1 to nops(poss) do
        p := poss[i];
        # compute the basis of the ideal of the current possiblity
        if use_FGb then
            basis := FGb[fgb_gbasis_elim]([op(p[2]), seq(1-t[k]*op(k, ineqs), k=1..nops(ineqs))], 0, [seq(t[k], k=1..nops(ineqs))], ind)
        else
            basis := Groebner[Basis]([op(p[2]), seq(1-t[k]*op(k, ineqs), k=1..nops(ineqs))], lexdeg([seq(t[k], k=1..nops(ineqs))], ind));
            for j from 1 to nops(ineqs) do
                basis := remove(has, b, t[j])
            end do
        end if;
        if basis = 0 then basis := [] end if;
        # normalize all equations with respect to the basis
        g2 := PolynomialTools[CoefficientList](g, y);
        g2 := map(PolynomialTools[CoefficientList], g2, x);
        for j from 1 to nops(g2) do
            g2[j] := PolynomialTools[FromCoefficientList](map(Groebner[NormalForm], g2[j], basis, tdeg(op(ind))), x)
        end do;
        g2 := PolynomialTools[FromCoefficientList](g2, y);
        LDE2 := OreTools[Converters][FromOrePolyToLinearEquation](normalize_ore(OreTools[Converters][FromLinearEquationToOrePoly](LDE, y, A), x, basis, ind), y, A);
        deq2 := OreTools[Converters][FromOrePolyToLinearEquation](normalize_ore(OreTools[Converters][FromLinearEquationToOrePoly](deq, y, A), x, basis, ind), y, A);
        poss[i] := [op(poss[i]), basis, g2, LDE2, deq2];
        for j from 1 to nops(sing) do
            s := sing[j];
            if ldegree(g2, y) <> 0 then
                break
            end if;
            if s[2] = infinity then
                s2 := s[2];
                pol := 1/x
            elif type(s[2], 'RootOf') then
                # polynomial may be reducible after normalization
                # keep only the first factor for now
                pol := PolynomialTools[FromCoefficientList](map(Groebner[NormalForm], PolynomialTools[CoefficientList](op(1, s[2]), _Z), basis, tdeg(op(ind))), x);
                s2 := RootOf(factors(pol)[2][1][1], x)
            elif type(s[2], 'polynom') then
                s2 := Groebner[NormalForm](s[2], basis, tdeg(op(ind)));
                pol := x - s2;
            elif type(s[2], 'ratpoly') then
                pol := Groebner[NormalForm](denom(s[2]), basis, tdeg(op(ind)));
                if pol = 0 then
                    s2 := infinity;
                    pol := 1/x
                else
                    s2 := (Groebner[NormalForm](numer(s[2]), basis, tdeg(op(ind))))/pol;
                    pol := x - s2
                end if;
            end if;
            tay := convert(eval(subs(O=(_->0), algeqtoseries(g2, y, x, s2, 2)))[1], 'polynom');
            tay := subs(x=`if`(s2 = infinity, 1/x, x+s2), tay);
            if ldegree(tay, x) = 0 then
                tay := tay - subs(x=0, tay);
            end if;
            deg := ldegree(tay, x);
            tay := tcoeff(tay, x);
            fs1[s[1]] := formal_sol(LDE2, y, x, `if`(s[1][1]=0, infinity, RootOf(tab1[s[1][1]][s[1][2]], x)));
            fs1[s[1]][2] := fs1[s[1]][2]*deg;
            comp[p[1]][j] := {seq(pol^(fs1[s[1]][1][2] - k[1][2])*ln(pol)^(fs1[s[1]][1][3] - k[1][3]), k=permutations(formal_sol(deq2, y, x, s2)[..-2]))};
        end do;
        comp[p[1]] := map2(op, 2, [op(product([seq(comp[p[1]][k], k=1..nops(sinh))]))]);
    end do;
    for i from 1 to nops(poss) do
        poss[i] := [poss[i][-4], poss[i][-3], poss[i][-2], poss[i][-1], map((_ -> `*`(op(_))), comp[p[1]])]
    end do;
    return poss
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
#  ineqs(={}): polynomials in the parameters that must not be canceled
#  basis(=[]): polynomials in the parameters that are 0
# Output:
#
identities := proc (LDE, y, x, tab:=[], itype:='homography', ineqs:={}, basis:=[])
    local g, g2, g3, LDE2, deq0, deq2, deq3, ineqs2, basis2, sys, ndeqpar, ics, init_point, par, pars, ex, poss, deqsub, deq, rdeq, rdeq2, deqpar, icspars, sol, sol2, i, j;
    g, sys := getfunction(x, par, itype);
    if type(LDE, 'set') then
        deq0 := op(remove(type, LDE, `=`));
    else
        deq0 := LDE
    end if;
    for deq in {deq0, op(tab)} do
        pars := [op(indets(deq, 'name') minus {x})];
        ndeqpar := nops(pars);
        deq := subs(seq(pars[i]=deqpar[i], i=1..nops(pars)), deq);
        ineqs2 := ineqs union sys union subs(seq(pars[i]=deqpar[i], i=1..nops(pars)), ineqs union sys);
        print(LDE, deq, ineqs2);
        for poss in solve_singularities(deq0, y, x, deq, gfun[algfuntoalgeq](g, y(x)), ineqs2) do
            if poss <> false then
            basis2 := [op(poss[1]), op(basis)];
            g2 := poss[2];
            LDE2 := poss[3];
            deq2 := poss[4];
            if g2 <> 0 and LDE2 <> y(x) and deq2 <> y(x) then
                deqsub := gfun[algebraicsubs](LDE2, g2, y(x));
                for ex in poss[5] do
                    deq3 := gfun[`diffeq*diffeq`](gfun:-holexprtodiffeq(ex, y(x)), deq2, y(x));
                    rdeq, basis2 := symmetries(deqsub, y, x, deq3, ineqs2, basis2);
                    if rdeq <> y(x) then
                    for sol in [solve(basis2, {seq(deqpar[i], i=1..ndeqpar)} union indets(LDE, 'name') union indets(g) minus {x})] do
                        sol := [allvalues(sol)][1];
                        g3 := subs(op(sol), g);
                        rdeq2 := subs(op(sol), rdeq);
                        if resustant(numer(g3), denom(g3), x) <> 0  then
                            if degree(denom(g3), x) = 0 then
                                g3 := collect(g3, x)
                            end if;
                            print(rdeq2, g3);
                            print(recognize(LDE, rdeq2, g3, y, x, {}, icspars))
                        end if
                    end do
                    end if
                end do
            end if end if
        end do
    end do
end proc;

end module;