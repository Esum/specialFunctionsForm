#diffeqs_table
# Input:
#  y: the function variable
#  x: the variable
# Output: a table of linear differential equations and a basis of their solutions
#
diffeqs_table2 := proc(y, x)
{
    # triginonometric functions
    [(D@@2)(y)(x) + y(x), [
        [sin, [y(0)=0, D(y)(0)=1]],
        [cos, [y(0)=1, D(y)(0)=0]]],
        0],

    # hyperbolic functions
    [(D@@2)(y)(x) - y(x), [
        [sinh, [y(0)=0, D(y)(0)=1]],
        [cosh, [y(0)=1, D(y)(0)=0]]],
        0],

    [(x^2 + 1)*(D@@2)(y)(x) + 2*x*(D)(y)(x), [
        [arctan, [y(0)=0, D(y)(0)=1]],
        [proc (x) options operator, arrow; 1 end proc, [y(0)=1, D(y)(0)=0]]],
        0],

    [(D)(y)(x) - y(x), [
        [exp, [y(0)=1]]],
        0],

    [(D@@2)(y)(x) + 2*x*D(y)(x), [
        [erf, [y(0)=0, D(y)(0)=2/sqrt(pi)]],
        [erfc, [y(0)=1, D(y)(0)=-2/sqrt(pi)]]],
        0]
}
end proc;

#diffeqs_table
# A table inexed by differential equations with values its basis of solutions in the format
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

#values_table: a table of known values for special functions
values_table := {
    cos(pi/2)=0,
    sin(pi/2)=1,
    cos(pi)=-1,
    sin(pi)=0,
    cos(0)=1,
    sin(0)=0
};

#symmetries
# Input:
#  deq: a linear differential equation
#  y: the function variable of deq
#  x: the variable of deq
#  a: a variable or a 2x2 matrix of variables
# Output: a Groebner basis of the ideal of polynomials of variables a[i,j] (1 <= i,j <= 2) that stabilize the differential equation of y((a[1,1]*x+a[1,2])/(a[2,1]*x+a[2,2]))
#
symmetries := proc(deq, y, x, a)
    local poly_sym, poly_deq, sys, basis;
    poly_deq := DETools[de2diffop](deq, y(x), [Dx, x]);
    poly_deq := collect(poly_deq/lcoeff(poly_deq, Dx), Dx);
    poly_sym := DETools[de2diffop](gfun[algebraicsubs](deq, gfun[algfuntoalgeq]((a[1,1]*x+a[1,2])/(a[2,1]*x+a[2,2]), y(x)), y(x)), y(x), [Dx, x]);
    poly_sym := collect(poly_sym/lcoeff(poly_sym, Dx), Dx);
    sys := {op(map(coeffs, map(collect, map(numer, [coeffs(collect(poly_deq - poly_sym, Dx), Dx)]), x), x))};
    basis := Groebner[Basis](sys union {-a[1,1]*a[2,2]*t+a[1,2]*a[2,1]*t+1}, lexdeg([t], [a[1,1], a[1,2], a[2,1], a[2,2]]));
    remove(has, basis, t)
end proc;

#symmetric_diffeqs
# Input:
#  deq: a linear differential equation
#  y: the function variable of deq
#  x: the variable of deq
#  a: a variable or a 2x2 matrix of variables
# Output: a list of homographies that stabilize deq when composed with y
#
symmetric_diffeqs := proc(deq, y, x, a)
    local sols;
    sols := [solve(symmetries(deq, y, x, a), {a[1,1], a[1,2], a[2,1], a[2,2]})];
    [seq(expand(subs(op(sol),(a[1,1]*x+a[1,2])/(a[2,1]*x+a[2,2])), x), sol=sols)]
end proc;

#dsolve_symmetries
#  deq: a linear differential equation
#  y: the function variable of deq
#  x: the variable of deq
#  f: a known function solution of deq
#  a: a variable or a 2x2 matrix of variables
#  conditions(=[]): additionnal conditions for a
#  proof(=false): print a proof of the symmetries
# Output: a list of formulas satisfied by homographic compositions of f
#
dsolve_symmetries := proc(deq, y, x, f, a, conditions:=[], proof:=false)
    local order, eq, sing, eq2, cis, i, value, Dx, res, basis, sol, coefs, eqn;
    order := PDETools[difforder](deq);
    Dx := proc (_) options operator, arrow; diff(_, x) end proc;
    eqn := 1;
    for eq in symmetric_diffeqs(deq, y, x, a) do
        eq := subs(op(conditions), eq);
        sing := solve(denom(eq)=0, {x});
        if sing <> NULL then
            sing := op(op(sing))[2]
        end if;
        basis := diffeqs_table[subs(x=_x, y=_y, deq)];
        if type(basis, list) then
            if proof then
                if basis[-1] = sing then
                    printf("The function h = %a ↦ %a has a singularity at %a = %a\n", x, eq, x, subs(op(conditions), -a[2,2]/a[2,1]))
                end if;
                printf("(%a ∘ h) = %a ↦ %a(%a) satisfies the same differential equation as %a\n", f, x, f, eq, f);
                printf("Which has a basis : %a\n", [seq(basis[j][1], j=1..order)]);
                printf("(%a ∘ h) has the following initial conditions :\n", f);
                if basis[-1] = sing then
                    printf("\tSur ]%a, +∞[:\n", basis[-1])
                end if
            end if;
            cis := {};
            for i from 1 to order do
                if sing <> NULL and basis[-1] = sing then
                    value := eval(limit((Dx@@(i-1))(f(eq)), x=subs(op(conditions), -a[2,2]/a[2,1]), right))
                else
                    value := eval(subs(x=basis[-1], (Dx@@(i-1))(f(eq))));
                end if;
                if proof then
                    printf("\t(%a ∘ h)^(%d)(%a) = %a\n", f, i-1, basis[-1], value)
                end if;
                cis := {op(cis), value - add(l[j]*[op(basis[j][2][i])][2], j=1..order)}
            end do;
            coefs := {seq(l[i], i=1..order)};
            sol := solve(cis, coefs);
            if sol <> NULL then
                if proof then
                    printf("Its coefficients in the basis are %a, hence :\n", sol);
                end if;
                eq2 := subs(op(sol), eq);
                if basis[-1] = sing then
                    res[eqn] := [``(f)(eq2) = add(subs(op(sol), l[j])*basis[j][1](x), j=1..order), x > basis[-1]];
                    if proof then
                        printf("\t%a(%a) = %a when %a > %a\n\n", f, eq, op(res[eqn][1])[2], x, basis[-1])
                    end if
                else
                    res[eqn] := ``(f)(eq2) = add(subs(op(sol), l[j])*basis[j][1](x), j=1..order);
                    if proof then
                        printf("\t%a(%a) = %a\n\n", f, eq, op(res[eqn])[2])
                    end if
                end if;
                eqn := eqn + 1
            end if;
            if basis[-1] = sing then
                cis := {};
                if proof then
                    printf("\tSur ]-∞, %a[:\n", basis[-1])
                end if;
                for i from 1 to order do
                    if proof then
                        printf("\t\tlim (%a ∘ h)^(%d)(%a) = %a\n\t%a -> %a, %a < %a\n", f, i-1, eq, eval(limit((Dx@@(i-1))(f(eq)), x=subs(op(conditions), -a[2,2]/a[2,1]), left)), x, basis[-1], x, basis[-1])
                    end if;
                    cis := {op(cis), eval(limit((Dx@@(i-1))(f(eq)), x=subs(op(conditions), -a[2,2]/a[2,1]), left)) - add(l[j]*[op(basis[j][2][i])][2], j=1..order)}
                end do;
                if sol <> NULL then
                    eq2 := subs(op(sol), eq);
                    res[eqn] := [``(f)(eq2) = add(subs(op(sol), l[j])*basis[j][1](x), j=1..order), x < basis[-1]];
                    if proof then
                        printf("Its coefficients in the basis are %a, hence :\n", sol);
                        printf("\t%a(%a) = %a when %a < %a\n\n", f, eq, op(res[eqn][1])[2], x, basis[-1])
                    end if;
                    eqn := eqn + 1
                end if
            end if
        end if
    end do;
    subs(op(values_table), [seq(res[j], j=1..(eqn-1))])
end proc;

#known_transformations
# Input:
#  deq: a linear differential equation
#  y: the function variable of deq
#  x: the variable of deq
#  a: a variable or a 2x2 matrix of variables
# Output: a list of differential equations in diffeq_table and Groebner basis of the ideal that satisfies it (see symmetries) 
#
known_transformations := proc(deq, y, x, a)
    local eqd, poly_sym, poly_deq, sys, basis, res, i;
    poly_deq := DETools[de2diffop](deq, y(x), [Dx, x]);
    poly_deq := collect(poly_deq/lcoeff(poly_deq, Dx), Dx);
    i := 1;
    for eqd in diffeqs_table(y, x) do if eqd[1] <> deq then
        poly_sym := DETools[de2diffop](gfun[algebraicsubs](eqd[1], gfun[algfuntoalgeq]((a[1,1]*x+a[1,2])/(a[2,1]*x+a[2,2]), y(x)), y(x)), y(x), [Dx, x]);
        poly_sym := collect(poly_sym/lcoeff(poly_sym, Dx), Dx);
        sys := {op(map(coeffs, map(collect, map(numer, [coeffs(collect(poly_deq - poly_sym, Dx), Dx)]), x), x))};
        basis := Groebner[Basis](sys union {-a[1,1]*a[2,2]*t+a[1,2]*a[2,1]*t+1}, lexdeg([t], [a[1,1], a[1,2], a[2,1], a[2,2]]));
        if basis[1] <> 1 then
            res[i] := [eqd[1], remove(has, basis, t)];
            i := i + 1
        end if
    end if end do;
    [seq(res[j], j=1..(i-1))]
end proc;

#tranformations_diffeqs
# Input:
#  deq: a linear differential equation
#  y: the function variable of deq
#  x: the variable of deq
#  a: a variable or a 2x2 matrix of variables
# Output: a list of differential equations in diffeq_table and homographies that verifies the equitions when composed with y
#
transformations_diffeqs := proc(deq, y, x, a)
    local sol, sols, tr, transformations, i , res;
    i := 1;
    for tr in known_transformations(deq, y, x, a) do
        sols := [solve(tr[2], {a[1,1], a[1,2], a[2,1], a[2,2]})];
        for sol in sols do
            res[i] := [tr[1], expand(subs(op(sol),(a[1,1]*x+a[1,2])/(a[2,1]*x+a[2,2])), x)];
            i := i + 1
        end do
    end do;
    [seq(res[j], j=1..(i-1))]
end proc;

#dsolve_transformations
#  deq: a linear differential equation
#  y: the function variable of deq
#  x: the variable of deq
#  f: a known function solution of deq
#  a: a variable or a 2x2 matrix of variables
#  conditions: additionnal conditions for a
# Output: a list of formulas satisfied by homographic compositions of f
#
dsolve_transformations := proc(deq, y, x, f, a, init_point:=0, conditions:=[])
    local deq2, eq, eq2, cis, i, j, Dx, res, eqd, sol, coefs, eqn;
    Dx := proc (_) options operator, arrow; diff(_, x) end proc;
    eqn := 1;
    for eq in transformations_diffeqs(deq, y, x, a) do
        eq[2] := subs(op(conditions), eq[2]);
        for eqd in diffeqs_table(y, x) do if eqd[1] = eq[1] then
            cis := {};
            for i from 1 to nops(eqd[2]) do
                cis := {op(cis), eval(subs(x=eqd[3], (Dx@@(i-1))(f(eq[2])))) - add(l[j]*[op(eqd[2][j][2][i])][2], j=1..nops(eqd[2]))}
            end do;
            coefs := {seq(l[i], i=1..nops(eqd[2]))};
            sol := solve(cis, {a[1,1], a[1,2], a[2,1], a[2,2]} union coefs);
            if sol <> NULL then
                eq2 := subs(op(sol), eq[2]);
                res[eqn] := ``(f)(eq2) = add(subs(op(sol), l[j])*eqd[2][j][1](x), j=1..nops(eqd[2]));
                eqn := eqn + 1;
            end if
        end if; end do;
    end do;
    subs(op(values_table), [seq(res[j], j=1..(eqn-1))])
end proc;
