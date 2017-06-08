#diffeqs_table
# Input:
#  y: the function variable
#  x: the variable
# Output: a table of linear differential equations and a basis of their solutions
#
diffeqs_table := proc(y, x)
{
    # triginonometric functions
    [(D@@2)(y)(x) + y(x), [
        [sin, [y(0)=0, D(y)(0)=1]],
        [cos, [y(0)=1, D(y)(0)=0]]]],

    # hyperbolic funcitons
    [(D@@2)(y)(x) - y(x), [
        [sinh, [y(0)=0, D(y)(0)=1]],
        [cosh, [y(0)=1, D(y)(0)=0]]]],

    [(x^2 + 1)*(D@@2)(y)(x) + 2*x*(D)(y)(x), [
        [arctan, [y(0)=0, D(y)(0)=1]],
        [proc (x) options operator, arrow; 1 end proc, [y(0)=1, D(y)(0)=0]]]],

    [(D)(y)(x) - y(x), [
        [exp, [y(0)=1]]]],

    [(D@@2)(y)(x) + 2*x*D(y)(x), [
        [erf, [y(0)=0, D(y)(0)=2/sqrt(pi)]],
        [erfc, [y(0)=1, D(y)(0)=-2/sqrt(pi)]]]]
}
end proc;

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
#  y: the function vaviable of deq
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
    sys := {op(map(coeffs, map(sort, map(collect, map(numer, [coeffs(sort(collect(poly_deq - poly_sym, Dx), Dx), Dx)]), x), x), x))};
    basis := Groebner[Basis](sys union {-a[1,1]*a[2,2]*t+a[1,2]*a[2,1]*t+1}, lexdeg([t], [a[1,1], a[1,2], a[2,1], a[2,2]]));
    remove(has, basis, t)
end proc;

#symmetric_diffeqs
# Input:
#  deq: a linear differential equation
#  y: the function vaviable of deq
#  x: the variable of deq
#  a: a variable or a 2x2 matrix of variables
# Output: a list of homographies that stabilize deq when composed with y
#
symmetric_diffeqs := proc(deq, y, x, a)
    local sols;
    sols := [solve(symmetries(deq, y, x, a), {a[1,1], a[1,2], a[2,1], a[2,2]})];
    [seq(sort(expand(subs(op(sol),(a[1,1]*x+a[1,2])/(a[2,1]*x+a[2,2])), x), x), sol=sols)]
end proc;

#dsolve_symmetries
#  deq: a linear differential equation
#  y: the function vaviable of deq
#  x: the variable of deq
#  f: a known function solution of deq
#  a: a variable or a 2x2 matrix of variables
#  init_point(=0): the point used to determine inital conditions
#  conditions: additionnal conditions for a
# Output: a list of formulas satisfied by homographic compositions of f
#
dsolve_symmetries := proc(deq, y, x, f, a, init_point:=0, conditions:=[])
    local eq, eq2, cis, i, j, Dx, res, eqd, sol, coefs, eqn;
    Dx := proc (_) options operator, arrow; diff(_, x) end proc;
    eqn := 1;
    for eq in symmetric_diffeqs(deq, y, x, a) do
        eq := subs(op(conditions), eq);
        for eqd in diffeqs_table(y, x) do if eqd[1] = deq then
            cis := {};
            for i from 1 to nops(eqd[2]) do
                cis := {op(cis), eval(subs(x=init_point, (Dx@@(i-1))(f(eq)))) - add(l[j]*[op(eqd[2][j][2][i])][2], j=1..nops(eqd[2]))}
            end do;
            coefs := {seq(l[i], i=1..nops(eqd[2]))};
            sol := solve(cis, {a[1,1], a[1,2], a[2,1], a[2,2]} union coefs);
            if sol <> NULL then
                eq2 := subs(op(sol), eq);
                res[eqn] := o(f)(eq2) = add(subs(op(sol), l[j])*eqd[2][j][1](x), j=1..nops(eqd[2]));
                eqn := eqn + 1;
            end if
        end if end do;
    end do;
    subs(op(values_table), [seq(res[j], j=1..(eqn-1))])
end proc;

#known_transformations
# Input:
#  deq: a linear differential equation
#  y: the function vaviable of deq
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
        sys := {op(map(coeffs, map(sort, map(collect, map(numer, [coeffs(sort(collect(poly_deq - poly_sym, Dx), Dx), Dx)]), x), x), x))};
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
#  y: the function vaviable of deq
#  x: the variable of deq
#  a: a variable or a 2x2 matrix of variables
# Output: a list of differential equations in diffeq_table and homographies that verifies the equitions when composed with y
#
tranformations_diffeqs := proc(deq, y, x, a)
    local sol, sols, tr, transforms, i , res;
    transforms := known_transforms(deq, y, x, a);
    i := 1;
    for tr in transforms do
        sols := [solve(tr[2], {a[1,1], a[1,2], a[2,1], a[2,2]})];
        for sol in sols do
            res[i] := [tr[1], sort(expand(subs(op(sol),(a[1,1]*x+a[1,2])/(a[2,1]*x+a[2,2])), x), x)];
            i := i + 1
        end do
    end do;
    [seq(res[j], j=1..(i-1))]
end proc;

#dsolve_transformations
#  deq: a linear differential equation
#  y: the function vaviable of deq
#  x: the variable of deq
#  f: a known function solution of deq
#  a: a variable or a 2x2 matrix of variables
#  init_point(=0): the point used to determine inital conditions
#  conditions: additionnal conditions for a
# Output: a list of formulas satisfied by homographic compositions of f
#
dsolve_transformations := proc(deq, y, x, f, a, init_point:=0, conditions:=[])
    local deq2, eq, eq2, cis, i, j, Dx, res, eqd, sol, coefs, eqn;
    Dx := proc (_) options operator, arrow; diff(_, x) end proc;
    eqn := 1;
    for eq in tranformations_diffeqs(deq, y, x, a) do
        eq[2] := subs(op(conditions), eq[2]);
        for eqd in diffeqs_table(y, x) do if eqd[1] = eq[1] then
            cis := {};
            for i from 1 to nops(eqd[2]) do
                cis := {op(cis), eval(subs(x=init_point, (Dx@@(i-1))(f(eq[2])))) - add(l[j]*[op(eqd[2][j][2][i])][2], j=1..nops(eqd[2]))}
            end do;
            coefs := {seq(l[i], i=1..nops(eqd[2]))};
            sol := solve(cis, {a[1,1], a[1,2], a[2,1], a[2,2]} union coefs);
            if sol <> NULL then
                eq2 := subs(op(sol), eq[2]);
                res[eqn] := o(f)(eq2) = add(subs(op(sol), l[j])*eqd[2][j][1](x), j=1..nops(eqd[2]));
                eqn := eqn + 1;
            end if
        end if; end do;
    end do;
    subs(op(values_table), [seq(res[j], j=1..(eqn-1))])
end proc;
