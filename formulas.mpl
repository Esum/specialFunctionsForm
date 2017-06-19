recseq := module ()

    description "Tools for recursive sequences";

    export rscreate, rsdiff, `rseq=rseq`, diffeqtors, rstodiffeq, is_rssol, bound;

    #rscreate
    # Input:
    #  rec_eq: the equation of the recursive formula
    #  u: the name of the sequence
    #  n: the index variable
    #  cis(={}): initial conditions for the sequence u(n)
    # Output: a formatted reprensentation of the recursive sequence u(n)
    #
    rscreate := proc(rec_eq, u, n, cis:={})
        [rec_eq, u, n, cis];
    end proc;

    #rsdiff
    # Input:
    #  rs: a recursive sequence u(n) from rscreate
    # Output: the recursive sequence associated to u(n), i.e. (n+1) * u(n+1)
    #
    rsdiff := proc(rs, proof:=0)
        local rs_op, u, n, cis, i, diffcis, max_order, orders, common_factors;
        u := rs[2];
        n := rs[3];
        rs_op := [op(rs[1])];
        cis := rs[4];
        if proof > 0 then
            printf("The sequence %a satisfies the recursive relation %a = 0, with initial conditions %a\n", u(n), rs[1], cis)
        end if;
        # orders is the list of the i such that u(n+i) appears in rs
        if op(0, rs_op) = u then
            orders := [op(rs_op)-n]
        elif op(0, rs_op) = `*` then
            orders := [op([op(rs_op)][-1])]
        else 
            orders := [seq(0, i=1..nops(rs_op))];
            for i from 1 to nops(rs_op) do
                if op(0, rs_op[i]) = `*` then orders[i] := op([op(rs_op[i])][-1])-n else orders[i] := op(rs_op[i])-n end if
            end do
        end if;
        max_order := max(orders);
        if min(orders) = 0 then
            # shift the orders
            orders := [seq(orders[j]+1, j=1..nops(orders))];
            rs_op := subs(n=n+1, rs_op)
        end if;
        for i from 1 to nops(rs_op) do
            # mutiply rs by the correct polynomial to compute the recursive equation of the derivative
            if op(0, rs_op[i]) = `*` then
                rs_op[i] := subsop(nops(rs_op[i])=u(n+orders[i]-1), rs_op[i]);
            else 
                rs_op[i] := u(n+orders[i]-1)
            end if;
            rs_op[i] := mul(n+orders[j], j in remove(`=`, [seq(j, j=1..nops(orders))], i)) * rs_op[i]
        end do;
        # simplify the new equation
        common_factors := {op(rs_op[1])};
        for i from 2 to nops(rs_op) do if op(0, rs_op[i]) = `*` then
            common_factors := common_factors intersect {op(rs_op[i])}
        else
            common_factors := {}
        end if end do;
        for i from 1 to nops(rs_op) do
            rs_op[i] := remove(`in`, rs_op[i], common_factors)
        end do;
        # find the next initial condition if needed
        cis := cis union solve(subs(op(cis), subs(n=0, rs[1])), {u(max_order)});
        diffcis := {};
        for i in cis do
            if 0 < op(op(i)[1]) and nops(diffcis) < max_order then
                diffcis := diffcis union {u(op(op(i)[1])-1)=(op(op(i)[1]))*op(i)[2]}
            end if
        end do;
        if proof > 0 then
            printf("Thus the sequence of the derivative %a satisfies %a, with %a.\n", (n+1)*u(n+1), `+`(op(rs_op)), diffcis)
        end if;
        rscreate(`+`(op(rs_op)), u, n, diffcis)
    end proc;

    #`rseq=rseq`
    # Input:
    #  rs1: a recursive sequence
    #  rs2: a recursive sequence
    # Output: false if rs1 <> rs2
    #
    `rseq=rseq` := proc(rs1, rs2)
        local eq1, u, n, cisu, eq2, v, m, cisv;
        eq1 := rs1[1];
        u := rs1[2];
        n := rs1[3];
        cisu := rs1[4];
        eq2 := rs2[1];
        v := rs2[2];
        m := rs2[3];
        cisv := rs2[4];
        eq2 := subs(v=u, m=n, eq2);
        cisv := subs(v=u, cisv);
        eq1-eq2 = 0 and cisu = cisv
    end proc;

    #diffeqtors
    # Input:
    #  deq: a differential equtation
    #  y(x): the function of deq
    #  u: the name of recursive sequence
    #  n: the index vairable
    # Output: the recursive sequence of power series that is solution of deq
    #
    diffeqtors := proc(deq, y, u, n)
        local rs, cis, x0;
        if type(deq, set) then
            # initial condititions are given at x0
            x0 := op([op([op(deq)][-1])][1]);
            cis := {seq(op(0, [op(i)][1])(0)=[op(i)][2], i in [op(deq)][2..])};
            rs := gfun[diffeqtorec]({DETools[diffop2de](subs(op(y)=op(y)+op([op([op(deq)][-1])][1]), DETools[de2diffop]([op(deq)][1], y, [Dx, op(y)])), y, [Dx, op(y)])} union cis, y, u(n))
        else
            rs := gfun[diffeqtorec](deq, y, u(n))
        end if;
        if type(rs, set) then
            cis := {seq([op(rs)][i], i=2..nops(rs))};
            rs := [op(rs)][1]
        else
            cis := {}
        end if;
        if op(0, rs) =  `*` then
            rs := factor(rs)
        elif op(0, rs) = `+` then
            rs := `+`(seq(factor([op(rs)][i]), i=1..nops(rs)))
        end if;
        rscreate(rs, u, n, cis)
    end proc;

    #rstodiffeq
    # Input:
    #  rs: a recursive sequence
    #  y(x): the function of the differential equation
    # Output: a differential equation that is canceled by the power series of the sequence rs
    #
    rstodiffeq := proc(rs, y)
        gfun[rectodiffeq]({rs[1]} union rs[4], rs[2](rs[3]), y);
    end proc;

    #is_rssol
    # Input:
    #  rs: a recursive sequence
    #  expr: an expression
    #  n: the index variable
    # Output: false if expr(n) is not solution of rs
    #
    is_rssol := proc(rs, expr, n)
        local ci;
        for ci in rs[4] do
            if eval(subs(n=op([op(ci)][1]), expr)) <> [op(ci)][2] then
                return false
            end if
        end do;
        simplify(subs(rs[2]=proc (m) options operator, arrow; subs(n=m, expr) end proc, rs[1])) = 0
    end proc;

    #bound
    # Input:
    #  rs: a recursice sequence
    # Output: a bound for rs
    #
    bound := proc(rs)
        gfun[NumGfun][bound_rec]({rs[1]} union rs[4], rs[2](rs[3]));
    end proc;

end module;

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


derive := module ()

    description "Formal derivation of special functions with their differential equation";

    export Derive;

    local derive_node, get_diffeq, get_derivative;

    #get_diffeq
    #  Essentially a inverse of diffeq_table
    #
    get_diffeq[sin] := (D@@2)(_y)(_x) + _y(_x);
    get_diffeq[cos] := (D@@2)(_y)(_x) + _y(_x);
    get_diffeq[sinh] := (D@@2)(_y)(_x) - _y(_x);
    get_diffeq[cosh] := (D@@2)(_y)(_x) - _y(_x);
    get_diffeq[exp] := (D)(_y)(_x) - _y(_x);
    get_diffeq[ln] := _x*(D@@2)(_y)(_x) + (D)(_y)(_x);
    get_diffeq[arctan] := (_x^2 + 1)*(D@@2)(_y)(_x) + 2*_x*(D)(_y)(_x);
    get_diffeq[erf] := (D@@2)(_y)(_x) + 2*_x*(D)(_y)(_x);
    get_diffeq[erfc] := (D@@2)(_y)(_x) + 2*_x*(D)(_y)(_x);

    #derive_node
    # Input:
    #  f: a function
    #  deq: a differential equation satisfied by f
    #  y: the function variable of deq
    #  x: the variable of deq
    #  proof(=0): print a proof of the derivation
    #  remember(=false): remember the derivative for the next call with f
    # Output: The derivative of f at point x
    #
    derive_node := proc(f, deq, y, x, proof:=0, remember:=false)
        local gdeq, ddeq, rs, df, cis, basis, in_basis, i, sys;
        if assigned(get_derivative[f]) then
            return get_derivative[f](x)
        end if;
        gdeq := subs(x=_x, y=_y, deq);
        if assigned(diffeqs_table[gdeq]) then
            basis := diffeqs_table[gdeq][1..-2];
            rs := [seq(recseq[diffeqtors]({gdeq} union {op(basis[i][2])}, _y(_x), u, n), i=1..nops(basis))];
            in_basis := 0;
            for i from 1 to nops(basis) do
                if f = basis[i][1] then
                    if proof > 0 then
                        printf("The function %a, satisfies %a with initial conditions %a\n", f, deq, basis[i][2]);
                        printf("Thus its associated sequence is %a = 0 with initial conditions %a\n", rs[i][1], rs[i][4])
                    end if;
                    df := recseq[rsdiff](rs[i], proof);
                    if df[1] = rs[1][1] then
                        in_basis := i
                    end if
                end if
            end do;
            if in_basis > 0 then
                # the derivative can be expressed in the basis of solutions of deq
                cis := {};
                for i from 1 to nops(basis) do
                    cis := cis union {op([op(df[4])][i])[2] - add(l[j]*[op([op(rs[j][4])][i])][2], j=1..nops(basis))}
                end do;
                # do a gaussian elimination to find the coefficients in the basis
                cis := solve(cis, {seq(l[j], j=1..nops(basis))});
                df := subs(op(cis), add(l[j] * basis[j][1] , j=1..nops(basis)));
                if proof > 0 then
                    printf("The sequence of %a' yields the same differential equation as %a, so the derivative is %a\n", f, f, df)
                end if;
                if remember then
                    get_derivative[f] := df
                end if;
                return df(x)
            else
                ddeq := recseq[rstodiffeq](df, y(x));
                if PDETools[difforder](ddeq) = 0 then
                    # the value of y(x) can be computed directly by isolating y(x) in the equation
                    if proof > 0 then
                        printf("The differential equation %a associated to the sequence of %a' is of order 0\n", ddeq, f)
                    end if;
                    df := subs(x=x-diffeqs_table[gdeq][-1], solve(ddeq, y(x)));
                    if proof > 0 then
                        printf("So %a'(%a) = %a\n", f, x, df)
                    end if;
                    if remember then
                        get_derivative[f] := proc (_) options operator, arrow; subs(x=_, df) end proc
                    end if;
                    return df
                elif PDETools[difforder](ddeq) = 1 then
                    cis := [op(ddeq)][2];
                    ddeq := [op(ddeq)][1];
                    ddeq := collect(ddeq/y(x), diff(y(x), x));
                    df := solve(ddeq, diff(y(x), x)/y(x));
                    if type(df, polynom) then
                        # df is a polynomial
                        sys := eval(subs(x=0, int(df, x=0..x)));
                        df := exp(int(df, x=0..x));
                        df := subs(x=x-diffeqs_table[gdeq][-1], [op(cis)][2]/exp(sys) * df);
                        if proof > 0 then
                            printf("The derivative of %a(%a) is %a\n", f, x, df)
                        end if;
                        if remember then
                            get_derivative[f] := proc (_) options operator, arrow; subs(x=_, df) end proc
                        end if;
                        return df;
                    end if
                end if
            end if
        end if;
    end proc;

    #Derive
    # Input:
    #  expr: the expression to derive
    #  x: the variable of the function
    #  proof(=0): print a proof of the derivation
    #  remember(=false): remember special functions derivatives
    # Output: the derivative d/dx(expr)
    #
    Derive := proc(expr, x, proof:=0, remember:=false)
        local res;
        if type(expr, ratpoly) then
            # We know how to differentiate a rational fraction
            res := diff(expr, x);
            if proof > 1 then
                printf("%a is rational fraction in %a, thus its derivative is: %a\n", expr, x, res)
            end if;
            return res
        elif op(0, expr) = `+` then
            return `+`(op(map(Derive, [op(expr)], x, proof)))
        elif op(0, expr) = `*` then
            return `+`(seq(`*`(Derive([op(expr)][i], x), seq([op(expr)][j], j in remove(`=`, [seq(j, j=1..nops(expr))], i))), i=1..nops(expr)))
        elif op(0, expr) = `-` then
            return -(Derive(op(expr), x))
        elif op(0, expr) = `^` then
            if [op(expr)][2] = -1 then
                return -(Derive([op(expr)][1], x, proof))/([op(expr)][1]*[op(expr)][1])
            else
                return Derive(exp([op(expr)][2] * ln([op(expr)][1])), x, proof)
            end if
        elif assigned(get_diffeq(op(0, expr))) then
            # the node is a special function that we know
            return Derive(op(expr), x)*subs(_x=op(expr), derive_node(op(0, expr), get_diffeq[op(0, expr)], _y, _x, proof, remember))
        end if;
    end proc;

end module;


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

#proof_intro
# Input:
#  f: a function
#  x: a variable
#  eq: an expression
#  basis: a basis of solutions in the format of diffeqs_table
# Output: NULL (prints the begining of the proof of the symmetry for f(eq))
# 
proof_intro := proc(f, x, eq, basis, order)
    printf("(%a ∘ h) = %a ↦ %a(%a) satisfies the same differential equation as %a\n", f, x, f, eq, f);
    printf("Which has a basis of solutions : %a\n", [seq(basis[j][1], j=1..order)]);
    printf("(%a ∘ h) has the following initial conditions :\n", f);
end proc;

#dsolve_symmetries
# Input:
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
    local order, eq, gdeq, sing, cis, i, value, Dx, res, basis, sol, coefs, eqn;
    order := PDETools[difforder](deq);
    Dx := proc (_) options operator, arrow; derive[Derive](_, x, 1, true) end proc;
    eqn := 1;
    for eq in symmetric_diffeqs(deq, y, x, a) do
        eq := subs(op(conditions), eq);
        sing := solve(denom(eq)=0, {x});
        if sing <> NULL then
            sing := op(op(sing))[2]
        end if;
        gdeq := subs(x=_x, y=_y, deq);
        if assigned(diffeqs_table[gdeq]) then
            basis := diffeqs_table[gdeq];
            if proof then
                if basis[-1] = sing then
                    printf("The function h = %a ↦ %a has a singularity at %a = %a\n", x, eq, x, subs(op(conditions), -a[2,2]/a[2,1]))
                end if;
                proof_intro(f, x, eq, basis, order);
                if basis[-1] = sing then
                    printf("\tOn ]%a, +∞[:\n", basis[-1])
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
                if basis[-1] = sing then
                    res[eqn] := [``(f)(eq) = add(subs(op(sol), l[j])*basis[j][1](x), j=1..order), x > basis[-1]];
                    if proof then
                        printf("\t%a(%a) = %a when %a > %a\n\n", f, eq, op(res[eqn][1])[2], x, basis[-1])
                    end if
                else
                    res[eqn] := ``(f)(eq) = add(subs(op(sol), l[j])*basis[j][1](x), j=1..order);
                    if proof then
                        printf("\t%a(%a) = %a\n\n", f, eq, op(res[eqn])[2])
                    end if
                end if;
                eqn := eqn + 1
            end if;
            if basis[-1] = sing then
                cis := {};
                if proof then
                    printf("\tOn ]-∞, %a[:\n", basis[-1])
                end if;
                for i from 1 to order do
                    if proof then
                        printf("\t\tlim (%a ∘ h)^(%d)(%a) = %a\n\t%a -> %a, %a < %a\n", f, i-1, eq, eval(limit((Dx@@(i-1))(f(eq)), x=subs(op(conditions), -a[2,2]/a[2,1]), left)), x, basis[-1], x, basis[-1])
                    end if;
                    cis := {op(cis), eval(limit((Dx@@(i-1))(f(eq)), x=subs(op(conditions), -a[2,2]/a[2,1]), left)) - add(l[j]*[op(basis[j][2][i])][2], j=1..order)}
                end do;
                if sol <> NULL then
                    res[eqn] := [``(f)(eq) = add(subs(op(sol), l[j])*basis[j][1](x), j=1..order), x < basis[-1]];
                    if proof then
                        printf("Its coefficients in the basis are %a, hence :\n", sol);
                        printf("\t%a(%a) = %a when %a < %a\n\n", f, eq, op(res[eqn][1])[2], x, basis[-1])
                    end if;
                    eqn := eqn + 1
                end if
            end if
        elif type(f, set) then

        end if
    end do;
    subs(op(values_table), [seq(res[j], j=1..(eqn-1))])
end proc;

#hypergeom_symmetries
# Input:
#  a: a formal parameter
#  b: a formal parameter
#  c: a formal parameter
#  h: a list of 2 lists of 3 paramters
# Output: a list of expression and conditions on a, b and c that are equal to 2F1(a,b;c, (h[1,1]+h[1,2]*_z+h[1,3]*_z^2)/(h[2,1]+h[2,2]*_z+h[2,3]*_z^2))
#
hypergeom_symmetries := proc(a, b, c, h)
    local deq, deq2, deq_polypow, deq_sym, deq_sym2, sol, coef, facto, sys, cis, cond1, cond2, constant, hf, d, u, v, w, l, _y, _z, D_z, valid;
    deq := _z*(1-_z)*(D@@2)(_y)(_z) + (c - (a + b + 1)*_z)*D(_y)(_z) - a*b*_y(_z);
    deq2 := DETools[de2diffop](_z*(1-_z)*(D@@2)(_y)(_z) + (w - (u + v + 1)*_z)*D(_y)(_z) - u*v*_y(_z), _y(_z), [D_z, _z]);
    deq_polypow := {(d[1]*_z+d[2])*D(_y)(_z) - d[1]*d[3]*_y(_z), _y(0) = d[2]^d[3]};
    if h[1,1] <> 0 then
        print("h[1,1] must be null");
        return NULL
    end if;
    hf := (h[1,1]+h[1,2]*_z+h[1,3]*_z^2)/(h[2,1]+h[2,2]*_z+h[2,3]*_z^2);
    deq_sym := gfun[algebraicsubs](deq, gfun[algfuntoalgeq](hf, _y(_z)), _y(_z));
    deq_sym := gfun[`diffeq*diffeq`](deq_sym, deq_polypow, _y(_z));
    cis :=  [_y(0) = d[2]^d[3], D(_y)(0) = d[2]^d[3] * subs(_z=0, diff(hf, _z)) * a*b/c + d[1]*d[3] * d[2]^(d[3]-1)];
    deq_sym := DETools[de2diffop](deq_sym, _y(_z), [D_z, _z]);
    if rem(lcoeff(deq_sym, D_z), _z*(1-_z), _z) <> 0 then
        print("No solution found");
        return NULL
    end if;
    facto := quo(lcoeff(deq_sym, D_z), _z*(1-_z), _z);
    sys := {};
    for coef in [coeffs(deq_sym, D_z)] do
        sys := sys union {coeffs(rem(coef, facto, _z), _z)}
    end do;
    for cond1 in [solve(sys, {a, b, c, d[1], d[2], d[3]})] do
        deq_sym2 := subs(op(cond1), deq_sym);
        deq_sym2 := PolynomialTools[FromCoefficientList](map(quo, PolynomialTools[CoefficientList](deq_sym2, D_z), facto, _z), D_z);
        sys := {op(map(coeffs, [coeffs(deq_sym2-deq2, D_z)], _z))} union {subs(op(cond1), op(2, cis[1]) - 1), subs(op(cond1), op(2, cis[1])*u*v/w - op(2, cis[2]))};
        for cond2 in [solve(sys, {u, v, w, d[1], d[2], d[3]})] do
            valid := true;
            for sol in cond2 do
                if has(op(2, sol), u) or has(op(2, sol), v) or has(op(2, sol), w) then
                    valid := false
                end if
            end do;
            if valid then
                print(subs(op(map(proc (_) options operator, arrow; subsop(2=subs(op(cond1), op(2, _)), _) end proc, [op(cond2)])), (d[1]*_z + d[2])^(d[3]) * F[2,1](u, v, w, _z)), select(proc (_) options operator, arrow; op(1, _) in {a, b, c} end proc, [op(cond1)]))
            end if
        end do
    end do
end proc;

#diffeq_singularities
# Input:
#  deq: a linear differential equation with polynomials as coefficiens
#  y: the function variable of deq
#  x: the variable of deq
# Output: the list of singularities of deq
#
diffeq_singularities := proc(deq, y, x)
    return solve([PDETools[dcoeffs](deq, y(x))][1], x)
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