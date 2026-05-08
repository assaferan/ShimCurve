// Number of positive divisors (internal helper).
function e(n)
    assert n ge 1;
    if n eq 1 then return 1; end if;
    return &*[Valuation(n, p) + 1 : p in PrimeDivisors(n)];
end function;


intrinsic IsDNew(D::RngIntElt, M::RngIntElt) -> BoolElt
{Returns true iff the newform of exact level M is D-new, i.e. p | M for all p | D.}
    return &and[IsDivisibleBy(M, p) : p in PrimeDivisors(D)];
end intrinsic;


intrinsic JLDecomposition(D::RngIntElt, N::RngIntElt, X::Assoc : g:=-1) -> SeqEnum, SeqEnum, SeqEnum, SeqEnum, RngIntElt, BoolElt
{Returns forms, mult, dims, conductor, rank, is_simple for the JL isogeny decomposition of J_0^D(N).
 forms[i] is the LMFDB label of the i-th newform, appearing with multiplicity mult[i].
 dims[i] is the dimension of the i-th newform.
 conductor is the prime factorization of prod_i level(f_i)^(mult[i]*dims[i]), as a flat [p,e,...] list.
 Only newforms with trivial character and nonzero multiplicity are included.
 If g is provided, asserts that the weighted sum of dimensions equals g.
 is_simple is true if the Jacobian is simple (one form with multiplicity 1).}
    AmbientLevel := D*N;

    labels := [];
    mults := [];

    for label in Keys(X) do
        f := X[label];
        M := f`level;

        if not IsDivisibleBy(AmbientLevel, M) then continue; end if;
        if f`cond ne 1 then continue; end if;
        if not IsDNew(D, M) then continue; end if;

        Append(~labels, label);
        Append(~mults, e(AmbientLevel div M));
    end for;

    perm := Sort([1..#labels], func<i,j | CMFLabelCompare(labels[i], labels[j])>);
    forms := [labels[i] : i in perm];
    mult := [mults[i] : i in perm];
    if #forms eq 0 then return [], [], [], [], 0, true; end if;
    dims := [X[forms[j]]`dim : j in [1..#forms]];
    if g ne -1 then assert &+[dims[j]*mult[j] : j in [1..#forms]] eq g; end if;
    rank := &+[X[forms[j]]`rank * mult[j] : j in [1..#forms]];
    is_simple := #forms eq 1 and mult[1] eq 1;
    total_cond := &*[X[forms[j]]`level ^ (mult[j] * dims[j]) : j in [1..#forms]];
    conductor := Factorization(total_cond);

    return forms, mult, dims, conductor, rank, is_simple;
end intrinsic;


intrinsic ShimuraNewformDecomposition(B::AlgQuat, X::Assoc, H::GrpMat, g::RngIntElt, N::RngIntElt
        : G:=-1, i_new:=-1, j_new:=-1, I:=-1, J:=-1) -> SeqEnum, SeqEnum, SeqEnum, SeqEnum, RngIntElt, BoolElt
{Returns forms, mult, dims, conductor, rank, is_simple for the newform decomposition of the Shimura curve Jacobian.
 Identifies the decomposition by matching Hecke traces via a linear system.
 dims[i] is the dimension of the i-th newform.
 conductor is the prime factorization of prod_i level(f_i)^(mult[i]*dims[i]), as a flat [p,e,...] list.
 is_simple is true if the Jacobian is simple (one form with multiplicity 1).
 Return codes for rank: -1 genus 0, -2 linear system error, -3 cutoff reached.}
    D := &*RamifiedPrimes(B);
    if g eq 0 then return [], [], [], [], -1, true; end if;
    Z := [r:r in X|r`dim le g and r`level le D*N^2 and r`cond le N];
    m := Min([#r`traces:r in Z]);
    cutoff := #[p : p in PrimesInInterval(1,NthPrime(m))];
    maxi := Ceiling(2*#Z+10);  B0:=1;
    t := [g]; P := [];
    while true do
        if maxi gt cutoff then maxi := cutoff; end if;
        maxp := NthPrime(maxi);
        Q := [p : p in PrimesInInterval(B0,maxp)|Gcd(N*D,p) eq 1];  B0 := maxp+1;
        print(Q);
        P cat:= Q;
        if Gcd(D, N) eq 1 then
            t cat:= HTraces(B, H, N, Q);
        else
            t cat:= HTraces(B, H, N, Q:G:=G,i_new:=i_new,j_new:=j_new,I:=I,J:=J);
        end if;
        b := Vector(t);
        A := Matrix([[r`dim] cat [r`traces[p]:p in P]:r in Z]);
        try x,K := Solution(A,b); catch e print(A); print(b); print(e);; return [], [], [], [], -2, false; end try;
        if Dimension(K) eq 0 then
            print(A); print(b);
            rawmult := [Integers()!x[i]:i in [1..Degree(x)]];
            forms := Sort([Z[i]`label:i in [1..Degree(x)] | rawmult[i] ne 0], CMFLabelCompare);
            mult := [rawmult[i]:i in [1..Degree(x)] | rawmult[i] ne 0];
            dims := [X[forms[j]]`dim:j in [1..#forms]];
            assert &+[dims[j]*mult[j]:j in [1..#forms]] eq g;
            rank := &+[X[forms[j]]`rank*mult[j]:j in [1..#forms]]; // note that cmfdata.txt stores the rank of the Galois orbit
            is_simple := #forms eq 1 and mult[1] eq 1;
            total_cond := &*[X[forms[j]]`level ^ (mult[j] * dims[j]) : j in [1..#forms]];
            conductor := Factorization(total_cond);
            return forms, mult, dims, conductor, rank, is_simple;
        end if;
        if maxi eq cutoff then return [], [], [], [], -3, false; end if;
        maxi := Ceiling(1.5*maxi);
    end while;
end intrinsic;
