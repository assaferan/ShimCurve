// Authors: Santiago Arango-Pineros, Oana Padurariu, Tristan Phillips, Freddy Saia
// Date: 02/08/2024

// Preliminary arithmetic functions

// SqFreePart
// given positive integer m, returns the sqfree part of m
intrinsic SqFreePart(m::RngIntElt) -> RngIntElt
    {Returns the square free part of a positive integer m.}
    
    assert m ge 1;
    S := 1;
    for pair in Factorization(m) do
        v := Valuation(m,pair[1]);
        if (v mod 2) eq 1 then 
            S := S*pair[1];
        end if;
    end for;

    return S;
end intrinsic; 

intrinsic PhiFromFactorization(N::RngIntElt,F::RngIntEltFact) -> RngIntElt
    {Given positive integer N, and the factorization of N, computes the Euler totient phi(N)}

    assert N ge 1;
    if #F eq 0 then
        return 1;
    else
        return IntegerRing()!(N*(&*[1-1/(F[i][1]) : i in [1..#F]]));
    end if;
end intrinsic;


intrinsic PsiFromFactorization(N::RngIntElt,F::RngIntEltFact) -> RngIntElt
    {Given positie integer N, and the factorization of N, computes the Dedekind psi function psi(N)}

    assert N ge 1;
    if #F eq 0 then
        return 1;
    else
        return IntegerRing()!(N*(&*[1+1/(F[i][1]) : i in [1..#F]]));
    end if;
end intrinsic;


intrinsic HallDivisors(N::RngIntElt) -> Any
    {Given a positive integer N, returns a list of divisors d | n such that GCD(d,N/d) = 1.}

    assert N ge 1;
    return [d : d in Divisors(N) | GCD(d,Integers()!(N/d)) eq 1];
end intrinsic;


intrinsic OggPsi_p(N::RngIntElt,p::RngIntElt) -> Any
    {Given positive integer N and a prime p, computes OggPsi_p(N) as in Ogg83 Thm 2.}

    assert N ge 1;
    k := Valuation(N,p);
    if k eq 0 then 
        return 1;
    else 
        return p^k + p^(k-1); 
    end if;
end intrinsic; 



// Signature functions

intrinsic e2FromFactorization(Factorization_D::RngIntEltFact,Factorization_N::RngIntEltFact, N::RngIntElt) -> Any
    {Given factorizations of a rational quaternion discriminant D and a natural number N which is coprime to D, returns the number of elliptic points of order 2 in X0(D;N)}

    if (N mod 4) eq 0 then
        return 0;
    else
        P := 1;
        for i in [1..#Factorization_D] do
            P := P*(1-KroneckerSymbol(-4,Factorization_D[i][1]));
        end for;
        for i in [1..#Factorization_N] do
            P := P*(1+KroneckerSymbol(-4,Factorization_N[i][1]));
        end for;
        return P;
    end if;
end intrinsic;


intrinsic e3FromFactorization(Factorization_D::RngIntEltFact,Factorization_N::RngIntEltFact, N::RngIntElt) -> Any
    {Given factorizations of a rational quaternion discriminant D and a natural number N which is coprime to D, returns the number of elliptic points of order 3 in X0(D;N)}

    if (N mod 9) eq 0 then
        return 0;
    else
        P := 1;
        for i in [1..#Factorization_D] do
            P := P*(1-KroneckerSymbol(-3,Factorization_D[i][1]));
        end for;
        for i in [1..#Factorization_N] do
            P := P*(1+KroneckerSymbol(-3,Factorization_N[i][1]));
        end for;
        return P;
    end if; 
end intrinsic;


intrinsic SignatureX0DN(D::RngIntElt,N::RngIntElt) -> Any
    {Given factorizations of a rational quaternion discriminant D and a natural number N which is coprime to D, returns the signature of X0(D;N)}

    FD := Factorization(D);
    FN := Factorization(N);
    e2 := e2FromFactorization(FD,FN,N);
    e3 := e3FromFactorization(FD,FN,N);
    g := IntegerRing()!(1+PhiFromFactorization(D,FD)*PsiFromFactorization(N,FN)/12 - e2/4 - e3/3);
    return [* g,[2,e2],[3,e3] *];
end intrinsic;



intrinsic OggCountLocalEmbeddings(D::RngIntElt,N::RngIntElt,p::RngIntElt,delta_K::RngIntElt,f::RngIntElt) -> RngIntElt
    {Counts number of local embeddings of an order R of discriminant f^2*delta_K into an order of level N in a quaternion algebra B of discriminant D, via Ogg83 Theorem 2.}

    assert IsDivisibleBy(D*N,p);
    
    if (f mod p eq 0) then 
        symbol_R_p := 1;
    else
        symbol_R_p := KroneckerSymbol(delta_K,p);
    end if; 

    if (D mod p) eq 0 then // case i
        return 1 - symbol_R_p;

    elif (N mod p) eq 0 then 

        k := Valuation(N,p); //3
        l := Valuation(f,p); //0

        if k eq 1 then // case ii
            return 1 + symbol_R_p;

        elif k ge (2+2*l) then  // case iii a
            if KroneckerSymbol(delta_K,p) eq 1 then
                return 2*OggPsi_p(f,p); 
            else
                return 0;
            end if; 

        elif k eq (1+2*l) then  // case iii b
            if KroneckerSymbol(delta_K,p) eq 1 then
                return 2*OggPsi_p(f,p);
            elif KroneckerSymbol(delta_K,p) eq 0 then
                return p^l;
            else 
                return 0;
            end if;

        elif k eq 2*l then  // case iii c
            return p^(l-1)*(p+1+KroneckerSymbol(delta_K,p));

        elif (f^2 mod p*N) eq 0 then // case iii d
            if (k mod 2) eq 0 then
                return p^k+p^(k-1);
            else
                return 2*p^k;
            end if;

        end if;
    end if;
end intrinsic;


intrinsic OggCountFixedPoints(D::RngIntElt,N::RngIntElt,m::RngIntElt,delta_K::RngIntElt,f::RngIntElt) -> Any
    {Given a quaternion discriminant D, a positive integer N coprime to D, and m || DN, delta_K, and f, computes number of f^2*delta_K-CM fixed points of w_m on X_0(D;N) by Eichler`s Theorem, see Thm 1 in Ogg83 and Eq. 4 in Ogg83.}

    P := 1;
    for pair in Factorization(Integers()!(D*N/m)) do 
        p := pair[1];
        P := P*OggCountLocalEmbeddings(D,N,p,delta_K,f);
    end for;

    return ClassNumber(delta_K*f^2)*P;
end intrinsic;


intrinsic SignatureX0DNmodAtkinLehnerElement(D::RngIntElt,N::RngIntElt,m::RngIntElt) -> Any
    {Given a quaternion discriminant D, a positive integer N coprime to D, and a Hall divisor m || DN, outputs the signature of the quotient X_0(D;N)/<w_m> in the form [* genus, elliptic_pts *] where elliptic_pts is a list of pairs [ord, number] indicating that this quotient curve has number elliptic points with stabilizer of order ord. The CM orders of fixed points are given by Ogg83, and the genus is computed by Riemann--Hurwitz (see Ogg83 Eqn 3). The m=1 case is allowed, corresponding to the trivial quotient X_0(D;N)}

    assert IsSquarefree(N);
    assert GCD(D,N) eq 1;

    sig := SignatureX0DN(D,N);
    g := sig[1]; // genus of X_0(D;N)
    e2 := sig[2][2]; // number of order 2 elliptic pts on X_0(D;N)
    e3 := sig[3][2]; // number of order 3 elliptic pts on X_0(D;N)

    // initializing elliptic point counts on the quotient in case there are no -3 or -4 CM points fixed by w_m
    s4 := 0;
    s6 := 0;

    if m eq 1 then
        return [*g,[2,e2],[3,e3],[4,0],[6,0]*];

    elif m eq 2 then
        s4 := OggCountFixedPoints(D,N,m,-4,1); // number of elliptic points of order 4 on the quotient
        s2 := OggCountFixedPoints(D,N,m,-8,1); // number of elliptic points of order 2 on the quotient

        fixed_number := s4 + s2;

        s3 := Integers()!(e3/2); // number of elliptic points of order 3 on the quotient

    elif m eq 3 then // have -3-CM fixed points in this case

        s6 := OggCountFixedPoints(D,N,m,-3,1); // number of elliptic points of order 6 on the quotient
        s3 := 0; // number of elliptic points of order 3 on the quotient
        fixed_12 := OggCountFixedPoints(D,N,m,-3,2); // number of elliptic points of order 2 on the quotient

        fixed_number := s6 + fixed_12;

        s2 := Integers()!(e2/2) + fixed_12; // number of elliptic points of order 2 on the quotient


    elif (m mod 4) eq 3 then
        disc_K := -1*SqFreePart(m); // K = Q(sqrt(-m))
        _,f := IsSquare(Integers()!(m/SqFreePart(m)));

        fixed_number := OggCountFixedPoints(D,N,m,disc_K,f) + OggCountFixedPoints(D,N,m,disc_K,2*f);

        s3 := Integers()!(e3/2); // number of elliptic points of order 3 on the quotient
        s2 := Integers()!(e2/2) + fixed_number; // number of elliptic points of order 2 on the quotient

    else
        disc_K := -4*(SqFreePart(m)); // K = Q(sqrt(-m))
        _,f := IsSquare(Integers()!(m/SqFreePart(m)));

        fixed_number := OggCountFixedPoints(D,N,m,disc_K,f);

        s3 := e3; // number of elliptic points of order 3 on the quotient
        s2 := Integers()!(e2/2) + fixed_number; // number of elliptic points of order 2 on the quotient

    end if;

    g_quotient := (1/4)*(2*g+2 - fixed_number);
    return [* g_quotient,<2,s2>,<3,s3>, <4,s4>, <6,s6> *];
end intrinsic;


// Signature tables

intrinsic SignatureTable(DBound::RngIntElt, NBound::RngIntElt) -> Any
    {Outputs signature table of the shimura curves X0(D;N)/<w_m> and for all Atkin-Lehner elements w_m, where m is a Hall divisor of N*D.}

    filename := Sprintf("~/Desktop/ShimCurve/data/signature-tables/SignatureTableSingleALX0DN_%o_%o.txt", DBound, NBound);
    Write(filename, Sprint("Discriminant ? Level ? w_m ? Genus ? Elliptic Point Counts"));
    // we only want D square-free, with an even number of prime factors.
    for D in [D : D in [6..DBound] | MoebiusMu(D) eq 1] do
        // we want N that are coprime to D and square-free.
        for N in [M : M in [1..NBound] | GCD(D,M) eq 1 and IsSquarefree(M)] do
            for m in HallDivisors(D*N) do
                signature := SignatureX0DNmodAtkinLehnerElement(D,N,m);
                g := signature[1];
                Write(filename, Sprintf("%o ? %o ? %o ? %o ? %o,%o,%o,%o ", D, N, m, g, signature[2], signature[3], signature[4], signature[5]));
            end for;
        end for;
    end for;
    return Sprint("Signature table produced :)");
end intrinsic;