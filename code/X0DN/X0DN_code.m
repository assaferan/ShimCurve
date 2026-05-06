// Authors: Santiago Arango-Pineros, Oana Padurariu, Freddy Saia
// Date: 02/09/2024


//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Signatures of X_0(D;N) and X_0(D;N)/<w_m>
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////

// Preliminary arithmetic functions

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
    return IntegerRing()!(N*(&*([1] cat [1-1/(F[i][1]) : i in [1..#F]])));
end intrinsic;


intrinsic PsiFromFactorization(N::RngIntElt,F::RngIntEltFact) -> RngIntElt
    {Given positive integer N, and the factorization of N, computes the Dedekind psi function psi(N)}

    assert N ge 1;
    return IntegerRing()!(N*(&*([1] cat [1+1/(F[i][1]) : i in [1..#F]])));
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
    {Counts the number of local embeddings of the quadratic order R of discriminant f^2*delta_K into an order of level N in the quaternion algebra B of discriminant D, via Ogg83 Theorem 2.}

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
    {Given a quaternion discriminant D, a positive integer N coprime to D, a Hall divisor m || DN, a fundamental discriminant delta_K, and a CM conductor f, outputs the number of f^2*delta_K-CM fixed points of w_m on X_0(D;N) by Eichler`s Theorem, see Thm 1 in Ogg83 and Eq. 4 in Ogg83.}

    P := 1;
    for pair in Factorization(Integers()!(D*N/m)) do 
        p := pair[1];
        P := P*OggCountLocalEmbeddings(D,N,p,delta_K,f);
    end for;

    return ClassNumber(delta_K*f^2)*P;
end intrinsic;


intrinsic SignatureX0DNmodAtkinLehnerElement(D::RngIntElt,N::RngIntElt,m::RngIntElt) -> Any
    {Given a quaternion discriminant D, a positive integer N coprime to D, and the list of all non-trivial Hall divisors m || DN so that w_m is in the subgroup W of the full Atkin--Lehner group W_0(D;N), outputs the signature of the quotient X_0(D;N)/W in the form [* genus, elliptic_pts *] where elliptic_pts is a list of pairs [ord, number] indicating that this quotient curve has number elliptic points with stabilizer of order ord. The CM orders of fixed points are given by Ogg83, and the genus is computed by Riemann--Hurwitz (see Ogg83 Eqn 3). The m=1 case is allowed, corresponding to the trivial quotient X_0(D;N)}

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
    return [* g_quotient,[2,s2],[3,s3], [4,s4], [6,s6] *];
end intrinsic;



//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// CM Points on X^D_0(N), code from Saia22
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


intrinsic CMPointsXD0NPrimePower(D_Fact::RngIntEltFact, f::RngIntElt, d_K::RngIntElt, l::RngIntElt, a::RngIntElt) -> SeqEnum
{Given D_Fact the factorization of an indefinite rational quaternion discriminant D, a CM conductor f, fundamental imaginary quadratic discriminant d_K, prime l coprime to D, and non-negative integer a, returns a sequence of two sequences of sequences of the form [conductor, ram, degree, number], with the first sequence in the pair giving the sequences of index 2 subfields of ring class fields (as described in work of Jordan and Gonzalez--Rotger) corresponding to the order of discriminant f^2d_K which arise as residue fields of f^2d_K-CM points on X^D_0(l^a). The information here is the CM conductor of the ring class field, the ramification index w.r.t. X^D_0(l^a)-->X^D(1) (which is 1, 2, or 3), the degree over Q of the residue field, and the number of points with this residue field and ramification index. The second sequence gives the same ordered information for ring class fields corresponding to the same order which arise as residue fields of such points}

    assert a ge 0; 

    L := Valuation(f,l); // "level" of d in G_{K,l,f_0}
    f_0 := IntegerRing()!(f/l^L); // coprime to l part of conductor f

    // checking that D is a quaternion discriminant and l doesn't divide D
    if #D_Fact mod 2 eq 1 then 
        return "D not a quaternion discriminant!";
    end if;

    for pair in D_Fact do 
        if pair[2] gt 1 then 
            return "D not a quaternion discriminant!";
        end if; 

        if pair[1] eq l then 
            return "level not coprime to quaternion discriminant D";
        end if; 
    end for; 

    // checking that K splits the quaternion algebra and computing
    // b = number of primes dividing D which are inert in K
    b := 0; 
    for pair in D_Fact do 
        if KroneckerSymbol(d_K,pair[1]) eq 1 then 
            return "K does not split the quaternion algebra of discriminant D";
        elif KroneckerSymbol(d_K,pair[1]) eq -1 then 
            b := b+1; 
        end if;
    end for; 

    // initializing CM points list 
    points := [*[],[]*];

    // setting splitting behavior of l in K, to be used often
    symbol_l_K := KroneckerSymbol(d_K,l);

    // D_check: true if all primes dividing D are ramified in K, false otherwise 
    D_check := true; 
    for pair in D_Fact do
        if (KroneckerSymbol(d_K,pair[1]) eq -1) then
            D_check := false;
            break;
        end if;
    end for; 


    // Case all primes dividing D ramify in K
    if D_check eq true then 
        
        // 6.1: General Case 

        // Type I
        if (f_0^2*d_K eq -4) and (L eq 0) then
            Append(~points[1],[l^a*f,2,ClassNumber((l^(a)*f)^2*d_K),2^b]); 
        elif (f_0^2*d_K eq -3) and (L eq 0) then
            Append(~points[1],[l^a*f,3,ClassNumber((l^(a)*f)^2*d_K),2^b]); 
        else 
            Append(~points[1],[l^a*f,1,ClassNumber((l^(a)*f)^2*d_K),2^b]); 
        end if; 

        // Type II
        if a le L then
            Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]); 
        end if;

        if L eq 0 then 

            if (f_0^2*d_K eq -4) then 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[1],[l^(a-1)*f,2,ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,2,2*ClassNumber((l^(a-h)*f)^2*d_K),2^b]);
                    end for;
                end if;

            elif (f_0^2*d_K eq -3) then
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[1],[l^(a-1)*f,3,ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,3,2*ClassNumber((l^(a-h)*f)^2*d_K),2^b]);
                    end for;
                end if;

            else 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[1],[l^(a-1)*f,1,ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,1,2*ClassNumber((l^(a-h)*f)^2*d_K),2^b]);
                    end for;
                end if;
            end if; 

        end if;

        // Type X
        if (L ge 1) and (a gt L) and (symbol_l_K eq 1) then
            Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]); 
        end if;

        // 6.2: l > 2
        if l gt 2 then 

            // Type V
            if (L ge 2) then 
                for c in [1..Min(a-1,L-1)] do 
                    Append(~points[2],[l^(Max(a-2*c,0))*f,1,2*ClassNumber((l^(Max(a-2*c,0))*f)^2*d_K),2^b*((l-1)/2)*l^(Min(c,a-c)-1)]);
                end for;
            end if;

            // Type VI
            if (a gt L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                Append(~points[1],[l^(Max(a-2*L,0))*f,1,ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b]);
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*(l^(Min(L,a-L))-1)/2]);
            end if; 

            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 0) then 

                // Type VII
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-1)/2)*l^(Min(L,a-L)-1)]);

                // Type VIII
                Append(~points[1],[l^(Max(a-2*L-1,0))*f,1,ClassNumber((l^(Max(a-2*L-1,0))*f)^2*d_K),2^b]);
                if (a-L-1 gt 0) then 
                    Append(~points[2],[l^(Max(a-2*L-1,0))*f,1,2*ClassNumber((l^(Max(a-2*L-1,0))*f)^2*d_K),2^b*(l^(Min(L,a-L-1))-1)/2]);
                end if; 

            end if; 
             
            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 1) then

                // Type IX
                Append(~points[1],[l^(Max(a-2*L,0))*f,1,ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b]);
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-2)*l^(Min(L,a-L)-1)-1)/2]);

                // Type XI
                if (a ge L+2) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[l^(Max(a-2*L-h,0))*f,1,2*ClassNumber((l^(Max(a-2*L-h,0))*f)^2*d_K),2^b*(l-1)*l^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            end if;

        elif l eq 2 then 

            // 6.3: l=2, unramified 
            if symbol_l_K ne 0 then 

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if;

                // Type V_2
                if (L ge a) and (a ge 3) then 
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                if (a ge L+1) and (L ge 3) then 
                    Append(~points[1],[2^(Max(a-2*L+2,0))*f,1,ClassNumber((2^(Max(a-2*L+2,0))*f)^2*d_K),2^b*2]);
                    Append(~points[2],[2^(Max(a-2*L+2,0))*f,1,2*ClassNumber((2^(Max(a-2*L+2,0))*f)^2*d_K),2^b*(2^(Min(a-L+1,L-1)-2)-1)]);
                end if;

                // Type V_4
                for c in [2..Min(L-2,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^b*2^(Min(c,a-c)-2)]);
                end for; 

                // Type VI
                if (a ge L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*2^(Min(L,a-L)-1)]);
                end if;

                // Type XI
                if (a ge L+2) and (L ge 1) and (symbol_l_K eq 1) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[2^(Max(a-2*L-h,0))*f,1,2*ClassNumber((2^(Max(a-2*L-h,0))*f)^2*d_K),2^b*2^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            // 6.4: l=2, ord_2(d_K) = 2
            elif Valuation(d_K,2) eq 2 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^b*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[1],[2^(Max(a-2*L,0))*f,1,ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*2]);
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*(2^(Min(L,a-L)-2)-1)]);
                end if; 

                // Type VIII

                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^b*2^(Min(L,a-1-L)-1)]);
                    end if;

                end if;


            // 6.5: l=2, ord_2(d_K) = 3
            elif Valuation(d_K,2) eq 3 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^b*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[1],[2^(a-2)*f,1,ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^b*2^(Min(L,a-L)-2)]);
                end if; 

                // Type VIII
                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[1],[f,1,ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[1],[2^(Max(a-2*L-1,0))*f,1,ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^b*2]);
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^b*(2^(Min(L,a-1-L)-1)-1)]);
                    end if;
                end if;
            end if;
        end if;


    // Case some prime dividing D is inert in K
    elif D_check eq false then 

        // 6.1: General Case 

        // Type I
        if (f_0^2*d_K eq -4) and (L eq 0) then
            Append(~points[2],[l^a*f,2,2*ClassNumber((l^(a)*f)^2*d_K),2^(b)]); 
        elif (f_0^2*d_K eq -3) and (L eq 0) then
            Append(~points[2],[l^a*f,3,2*ClassNumber((l^(a)*f)^2*d_K),2^(b)]); 
        else 
            Append(~points[2],[l^a*f,1,2*ClassNumber((l^(a)*f)^2*d_K),2^(b)]); 
        end if; 

        // Type II
        if a le L then
            Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^(b)]); 
        end if;

        if L eq 0 then 

            if (f_0^2*d_K eq -4) then 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[2],[l^(a-1)*f,2,2*ClassNumber((l^(a-1)*f)^2*d_K),2^(b)]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,2,2*ClassNumber((l^(a-h)*f)^2*d_K),2^(b+1)]);
                    end for;
                end if;

            elif (f_0^2*d_K eq -3) then
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[2],[l^(a-1)*f,3,2*ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,3,2*ClassNumber((l^(a-h)*f)^2*d_K),2^(b+1)]);
                    end for;
                end if;

            else 
                // Type III
                if symbol_l_K eq 0 then 
                    Append(~points[2],[l^(a-1)*f,1,2*ClassNumber((l^(a-1)*f)^2*d_K),2^b]); 
                end if;

                // Type IV
                if symbol_l_K eq 1 then 
                    for h in [1..a] do 
                        Append(~points[2],[l^(a-h)*f,1,2*ClassNumber((l^(a-h)*f)^2*d_K),2^(b+1)]);
                    end for;
                end if;
            end if; 

        end if;

        // Type X
        if (L ge 1) and (a gt L) and (symbol_l_K eq 1) then
            Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^(b+1)]); 
        end if;

        // 6.2: l > 2
        if l gt 2 then 

            // Type V
            if (L ge 2) then 
                for c in [1..Min(a-1,L-1)] do 
                    Append(~points[2],[l^(Max(a-2*c,0))*f,1,2*ClassNumber((l^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*((l-1)/2)*l^(Min(c,a-c)-1)]);
                end for;
            end if;

            // Type VI
            if (a gt L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*(l^(Min(L,a-L)))]);
            end if; 

            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 0) then 

                // Type VII
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-1))*l^(Min(L,a-L)-1)]);

                // Type VIII
                Append(~points[2],[l^(Max(a-2*L-1,0))*f,1,2*ClassNumber((l^(Max(a-2*L-1,0))*f)^2*d_K),2^b*(l^(Min(L,a-L-1)))]);

            end if; 
             
            if (a ge L+1) and (L ge 1) and (symbol_l_K eq 1) then

                // Type IX
                Append(~points[2],[l^(Max(a-2*L,0))*f,1,2*ClassNumber((l^(Max(a-2*L,0))*f)^2*d_K),2^b*((l-2)*l^(Min(L,a-L)-1))]);

                // Type XI
                if (a ge L+2) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[l^(Max(a-2*L-h,0))*f,1,2*ClassNumber((l^(Max(a-2*L-h,0))*f)^2*d_K),2^(b+1)*(l-1)*l^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            end if;

        elif l eq 2 then 

            // 6.3: l=2, unramified 
            if symbol_l_K ne 0 then 

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if;

                // Type V_2
                if (L ge a) and (a ge 3) then 
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                if (a ge L+1) and (L ge 3) then 
                    Append(~points[2],[2^(Max(a-2*L+2,0))*f,1,2*ClassNumber((2^(Max(a-2*L+2,0))*f)^2*d_K),2^(b+1)*2^(Min(a-L+1,L-1)-2)]);
                end if;

                // Type V_4
                for c in [2..Min(L-2,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*2^(Min(c,a-c)-2)]);
                end for; 

                // Type VI
                if (a ge L+1) and (L ge 1) and (symbol_l_K eq -1) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-L)-1)]);
                end if;

                // Type XI
                if (a ge L+2) and (L ge 1) and (symbol_l_K eq 1) then 
                    for h in [1..a-L-1] do 
                        Append(~points[2],[2^(Max(a-2*L-h,0))*f,1,2*ClassNumber((2^(Max(a-2*L-h,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-L-h)-1)]);
                    end for;
                end if;

            // 6.4: l=2, ord_2(d_K) = 2
            elif Valuation(d_K,2) eq 2 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^(b+1)*(2^(Min(L,a-L)-2))]);
                end if; 

                // Type VIII
                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-1-L)-1)]);
                    end if;

                end if;

            // 6.5: l=2, ord_2(d_K) = 3
            elif Valuation(d_K,2) eq 3 then

                // Type V_1
                if (L ge 2) and (a ge 2) then 
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type V_2
                if (L ge a) and (a ge 3) then
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if;

                // Type V_3
                for c in [2..Min(L-1,a-2)] do 
                    Append(~points[2],[2^(Max(a-2*c,0))*f,1,2*ClassNumber((2^(Max(a-2*c,0))*f)^2*d_K),2^(b+1)*2^(Min(c,a-c)-2)]);
                end for;

                // Type VI_1
                if (L eq 1) and (a ge 2) then
                    Append(~points[2],[2^(a-2)*f,1,2*ClassNumber((2^(a-2)*f)^2*d_K),2^b]);
                end if; 

                // Type VI_2
                if (a eq L+1) and (L ge 2) then 
                    Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                end if; 

                // Type VI_3
                if (a ge L+2) and (L ge 2) then 
                    Append(~points[2],[2^(Max(a-2*L,0))*f,1,2*ClassNumber((2^(Max(a-2*L,0))*f)^2*d_K),2^(b+1)*2^(Min(L,a-L)-2)]);
                end if; 

                // Type VIII
                if L ge 1 then 

                    // Type VIII_1
                    if a eq L+1 then 
                        Append(~points[2],[f,1,2*ClassNumber((f)^2*d_K),2^b]);
                    end if; 

                    // Type VIII_2
                    if a ge L+2 then 
                        Append(~points[2],[2^(Max(a-2*L-1,0))*f,1,2*ClassNumber((2^(Max(a-2*L-1,0))*f)^2*d_K),2^(b+1)*(2^(Min(L,a-1-L)-1))]);
                    end if;
                end if;
            end if;
        end if;
    end if; 

    // sort both sequences of point information by conductor (hence also by degree)
    points := [* Sort(points[1],func<x,y | x[1]-y[1]>), Sort(points[2],func<x,y | x[1]-y[1]>) *];
    return points;

end intrinsic; 



intrinsic CMPointsXD0N(D::RngIntElt, f::RngIntElt, d_K::RngIntElt, N::RngIntElt) -> SeqEnum
{Given D an indefinite rational quaternion discriminant D, a CM conductor f, fundamental imaginary quadratic discriminant d_K, and positive integer N coprime to D, returns a sequence of two sequences of sequences of the form [conductor, ram, degree, number], with the first sequence in the pair giving the sequences of index 2 subfields of ring class fields (as described in work of Jordan and Gonzalez--Rotger) corresponding to the order of discriminant f^2d_K which arise as residue fields of f^2d_K-CM points on X^D_0(l^a). The information here is the CM conductor of the ring class field, the ramification index w.r.t. X^D_0(l^a)-->X^D(1) (which is 1, 2, or 3), the degree over Q of the residue field, and the number of points with this residue field and ramification index. The second sequence gives the same ordered information for ring class fields corresponding to the same order which arise as residue fields of such points}

    N_Fact := Factorization(N); 
    r := #N_Fact;
    D_Fact := Factorization(D);

    // N = 1 case, X^D_0(N) = X^D(1)
    if N eq 1 then 

        // checking that D is a quaternion discriminant
        if #D_Fact mod 2 eq 1 then 
            return "D not a quaternion discriminant!";
        end if;

        for pair in D_Fact do 
            if pair[2] ne 1 then 
                return "D not a quaternion discriminant!";
            end if; 
        end for; 

        // checking that K splits the quaternion algebra and computing
        // b = number of primes dividing D which are inert in K
        b := 0; 
        for pair in D_Fact do 
            if KroneckerSymbol(d_K,pair[1]) eq 1 then 
                return "K does not split the quaternion algebra of discriminant D";
            elif KroneckerSymbol(d_K,pair[1]) eq -1 then 
                b := b+1; 
            end if;
        end for; 

        // D_check: true if all primes dividing D are ramified in K, false otherwise 
        D_check := true; 
        for pair in D_Fact do
            if (KroneckerSymbol(d_K,pair[1]) eq -1) then
                D_check := false;
                break;
            end if;
        end for; 

        // Case all primes dividing D ramified in K
        if D_check eq true then 
            return [*[[f,1,ClassNumber(f^2*d_K),2^b]], [] *];

        // Case some prime dividing D inert in K
        elif D_check eq false then 
            return [*[], [[f,1,2*ClassNumber(f^2*d_K),2^b]] *];
        end if; 

    // N > 1 case
    elif N gt 1 then 

        // factors for creating cartesian product of information on pts at prime power levels
        prime_level_factors := [];
        for i in [1..r] do 

            // output list from prime_power function
            prime_power_pts := CMPointsXD0NPrimePower(D_Fact,f,d_K,N_Fact[i][1],N_Fact[i][2]);

            if Type(prime_power_pts) eq MonStgElt then
                return prime_power_pts; // returns relevant string if K doesn't split B_D or level N not coprime to D
            end if;

            // condensing information to single sequence of pts, each a list with four entries:
                // field type: "NR" for ring class field or "R" for index 2 subfield thereof
                // conductor: CM conductor of the corresponding 
                // ram: ramification index w.r.t map X^D_0(l^a)-->X^D(1)
                // number: number of pts with this res fld and ramification index 
            prime_power_pts_factor := []; 

            // appending rational ring class field residue field pts
            for pt in prime_power_pts[1] do 
                Append(~prime_power_pts_factor,[*"R",pt[1],pt[2],pt[4]*]);
            end for;

            // appending ring class field residue field pts
            for pt in prime_power_pts[2] do
                Append(~prime_power_pts_factor,[*"NR",pt[1],pt[2],pt[4]*]);
            end for; 

            Append(~prime_level_factors,prime_power_pts_factor); 

        end for; 

        // creating cartesian product of information on pts at prime power levels
        prime_level_product := CartesianProduct(prime_level_factors); 

        // initializing list of infromation on CM points on X_0(N) to output
        points := [*[],[]*];

        for pt_tuple in prime_level_product do 

            s := #[i : i in [1..r] | pt_tuple[i][1] eq "NR"];
            conductors := [(Integers() ! pt[2]) : pt in pt_tuple]; 
            cond_lcm := Lcm(conductors); 

            ram := 1;
            for i in [1..r] do
                if pt_tuple[i][3] ne 1 then
                    ram := pt_tuple[i][3];
                    break;
                end if; 
            end for;

            // product of numbers of points at each prime power level 
            count := 1;
            for i in [1..r] do
                count := count*pt_tuple[i][4];
            end for; 

            // Case: all residue fields index 2 subfields of ring class fields 
            if s eq 0 then 
                Append(~points[1],[cond_lcm,ram,ClassNumber(cond_lcm^2*d_K),count]);

            // Case: at least one residue field is a ring class field
            else 
                Append(~points[2],[cond_lcm,ram,2*ClassNumber(cond_lcm^2*d_K),2^(s-1)*count]);
            end if; 

        end for;

        // sort list of points by conductor (hence also by degree)
        points := [* Sort(points[1],func<x,y | x[1]-y[1]>), Sort(points[2],func<x,y | x[1]-y[1]>) *];
        return points;

    end if; 
end intrinsic; 




//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Rational CM points on Quotients X_0(D;N)/<w_m> with N squarefree
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


intrinsic QuadraticCMPointsX0DN(D::RngIntElt, N::RngIntElt) -> List
{Given an indefinite rational quaternion discriminant D and a positive integer N coprime to D, returns a list containing information on all quadratic CM points on the curve X_0(D;N). The format of the output is a list which consists of two lists. The second is for points with residue field the ring class field corresponding to the relevant order, and the first is for points with residue field an index 2 subfield of said ring class field. Each of these two sequences has elements of the form [d_K,f,f',number] where [f,d_K] is the order of the CM point, f' is the conductor corresponding to the residue field, and number is the number of points with that same residue field (and ramification index w.r.t. the map to trivial level, which we do not track here). This uses results and code from Saia22}
    quad_pts := [*[**],[**]*]; 
    // cond_disc_list_hle2 : list of all (not just maximal) imaginary quadratic orders of class number up to 2. 
    // The ith element is the complete list of sequences [f,d_K] = [conductor, fundamental disc] for imaginary 
    // quadratic orders of class number i.
    cond_disc_list_hle2 := [* [*
    [ 1, -3 ],
    [ 2, -3 ],
    [ 3, -3 ],
    [ 1, -4 ],
    [ 2, -4 ],
    [ 1, -7 ],
    [ 2, -7 ],
    [ 1, -8 ],
    [ 1, -11 ],
    [ 1, -19 ],
    [ 1, -43 ],
    [ 1, -67 ],
    [ 1, -163 ]
    *], [*
    [ 4, -3 ],
    [ 5, -3 ],
    [ 7, -3 ],
    [ 3, -4 ],
    [ 4, -4 ],
    [ 5, -4 ],
    [ 4, -7 ],
    [ 2, -8 ],
    [ 3, -8 ],
    [ 3, -11 ],
    [ 1, -15 ],
    [ 2, -15 ],
    [ 1, -20 ],
    [ 1, -24 ],
    [ 1, -35 ],
    [ 1, -40 ],
    [ 1, -51 ],
    [ 1, -52 ],
    [ 1, -88 ],
    [ 1, -91 ],
    [ 1, -115 ],
    [ 1, -123 ],
    [ 1, -148 ],
    [ 1, -187 ],
    [ 1, -232 ],
    [ 1, -235 ],
    [ 1, -267 ],
    [ 1, -403 ],
    [ 1, -427 ]
    *] *];
    class_num_1 := cond_disc_list_hle2[1];
    class_num_2 := cond_disc_list_hle2[2];
    for order in class_num_1 do
        pts := CMPointsXD0N(D,order[1],order[2],N);

        if Type(pts) ne MonStgElt then 

            for pt in pts[1] do 
                if pt[3] eq 2 then 
                    Append(~quad_pts[1],[order[2],order[1],pt[1],pt[4]]);
                end if;
            end for;

            for pt in pts[2] do 
                if pt[3] eq 2 then 
                    Append(~quad_pts[2],[order[2],order[1],pt[1],pt[4]]);
                end if;
            end for;
        end if; 
    end for; 

    for order in class_num_2 do
        pts := CMPointsXD0N(D,order[1],order[2],N);

        if Type(pts) ne MonStgElt then 

            for pt in pts[1] do 
                if pt[3] eq 2 then 
                    Append(~quad_pts[1],[order[2],order[1],pt[1],pt[4]]);
                end if;
            end for;
        end if; 
    end for; 

    return quad_pts;
end intrinsic; 



intrinsic RationalCMQuotientsX0DN(D::RngIntElt, N::RngIntElt) -> SeqEnum
{Given an indefinite rational quaternion discriminant D and a squarefree positive integer N coprime to D, outputs a sequence of Hall Divisors m of DN such that there exists a rational CM point on the quotient X_0(D;N)/<w_m>. This list may not be exhaustive. This uses Corollary 5.14 of Gonzalez--Rotger 2006}

    assert IsSquarefree(N);

    // computing list of quadratic CM points on X_0(D;N)
    quad_pts := QuadraticCMPointsX0DN(D,N); 

    HD := HallDivisors(D*N); 
    m_list := []; // initializing list of m with corresponding quotients having a rational CM point

    for m_index in [2..#HD] do // not allowing m=1

        m := HD[m_index];
        found_rat_pt := false; 

        for pt in quad_pts[1] do // GR06 Cor 5.14 (2)
            d_K := pt[1];
            f_R := pt[3];
            disc_R := f_R^2*d_K;
            m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,f_R)));
            Q := m/m_r;

            D_R := 1;
            for pair in Factorization(D) do
                if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                    D_R := D_R*pair[1];
                end if;
            end for;

            N_star_R := 1;
            for pair in Factorization(N) do 
                if (KroneckerSymbol(disc_R,pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                    N_star_R := N_star_R*pair[1];
                end if;
            end for; 

            // Now we use GRO6 Cor. 5.14 (2) to determine rationality of image points
            // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
            // orders to attach in GR06's framework. We lose nothing by ignoring these orders,
            // as if we actually have fixed points of these orders we have fixed points of 
            // order -3 or -4.
            if (Q eq 1) and (not (D_R in [-12,-16,-27])) then 
                found_rat_pt := true;
                break;
            end if; 
        end for;

        if found_rat_pt eq true then
            Append(~m_list,m);
        
        else

            for pt in quad_pts[2] do // GR06 Cor 5.14 (1)
                d_K := pt[1];
                f_R := pt[3];
                disc_R := f_R^2*d_K;
                m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,Integers()!f_R)));
                Q := m/m_r;

                D_R := 1;
                for pair in Factorization(D) do
                    if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                        D_R := D_R*pair[1];
                    end if;
                end for;

                N_star_R := 1;
                for pair in Factorization(N) do 
                    if (KroneckerSymbol(Integers()!disc_R,Integers()!pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                        N_star_R := N_star_R*pair[1];
                    end if;
                end for; 

                // Now we use GRO6 Cor. 5.14 (1) to determine rationality of image points
                // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
                // orders to attach in GR06's framework. We lose nothing by ignoring these orders,
                // as if we actually have fixed points of these orders we have fixed points of 
                // order -3 or -4.
                if (Q eq D_R*N_star_R) and (not (disc_R in [-12,-16,-27])) then
                    found_rat_pt := true;
                    break; 
                end if; 
            end for;

            if found_rat_pt eq true then
                Append(~m_list,m);
            end if;
        end if;
    end for;

    return m_list;

end intrinsic; 


intrinsic RationalCMPointsX0DN(D::RngIntElt, N::RngIntElt) -> List
{Given an indefinite rational quaternion algebra D and a squarefree positive integer N coprime to D, returns a list [* D,N,quotient_list *] where quotient_list is a list of lists of the form [* m,rat_CM_pts *]. Here, rat_CM_pts is a sequence of sequences [d_K,number] of fundamental discriminants d_K such that the quotient X_0(D;N)/<w_m> has at least (number > 0) rational d_K-CM points. This list may not be exhaustive. This uses Corollary 5.14 of Gonzalez--Rotger 2006}

    assert IsSquarefree(N);

    // computing list of quadratic CM points on X_0(D;N)
    quad_pts := QuadraticCMPointsX0DN(D,N); 

    HD := HallDivisors(D*N); 
    quotient_list := [* *]; // initializing quotient_list

    for m_index in [1..#HD] do

        m := HD[m_index];
        rat_CM_pts := []; 

        for pt in quad_pts[1] do // GR06 Cor 5.14 (2)
            d_K := pt[1];
            f_R := pt[3];
            disc_R := f_R^2*d_K;
            m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,f_R)));
            Q := m/m_r;

            D_R := 1;
            for pair in Factorization(D) do
                if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                    D_R := D_R*pair[1];
                end if;
            end for;

            N_star_R := 1;
            for pair in Factorization(N) do 
                if (KroneckerSymbol(disc_R,pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                    N_star_R := N_star_R*pair[1];
                end if;
            end for; 

            // Now we use GRO6 Cor. 5.14 (2) to determine rationality of image points
            // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
            // orders to attach in GR06's framework. We don't lose information here, since we only track fundamental discriminants.
            if (Q eq 1) and (not (D_R in [-12,-16,-27])) then 
                Append(~rat_CM_pts,[d_K,pt[4]]); // tracking CM discriminant
            end if; 
        end for;


        for pt in quad_pts[2] do // GR06 Cor 5.14 (1)
            d_K := pt[1];
            f_R := pt[3];
            disc_R := f_R^2*d_K;
            m_r := GCD(IntegerRing()!m,IntegerRing()!(disc_R/GCD(N,Integers()!f_R)));
            Q := m/m_r;

            D_R := 1;
            for pair in Factorization(D) do
                if ((f_R mod pair[1]) ne 0) and (KroneckerSymbol(disc_R,pair[1]) eq -1) then
                    D_R := D_R*pair[1];
                end if;
            end for;

            N_star_R := 1;
            for pair in Factorization(N) do 
                if (KroneckerSymbol(Integers()!disc_R,Integers()!pair[1]) eq 1) and ((f_R mod pair[1]) ne 0) then
                    N_star_R := N_star_R*pair[1];
                end if;
            end for; 

            // Now we use GRO6 Cor. 5.14 (1) to determine rationality of image points
            // note: d_R in {-12,-16,-27} give false info, as these aren't the correct
            // orders to attach in GR06's framework. We don't lose information here, since we only track fundamental discriminants.
            if (Q eq D_R*N_star_R) and (not (disc_R in [-12,-16,-27])) then
                Append(~rat_CM_pts,[d_K,pt[4]]); // tracking CM discriminant, number
            end if; 
        end for;

        Append(~quotient_list,[*m,rat_CM_pts*]);

    end for;

    return [* D,N,quotient_list *];

end intrinsic; 




//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////
//
// Gonality Bounds for X_0(D;N)
//
//////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////


intrinsic GonalityBoundListX0DN(D::RngIntElt, N::RngIntElt) -> List
{Given an indefinite rational quaternion discriminant D, a coprime positive integer N, returns a list [*gon_Q, [gon_Q_low, gon_Q_high], gon_Qbar, [gon_Qbar_low, gon_Qbar_high]*] where gon_Q_low is a lower bound for the Q-gonality of X_0(D;N) gon_Q_high is an upper bound for the Q-gonality of X_0(D;N) gon_Qbar_low is a lower bound for the Qbar-gonality of X_0(D;N) gon_Qbar_high is an upper bound for the Qbar-gonality of X_0(D;N), gon_Q is the Q-gonality of X_0(D;N) if the lower and upper bounds match and "\\N", and similarly for the Qbar-gonality}

    // g <= 2
    g_eq0 := [[6,1],[10,1],[22,1]];
    g_eq1 := [[6,5],[6,7],[6,13],[10,3],[10,7],[14,1],[15,1],[21,1],[33,1],[34,1],[46,1]];

    // geometrically hyperelliptic (Ogg83, GY17)
    hyp_ell := [[6,11],[6,17],[6,19],[6,29],[6,31],[6,37],[10,11],[10,13],[10,19],[10,23],[14,3],[14,5],[15,2],[15,4],[21,2],[22,3],[22,5],[26,1],[26,3],[35,1],
        [38,1],[39,1],[39,2],[51,1],[55,1],[57,1],[58,1],[62,1],[69,1],[74,1],[82,1],[86,1],[87,1],[93,1],[94,1],[95,1],[111,1],
        [119,1],[134,1],[146,1],[159,1],[194,1],[206,1]];

    // hyperelliptic over Q (Ogg83, GY17)
    hyp_ell_gonQ_eq2 := [[6,11],[6,19],[6,29],[6,31],[6,37],[10,11],[10,23],[14,5],[15,2],[22,3],[22,5],[26,1],[35,1],
        [38,1],[39,1],[39,2],[51,1],[55,1],[58,1],[62,1],[69,1],[74,1],[86,1],[87,1],[94,1],[95,1],[111,1],
        [119,1],[134,1],[146,1],[159,1],[194,1],[206,1]];

    // bielliptic and not hyperelliptic or of genus at most 1 (Rotger02 for N=1 and PS24 for N>1)
    bielliptic := [[57,1],[65,1],[77,1],[82,1],[85,1],[106,1],[115,1],[118,1] ,[122,1],[129,1],[143,1],
    [166,1],[178,1],[202,1],[210,1],[215,1],[314,1],[330,1],[390,1],[462,1],[510,1],[546,1],[6,17],[6,23],[6,41],[6,43],
    [6,47],[6,71],[10,17],[10,29],[10,31],[14,13],[14,19],[15,7],[15,11],[15,13],[15,17],[21,5],[21,11],[22,7],[22,17],
    [26,5],[33,2],[33,5],[33,7],[34,3],[35,2],[35,3],[38,3],[46,5],[6,25],[10,9],[15,8],[21,4],[39,4]];

    // cond_disc_list_hle2 : list of all (not just maximal) imaginary quadratic orders of class number up to 2. 
    // The ith element is the complete list of sequences [f,d_K] = [conductor, fundamental disc] for imaginary 
    // quadratic orders of class number i.
    cond_disc_list_hle2 := [* [*
    [ 1, -3 ],
    [ 2, -3 ],
    [ 3, -3 ],
    [ 1, -4 ],
    [ 2, -4 ],
    [ 1, -7 ],
    [ 2, -7 ],
    [ 1, -8 ],
    [ 1, -11 ],
    [ 1, -19 ],
    [ 1, -43 ],
    [ 1, -67 ],
    [ 1, -163 ]
    *], [*
    [ 4, -3 ],
    [ 5, -3 ],
    [ 7, -3 ],
    [ 3, -4 ],
    [ 4, -4 ],
    [ 5, -4 ],
    [ 4, -7 ],
    [ 2, -8 ],
    [ 3, -8 ],
    [ 3, -11 ],
    [ 1, -15 ],
    [ 2, -15 ],
    [ 1, -20 ],
    [ 1, -24 ],
    [ 1, -35 ],
    [ 1, -40 ],
    [ 1, -51 ],
    [ 1, -52 ],
    [ 1, -88 ],
    [ 1, -91 ],
    [ 1, -115 ],
    [ 1, -123 ],
    [ 1, -148 ],
    [ 1, -187 ],
    [ 1, -232 ],
    [ 1, -235 ],
    [ 1, -267 ],
    [ 1, -403 ],
    [ 1, -427 ]
    *] *];

    g := SignatureX0DN(D,N)[1];
    Abramovich_bound := Ceiling((21/200)*(g-1)); // Abramovich 
    gon_Q_low := Abramovich_bound;  
    gon_Q_high := 2*g-2; // see, for example, Poonen 07 Appendix A
    gon_Qbar_low := Abramovich_bound;
    gon_Qbar_high := Floor((g+3)/2); // see, for example, Poonen 07 Appendix A

    if [D,N] in g_eq0 then 
        gon_Q_low := 2;
        gon_Q_high := 2;
        gon_Qbar_low := 1;
        gon_Qbar_high := 1;

    elif [D,N] in g_eq1 then 
        gon_Q_low := 2;
        gon_Q_high := 2;
        gon_Qbar_low := 2;
        gon_Qbar_high := 2;

    elif [D,N] in hyp_ell_gonQ_eq2 then 
        gon_Q_low := 2;
        gon_Q_high := 2;
        gon_Qbar_low := 2;
        gon_Qbar_high := 2;

    elif [D,N] in hyp_ell then 
        gon_Q_low := 4;
        gon_Q_high := 4;
        gon_Qbar_low := 2;
        gon_Qbar_high := 2;

    elif [D,N] in bielliptic then 
        gon_Q_low := 4;
        gon_Q_high := 4;
        gon_Qbar_low := 4;
        gon_Qbar_high := 4;

    elif gon_Q_high eq 4 then 
        gon_Q_low := 4;
        gon_Q_high := 4;
        gon_Qbar_low := 4;
        gon_Qbar_high := 4;

    elif gon_Q_high eq 4 then 
        gon_Qbar_low := 4;
        gon_Qbar_high := 4;

    else 
    
        if gon_Qbar_low lt 3 then 
            qon_Qbar_low := 3;
        end if;

        if gon_Q_low lt 4 then
            gon_Q_low := 4; 
        end if; 

    end if;

    if ((gon_Q_low ne gon_Q_high) or (gon_Qbar_low ne gon_Qbar_high)) and IsSquarefree(N) then
        m_list := RationalCMQuotientsX0DN(D,N);

        if #m_list gt 0 then // if we have a rational (CM) point on a quotient, then we obtain a possibly better upper bound on the gonalities

            g_quot_min := Min([SignatureX0DNmodAtkinLehnerElement(D,N,m)[1] : m in m_list]);

            if g_quot_min ge 2 then
                gon_bound := 2*g_quot_min;
            else
                gon_bound := 2*(g_quot_min+1);
            end if;

            if gon_bound lt gon_Qbar_high then
                gon_Q_high := gon_bound;
                gon_Qbar_high := gon_bound;
            elif gon_bound lt gon_Q_high then 
                gon_Q_high := gon_bound; 
            end if;  

        end if;
    end if;

    // Shimura curves cannot have odd-degree points (no real points), so Q-gonalities must 
    // be even 
    gon_Q_low := Ceiling(gon_Q_low/2)*2;
    gon_Q_high := Floor(gon_Q_high/2)*2;

    if gon_Q_low eq gon_Q_high then 
        gon_Q := gon_Q_low;
    else 
        gon_Q := "\\N";
    end if;

    if gon_Qbar_low eq gon_Qbar_high then 
        gon_Qbar := gon_Q_low;
    else 
        gon_Qbar := "\\N";
    end if;

    return [*gon_Q,[gon_Q_low,gon_Q_high],gon_Qbar,[gon_Qbar_low,gon_Qbar_high]*];
end intrinsic;





