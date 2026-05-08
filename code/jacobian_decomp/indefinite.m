// local helpers

function IndefiniteTrace(B, N, n, f: G:=-1, i_new:=-1, j_new:=-1, I:=-1, J:=-1, g:=-1, verbose:=false)
    if IsSquare(n) and g eq -1 then
        return "needs to input the genus when n is a square";
    end if;
    discB := &*RamifiedPrimes(B);
    O := MaximalOrder(B);
    R<x> := PolynomialRing(Integers());
    if N ne 1 then
        ZN:= Integers(N);
        if Gcd(N, discB) eq 1 then
            G := GL(2, ZN);
        end if;
    end if;

    trace := 0;
    htab := ClassNumberTable(4*n);
    bad_primes := RamifiedPrimes(B);

    for t in [-Floor(2*Sqrt(n))..0] do
        if t^2-4*n ge 0 then continue; end if;
        K := NumberField(x^2-t*x+n);

        D1 := t^2-4*n;
        D0 := FundamentalDiscriminant(D1);

        lsym := 1;
        for p in bad_primes do
            if IsOdd(p) then
                lsym := lsym * (1 - LegendreSymbol(D0, p));
            elif (D0 mod 2) eq 0 then
                lsym := lsym * 1;
            elif ((D0 mod 8) eq 3) or ((D0 mod 8) eq 5) then
                lsym := lsym * 2;
            else
                lsym := 0;
            end if;
        end for;
        if verbose then printf "t = %o, D1=%o, D0=%o, local embedding number=%o\n", t, D1, D0, lsym; end if;

        if lsym ne 0 then
            Ktilde<c> := QuadraticField(D0);
            Smax := MaximalOrder(Ktilde);
            _, v := IsSquare(D1 div D0);

            for u in Divisors(v) do
                emb_num_S := lsym;
                D := u^2 * D0;
                S := sub<Smax|u>;
                for p in bad_primes do
                    if Gcd(u, p) gt 1 then emb_num_S := 0; end if;
                end for;
                b := v/u;
                if IsSquare(n) and (b^2 eq n) and ((D0 eq -3) or (D0 eq -4)) then continue; end if;
                if verbose then printf "embedding number = %o, v=%o, D0=%o, u=%o, b=%o\n", emb_num_S, v, D0, u, b; end if;

                if (N ne 1) and (emb_num_S ne 0) and (Gcd(discB, N) eq 1) then
                    if Gcd(Integers()!b, N) eq 1 then
                        beta := G!(Matrix(ZN, 2, 2, [0, -n/b, b, t]));
                    else
                        S_norm:= Norm(S.2); S_trace := Trace(S.2);
                        beta := G!((t-b*S_trace)/2*IdentityMatrix(Integers(N), 2) + b*Matrix(Integers(N), 2, 2, [0,-S_norm,1,S_trace]));
                    end if;
                    trace +:= emb_num_S * f(beta) * GetClassNumber(htab, D)/Order(UnitGroup(S));
                elif (N eq 1) and (emb_num_S ne 0) and (Gcd(discB, N) eq 1) then
                    trace +:= emb_num_S * GetClassNumber(htab, D)/Order(UnitGroup(S));
                elif (emb_num_S ne 0) then
                    alpha, _ := Embed(K, B);
                    assert (alpha^2-t*alpha+n) eq 0;
                    assert <Norm(B!alpha), Trace(B!alpha)> eq <n, t>;
                    IJ := I*J;
                    tmp := CoeffsInBasis(B!alpha,i_new,j_new);
                    assert (B!(tmp[1,1] + tmp[1,2]*i_new + tmp[1,3]*j_new + tmp[1,4]*(i_new*j_new))) eq B!alpha;
                    beta := tmp[1,1]+tmp[1,2]*I+tmp[1,3]*J+tmp[1,4]*IJ;
                    assert beta in G;
                    assert (beta^2-t*beta+n) eq 0;
                    if verbose then print(<emb_num_S, f(G!beta), GetClassNumber(htab, D), Order(UnitGroup(S))>); end if;
                    trace +:= t ne 0 select 2 * emb_num_S * f(G!beta) * GetClassNumber(htab, D)/Order(UnitGroup(S)) else emb_num_S * f(G!beta) * GetClassNumber(htab, D)/Order(UnitGroup(S));
                end if;
            end for;
        end if;
    end for;
    return (IsSquare(n) select &+Divisors(n) - 1 - trace + g else &+Divisors(n) - trace);
end function;


intrinsic HTraces(B::AlgQuat, H::GrpMat, N::RngIntElt, Q::SeqEnum
        : G:=-1, i_new:=-1, j_new:=-1, I:=-1, J:=-1, g:=-1, verbose:=false) -> SeqEnum
{Computes the Frobenius traces of X_H/F_q for q in Q (which must be coprime to D*N).}
    D := &*RamifiedPrimes(B);
    for p in Q do assert Gcd(p, D*N) eq 1; end for;

    if Gcd(D, N) eq 1 then
        f := GL2PermutationCharacter(H);
        return [IndefiniteTrace(B, N, p, f): p in Q];
    else
        f := HPermutationCharacter(G, H);
        return [Integers()!IndefiniteTrace(B, N, p, f:G:=G,i_new:=i_new,j_new:=j_new,I:=I,J:=J,g:=g,verbose:=verbose): p in Q];
    end if;
end intrinsic;
