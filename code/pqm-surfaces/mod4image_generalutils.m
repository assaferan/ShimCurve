Z4 := Integers(4);
GSp2 := Sp(4,2);
G := MatrixGroup<4,Z4|[
    [ 1, 0, 0, 1, 0, 1, 3, 0, 1, 1, 0, 1, 0, 1, 3, 1 ],
    [ 3, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3 ],
    [ 1, 0, 0, 0, 2, 1, 0, 0, 2, 0, 1, 0, 0, 2, 2, 1 ],
    [ 1, 0, 0, 2, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1 ],
    [ 1, 2, 0, 0, 0, 1, 0, 0, 2, 0, 1, 2, 0, 2, 0, 1 ],
    [ 1, 0, 2, 2, 2, 3, 0, 2, 2, 3, 3, 2, 0, 0, 2, 1 ],
    [ 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3 ],
    [ 3, 2, 2, 0, 2, 1, 2, 2, 2, 0, 1, 2, 2, 2, 2, 3 ],
    [ 1, 0, 2, 0, 0, 1, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1 ],
    [ 1, 0, 0, 0, 0, 1, 0, 0, 2, 0, 1, 0, 0, 2, 0, 1 ],
    [ 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 2, 0, 0, 1 ],
    [ 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3, 0, 0, 0, 0, 3 ],
    [ 3, 2, 0, 0, 0, 1, 0, 0, 0, 2, 1, 2, 0, 0, 0, 3 ]
]>;
f := hom<G -> GSp2 | [ChangeRing(G.i,GF(2)) : i in [1..#Generators(G)]]>;
kerf := Kernel(f);

P<x> := PolynomialRing(Rationals());
BigG := GL(4,Z4);
U, incl := UnitGroup(Z4);
J := Matrix(Z4,4,4,[0,0,0,1,0,0,1,0,0,-1,0,0,-1,0,0,0]);
// [G.i*J*Transpose(G.i) eq J : i in [1..#Generators(G)]];
chi := hom<G -> U | [(G.i*J*Transpose(G.i) eq J) select Identity(U) else U.1 : i in [1..#Generators(G)]]>;
assert &and[G.i*J*Transpose(G.i) eq incl(chi(G.i))*J : i in [1..#Generators(G)]];
kerchi := Kernel(chi);

CCs := ConjugacyClasses(G);
classmap := ClassMap(G);


intrinsic GassmanDistribution(G :: Grp, H :: Grp : CCG := [], classmap := false, ordsH := []) -> SeqEnum, SeqEnum, Map
{returns the gassman distribution of H as a subgroup of G, i.e., distribution of elements of H
according to their G-conjugacy classes CCG. If the list of possible orders of elements of H is
known, it can be given as the optional parameter ordsH.}
    if ordsH ne [] then
        if CCG eq [] then CCG := ConjugacyClasses(G); classmap := ClassMap(G); end if;
        return [(cc[1] in ordsH) select #(Set(H) meet Orbit(G,cc[3]))/#H else 0: cc in CCG], CCG, classmap;
    end if;
    if CCG eq [] then CCG := ConjugacyClasses(G); classmap := ClassMap(G); end if;
    CCH := ConjugacyClasses(H);
    lis := [0/1 : x in CCG];
    printf "The subgroup has %o conjugacy classes\n", #CCH;
    for cc in CCH do
        cc_n := classmap(cc[3]);
        lis[cc_n] := lis[cc_n] + cc[2];
        printf "After %oth class, we have the distribution \n%o\n", Index(CCH,cc), lis;
    end for;
    assert &+lis eq #H;
    return [x/#H : x in lis], CCG, classmap;
end intrinsic;


intrinsic allvalidccs(sig :: SeqEnum) -> SeqEnum
    {returns the indices of (charpolys of) conjugacy classes showing up in the sampled signature}
    return [i : i in [1..#sig] | sig[i] ne 0];
end intrinsic;

intrinsic distinguish(C :: CrvHyp, poss :: SeqEnum) -> SeqEnum
    {distinguish among possible images}
    // TODO
    return poss;
end intrinsic;

intrinsic monicquinticmodel(f :: RngUPolElt : alp := false) -> RngUPolElt
{returns a monic quintic polynomial g such that the genus 2 curves y^2=f(x) and y^2=g(x) are isomorphic, 
and the point (alp,0) on the first curve is moved to the point at infinity on the second curve}
    P<x> := Parent(f);
    if Type(alp) eq BoolElt then
        boo, Cg := HasOddDegreeModel(HyperellipticCurveOfGenus(2,f));
        require boo : "Curve does not have an odd degree model";
        return HyperellipticPolynomials(Cg);
    end if;
    require Evaluate(f,alp) eq 0 : "Not a root";
    g := P ! (Evaluate(f,alp+1/x)*x^6);
    a5 := Coefficient(g,5);
    g := Evaluate(g,a5*x)/a5^6;
    return g;
end intrinsic;

intrinsic mod2image(C :: CrvHyp) -> GrpMat
{returns the mod2 Galois image as a subgroup of GSp(4,F_2)}
    require Genus(C) eq 2 : "Genus must be 2";
    GSp2 := Sp(4,2);
    S6 := Sym(6);
    bool, phi := IsIsomorphic(S6, GSp2);
    somesubsGSp2 := Subgroups(GSp2 : OrderEqual := 48);
    somesubsS6 := Subgroups(S6 : OrderEqual := 48);
    A := AutomorphismGroup(GSp2);
    assert exists(out_aut){g : g in Generators(A) | not IsInner(g)};
    if Dimension(Fix(GModule(somesubsGSp2[1]`subgroup))) ne 0 then
        somesubsGSp2 := Reverse(somesubsGSp2);
    end if;
    if #Orbits(somesubsS6[1]`subgroup) eq 2 then
        somesubsS6 := Reverse(somesubsS6);
    end if;
    if IsConjugate(GSp2, somesubsGSp2[1]`subgroup, phi(somesubsS6[1]`subgroup)) then
        goodphi := phi;
    else
        goodphi := phi*out_aut;
    end if;

    C1 := SimplifiedModel(C);
    f := HyperellipticPolynomials(C1);
    if Degree(f) eq 6 then
        return goodphi(GaloisGroup(f));
    else
        S5 := Stabiliser(S6,6);
        Sy5 := Sym(5);
        boo, isom := IsIsomorphic(Sy5,S5);
        return goodphi(isom(GaloisGroup(f)));
    end if;
end intrinsic;

intrinsic Mod2EnhancedImage(X :: CrvHyp : prec := 100) -> .
{returns the image of the mod2 enhanced representation (as a subgroup of GL(4,Z/2) and as a set of enhanced elements).
TODO: Enhance the image using image of endomorphism representation.}
    QQ := Rationals();
    CC := ComplexField(prec);
    Z2 := Integers(2);

    endos:=HeuristicEndomorphismRepresentation( X : CC:=true);
    endosM2:=[ ChangeRing(m[1],CC) : m in endos ];
    endosM4:=[ ChangeRing(m[2],QQ) : m in endos ]; 
    Bmat:=MatrixAlgebra< QQ, 4 | endosM4 >;
    tr, B, maptoB := IsQuaternionAlgebra(Bmat);
//    assert forall(b){ [Bmat.u,Bmat.v] : u,v in [1..4] | maptoB(Bmat.u*Bmat.v) eq maptoB(Bmat.u)*maptoB(Bmat.v) };
    Obasis:=[ maptoB(b) : b in endosM4 ];
    O:=QuaternionOrder(Obasis : IsBasis:=true);

    boo, nu := HasPolarizedElementOfDegree(O,1); assert boo;
    G2, Omod2cross, aut2 := EnhancedImageGL4(O,nu,2);
/*
    print aut2;
    print Type(aut2);
    printf "Type of aut2 is %o\n", Type(aut2);
    printf "Type of Image(aut2) is %o\n", Type(Image(aut2));
// Runtime error in '#': Map is not a coset table
*/
    printf "#G2 : %o, #Omod2cross: %o, #aut2 : %o\n", #G2, #Omod2cross, #Image(aut2);
    printf "Index of Omod2cross in EnhancedSemidirectProduct is %o.\n\n", Index(G2,Omod2cross);
G2 := ChangeRing(G2,GF(2));
Gl4 := GL(4,2);
GSp4 := Sp(4,2);
ZGSp4 := [x`subgroup : x in Subgroups(GSp4 : OrderEqual := #G2) | IsConjugate(Gl4,G2,x`subgroup)];
// This will not work in general, because the enhanced semidirect product G2 does not embed in GSp(4,2)
// (or even GL(4,2)) in general. The homomorphism to GL(4,2) has a kernel in general.
// Question: Why does this G2 embed uniquely in Sp(4,2)? Does it mean that this is not the map we want?
assert #ZGSp4 eq 1;
iG2 := ZGSp4[1];
boo, M := IsConjugate(Gl4,G2,iG2);
assert Conjugate(G2,M) eq iG2;
i := hom<G2 -> GSp4 | [G2.i^M : i in [1..#GeneratorsSequence(G2)]]>;
assert i(G2) eq iG2;

/*
newans := [Conjugate(ChagneRing(x,GF(2)),M) : x in ans];
&and[x subset GSp4 : x in newans];
IsConjugate(GSp4,newans[1],newans[2]);
*/

G2X := mod2image(X);

// conjs_G2X := [x`subgroup : x in Subgroups(iG2 : OrderEqual := #G2X) | IsConjugate(GSp4,G2X,x`subgroup)];

boo, M := IsConjugateSubgroup(GSp4,iG2,G2X);
assert M in GSp4;
G2X := Conjugate(G2X,M);
assert G2X subset iG2;

/*
    Gl4 := GL(4,Z2);
    G2X := ChangeRing(mod2image(X),Z2);
    conjs_G2X := [x`subgroup : x in Subgroups(G2 : OrderEqual := #G2X) | IsConjugate(Gl4,G2X,x`subgroup)];
    printf "There are %o GL(4)-conjugates of the mod-2 image, lying inside EnhancedSemidirectProduct up to conjugacy.\n", #conjs_G2X;
*/

    EndfieldGalgrp, Endfieldpols := HeuristicEndomorphismFieldAsSplittingField(ChangeRing(X,RationalsExtra(prec)));
    Endfield := SplittingField(Endfieldpols);
    fX := HyperellipticPolynomials(SimplifiedModel(X));
    K2 := SplittingField(fX);
//    ind := Degree(Endfield, Endfield meet K2);
//    ind := Degree(SplittingField([ChangeRing(g,K2) : g in Endfieldpols]), K2);
    ind := ExactQuotient(Degree(Compositum(Endfield,K2)),Degree(K2));
    printf "Endomorphism field degree: %o, 2-torsion field degree: %o.\nDegree of compositum over 2-torsion field: %o.\n\n", Degree(Endfield), Degree(K2), ind;

    if ind eq 1 then return [ChangeRing(G2X @@ i,Z2)], ind; end if;
    mod2enhimg_possibilities := [ChangeRing(x`subgroup, Z2) : x in Subgroups(G2 : OrderEqual := #G2X*ind) | IsConjugateSubgroup(G2,x`subgroup,G2X @@ i)];
    return mod2enhimg_possibilities, ind;
end intrinsic;

QQ := Rationals();
Invs := SFAElementary(QQ);
P5 := PolynomialRing(QQ,5);
s1 := Polynomial(Invs.[1],P5);
s2 := Polynomial(Invs.[2],P5);
s3 := Polynomial(Invs.[3],P5);
s4 := Polynomial(Invs.[4],P5);
s5 := Polynomial(Invs.[5],P5);

function Ur(a,r);
    L := Parent(r[1]);
    PL<x> := PolynomialRing(L);
    ans := (a-x)^2 + Evaluate(s2,r)*(a-x) + Evaluate(s4,r);
    return ans;
end function;

function Vr(a,r);
    L := Parent(r[1]);
    PL<x> := PolynomialRing(L);
    ans := Evaluate(s1,r)*(a-x)^2 + Evaluate(s3,r)*(a-x) - Evaluate(s1,r)*Ur(a,r);
    return ans;
end function;

function zeros(n);
    return [0 : i in [1..n]];
end function;

intrinsic orderofkernelofredmod2(C :: CrvHyp) -> RngIntElt
{returns the F_2-dimension of the kernel of the reduction map from mod-4 Galois image to mod-2 Galois image}
    C1 := SimplifiedModel(C);
    radcond := 2*&*BadPrimes(C1);
    f := HyperellipticPolynomials(C1);
    roo := Roots(f);
    if #roo ge 1 then
        newf := monicquinticmodel(f : alp := roo[1,1]);
        C2 := HyperellipticCurveOfGenus(2,newf);
        K := SplittingField(f);
        FintoK := hom<Rationals() -> K |>;
        roo := Roots(newf,K);
    else
        Fac := Factorisation(f);
        F<alp> := NumberField(Fac[1,1]);
        newf := monicquinticmodel(ChangeRing(f,F) : alp := alp);
        K, roos := SplittingField([h[1] : h in Fac]);
        FintoK := hom<F -> K | roos[1][1]>;
        PK<x> := PolynomialRing(K);
        coercePintoPK := hom<Parent(newf) -> PK | FintoK, x>;
        roo := Roots(coercePintoPK(newf),K);
    end if;

    rootdiffs := [K ! -1] cat &cat[[roo[j,1]-roo[k,1] : k in [j+1..5]] : j in [1..4]];

    gens := [];
    upperbound := 11;
    for j := 1 to #rootdiffs do
        alpha := rootdiffs[j];
        if #gens eq 0 then
            bool, sqrt_i := IsSquare(alpha);
            if bool then
                upperbound := upperbound - 1;
            else
                Append(~gens,alpha);
            end if;
//            printf "Current lower and upper bound for F_2-dimension of mod4image over 2-torsion field: %o %o\n", #gens, upperbound;
        else
            binarystrings := VectorSpace(GF(2),#gens);
            boo := true;
            for x in binarystrings do
                a := alpha*&*[(x[j] eq 1) select gens[j] else 1 : j in [1..#gens]];
                bool, sqrt_i := IsSquare(a);
                if bool then
//                    print Eltseq(x);
                    upperbound := upperbound -1;
                    boo := false;
                    break;
                end if;
            end for;
            if boo then
                Append(~gens,alpha);
            end if;
//            printf "Current lower and upper bound for F_2-dimension of mod4image over 2-torsion field: %o %o\n", #gens, upperbound;
        end if;
    end for;
    return #gens;
end intrinsic;


intrinsic basisoffourtors(C :: CrvHyp, p :: RngIntElt) -> SeqEnum
{computes a basis of four torsion of the Jacobian of the reduced curve C_p over a suitable extension of F_p}
    C1 := SimplifiedModel(C);
    radcond := 2*&*BadPrimes(C1);
    require radcond mod p ne 0 : "Possibly bad prime";
    C1p := ChangeRing(C1,GF(p));
    f := HyperellipticPolynomials(C1p);
    roo := Roots(f);
    if #roo ge 1 then
        newf := monicquinticmodel(f : alp := roo[1,1]);
        C2p := HyperellipticCurveOfGenus(2,newf);
        K := SplittingField(f);
        FintoK := hom<GF(p) -> K |>;
        roo := Roots(newf,K);
    else
        Fac := Factorisation(f);
        F<alp> := ext<GF(p) | Fac[1,1]>;
        newf := monicquinticmodel(ChangeRing(f,F) : alp := alp);
        C2p := HyperellipticCurveOfGenus(2,newf);
        K := GF(p,LCM([Degree(h[1]) : h in Fac]));
        FintoK := hom<F -> K | Roots(Fac[1,1],K)[1,1]>;
        PK<x> := PolynomialRing(K);
        coercePintoPK := hom<Parent(newf) -> PK | FintoK, x>;
        roo := Roots(coercePintoPK(newf),K);
    end if;

    rootdiffs := [[roo[j,1]-roo[k,1] : k in [1..5]] : j in [1..4]];

    rootdiffs_intermsof_gens := [];
    for_sqrts := <>;
    gens := [];
    for j := 1 to 4 do
        temp_rels := [];
        temp_forsqrts := <>;
        for k := 1 to 5 do
            if j eq k then
                Append(~temp_rels,[]);
                temp_forsqrts := temp_forsqrts cat <0>;
            else
                alpha := rootdiffs[j,k];
                if #gens eq 0 then
                    bool, sqrt_i := IsSquare(alpha);
                    if bool then
                        Append(~temp_rels, []);
                        temp_forsqrts := temp_forsqrts cat <sqrt_i>;
                    else
                        Append(~gens,alpha);
                        Append(~temp_rels, [1]);
                        temp_forsqrts := temp_forsqrts cat <0>;
                    end if;
                else
                    binarystrings := VectorSpace(GF(2),#gens);
                    boo := true;
                    for x in binarystrings do
                        a := alpha*&*[(x[j] eq 1) select gens[j] else 1 : j in [1..#gens]];
                        bool, sqrt_i := IsSquare(a);
                        if bool then
            //			    print Eltseq(x);
                            Append(~temp_rels, Eltseq(x));
                            temp_forsqrts := temp_forsqrts cat <sqrt_i>;
                            boo := false;
                            break;
                        end if;
                    end for;
                    if boo then
                        Append(~gens,alpha);
                        Append(~temp_rels, [0 : j in [1..#gens-1]] cat [1]);
                        temp_forsqrts := temp_forsqrts cat <0>;
                    end if;
                end if;
            end if;
        end for;
        Append(~rootdiffs_intermsof_gens, temp_rels);
        for_sqrts := for_sqrts cat <temp_forsqrts>;
    end for;


    logdeg := #gens;

    rootdiffs_intermsof_gens := [[y cat [0 : j in [1..logdeg-#y]] : y in x] : x in rootdiffs_intermsof_gens];
    assert #rootdiffs_intermsof_gens eq 4 and [#x : x in rootdiffs_intermsof_gens] eq [5,5,5,5];

    L := ext<K|2^logdeg>;


    Z4 := IntegerRing(4);
    Z := Integers();

    C2_K := BaseChange(C2p, FintoK);
    J2_K := Jacobian(C2_K);
    infty_pt := PointsAtInfinity(C2_K);
    assert #infty_pt eq 1;
    infty_pt := infty_pt[1];
    basis_2tors := [];
    for i := 1 to 4 do
        bool, pt_i := IsPoint(C2_K,[roo[i,1],0]);
        jac_pt := J2_K ! [pt_i, infty_pt];
        assert 2*jac_pt eq J2_K ! 0;
        Append(~basis_2tors,jac_pt);
    end for;
    all_2tors := [];
    all_2tors_coords := [];
    for i, j, k, l in [0,1] do
        Append(~all_2tors,i*basis_2tors[1] + j*basis_2tors[2] + k*basis_2tors[3] + l*basis_2tors[4]);
        Append(~all_2tors_coords,[i,j,k,l]);
    end for;


    PK<x> := PolynomialRing(K);
    basis_4tors := <>;
    for i := 1 to #rootdiffs do
        ith_rootdiff := rootdiffs[i];
        ith_forsqrts := for_sqrts[i];
        ith_rditogens := rootdiffs_intermsof_gens[i];
        V := VectorSpace(GF(2),#gens);
        V_Z := RSpace(Z,#gens);
        ithvectors := [V ! y : y in ith_rditogens];
        basis_ithvectors := Basis(sub<V|ithvectors>);
        basismat := Matrix(GF(2),#basis_ithvectors,#gens,basis_ithvectors);
        solutions := [];
        leftovers := [];
        for j := 1 to #ithvectors do
            sol := Solution(basismat,ithvectors[j]);
            Append(~solutions,sol);
            if #basis_ithvectors ne 0 then
                leftover := Eltseq((&+[(sol[k] eq 1) select V_Z ! basis_ithvectors[k] else V_Z ! 0 : k in [1..#basis_ithvectors]] - V_Z ! ith_rditogens[j]) div 2);
                Append(~leftovers,leftover);
            end if;
        end for;
    //	print #gens, ithvectors, basis_ithvectors, solutions;
        ith_gens := [&*[(v[k] eq 0) select 1 else gens[k] : k in [1..#gens]] : v in basis_ithvectors];

        Lidotks := [];
        for albegade in ith_gens do
            bool, sqrtalbegade := IsSquare(L ! albegade);
            assert bool;
            Append(~Lidotks,sqrtalbegade);
        end for;
        Rhalf_elt := [];
        for j := 1 to 5 do
    //	    print i,j;
            if j eq i then
                Append(~Rhalf_elt, L ! 0);
                assert Rhalf_elt[#Rhalf_elt]^2 eq rootdiffs[i,j];
            else
                sol := solutions[j];
                if #basis_ithvectors eq 0 then
                    den := 1;
                else
                    den := &*[(sol[k] eq 0) select 1 else Lidotks[k] : k in [1..#basis_ithvectors]];
                    leftover := leftovers[j];
                    adjustment := &*[gens[k]^leftover[k] : k in [1..#leftover]];
                    den := den/adjustment;
                end if;

        //		ith_forsqrts[j];
                if ith_forsqrts[j] eq 0 then
                    assert den^2 eq rootdiffs[i,j];
                    Append(~Rhalf_elt,den);
                    assert Rhalf_elt[#Rhalf_elt]^2 eq rootdiffs[i,j];
                else
                    Append(~Rhalf_elt,L ! ith_forsqrts[j]/den);
                    assert Rhalf_elt[#Rhalf_elt]^2 eq rootdiffs[i,j];
                end if;
            end if;
        end for;
        J2_L := BaseExtend(J2_K,L);
        P_i := elt<J2_L | [Ur(roo[i,1],Rhalf_elt), Vr(roo[i,1],Rhalf_elt)]>;
        assert 4*P_i eq J2_L ! 0;
        basis_4tors := basis_4tors cat <P_i>;
    //	#basis_4tors;
    end for;

    basis4tors_originalcurve := [];
    C1_L := ChangeRing(C1p,L);
    J1_L := Jacobian(C1_L);
    C2_L := Curve(J2_L);
    bool, psi := IsIsomorphic(C1_L,C2_L);
    for Pi in basis_4tors do
        P<X,Y,Z> := CoordinateRing(Ambient(C2_L));
        polfirst := Pi[1];
        polsecond := Pi[2];
        polfirst_homgnsd := Coefficient(polfirst,2)*X^2 + Coefficient(polfirst,1)*X*Z + Coefficient(polfirst,0)*Z^2;
        polsecond_homgnsd := Y - Coefficient(polsecond,1)*X*Z^2 - Coefficient(polsecond,0)*Z^3;
        div2 := Divisor(C2_L, ideal<P | polfirst_homgnsd, polsecond_homgnsd>);
        div1 := Pullback(psi, div2);
        Pi1 := J1_L ! div1;
        Append(~basis4tors_originalcurve, Pi1);
    //	#basis4tors_originalcurve;
    end for;
    return basis4tors_originalcurve;
end intrinsic;

intrinsic symplecticbasis(fourpoints :: SeqEnum) -> SeqEnum
{returns a symplectic basis of four torsion from a given basis}
    Z4 := Integers(4);
    P1 := fourpoints[1];
    for pt in fourpoints do
        temp := WeilPairing(P1,pt,4);
        if temp^2 ne 1 then
            P4 := pt;
            zeta4 := temp;
            break;
        end if;
    end for;
    remainingpoints := Exclude(Exclude(fourpoints,P1),P4);
    m := AssociativeArray();
    m[zeta4] := 1; m[zeta4^2] := 2; m[zeta4^3] := 3; m[zeta4^4] := 0;
    mi := AssociativeArray();
    mi[zeta4] := 1; mi[zeta4^3] := 3;
    P2 := remainingpoints[1];
    P3 := remainingpoints[2];
    P2 := P2 + m[WeilPairing(P4,P2,4)]*P1 - m[WeilPairing(P1,P2,4)]*P4;
    P3 := mi[WeilPairing(P2,P3,4)]*P3;
    P3 := P3 + m[WeilPairing(P4,P3,4)]*P1 - m[WeilPairing(P1,P3,4)]*P4;
    sympbasis := [P1, P2, P3, P4];
    pairingsmat := Matrix(Z4,4,4,[[m[WeilPairing(x,y,4)] : y in sympbasis] : x in sympbasis]);
    J := StandardAlternatingForm(4,Z4);
    assert pairingsmat eq J;
    return sympbasis;
end intrinsic;

intrinsic frobconjclass(C :: CrvHyp, p :: RngIntElt) -> GrpMatElt
{returns a 4x4 matrix in GSp(4,Z/4) representing the conjugacy class of Frob_p acting on the 4-torsion}
    Z4 := Integers();
    C1 := SimplifiedModel(C);
    radcond := &*BadPrimes(C1)*2;
    require radcond mod p ne 0 : "Possibly bad prime";
	basis := basisoffourtors(C1,p);
	Jackpf := Parent(basis[1]);
	kpf := BaseRing(Jackpf);
	Pred<x> := PolynomialRing(kpf);
	sympbasis := symplecticbasis(basis);
	sigmabasis := [];
	for i := 1 to #basis do
	    Pi := sympbasis[i];
	    sigmai1 := Pred ! [Frobenius(coe) : coe in Coefficients(Pi[1])];
	    sigmai2 := Pred ! [Frobenius(coe) : coe in Coefficients(Pi[2])];
	    sigmaPi := elt<Jackpf | sigmai1, sigmai2, Pi[3]>;
	    Append(~sigmabasis,sigmaPi);
	end for;
	all_pts_k := [];
	coords := [];
	for i1, i2, i3, i4 in [0..3] do
	    po := i1*sympbasis[1] + i2*sympbasis[2] + i3*sympbasis[3] + i4*sympbasis[4];
	    Append(~all_pts_k,po);
	    Append(~coords,[i1, i2, i3, i4]);
	end for;
	sigmabasiscoords := [coords[Index(all_pts_k,sigmabasis[i])] : i in [1..#sigmabasis]];
	frobpmat := G ! Matrix(Z4,4,4,sigmabasiscoords);
	return frobpmat;
end intrinsic;


intrinsic mod4imageovertwotorsionfield(C :: CrvHyp) -> GrpMat, Tup, SeqEnum
{returns the mod-4 Galois image of Jacobian of C over the two-torsion field,
as a subgroup of GL(4,Z/4). Note a suitable conjugate lies inside ker (GSp(4,Z/4) ---> GSp(4,Z/2)).
If it is strictly smaller, then the corresponding choice of a (not-necessarily symplectic)
basis of the 4-torsion is returned as a 4-tuple, and the third return value contains the 
defining fields of these 4 points as extensions over the 2-torsion field.}
    C1 := SimplifiedModel(C);
    badprimes := 2*&*BadPrimes(C1);
    f := HyperellipticPolynomials(C1);
    roo := Roots(f);
    if #roo ge 1 then
        newf := monicquinticmodel(f : alp := roo[1,1]);
        C2 := HyperellipticCurveOfGenus(2,newf);
        K := SplittingField(f);
        FintoK := hom<Rationals() -> K |>;
        roo := Roots(newf,K);
    else
        Fac := Factorisation(f);
        F<alp> := NumberField(Fac[1,1]);
        newf := monicquinticmodel(ChangeRing(f,F) : alp := alp);
        C2 := HyperellipticCurveOfGenus(2,newf);
        K, roos := SplittingField([h[1] : h in Fac]);
        FintoK := hom<F -> K | roos[1][1]>;
        PK<x> := PolynomialRing(K);
        coercePintoPK := hom<Parent(newf) -> PK | FintoK, x>;
        roo := Roots(coercePintoPK(newf),K);
    end if;

    rootdiffs := [[roo[j,1]-roo[k,1] : k in [1..5]] : j in [1..4]];
//    printf "The table of differences of Weierstrass points\n%o\n", rootdiffs;

    rootdiffs_intermsof_gens := [];
    for_sqrts := <>;
    gens := [];
    for j := 1 to 4 do
        temp_rels := [];
        temp_forsqrts := <>;
        for k := 1 to 5 do
            if j eq k then
                Append(~temp_rels,[]);
                temp_forsqrts := temp_forsqrts cat <0>;
            else
                alpha := rootdiffs[j,k];
                if #gens eq 0 then
                    bool, sqrt_i := IsSquare(alpha);
                    if bool then
                        Append(~temp_rels, []);
                        temp_forsqrts := temp_forsqrts cat <sqrt_i>;
                    else
                        Append(~gens,alpha);
                        Append(~temp_rels, [1]);
                        temp_forsqrts := temp_forsqrts cat <0>;
                    end if;
                else
                    binarystrings := VectorSpace(GF(2),#gens);
                    boo := true;
                    for x in binarystrings do
                        a := alpha*&*[(x[j] eq 1) select gens[j] else 1 : j in [1..#gens]];
                        bool, sqrt_i := IsSquare(a);
                        if bool then
//            			    print Eltseq(x);
                            Append(~temp_rels, Eltseq(x));
                            temp_forsqrts := temp_forsqrts cat <sqrt_i>;
                            boo := false;
                            break;
                        end if;
                    end for;
                    if boo then
                        Append(~gens,alpha);
                        Append(~temp_rels, [0 : j in [1..#gens-1]] cat [1]);
                        temp_forsqrts := temp_forsqrts cat <0>;
                    end if;
                end if;
            end if;
        end for;
        Append(~rootdiffs_intermsof_gens, temp_rels);
        for_sqrts := for_sqrts cat <temp_forsqrts>;
    end for;


    logdeg := #gens;
    if logdeg eq 11 then return kerf, <>, []; end if;
    printf "Degree of 4-torsion field over 2-torsion field : 2^%o\n", logdeg;
//    print rootdiffs_intermsof_gens;

    rootdiffs_intermsof_gens := [[y cat [0 : j in [1..logdeg-#y]] : y in x] : x in rootdiffs_intermsof_gens];
    assert #rootdiffs_intermsof_gens eq 4 and [#x : x in rootdiffs_intermsof_gens] eq [5,5,5,5];




    Z4 := IntegerRing(4);
    Z := Integers();

    C2_K := BaseChange(C2, FintoK);
    J2_K := Jacobian(C2_K);
    infty_pt := PointsAtInfinity(C2_K);
    assert #infty_pt eq 1;
    infty_pt := infty_pt[1];
    basis_2tors := [];
    for i := 1 to 4 do
        bool, pt_i := IsPoint(C2_K,[roo[i,1],0]);
        jac_pt := J2_K ! [pt_i, infty_pt];
        assert 2*jac_pt eq J2_K ! 0;
        Append(~basis_2tors,jac_pt);
    end for;
    all_2tors := [];
    all_2tors_coords := [];
    for i, j, k, l in [0,1] do
        Append(~all_2tors,i*basis_2tors[1] + j*basis_2tors[2] + k*basis_2tors[3] + l*basis_2tors[4]);
        Append(~all_2tors_coords,[i,j,k,l]);
    end for;
    printf "Done listing all 2-torsion points over splitting field of f\n";

    PK<x> := PolynomialRing(K);
    Ls := [];
    basis_4tors := <>;
    mat_gens := [[] : k in [1..#gens]];
    gens_of_quadextns := [];
    for i := 1 to #rootdiffs do
        ith_rootdiff := rootdiffs[i];
        ith_forsqrts := for_sqrts[i];
        ith_rditogens := rootdiffs_intermsof_gens[i];
        V := VectorSpace(GF(2),#gens);
        V_Z := RSpace(Z,#gens);
        ithvectors := [V ! y : y in ith_rditogens];
        basis_ithvectors := Basis(sub<V|ithvectors>);
        basismat := Matrix(GF(2),#basis_ithvectors,#gens,basis_ithvectors);
        solutions := [];
        leftovers := [];
        for j := 1 to #ithvectors do
            sol := Solution(basismat,ithvectors[j]);
            Append(~solutions,sol);
            if #basis_ithvectors ne 0 then
                leftover := Eltseq((&+[(sol[k] eq 1) select V_Z ! basis_ithvectors[k] else V_Z ! 0 : k in [1..#basis_ithvectors]] - V_Z ! ith_rditogens[j]) div 2);
                Append(~leftovers,leftover);
            end if;
        end for;
//    	print #gens, ithvectors, basis_ithvectors, solutions;
        ith_gens := [&*[(v[k] eq 0) select 1 else gens[k] : k in [1..#gens]] : v in basis_ithvectors];
        Append(~gens_of_quadextns,ith_gens);
        if #ith_gens eq 0 then
            Li := K;
            Lidotks := [];
        elif #ith_gens eq 1 then
            Li  := ext<K | [x^2 - ith_gens[k] : k in [1..#ith_gens]]>;
            Lidotks := [Li.1];
        elif #ith_gens eq 2 then
            alpha, beta := Explode(ith_gens);
            defpolLi := x^4-2*(alpha+beta)*x^2+(alpha-beta)^2;
            Li<w> := ext<K | defpolLi>;
            Mw := Matrix(K,4,4,[[0,1,1,0],[alpha,0,0,1],[beta,0,0,1],[0,beta,alpha,0]]);
            e1 := VectorSpace(K,4) ! [1,0,0,0];
            cofb_mat := Matrix(K,4,4,[Eltseq(e1*Mw^(i-1)) : i in [1..4]]);
            cofb_invmat := cofb_mat^-1;
            sqrtalpha := &+[cofb_invmat[2,k]*w^(k-1) : k in [1..4]];
            sqrtbeta := &+[cofb_invmat[3,k]*w^(k-1) : k in [1..4]];
            Lidotks := [sqrtalpha, sqrtbeta];
            assert sqrtalpha^2 eq alpha;
            assert sqrtbeta^2 eq beta;
/*
            Li  := ext<K | [x^2 - ith_gens[k] : k in [1..#ith_gens]]>;
            Lidotks := [Li.1, Li.2];
*/
        elif #ith_gens eq 3 then
            alpha, beta, gamma := Explode(ith_gens);
            tempPK<tt,uu> := PolynomialRing(K,2);
            defpolLi := UnivariatePolynomial(Resultant(tt^4-2*(alpha+beta)*tt^2+(alpha-beta)^2, (uu-tt)^2-gamma, tt));
            Li<w> := ext<K | defpolLi>;
            Mw := Matrix(K,8,8,[[0,1,1,1,0,0,0,0],[alpha,0,0,0,1,0,1,0],[beta,0,0,0,1,1,0,0],[gamma,0,0,0,0,1,1,0],[0,beta,alpha,0,0,0,0,1],[0,0,gamma,beta,0,0,0,1],[0,gamma,0,alpha,0,0,0,1],[0,0,0,0,gamma,alpha,beta,0]]);
            e1 := VectorSpace(K,8) ! [1,0,0,0,0,0,0,0];
            cofb_mat := Matrix(K,8,8,[Eltseq(e1*Mw^(i-1)) : i in [1..8]]);
            cofb_invmat := cofb_mat^-1;
            sqrtalpha := &+[cofb_invmat[2,k]*w^(k-1) : k in [1..8]];
            sqrtbeta := &+[cofb_invmat[3,k]*w^(k-1) : k in [1..8]];
            sqrtgamma := &+[cofb_invmat[4,k]*w^(k-1) : k in [1..8]];
            Lidotks := [sqrtalpha, sqrtbeta, sqrtgamma];
            assert sqrtalpha^2 eq alpha;
            assert sqrtbeta^2 eq beta;
            assert sqrtgamma^2 eq gamma;
        elif #ith_gens eq 4 then
            alpha, beta, gamma, delta := Explode(ith_gens);
            tempPK<tt,uu> := PolynomialRing(K,2);
            defpolLi := UnivariatePolynomial(Resultant(tt^4-2*(alpha+beta)*tt^2+(alpha-beta)^2, (uu-tt)^4-2*(gamma+delta)*(uu-tt)^2+(gamma-delta)^2, tt));
            Li<w> := ext<K | defpolLi>;
            Msqrtalpha := Matrix(K,16,16,[[0,1] cat zeros(14),[alpha] cat zeros(15),zeros(5) cat [1] cat zeros(10),zeros(6) cat [1] cat zeros(9),zeros(7) cat [1] cat zeros(8),[0,0,alpha] cat zeros(13),[0,0,0,alpha] cat zeros(12),[0,0,0,0,alpha] cat zeros(11), zeros(11) cat [1] cat zeros(4), zeros(12) cat [1] cat zeros(3), zeros(13) cat [1] cat zeros(2), zeros(8) cat [alpha] cat zeros(7), zeros(9) cat [alpha] cat zeros(6), zeros(10) cat [alpha] cat zeros(5), zeros(15) cat [1], zeros(14) cat [alpha,0]]);
            Msqrtbeta := Matrix(K,16,16,[[0,0,1] cat zeros(13),zeros(5) cat [1] cat zeros(10),[beta] cat zeros(15),zeros(8) cat [1] cat zeros(7),zeros(9) cat [1] cat zeros(6),[0,beta] cat zeros(14),zeros(11) cat [1] cat zeros(4),zeros(12) cat [1,0,0,0], [0,0,0,beta] cat zeros(12), [0,0,0,0,beta] cat zeros(11), zeros(14) cat [1,0], zeros(6) cat [beta] cat zeros(9), zeros(7) cat [beta] cat zeros(8), zeros(15) cat [1], zeros(10) cat [beta] cat zeros(5), zeros(13) cat [beta,0,0]]);
            Msqrtgamma := Matrix(K,16,16,[[0,0,0,1] cat zeros(12),zeros(6) cat [1] cat zeros(9),zeros(8) cat [1] cat zeros(7),[gamma] cat zeros(15),zeros(10) cat [1] cat zeros(5),zeros(11) cat [1] cat zeros(4),[0,gamma] cat zeros(14),zeros(13) cat [1,0,0], [0,0,gamma] cat zeros(13), zeros(14) cat [1,0], [0,0,0,0,gamma] cat zeros(11), [0,0,0,0,0,gamma] cat zeros(10), zeros(15) cat [1], zeros(7) cat [gamma] cat zeros(8), zeros(9) cat [gamma] cat zeros(6), zeros(12) cat [gamma,0,0,0]]);
            Msqrtdelta := Matrix(K,16,16,[[0,0,0,0,1] cat zeros(11),zeros(7) cat [1] cat zeros(8),zeros(9) cat [1] cat zeros(6),zeros(10) cat [1] cat zeros(5),[delta] cat zeros(15),zeros(12) cat [1,0,0,0],zeros(13) cat [1,0,0],[0,delta] cat zeros(14), zeros(14) cat [1,0], [0,0,delta] cat zeros(13), [0,0,0,delta] cat zeros(12), zeros(15) cat [1], zeros(5) cat [delta] cat zeros(10), zeros(6) cat [delta] cat zeros(9), zeros(8) cat [delta] cat zeros(7), zeros(11) cat [delta] cat zeros(4)]);
            Mw := Msqrtalpha + Msqrtbeta + Msqrtgamma + Msqrtdelta;
            e1 := VectorSpace(K,16) ! ([1] cat zeros(15));
            cofb_mat := Matrix(K,16,16,[Eltseq(e1*Mw^(i-1)) : i in [1..16]]);
            cofb_invmat := cofb_mat^-1;
            sqrtalpha := &+[cofb_invmat[2,k]*w^(k-1) : k in [1..16]];
            sqrtbeta := &+[cofb_invmat[3,k]*w^(k-1) : k in [1..16]];
            sqrtgamma := &+[cofb_invmat[4,k]*w^(k-1) : k in [1..16]];
            sqrtdelta := &+[cofb_invmat[5,k]*w^(k-1) : k in [1..16]];
            Lidotks := [sqrtalpha, sqrtbeta, sqrtgamma, sqrtdelta];
            assert sqrtalpha^2 eq alpha;
            assert sqrtbeta^2 eq beta;
            assert sqrtgamma^2 eq gamma;
            assert sqrtdelta^2 eq delta;
        end if;
        Rhalf_elt := [];
        for j := 1 to 5 do
//    	    print i,j;
            if j eq i then
                Append(~Rhalf_elt, Li ! 0);
                assert Rhalf_elt[#Rhalf_elt]^2 eq rootdiffs[i,j];
            else
                sol := solutions[j];
                if #basis_ithvectors eq 0 then
                    den := 1;
                else
                    den := &*[(sol[k] eq 0) select 1 else Lidotks[k] : k in [1..#basis_ithvectors]];
                    leftover := leftovers[j];
                    adjustment := &*[gens[k]^leftover[k] : k in [1..#leftover]];
                    den := den/adjustment;
                end if;

//        		print ith_forsqrts[j];
                if ith_forsqrts[j] eq 0 then
                    assert den^2 eq rootdiffs[i,j];
                    Append(~Rhalf_elt,den);
                    assert Rhalf_elt[#Rhalf_elt]^2 eq rootdiffs[i,j];
                else
                    Append(~Rhalf_elt,Li ! ith_forsqrts[j]/den);
                    assert Rhalf_elt[#Rhalf_elt]^2 eq rootdiffs[i,j];
                end if;
            end if;
        end for;
        J2_Li := BaseExtend(J2_K,Li);
        P_i := elt<J2_Li | [Ur(roo[i,1],Rhalf_elt), Vr(roo[i,1],Rhalf_elt)]>;
        assert 4*P_i eq J2_Li ! 0;
        Append(~Ls,Li);
        basis_4tors := basis_4tors cat <P_i>;
        for k := 1 to #gens do
            sigma_Rhalfelt := [(-1)^(Z ! rootdiffs_intermsof_gens[i,j,k])*Rhalf_elt[j] : j in [1..5]];
            sigma_Pi := elt<J2_Li | [Ur(roo[i,1],sigma_Rhalfelt), Vr(roo[i,1],sigma_Rhalfelt)]>;
            kthmat_row := all_2tors_coords[Index(all_2tors,sigma_Pi-P_i)];
            mat_gens[k] := mat_gens[k] cat [kthmat_row];
        end for;
//    	print #basis_4tors;
    end for;

    mats := [IdentityMatrix(Z4,4) + 2*Matrix(Z4,4,4,matgen) : matgen in mat_gens];
    matgrp := sub<GL(4,Z4) | mats>;
    assert IsElementaryAbelian(matgrp);
    assert #matgrp eq 2^#gens;
//    return sub<kerf | mats>;
    return matgrp, basis_4tors, Ls;
end intrinsic;

intrinsic uptoGconjugacy(G :: Grp, ZK :: SeqEnum) -> SeqEnum
{cleans up the given list ZK of subgroups of G, by searching and removing G-conjugate subgroups}
    ZKtrue := [];
    for K in ZK do
        Kord := #K;
        ZKtrue_sub := [x : x in ZKtrue | #x eq Kord];
        if not exists(temp){Kold : Kold in ZKtrue_sub | IsConjugate(G,K,Kold)} then
            Append(~ZKtrue,K);
        end if;
    end for;
    return ZKtrue;
end intrinsic;

intrinsic IsAConjugateIn(H :: Grp, lis :: SeqEnum) -> BoolElt, RngIntElt
{returns whether a GSp(4,Zmod4)-conjugate of H lies in the given list of subgroups,
and if true, also returns the index of the conjugate in the given list}
	boo := exists(ii){i : i in [1..#lis] | IsConjugate(G,H,lis[i])};
	if boo then return boo, ii; end if;
    return false;
end intrinsic;

intrinsic PossibleLifts(Gamma :: GrpMat, N :: GrpMat, sampledconjclasses :: Set) -> SeqEnum
{This returns all subgroups of GSp(4,Zmod4) upto conjugacy, that have N as a subgroup, with Gamma equal to the
corresponding quotient. There may be some repeats.}
    overgrp := Normalizer(Gamma @@ f, N);
	comps := Complements(overgrp, kerf, N);
	printf "Number of complements = %o\n", #comps;
	ans := [];
	for C in comps do
		if C subset kerchi then continue; end if;
		tempccs := ConjugacyClasses(C);
		if forall(ii){i : i in sampledconjclasses | not IsDisjoint(Orbit(G,CCs[i,3]),Set(C))} then
			if exists(x){cc : cc in tempccs | cc[1] eq 2 and not cc[3] in kerchi} then
				Append(~ans,C);
			end if;
		end if;
//		if Index(comps,C) mod 100 eq 0 then print Index(comps,C); end if;
	end for;
	return ans;
end intrinsic;

intrinsic PossibilitiesFromFrobSampling(C :: CrvHyp, mod2img :: GrpMat, mod4imgover2fld :: GrpMat : CCsshowingup := [], possibs := [], possible_CCstats := [], primesstart := 4, primesend := 100, list_of_counts := [0/1 : i in [1..#CCs]]) -> SeqEnum
{returns the list of possibilities for mod-4 Galois image for the Jacobian of the given genus 2 curve C,
based on sampling Frobenius matrices for primes upto a given bound.}
    badprimes := &*BadPrimes(C)*2;
    if &+(list_of_counts) eq 0 then
        if #mod4imgover2fld eq 2^11 then
            return [mod2img @@ f];
        else
            while &+(list_of_counts) lt 50 do
                p := NthPrime(primesstart);
                if badprimes mod p ne 0 then
                    frobpmat := frobconjclass(C,p);
                    assert exists(iii){i : i in [1..#CCs] | IsConjugate(G,CCs[i][3],frobpmat)};
//        		    print primesstart, p, iii;
                    list_of_counts[iii] := list_of_counts[iii]+1;
                    if not iii in CCsshowingup then Append(~CCsshowingup,iii); end if;
                end if;
                primesstart := primesstart + 1;
            end while;

            Norm_mod2img := Normalizer(GSp2,mod2img);
            Norm_mod2img_inv := Norm_mod2img @@ f;
            BigG := GL(4,Integers(4));
            if #mod4imgover2fld ne 1 then assert IsElementaryAbelian(mod4imgover2fld); end if;
            conjugates_mod4imgover2fld := [H : H in Conjugates(BigG, mod4imgover2fld) | H subset kerf];
            printf "There are %o GL(4)-conjugates of the mod4 img over Q(A[2]) inside kerf = ker(GSp(4,Z/4) --> GSp(4,Z/2))\n", #conjugates_mod4imgover2fld;
            desired_conjmod4imgover2flds := [];
            kerfconjclasses := {i : i in [1..#CCs] | CCs[i,3] in kerf};
            for H in conjugates_mod4imgover2fld do
//                if not (Set(CCsshowingup) meet kerfconjclasses) subset {classmap(cc[3]) : cc in ConjugacyClasses(H)} then continue; end if;
                if exists(ii){i : i in Set(CCsshowingup) meet kerfconjclasses | IsDisjoint(Orbit(G,CCs[i,3]),Set(H))} then continue; end if;
                Hconjs := Conjugates(Norm_mod2img_inv,H);
                if not Hconjs in desired_conjmod4imgover2flds then
                    Append(~desired_conjmod4imgover2flds, Hconjs);
                end if;
            end for;
            printf "There are %o possible conjugacy classes of mod4 img over Q(A[2]) inside Normalizer(pi^-1(mod2img))\n", #desired_conjmod4imgover2flds;

            all_possibilities := [];
            for Hconjs in desired_conjmod4imgover2flds do
                H := Random(Hconjs);
//    			print Set(CCsshowingup);
                lifts := PossibleLifts(mod2img,H,Set(CCsshowingup));
                printf "Number of computed complements = %o.\n", #lifts;
                for li in lifts do
                    if not IsAConjugateIn(li,all_possibilities) then
                       Append(~all_possibilities,li);
                    end if;
                end for;
            end for;
            printf "Upto conjugacy = %o\n", #all_possibilities;
            if #all_possibilities eq 1 then return all_possibilities; end if;

            all_ccstats := [];
            subs_with_ccstat := [];
            for li in all_possibilities do
//                ccstat := GassmanDistribution(G, li : CCG := CCs, classmap := classmap);
                ccstat := GassmanDistribution(G, li : CCG := CCs, classmap := classmap, ordsH := Divisors(#li));
                if not ccstat in all_ccstats then
                    Append(~all_ccstats,ccstat);
                    Append(~subs_with_ccstat,[li]);
                else
                    indi := Index(all_ccstats,ccstat);
                    subs_with_ccstat[indi] := subs_with_ccstat[indi] cat [li];
                end if;
            end for;

            subs_with_ccstat_GLconjinfo := [];
            for k := 1 to #subs_with_ccstat do
                subs := subs_with_ccstat[k];
                temp := [];
                for l := 1 to #subs do
                    H := subs[l];
                    bool := true;
                    for m := 1 to #temp do
                        if IsConjugate(BigG,H,temp[m][1]) then
                            temp[m] := temp[m] cat [H];
                            bool := false;
                            break;
                        end if;
                    end for;
                    if bool then Append(~temp,[H]); end if;
                end for;
                Append(~subs_with_ccstat_GLconjinfo,temp);
            end for;
            possibs := subs_with_ccstat_GLconjinfo;
            possible_CCstats := all_ccstats;
        end if;
    end if;

    print #possibs, [[#y : y in x] : x in possibs];

    possible_validccs := [allvalidccs(CCstatH) : CCstatH in possible_CCstats];
    skipfrobdistcalc := false;
    for N := primesstart to primesend do
        if N mod 100 eq 0 then print N; end if;
        if #possibs eq 1 then
            skipfrobdistcalc := true;
            possibilities := possibs;
            break;
        end if;
        p := NthPrime(N);
        if badprimes mod p eq 0 then continue; end if;
        frobpmat := frobconjclass(C,p);
        assert exists(iii){i : i in [1..#CCs] | IsConjugate(G,CCs[i][3],frobpmat)};
//	    print N, p, iii;
        list_of_counts[iii] := list_of_counts[iii]+1;
        if not iii in CCsshowingup then
//    		print #possibs, #possible_CCstats;
            Append(~CCsshowingup,iii);
            possibs := [possibs[j] : j in [1..#possibs] | iii in possible_validccs[j]];
            possible_CCstats := [possible_CCstats[j] : j in [1..#possible_CCstats] | iii in possible_validccs[j]];
            possible_validccs := [possible_validccs[j] : j in [1..#possible_validccs] | iii in possible_validccs[j]];
        end if;
    end for;

    if not skipfrobdistcalc then
        totalprimes := &+list_of_counts;
        freqstat := [list_of_counts[i]/totalprimes : i in [1..#list_of_counts]];
//    	totalprimes;
        V := VectorSpace(RealField(),#CCs);
        localmindists := [];
        for i := 1 to #possible_CCstats do
            mindist := 1;
            for j := 1 to #possible_CCstats do
                if j ne i then mindist := Minimum(mindist,Norm(V ! possible_CCstats[j] - V ! possible_CCstats[i])); end if;
            end for;
            Append(~localmindists,mindist/4);
        end for;
        print localmindists;
        possibilities := [];
        errors := [];
        for i := 1 to #possible_CCstats do
            CCstatH := possible_CCstats[i];
            err := V ! CCstatH - V ! freqstat;
            print i, Norm(err), localmindists[i];
            if Norm(err) lt localmindists[i] then
                Append(~possibilities,possibs[i]);
                Append(~errors,Norm(err));
            end if;
        end for;
        print #possibilities, #errors;
        print errors;
    end if;

    if #possibilities ne 1 then
        print "More primes need to be sampled. Sampling more primes...";
        newprimesstart := Maximum(primesstart,primesend + 1);
        newprimesend := newprimesstart + 100;
    	return PossibilitiesFromFrobSampling(C, mod2img, mod4imgover2fld : CCsshowingup := CCsshowingup, possibs := possibs, possible_CCstats := possible_CCstats, primesstart := newprimesstart, primesend := newprimesend, list_of_counts := list_of_counts);
    elif #possibilities[1] gt 1 then
        print "Sampled data about frobenius cannot distinguish the image upto GL conjugacy uniquely.";
        print "The image could be one of the following subgroups:";
//    	print possibilities[1];
//    	print "Looking at global data to distinguish between the", #possibilities[1], "possible images...";
        return distinguish(C,possibilities[1]);
    else
    	return possibilities[1][1];
    end if;
end intrinsic;

/*
intrinsic Mod4EnhancedImage(X :: CrvHyp : prec := 100) -> .
{returns the image of the mod4 enhanced representation (as a subgroup of GL(4,Z/4) and as a set of enhanced elements).
TODO: add details.}
    Z4 := Integers(4);
    Z2 := Integers(2);
    Galgrp2, Galmap2, rho_enhanced, O := EnhancedRepresentationMod2PQM(X : prec := prec);
    boo, nu := HasPolarizedElementOfDegree(O,1); assert boo;
    G2, Omod2cross, aut2 := EnhancedImageGL4(O,nu,2);
    mod2img := sub<G2|[EnhancedElementRecord(rho_enhanced(x))`GL4 : x in Generators(Galgrp2)]>;
    G4, Omod4cross, aut4 := EnhancedImageGL4(O,nu,4);
    phi := hom<G4 -> G2 | [ChangeRing(g,Z2) : g in GeneratorsSequence(G4)]>;
    kerphi := Kernel(phi);
    printf "Enhanced semi-direct products mod %o have orders %o.\nKernel of the natural reduction has abelian invariants %o.\n\n", [4,2], [#G4,#G2], AbelianInvariants(kerphi);

    Gl4 := GL(4,Z4);
    H, basis, Ls := mod4imageovertwotorsionfield(X);
    assert IsElementaryAbelian(H);
    printf "Galois images mod %o have orders %o,\nwith abelian invariants of kernel = %o.\n", [4,2], [#mod2img*#H,#mod2img], AbelianInvariants(H);
    ConjugatesH := Conjugates(Gl4,H);
    goodHs := [Hconj : Hconj in ConjugatesH | Hconj subset kerphi];
    goodHs := uptoGconjugacy(G4,goodHs);
    assert #goodHs ge 1;
    printf "Found %o possibilities for mod 4 image over 2-torsion field inside enhanced semidirect product.\n", #goodHs;
    pullback := mod2img @@ phi;
    mod4img_possibilities := &cat[Complements(pullback,kerphi,Hconj) : Hconj in goodHs];
    printf "Found %o possibilities for mod 4 image over Q inside enhanced semidirect product.\n\n", #mod4img_possibilities;
    if #mod4img_possibilities eq 1 then return mod4img_possibilities[1]; end if;

    G2X := mod2image(X); assert IsConjugate(GL(4,Z2),mod2img,ChangeRing(G2X,Z2));
    printf "Sampling Frobenius to compute image in GSp(4,Z/4)...\n";
    ans := PossibilitiesFromFrobSampling(X, G2X, H);
    printf "Found %o possibilities for mod 4 image over Q inside GSp(4,Z/4).\n", #ans;
    assert #ans eq 1;
    ans := ans[1];
/*
    f2 := hom<ans -> GL(4,Z2) | [ChangeRing(g,Z2) : g in GeneratorsSequence(ans)]>;
    ans4over2 := Kernel(f2);
    AllconjsofansinG4 := [];
    printf "Trying to find all those GL4-conjugates of the just-found mod 4 image, that lie in the enhanced semidirect product...\n";
    for Hconj in goodHs do
        boo, M := IsConjugate(Gl4,ans4over2,Hconj);
        newans := Conjugate(ans,M);
        assert Hconj subset newans;
        AllconjsofansinG4 := AllconjsofansinG4 cat [x : x in Conjugates(Normalizer(Gl4,Hconj),newans) | x subset G4];
    end for;
    AllconjsofansinG4_uptoG4conjugacy := uptoGconjugacy(G4,AllconjsofansinG4);
*/
/*
    AllconjsofansinG4_uptoG4conjugacy := [x`subgroup : x in Subgroups(G4 : OrderEqual := #ans) | IsConjugate(Gl4,ans,x`subgroup)];
    printf "Found %o GL4-conjugates of the just-found mod 4 image, lying inside the enhanced semidirect product upto conjugacy\n", #AllconjsofansinG4_uptoG4conjugacy;
    final := [x : x in AllconjsofansinG4_uptoG4conjugacy | IsConjugate(G2,phi(x),mod2img)];
    if #final eq 1 then return final[1]; end if;
    return final;
end intrinsic;
*/

intrinsic GeometricEndomorphismOrder(X::CrvHyp : prec:=30) -> Any
  {Given X/F such that Jac(X) is a PQM surface, returns the geometric endomorphism ring as an order in a quaternion algebra}

    CC:=ComplexFieldExtra(prec);
    //CC`epscomp:=10^-Floor(prec/2);
    assert BaseRing(X) eq Rationals();
    assert IsSimplifiedModel(X);
    B1,B2,B3:=HeuristicEndomorphismAlgebra( X : CC:=true);
    assert IsQuaternionAlgebra(B2);

    f:=HyperellipticPolynomials(X);
    XR:=RiemannSurface(f,2 : Precision:=prec);
    //assert that the basepoint is of the form (x,0)
    assert Coordinates(XR`BasePoint)[2] eq 0;

    BPM:=ChangeRing(BigPeriodMatrix(XR),CC);
    //endos:=HeuristicEndomorphismRepresentation( X : CC:=true);
    endos := GeometricEndomorphismRepresentationCC(BPM);
    endosM4:=[ ChangeRing(m[2],Rationals()) : m in endos ]; 
    Bmat:=MatrixAlgebra< Rationals(), 4 | endosM4 >;
    tr, B, maptoB := IsQuaternionAlgebra(Bmat);
    //assert maptoB is indeed an algebra-hom
    assert forall(b){ [Bmat.u,Bmat.v] : u,v in [1..4] | maptoB(Bmat.u*Bmat.v) eq maptoB(Bmat.u)*maptoB(Bmat.v) };

    Obasis:=[ maptoB(b) : b in endosM4 ];
    O:=QuaternionOrder(Obasis : IsBasis:=true);
    assert Basis(O) eq Obasis;
    return O;
end intrinsic;

intrinsic Mod4EnhancedImage(X :: CrvHyp : prec := 100, precise := true, Endring := 0) -> .
{returns the image of the mod4 enhanced representation (as a subgroup of GL(4,Z/4) and as a set of enhanced elements).
TODO: add details.}
    Z4 := Integers(4);
    Z2 := Integers(2);
    if Type(Endring) eq RngIntElt then
/*
        try
            _, _, _, O := EndomorphismRepresentationPQM(X : prec := prec); // We just want O, to construct G4, G2.
        catch e;
            _, _, _, O := Mod2GaloisMapPQM(X : prec := prec); // We just want O, to construct G4, G2.
        end try;
*/
        O := GeometricEndomorphismOrder(X : prec := prec);
    else
        O := Endring;
    end if;
    boo, nu := HasPolarizedElementOfDegree(O,1); assert boo;
    G2, Omod2cross, aut2 := EnhancedImageGL4(O,nu,2);
    G4, Omod4cross, aut4 := EnhancedImageGL4(O,nu,4);
    phi := hom<G4 -> G2 | [ChangeRing(g,Z2) : g in GeneratorsSequence(G4)]>;
    kerphi := Kernel(phi);
    printf "The images in GL4 of the Enhanced semi-direct products mod %o have orders %o.\nKernel of the corresponding reduction has abelian invariants %o.\n\n", [4,2], [#G4,#G2], AbelianInvariants(kerphi);

    mod2img := mod2image(X);
    printf "Galois image mod 2 has order %o\n", #mod2img;
    Gl4 := GL(4,Z4);
    H, basis, Ls := mod4imageovertwotorsionfield(X);
    assert IsElementaryAbelian(H);
    printf "Galois image mod 4 has order %o,\nwith abelian invariants of kernel = %o.\n", #mod2img*#H, AbelianInvariants(H);
/*
    ConjugatesH := Conjugates(Gl4,H);
    goodHs := [Hconj : Hconj in ConjugatesH | Hconj subset kerphi];
    goodHs := uptoGconjugacy(G4,goodHs);
    assert #goodHs ge 1;
    printf "Found %o possibilities for mod 4 image over 2-torsion field inside enhanced semidirect product.\n", #goodHs;
    pullback := ChangeRing(mod2img,Z2) @@ phi;
    mod4img_possibilities := &cat[Complements(pullback,kerphi,Hconj) : Hconj in goodHs];
    printf "Found %o possibilities for mod 4 image over Q inside enhanced semidirect product.\n\n", #mod4img_possibilities;
    if #mod4img_possibilities eq 1 then return mod4img_possibilities[1]; end if;
*/

    printf "Sampling Frobenius to compute image in GSp(4,Z/4)...\n";
    ans := PossibilitiesFromFrobSampling(X, mod2img, H);
    printf "Found %o possibilities for mod 4 image over Q inside GSp(4,Z/4).\n", #ans;

/*
    ans := ans[1];
    f2 := hom<ans -> GL(4,Z2) | [ChangeRing(g,Z2) : g in GeneratorsSequence(ans)]>;
    ans4over2 := Kernel(f2);
    AllconjsofansinG4 := [];
    printf "Trying to find all those GL4-conjugates of the just-found mod 4 image, that lie in the enhanced semidirect product...\n";
    for Hconj in goodHs do
        boo, M := IsConjugate(Gl4,ans4over2,Hconj);
        newans := Conjugate(ans,M);
        assert Hconj subset newans;
        AllconjsofansinG4 := AllconjsofansinG4 cat [x : x in Conjugates(Normalizer(Gl4,Hconj),newans) | x subset G4];
    end for;
    AllconjsofansinG4_uptoG4conjugacy := uptoGconjugacy(G4,AllconjsofansinG4);
*/

/*
    assert #ans eq 1;
    ans := ans[1];
    AllconjsofansinG4_uptoG4conjugacy := [x`subgroup : x in Subgroups(G4 : OrderEqual := #ans) | IsConjugate(Gl4,ans,x`subgroup)];
    printf "Found %o GL4-conjugates of the just-found mod 4 image, lying inside the enhanced semidirect product upto conjugacy\n", #AllconjsofansinG4_uptoG4conjugacy;
*/
    ansords := Sort(Setseq({#H : H in ans}));
    AllconjsofansinG4_uptoG4conjugacy := [];
    for ansord in ansords do
        AllconjsofansinG4_uptoG4conjugacy := AllconjsofansinG4_uptoG4conjugacy cat [x`subgroup : x in Subgroups(G4 : OrderEqual := ansord) | exists(temp){H : H in ans | IsConjugate(Gl4,H,x`subgroup)}];
    end for;
    printf "Found %o GL4-conjugates of the mod 4 image possibilities, lying inside the enhanced semidirect product upto conjugacy\n", #AllconjsofansinG4_uptoG4conjugacy;

    if #AllconjsofansinG4_uptoG4conjugacy eq 1 then return AllconjsofansinG4_uptoG4conjugacy; end if;

    if not precise then return AllconjsofansinG4_uptoG4conjugacy; end if;

    // need to fix the following. Either Mod2EnhancedImage is not working properly, or phi(x) need not be conjugate to Mod2EnhancedImage
    mod2enhimg := Mod2EnhancedImage(X);
    printf "Number of possibilities for the mod-2 enhanced image : %o, and their orders : \n%o\n\n", #mod2enhimg, [#x : x in mod2enhimg];
    final := [x : x in AllconjsofansinG4_uptoG4conjugacy | exists(y){y : y in mod2enhimg | IsConjugate(G2,phi(x),y)}];
    if #final eq 1 then return final[1]; end if;
    return final;
end intrinsic;
