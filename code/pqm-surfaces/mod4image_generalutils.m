Z4 := Integers(4);
G2 := Sp(4,2);
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
f := hom<G -> G2 | [ChangeRing(G.i,GF(2)) : i in [1..#Generators(G)]]>;
kerf := Kernel(f);

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
    G2 := Sp(4,GF(2));
    S6 := Sym(6);
    bool, phi := IsIsomorphic(S6, G2);
    somesubsG2 := Subgroups(G2 : OrderEqual := 48);
    somesubsS6 := Subgroups(S6 : OrderEqual := 48);
    A := AutomorphismGroup(G2);
    assert exists(out_aut){g : g in Generators(A) | not IsInner(g)};
    if Dimension(Fix(GModule(somesubsG2[1]`subgroup))) ne 0 then
        somesubsG2 := Reverse(somesubsG2);
    end if;
    if #Orbits(somesubsS6[1]`subgroup) eq 2 then
        somesubsS6 := Reverse(somesubsS6);
    end if;
    if IsConjugate(G2, somesubsG2[1]`subgroup, phi(somesubsS6[1]`subgroup)) then
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
/*
    rootdiffs;
*/

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
    if logdeg eq 11 then
    	return kerf, <>, [];
    end if;
/*
    print rootdiffs_intermsof_gens;
    print logdeg;
*/
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
    for i := 0 to 1 do
    for j := 0 to 1 do
    for k := 0 to 1 do
    for l := 0 to 1 do
	Append(~all_2tors,i*basis_2tors[1] + j*basis_2tors[2] + k*basis_2tors[3] + l*basis_2tors[4]);
	Append(~all_2tors_coords,[i,j,k,l]);
    end for;
    end for;
    end for;
    end for;


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
//	print #gens, ithvectors, basis_ithvectors, solutions;
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
//	    print i,j;
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

//		ith_forsqrts[j];
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
//	#basis_4tors;
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

intrinsic Mod4EnhancedImage(X :: CrvHyp : prec := 30) -> .
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
    printf "Enhanced semi-direct products mod %o have orders %o.\nKernel of the natural reduction has abelian invariants %o.\n", [4,2], [#G4,#G2], AbelianInvariants(kerphi);

    Gl4 := GL(4,Z4);
    H, basis, Ls := mod4imageovertwotorsionfield(X);
    assert IsElementaryAbelian(H);
    printf "Galois images mod %o have orders %o,\nwith abelian invariants of kernel = %o.\n", [4,2], [#mod2img*#H,#mod2img], AbelianInvariants(H);
    ConjugatesH := Conjugates(Gl4,H);
    goodHs := [Hconj : Hconj in ConjugatesH | Hconj subset kerphi];
    goodHs := uptoGconjugacy(G4,goodHs);
    assert #goodHs ge 1;
    printf "Found %o possibilities for mod 4 image over 2-torsion field.\n", #goodHs;
    pullback := mod2img @@ phi;
    mod4img_possibilities := &cat[Supplements(pullback,kerphi,Hconj) : Hconj in goodHs];
    printf "Found %o possibilities for mod 4 image over Q.\n", #mod4img_possibilities;
    if #mod4img_possibilities eq 1 then
        return mod4img_possibilities[1];
    else
        return mod4img_possibilities;
    end if;
end intrinsic;

