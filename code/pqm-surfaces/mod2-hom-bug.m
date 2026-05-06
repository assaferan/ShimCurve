Rx<x>:=PolynomialRing(Rationals());
//f:=-x^5+4*x^4-10*x^3+8*x^2-2*x; //this one actually works
//f:= 3*x^5 + 3*x^4 - 4*x^3 + 3*x - 1; //this returns a map which is not a hom
//f:=-83*x^6-909*x^5-3075*x^4-2875*x^3-2460*x^2+1422*x-844; //this has PQM disc 10, the map is a homomorphism!! It also has image of size 48 so takes about 30 mins to run. 
//f := -x^6 - 8*x^5 - 2*x^4 + 36*x^3 - 16*x^2 + 8*x + 8; //PQM6 example where map is not a hom

prec:=30;
CC:=ComplexFieldExtra(prec);
X:=HyperellipticCurve(f);
TwoTorsionSubgroup(Jacobian(X));


////////////////////////////////
//The bug might have something to do with the BASEPOINT!
Rx<x>:=PolynomialRing(Rationals());
f:=-x^5+4*x^4-10*x^3+8*x^2-2*x;
prec:=30;
CC:=ComplexFieldExtra(prec);
QA2:=SplittingField(f);
ooplaces:=InfinitePlaces(QA2);
embC:=ooplaces[4];

frootsM:=[ a[1] : a in Roots(ChangeRing(f,QA2))];
frootsC:=[ CC!Evaluate(a,embC) : a in frootsM ];

XR:=RiemannSurface(f,2 : Precision:=prec);
BPM:=ChangeRing(BigPeriodMatrix(XR),CC);
Q:=AbelJacobi(XR![frootsC[2],0],XR`BasePoint);

Latendo:=RealLatticeOfPeriodMatrix(BPM);
IsCoercible(Latendo,Eltseq(RealVector(2*Q)));

P1:=ColumnSubmatrix(BPM,1,2);
IsCoercible(Latendo,Eltseq(RealVector(2*P1*Q)));

IntegralRightKernel();

endos:=GeometricEndomorphismRepresentationCC(BPM);
assert forall(e){ <endo[1], basis> : endo in endos, basis IsCoercible(Latendo,Eltseq(RealVector(endos[1,1]*ColumnSubmatrix(BPM,4,1))));

SmallBasePoint(X);
base_point_endo := X`base_point;

XR:=RiemannSurface(f,2 : Precision:=prec);

base_point_magma:= XR`BasePoint;

base_point_magma; //(-6.903181565, 0.0000000000)
base_point_endo; //(1 : -5 : 1)





L:=HeuristicEndomorphismFieldOfDefinition(X);
L:=NumberField(Polredbest(DefiningPolynomial(L)));

M:=Compositum(QA2,L);
Mdef:=DefiningPolynomial(M);
Mdefred:=Polredbest(Mdef);
M:=NumberField(Mdefred);


ooplaces:=InfinitePlaces(M);
//CAREFUL: we choose an embedding here which affects the final output.
embC:=ooplaces[1];

//These are the roots a_i of the hyperelliptic polynomial
// [(a_2,0)] - [(a_1,0)] will be an O/2O-basis element of A[2](C)
//after apply the Abel-Jacobi map. assert a1 is rational.
frootsM:=[ a[1] : a in Roots(ChangeRing(f,M))];
frootsC:=[ CC!Evaluate(a,embC) : a in frootsM ];

//We can compute endos directly from the period matrix
XR:=RiemannSurface(f,2 : Precision:=prec);
BPM:=ChangeRing(BigPeriodMatrix(XR),CC);
Q:=AbelJacobi(XR![frootsC[2],0],XR`BasePoint);

Latendo:=RealLatticeOfPeriodMatrix(BPM);
IsCoercible(Latendo,Eltseq(RealVector(2*Q)));

/////////////////////////////////




GalM,mapM,rho2,O :=EnhancedRepresentationMod2PQM(X : prec:=prec);

N:=2;
GalM,map2,f2:=Mod2GaloisMapPQM(X);
GalM;
f2;
 
QA2:=SplittingField(f);
L:=HeuristicEndomorphismFieldOfDefinition(X);
assert Degree(L) eq 4;
assert IsSubfield(L,QA2);

M:=Domain(mapM(GalM.1));
JM:=Jacobian(ChangeRing(X,M));
T2,J2:=TwoTorsionSubgroup(JM);

assert IsMaximal(O);
tr,mu:=HasPolarizedElementOfDegree(O,1);

perm_rep:=EnhancedPermutationRepresentationMod2(O,mu);

//list the subgroups of the semidirect product isomorphic to D4 up to conjugation
D4subs := [ sub`subgroup : sub in Subgroups(Codomain(perm_rep)) | GroupName(sub`subgroup) eq "D4" ];
D4enh := [ [ Inverse(perm_rep)(a) : a in sub ] : sub in D4subs ];
D4enh := [ sub : sub in D4enh | #Set([a`element[1] : a in sub]) eq 4 ];

rho2_image := [ rho2(a) : a in GalM ];
exists(e){ [a,b] : a,b in rho2_image | a*b notin rho2_image };

Omod2_elements := Setseq(Set(quo(O,2)));
Omod2_units := [ a : a in Omod2_elements | IsUnit(a) ];
Oenh:=Codomain(rho2);


//Let's see
for subgrp in D4enh do 
  for unit in Omod2_units do 
    unit_enh := Oenh!<1,unit>;
    U:=Universe(Set(subgrp));
    item:=ChangeUniverse(Set([ unit_enh^-1*a*unit_enh : a in rho2_image ]),U);
    if item eq Set(subgrp) then 
      conj_elt:=unit_enh;
      D4grp := subgrp;
      conj_elt;
      D4grp;
    end if;
  end for;
end for;

// conj_elt^-1*rho2*conj_elt = D4grp which is true for the example that works


