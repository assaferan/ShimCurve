// WARNING: This file has not been updated to account for code refactoring


/*
s:=GeneraTableToRecords(6,1,4 : torsioninvariants:=[2], genus:=0, endogroup:=" C2 ", sort:=true)[1];

rec<recformat<n: IntegerRing(), genus, fuchsindex, torsioninvariants, endogroup, AutmuOnorms, Hsplit, generators, ramification_data> | 
genus := 0,
fuchsindex := 6,
torsioninvariants := [ 2 ],
endogroup :=  C2 ,
AutmuOnorms := { 1, 6 },
Hsplit := false,
generators :=  [ < 1, [ 1, 0, 2, 0 ] >, < 1, [ 3, 1, 0, 1 ] >, < 1, [ 1, 2, 2, 0 ] >, < 1, [ 3, 0, 3, 3 ] >, < 1, [ 3, 2, 3, 1 ] >, < 1, [ 3, 0, 0, 0 ] >, < -3*j + k, [ 2, 0, 1, 0 ] > ] ,
ramification_data := [
(1, 2, 5, 3, 4, 6),
(1, 3)(2, 5)(4, 6),
(1, 4)(2, 3)
]>
]>
*/


B<i,j,k>:=QuaternionAlgebra< Rationals() | 3,-1 >;
O:=QuaternionOrder([ 1, 1/2 + 1/2*i + 1/2*j + 1/2*k, 1/2 - 1/2*i + 1/2*j - 1/2*k, 1/2 - 1/2*i - 1/2*j + 1/2*k ]);
N:=4;
Ocirc:=EnhancedSemidirectProduct(O : N:=4);

tr,mu:=HasPolarizedElementOfDegree(O,1);
mu;
assert mu^2 eq -6;
IsTwisting(O,mu);
AutmuO:=Aut(O,mu);
AutmuO;


Hgens:=[ Ocirc!< 1, [ 1, 0, 2, 0 ] >, Ocirc!< 1, [ 3, 1, 0, 1 ] >, Ocirc!< 1, [ 1, 2, 2, 0 ] >, Ocirc!< 1, [ 3, 0, 3, 3 ] >, Ocirc!< 1, [ 3, 2, 3, 1 ] >, Ocirc!< 1, [ 3, 0, 0, 0 ] >, Ocirc!< -3*j + k, [ 2, 0, 1, 0 ] > ];
HgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in Hgens ];
HGL4:=sub< GL(4,ResidueClassRing(N)) | HgensGL4 >;

EnhancedElementRecord(Hgens[2]);

FixedSubspace(HGL4);

G:=EnhancedImageGL4(AutmuO,O,N);
elliptic:=EnhancedEllipticElements(O,mu);
elliptic; 

mon:=EnhancedRamificationData(HGL4,G,O,mu);
mon;
Genus(mon);

X,phi:=BelyiMap(mon);
BelyiMap:=LFT(phi,[3,2,1]);

GeneratePQMCurves(6 : BelyiMap:=BelyiMap, MestreIsSplit:=true, LinYang:=false, global:=true);



