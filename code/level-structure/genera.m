


intrinsic EnhancedGenus(sigma::SeqEnum) -> RngIntElt
  {Compute genus from permutation triple
  f:X -> Y. 2gX-2 = deg(f)*(2gY-2) + sum_x\inX (ex -1). 
  ex is the ramification degree of x. An element of S_n acts on sheets of the cover. 
  x is ramified if x is sent to another point under the action of an isotropy subgroup,
  i.e. the cycle type corresponding to x has length >1. The length is the ramification degree.}
  d := Degree(Parent(sigma[1]));
  // Riemann-Hurwitz formula
  rhs := -2*d + &+[ &+[ e[2]*(e[1]-1) : e in CycleStructure(sig) ] : sig in sigma ];
  assert rhs mod 2 eq 0;
  g := Integers()!((rhs+2)/2);
  return g;
end intrinsic;

intrinsic EnhancedEllipticPoints(sigma::SeqEnum) -> Assoc
  {Only works for discriminant 6!}
  ells := AssociativeArray([2,3,4,6]);
  for n in [2,3,4,6] do
    ells[n] := 0;
  end for;
  // sigma is ordered as the cycles above 2, 4, 6
  bottom := [2,4,6];
  for i->sig in sigma do
    for e in CycleStructure(sig) do
      n := bottom[i] div e[1];
      if (n gt 1) then
        assert IsDefined(ells, n);
        ells[n] +:= e[2];
      end if;
    end for;
  end for;
  return ells;
end intrinsic;

intrinsic EnhancedGenus(H::GrpMat, G::GrpMat,O::AlgQuatOrd,mu::AlgQuatOrdElt) -> Any 
  {compute the genus}

  sigma:=EnhancedRamificationData(H,G,O,mu);
  return EnhancedGenus(sigma);
end intrinsic;

/*
intrinsic EnhancedCosetRepresentation(G::GrpMat,H::GrpMat,Gplus::GrpMat) -> HomGrp
{}

Hnew1:=sub<G | H, -H!1 >;
Hnew2:= Hnew1 meet Gplus;
T := CosetTable(G,Hnew2);
piH := CosetTableToRepresentation(G,T);
return piH;
end intrinsic;
*/

intrinsic EnhancedCosetRepresentation(H::GrpMat, G::GrpMat,O::AlgQuatOrd,mu::AlgQuatElt) -> Any 
  {Make the coset representation of H in G}
  N:=#BaseRing(H);

  NBOplusgens:=NormalizerPlusGeneratorsEnhanced(O,mu);
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens ]; 

  assert -G!1 in G;
  Gplus:=sub< G | NBOplusgensGL4 >;
  assert #G/#Gplus eq 2;
  GO:= G meet sub< GL(4,ResidueClassRing(N)) | UnitGroup(O,N) >;

  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  KG:=sub< Gplus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;

  Gplusquo,Gmap:= quo< Gplus | KG >;

  Hplus := sub< Gplus | H meet Gplus >;
  HplusKG:= sub< Gplus | Hplus, KG >;
  HplusKGquoalt:= quo< HplusKG | KG >;

  Hplusquo:=Gmap(Hplus);

  T:=CosetTable(Gplusquo,Hplusquo);
  piH:=CosetTableToRepresentation(Gplusquo,T);

  return piH;
end intrinsic;



intrinsic EnhancedRamificationData(H::GrpMat, G::GrpMat,O::AlgQuatOrd,mu::AlgQuatElt) -> Any
  {return the image of the elliptic elements under the monodromy map}

  N:=#BaseRing(H);
  assert -G!1 in G;
  NBOplusgens:=NormalizerPlusGeneratorsEnhanced(O,mu);
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens ]; 
  Gplus:=sub< G | NBOplusgensGL4 >;

  elliptic_eltsGL4:= [ EnhancedElementInGL4modN(e,N) : e in EnhancedEllipticElements(O,mu) ]; 
  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  KG:=sub< Gplus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;

  Gplusquo,Gmap:= quo< Gplus | KG >;

  piH:=EnhancedCosetRepresentation(H,G,O,mu);
  sigma := [ piH(Gmap(v)) : v in elliptic_eltsGL4 ];

  return sigma;
end intrinsic;



