intrinsic ElementToAutomorphismModN(a::AlgQuatElt, OmodN::AlgQuatOrdRes) -> GrpAutoElt
  {a in B^x becomes an automorphism of (O/N)^x by considering the map a |-> (x|-> a^-1xa) 
  as long as a \in N_B^x(O). We apply this to (O/N)^x as a permutation group.}

  O:=OmodN`quaternionorder;
  N:=OmodN`quaternionideal;
  ON,piN:=quo(O,N);
  ONx,phi,phi_inv:=UnitGroup(OmodN);
  aut:=hom< ONx -> ONx | x :-> phi_inv(piN(a^(-1)*(phi(x)`element)*a)) >;
  return AutomorphismGroup(ONx)!aut;
end intrinsic;

intrinsic ElementToAutomorphismModN(a::AlgQuatElt, O::AlgQuatOrd, N::RngIntElt) -> GrpAutoElt
  {a in B^x becomes an automorphism of (O/N)^x by considering the map a |-> (x|-> a^-1xa) 
  as long as a \in N_B^x(O). We apply this to (O/N)^x as a permutation group.}

  return ElementToAutomorphismModN(a,quo(O,N));
end intrinsic;


intrinsic AutomorphismsModN(S::{ AlgQuatProjElt }, OmodN::AlgQuatOrdRes) -> Map
  {Given a subset of Aut(O) input as a finite subset S of B^x, create the map
   theta : S -> Aut((O/N)^x)}
  
  ONx,phi:=UnitGroup(OmodN);
  return map< S -> AutomorphismGroup(ONx) | s:->ElementToAutomorphismModN(s,OmodN) >;
end intrinsic;

intrinsic AutomorphismsModN(S::{ AlgQuatProjElt }, O::AlgQuatOrd, N::RngIntElt) -> Map
  {Given a subset of Aut(O) input as a finite subset S of B^x, create the map
  theta : S -> Aut((O/N)^x)}
  
  OmodN:=quo(O,N);
  return AutomorphismsModN(S,OmodN);
end intrinsic;





intrinsic NormalizingElementToGL4(w::AlgQuatElt,O::AlgQuatOrd) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  basis:=Basis(O);
  R:=BaseRing(O);
  assert R eq Integers();
  M4R:=MatrixAlgebra(R,4);

  w_map:=M4R![ Eltseq(O!(w^(-1)*b*w)) : b in basis ];
  assert Determinant(w_map) eq 1;

  return GL(4,R)!w_map, basis;
end intrinsic;


intrinsic NormalizingElementToGL4(w::AlgQuatProjElt,O::AlgQuatOrd) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  return NormalizingElementToGL4(w`element, O);
end intrinsic;


intrinsic NormalizingElementToGL4modN(w::AlgQuatElt,O::AlgQuatOrd, N::RngIntElt) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  ZmodN:=ResidueClassRing(N);
  return GL(4,ZmodN)!NormalizingElementToGL4(w, O);
end intrinsic;

intrinsic NormalizingElementToGL4modN(w::AlgQuatProjElt,O::AlgQuatOrd, N::RngIntElt) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

  ZmodN:=ResidueClassRing(N);
  return GL(4,ZmodN)!NormalizingElementToGL4(w`element,O);
end intrinsic;

intrinsic Random(ON::AlgQuatOrdRes) -> AlgQuatOrdResElt
{Random element of O/N}
  O := ON`quaternionorder;
  N := ON`quaternionideal;
  B := Basis(O);
  return ON!(&+[Random(N-1)*b : b in B]);
end intrinsic;

intrinsic UnitGroupOrder(ON::AlgQuatOrdRes) -> RngIntElt
{The cardinality of (O/N)^x}
  O := ON`quaternionorder;
  N := ON`quaternionideal;
  ans := 1;
  D := Discriminant(O);
  for pair in Factorization(N) do
    p, e := Explode(pair);
    ans *:= p^(4*(e-1)); // additive part
    if IsDivisibleBy(D, p) then
      inv := EichlerInvariant(O, p); // Lemma 24.3.12 of JV's book
      if inv eq 1 then
        ans *:= p^2 * (p - 1)^2;
      elif inv eq -1 then
        ans *:= p^2 * (p^2 - 1);
      else
        ans *:= p^3 * (p - 1);
      end if;
    else
      ans *:= p * (p - 1)^2 * (p + 1);
    end if;
  end for;
  return ans;
end intrinsic;

intrinsic UnitGroupGens(ON::AlgQuatOrdRes) -> SeqEnum, SeqEnum
{Generators for (O/N)^x}
  // For now, we always use a randomized approach
  N := ON`quaternionideal;
  ZmodN := ResidueClassRing(N);
  GL4 := GL(4, ZmodN);
  if N eq 1 then
    return [ON|], [GL4|];
  end if;
  U := sub<GL4|>;
  ONxorder := UnitGroupOrder(ON);
  ONgens := [];
  GL4gens := [];
  while true do
    //print #U, ONxorder;
    x := Random(ON);
    if IsUnit(x) then
      y := UnitGroupToGL4modN(x`element, N);
      V := sub<GL4|U,y>;
      if #V gt #U then
        Append(~ONgens, x);
        Append(~GL4gens, y);
        U := V;
        if #V eq ONxorder then
          return ONgens, GL4gens;
        end if;
      end if;
    end if;
  end while;
end intrinsic;

intrinsic UnitGroupToGL4(x::AlgQuatOrdElt) -> AlgMatElt
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_x : y --> y*x where g \in GL_1(O)}

  O:=Parent(x);
  basis:=Basis(O);
  R:=BaseRing(O);
  assert R eq Integers();
  M4R:=MatrixAlgebra(R,4);
  //ZmodN:=ResidueClassRing(N);

  x_map:=M4R![ Eltseq(O!(b*x)) : b in basis ];
  //assert ZmodN!Determinant(x_map) ne 0;
  return M4R!x_map;
end intrinsic;

intrinsic GL4ToUnitGroup(x::AlgMatElt, O::AlgQuatOrd) -> AlgQuatOrdElt
  {The inverse of the above map: given a 4x4 matrix in the regular representation of O/N,
  return a corresponding element of O}

  basis := Basis(O);
  assert basis[1] eq 1;
  return O!(&+[(Integers()!x[1][i]) * basis[i] : i in [1..4]]);
end intrinsic;

intrinsic GL4ToUnitGroup(x::GrpMatElt, O::AlgQuatOrd) -> AlgQuatOrdElt
  {The inverse of the above map: given a 4x4 matrix in the regular representation of O/N,
  return the corresponding element of O}
  R := BaseRing(Parent(x));
  M4R := MatrixAlgebra(R, 4);
  return GL4ToUnitGroup(M4R!x, O);
end intrinsic;

intrinsic inONx(x::AlgMatElt, O::AlgQuatOrd) -> BoolElt
  {Test whether an element of Mat(4,Z/N) is in the image of (O/N) under the regular representation}
  return x eq UnitGroupToGL4(GL4ToUnitGroup(x, O));
end intrinsic;

intrinsic GL4ToPair(x::GrpMatElt, O::AlgQuatOrd, Ahom::HomGrp) -> Tup
  {Given an element x in the image of Aut_mu(O) \ltimes (O/N)^x within GL(4,Z/N),
  the quaternion order O, and the map from Aut_mu(O) to GL(4,Z/N),
  returns the decomposition of x into a pair arising from the semidirect product:
  - an element of the domain of Ahom (an abstract group C_n or Dn)
  - an element of O}

  N := #BaseRing(Parent(x));
  for a in Domain(Ahom) do
    y := Ahom(a^-1) * x;
    z := GL4ToUnitGroup(y, O);
    if UnitGroupToGL4modN(z, N) eq y then
      return <a, z>;
    end if;
  end for;
end intrinsic;

intrinsic UnitGroupToGL4(x::AlgQuatOrdResElt) -> GrpMatElt
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_x : y --> y*x where g \in GL_1(O)}
  return UnitGroupToGL4(x`element);
end intrinsic;


intrinsic UnitGroupToGL4modN(x::AlgQuatOrdElt,N::RngIntElt) -> GrpMatElt 
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_g : g --> b*g where g \in GL_1(O)}

  ZmodN:=ResidueClassRing(N);
  return GL(4,ZmodN)!UnitGroupToGL4(x);
end intrinsic;

intrinsic UnitGroupToGL4modN(x::AlgQuatOrdResElt,N::RngIntElt) -> GrpMatElt 
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_g : g --> b*g where g \in GL_1(O)}

  return UnitGroupToGL4modN(x`element, N);
end intrinsic;



intrinsic EnhancedSemidirectInGL4(Ocirc::AlgQuatEnh) -> Map 
  {create the map from the semidirect product to GL4(R). R depends on the base 
  ring of Ocirc.}

  O:=Ocirc`quaternionorder;
  R:=Ocirc`basering;
  GL4:=GL(4,R);
  if Type(R) eq RngInt then 
    mapfromenhancedimage := map<  Ocirc -> GL4  |  
    s :-> NormalizingElementToGL4((s`element)[1], O)*UnitGroupToGL4((s`element)[2])  >;
  else 
    N:=Modulus(R);
    mapfromenhancedimage := map<  Ocirc -> GL4  |  
    s :-> NormalizingElementToGL4modN((s`element)[1],O,N)*UnitGroupToGL4modN(((s`element)[2])`element,N)  >;
  end if;

  return mapfromenhancedimage;
end intrinsic;


intrinsic EnhancedSemidirectInGL4(O::AlgQuatOrd) -> Map 
  {create the map from the semidirect product to GL4(R). R depends on the base 
  ring of Ocirc}

  Ocirc:=EnhancedSemidirectProduct(O);
  return EnhancedSemidirectInGL4(Ocirc);
end intrinsic;



intrinsic EnhancedSemidirectInGL4modN(Ocirc::AlgQuatEnh,N::RngIntElt) -> Map 
  {create the map from the semidirect product to GL4(Z/NZ)}

  O:=Ocirc`quaternionorder;

  ZmodN:=ResidueClassRing(N);
  GL4:=GL(4,ZmodN);
  mapfromenhancedimage := map<  Ocirc -> GL4  |  
    s :-> GL4!(NormalizingElementToGL4((s`element)[1],O)*UnitGroupToGL4((s`element)[2]))  >;
  
  return mapfromenhancedimage;
end intrinsic;


intrinsic EnhancedSemidirectInGL4modN(O::AlgQuatOrd,N::RngIntElt) -> Map 
  {create the map from the semidirect product to GL4(Z/NZ)}

  Ocirc:=EnhancedSemidirectProduct(O : N:=N);
  return EnhancedSemidirectInGL4modN(Ocirc,N);
end intrinsic;




intrinsic EnhancedElementInGL4(g::AlgQuatEnhElt) -> GrpMatElt
  {the enhanced element in GL4(R), R depends on the base ring of g}

  Ocirc:=Parent(g);
  map:=EnhancedSemidirectInGL4(Ocirc);
  return map(g);
end intrinsic;

intrinsic EnhancedElementInGL4modN(g::AlgQuatEnhElt,N::RngIntElt) -> GrpMatElt
  {the enhanced element in GL4}

  Ocirc:=Parent(g);
  map:=EnhancedSemidirectInGL4modN(Ocirc,N);
  return map(g);
end intrinsic;





intrinsic EnhancedImagePermutation(AutmuO::Map,OmodN::AlgQuatOrdRes) -> Grp 
  {AutmuO is a map from a finite group C -> B^x, which is isomorphic onto the image in B^x/Q^x. 
  We create the semidirect product of ONx by AutmuO, using AutomorphismModN as the map
  theta: AutmuO -> Aut(ONx)}

  assert MapIsHomomorphism(AutmuO : injective:=true);
  H:=Domain(AutmuO);
  ONx,phi := UnitGroup(OmodN);
  AutONx:=AutomorphismGroup(ONx);
  theta:=hom< H -> AutONx | h :-> ElementToAutomorphismModN(AutmuO(h),OmodN) >;

  rho_circ,m1,m2,m3:=SemidirectProduct(ONx,H,theta);
  return rho_circ,m1,m2,m3;
end intrinsic;

intrinsic EnhancedImagePermutation(AutmuO::.,O::AlgQuatOrd, N::RngIntElt) -> Grp 
  {AutmuO is a map from a finite group C -> B^x, which is isomorphic onto the image in B^x/Q^x. 
  We create the semidirect product of ONx by AutmuO, using AutomorphismModN as the map
  theta: AutmuO -> Aut(ONx)}

  OmodN:=quo(O,N);
  return EnhancedImagePermutation(AutmuO,OmodN);
end intrinsic;






intrinsic EnhancedElementRecord(elt::AlgQuatEnhElt) -> Any
  {given <w,x> in Autmu(O) \rtimes (O/N)^x or Autmu(O) \rtimes O^x  return <w,x> as a 
  record along with its embedding in GL_4xGL_4 and just GL_4}
  
  Ocirc:=Parent(elt);
  O:=Ocirc`quaternionorder;
  R:=Ocirc`basering;
  if Type(R) eq RngInt then 
    N:=0;
  else 
    N:=Modulus(R);
  end if;

  RF := recformat< n : Integers(),
  enhanced,
  GL4xGL4,
  GL4
  >
  ;  

  s := rec< RF | >;
  s`enhanced:=elt;
  if N eq 0 then 
    s`GL4xGL4:=<NormalizingElementToGL4(elt`element[1],O), UnitGroupToGL4(elt`element[2])>;
  else 
    s`GL4xGL4:=<NormalizingElementToGL4modN(elt`element[1],O,N), UnitGroupToGL4modN(elt`element[2],N)>;
  end if;
  s`GL4:=s`GL4xGL4[1]*s`GL4xGL4[2];
  return s;
end intrinsic;

intrinsic GL4ToEnhanced(g::GrpMatElt, O::AlgQuatOrd) -> AlgQuatEnhElt
{Given a 4x4 matrix in the image of the inclusion Aut_mu(O) ltimes (O/N)^x, give the two components as an enhanced element}
    R := BaseRing(Parent(g));
    N := #R;
    M4R := MatrixAlgebra(R,4);
end intrinsic;

intrinsic EnhancedImageGL4(AutmuO::Map, OmodN::AlgQuatOrdRes) -> GrpMat, GrpMat, HomGrp
  {return
   - the image of the enhanced semidirect product group G in GL4(Z/NZ)
   - the image of just (O/N)^x inside GL4(Z/NZ)
   - the homomorphism from the domain of AutmuO to this image.}

  O:=OmodN`quaternionorder;
  N:=OmodN`quaternionideal;
  Ocirc:=EnhancedSemidirectProduct(O: N:=N);
  A:=Domain(AutmuO);
  ZmodN:=ResidueClassRing(N);
  GL4 := GL(4, ZmodN);
  Angen := NumberOfGenerators(A);
  AinGL4 := [NormalizingElementToGL4modN(AutmuO(A.i)`element,O,N) : i in [1..Angen]];
  Ahom := hom<A -> GL4 |[<A.i, AinGL4[i]> : i in [1..Angen]]>;

  ONx, phi:= UnitGroup(OmodN);
  ONxgens := [ONx.i : i in [1..NumberOfGenerators(ONx)]];

  semidirGL4 := sub<GL4 | ONxgens cat AinGL4>;

  return semidirGL4, ONx, Ahom;

  /*
  auts:=[ AutmuO(a) : a in Generators(Domain(AutmuO)) ];

  enhanced_gens:=[ Ocirc!<w,x> : w in auts, x in Generators(ONx) ];

  RF := recformat< n : Integers(),
  enhanced,
  GL4xGL4,
  GL4
  >
  ;

  enhancedimage:=[];
  for elt in enhanced_gens do
    s := rec< RF | >;
    s`enhanced:=elt;
    s`GL4xGL4:=<NormalizingElementToGL4modN(elt`element[1],O,N), UnitGroupToGL4modN((elt`element[2])`element,N)>;
    s`GL4:=s`GL4xGL4[1]*s`GL4xGL4[2];
    Append(~enhancedimage,s);
  end for;


  semidirGL4:= sub< GL(4,ZmodN) |  [ x`GL4 : x in enhancedimage ] >;

  assert forall(u){ <s,t> : s in RandomSubset({1..#enhancedimage},10), t in RandomSubset({1..#enhancedimage},10)
  | EnhancedElementInGL4(enhancedimage[s]`enhanced*enhancedimage[t]`enhanced) eq enhancedimage[s]`GL4*enhancedimage[t]`GL4 };

  return semidirGL4;
  */
end intrinsic;




intrinsic EnhancedImageGL4(AutmuO::Map, O::AlgQuatOrd, N::RngIntElt) -> GrpMat, GrpMat, HomGrp
  {return the image of the enhanced semidirect product group G in GL4(Z/NZ). The second return value
  is a list of enhanced elements in record format.}

  OmodN:=quo(O,N);
  return EnhancedImageGL4(AutmuO, OmodN);
end intrinsic;


intrinsic EnhancedImageGL4(O::AlgQuatOrd, mu::AlgQuatElt, N::RngIntElt) -> GrpMat, GrpMat, HomGrp
  {return the image of the enhanced semidirect product group G in GL4(Z/NZ). The second return value
  is a list of enhanced elements in record format.}

  AutmuO:=Aut(O,mu);
  assert MapIsHomomorphism(AutmuO);
  OmodN:=quo(O,N);
  return EnhancedImageGL4(AutmuO, OmodN);
end intrinsic;

intrinsic EnhancedImageGL4(O::AlgQuatOrd, mu::AlgQuatOrdElt, N::RngIntElt) -> GrpMat, GrpMat, HomGrp
  {return the image of the enhanced semidirect product group G in GL4(Z/NZ). The second return value
  is a list of enhanced elements in record format.}

  AutmuO:=Aut(O,mu);
  assert MapIsHomomorphism(AutmuO);
  OmodN:=quo(O,N);
  return EnhancedImageGL4(AutmuO, OmodN);
end intrinsic;



intrinsic AutmuOinGL4modN(AutmuO::Map,O::AlgQuatOrd,N::RngIntElt) -> GrpMat
  {Embed AutmuO inside GL4(Z/NZ)}
  elts:=[ NormalizingElementToGL4modN(AutmuO(s),O,N) : s in Domain(AutmuO) ];
  group:= sub< GL(4,ResidueClassRing(N)) | elts >;
  assert #group eq #elts;
  return group;
end intrinsic;


intrinsic AutmuOinGL4modN(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt) -> GrpMat
  {Embed AutmuO inside GL4(Z/NZ)}
  AutmuO:=Aut(O,mu);
  return AutmuOinGL4modN(AutmuO,O,N);
end intrinsic;

intrinsic AutmuOinGL4modN(O::AlgQuatOrd,mu::AlgQuatOrdElt,N::RngIntElt) -> GrpMat
  {Embed AutmuO inside GL4(Z/NZ)}
  AutmuO:=Aut(O,mu);
  return AutmuOinGL4modN(AutmuO,O,N);
end intrinsic;


intrinsic AllEnhancedElements(O::AlgQuatOrd, mu::AlgQuatElt, N::RngIntElt) -> List
  {return the elements of the semidirect product Aut_mu(O) ltimes (O/N)^x as a list}

  AutmuO:=Aut(O,mu);
  OmodN:=quo(O,N);
  G,OG,Ahom:=EnhancedImageGL4(AutmuO,OmodN);
  Ocirc:=EnhancedSemidirectProduct(O : N:=N);
  elts1 := [ GL4ToPair(x,O,Ahom) : x in G];
  elts2 := [ Ocirc!<AutmuO(elt[1]),elt[2]> : elt in elts1 ];

  assert forall(e){ <a,b> : a in elts2, b in elts2 | a*b in elts2 };

  return elts2;
end intrinsic;


intrinsic GL4ToEnhancedSemidirect(O::AlgQuatOrd, mu::AlgQuatElt, N::RngIntElt) -> Map
  {return the inverse of the map from Aut_mu(O) ltimes (O/N)^x to GL_4(Z/N)}
  
  AutmuO:=Aut(O,mu);
  OmodN:=quo(O,N);
  G,OG,Ahom:=EnhancedImageGL4(AutmuO,OmodN);
  Ocirc:=EnhancedSemidirectProduct(O : N:=N);

  map := map< G -> Ocirc | g :-> Ocirc!< AutmuO(GL4ToPair(g,O,Ahom)[1]), GL4ToPair(g,O,Ahom)[2] > >;
  assert MapIsHomomorphism(map : injective:=true);
  return map;
end intrinsic;


