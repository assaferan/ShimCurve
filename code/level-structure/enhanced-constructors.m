
declare type AlgQuatOrdRes[AlgQuatOrdResElt];

declare attributes AlgQuatOrdRes :
  quaternionorder,
  quaternionideal;

declare attributes AlgQuatOrdResElt:
  element,
  parent;

declare type AlgQuatProj[AlgQuatProjElt];

declare attributes AlgQuatProj :
  quaternionalgebra;

declare attributes AlgQuatProjElt :
  element,
  parent;

declare type AlgQuatEnh[AlgQuatEnhElt];
 
declare attributes AlgQuatEnh :
  quaternionalgebra,
  quaternionorder,
  basering,
  lhs,
  rhs;

declare attributes AlgQuatEnhElt :
  element,
  parent;

intrinsic OmodNElement(OmodN::AlgQuatOrdRes, x::AlgQuatOrdElt) -> AlgQuatOrdResElt
  {Construct an element of the OmodN whose underlying element is x in O}
  elt := New(AlgQuatOrdResElt);
  elt`element := x;
  elt`parent := OmodN;
  
  return OmodN!elt;
end intrinsic;

intrinsic ElementModuloScalars(BxmodFx::AlgQuatProj, x::AlgQuatElt) -> AlgQuatProjElt
  {Construct an element of B^x/F^x whose underlying element is x in B}
  elt := New(AlgQuatProjElt);
  elt`element := x;
  elt`parent := BxmodFx;
  
  return elt;
end intrinsic;

intrinsic EnhancedElement(Ocirc::AlgQuatEnh, tup::<>) -> AlgQuatEnhElt
  {Construct and element of the enhances semidirect product whose underling element is a tuple in
   Autmu(O)x(O)^x or Autmu(O)x(O/N)^x }
   //assert Type(tup[1]) eq 

   O:=Ocirc`rhs;
   BxmodQx:=Ocirc`lhs;

   elt:= New(AlgQuatEnhElt);
   elt`element := <BxmodQx!tup[1],O!tup[2]>;
   elt`parent := Ocirc;

   return elt;
end intrinsic;
 

intrinsic 'eq'(x::AlgQuatOrdResElt,y::AlgQuatOrdResElt) -> BoolElt 
  {Decide if x equals y in OmodN}
  assert Parent(x) eq Parent(y);
  OmodN:=Parent(x);
  N:=OmodN`quaternionideal;
  O:=OmodN`quaternionorder;
  xO:=x`element;
  yO:=y`element;
  return xO-yO in N*O;
end intrinsic;

intrinsic 'eq'(x::AlgQuatProjElt,y::AlgQuatProjElt) -> BoolElt 
  {Decide if x equals y in OmodN}
  assert Parent(x) eq Parent(y);
  //BxmodFx:=Parent(x);
  x0:=x`element;
  y0:=y`element;
  assert x0*y0 ne 0;
  return IsScalar(x0/y0);
end intrinsic;

intrinsic 'eq'(g1::AlgQuatEnhElt,g2::AlgQuatEnhElt) -> BoolElt
  {decide if g1 eq g2 in enhanced semidirect product}

  h1:=g1`element;
  h2:=g2`element;
  if h1[1] eq h2[1] and h1[2] eq h2[2] then 
    return true;
  else 
    return false;
  end if;
end intrinsic;

intrinsic 'eq'(OmodN1::AlgQuatOrdRes,OmodN2::AlgQuatOrdRes) -> BoolElt 
  {Decide if OmodN1 equals OmodN2}
 
  O1:=OmodN1`quaternionorder;
  O2:=OmodN2`quaternionorder;

  N1:=OmodN1`quaternionideal;
  N2:=OmodN2`quaternionideal;

  if O1 eq O2 and N1 eq N2 then 
    return true;
  else 
    return false;
  end if;
end intrinsic;


intrinsic 'eq'(BxmodFx1::AlgQuatProj,BxmodFx2::AlgQuatProj) -> BoolElt 
  {Decide if BxmodFx1 equals BxmodFx2}
 
  B1:=BxmodFx1`quaternionalgebra;
  B2:=BxmodFx2`quaternionalgebra;

  if B1 eq B2 then 
    return true;
  else 
    return false;
  end if;
end intrinsic;


intrinsic 'eq'(Ocirc1::AlgQuatEnh,Ocirc2::AlgQuatEnh) -> BoolElt 
  {Decide if Ocirc1 equals Ocirc2}
 
  O1:=Ocirc1`quaternionorder;
  O2:=Ocirc2`quaternionorder;

  R1:=Ocirc1`basering;
  R2:=Ocirc2`basering;

  if O1 eq O2 and R1 eq R2 then 
    return true;
  else 
    return false;
  end if;
end intrinsic;

intrinsic '*'(x::AlgQuatOrdResElt,y::AlgQuatOrdResElt) -> AlgQuatOrdResElt 
  {compute x*y in OmodN}
  assert Parent(x) eq Parent(y);
  OmodN:=Parent(x);
  N:=OmodN`quaternionideal;
  O:=OmodN`quaternionorder;
  xO:=x`element;
  yO:=y`element;

  ON,piN:=quo(O,N);
  return OmodN!(piN(xO*yO));
end intrinsic;

intrinsic '*'(x::AlgQuatProjElt,y::AlgQuatProjElt) -> AlgQuatProjElt 
  {compute x*y in B^x/F^x}
  assert Parent(x) eq Parent(y);
  BxmodFx:=Parent(x);

  xO:=x`element;
  yO:=y`element;

  return BxmodFx!ElementModuloScalars(BxmodFx,xO*yO);
end intrinsic;

intrinsic '*'(g1::AlgQuatEnhElt,g2::AlgQuatEnhElt) -> AlgQuatEnhElt 
  {compute x*y in enhanced semidirect produt}  assert Parent(g1) eq Parent(g2);

  h1:=g1`element;
  h2:=g2`element;

  w1:=h1[1];
  w2:=h2[1];
  x1:=h1[2];
  x2:=h2[2];
  assert Parent(w1) eq Parent(w2);
  assert Parent(x1) eq Parent(x2);
  U:=Parent(x1);
  assert Type(U) in [AlgQuatOrd, AlgQuatOrdRes];
  w2elt:=w2`element;

  if Type(U) eq AlgQuatOrdRes then 
    x1elt:=x1`element;
    x2elt:=x2`element;
  else 
    x1elt:=x1;
    x2elt:=x2;
  end if;

  //assert (w2elt^-1)*x1elt*w2elt in U;
  Ocirc:=Parent(g1);
  return Ocirc!<w1*w2, U!((w2elt^-1)*x1elt*w2elt*x2elt) >;
end intrinsic;


intrinsic '^'(x::AlgQuatOrdResElt,exp::RngIntElt) -> AlgQuatOrdResElt
  {compute x^y in (O/N)^x}
  OmodN:=Parent(x);

  x0:=x`element;

  return OmodN!(x0^exp);
end intrinsic;


intrinsic '^'(x::AlgQuatProjElt,y::RngIntElt) -> AlgQuatProjElt 
  {compute x^y in B^x/F^x}
  BxmodFx:=Parent(x);

  xO:=x`element;

  return BxmodFx!ElementModuloScalars(BxmodFx,xO^y);
end intrinsic;


intrinsic '^'(g::AlgQuatEnhElt,exp::RngIntElt) -> AlgQuatEnhElt 
  {g^exp in enhanced semidirect product}

  if exp eq 0 then 
    return Parent(g)!<1,1>;
  elif exp eq 1 then 
    return g;
  elif exp ge 2 then  
    gi:=g;
    for i in [1..exp-1] do 
      gi:= gi*g;
    end for;
    return gi;
  elif exp eq -1 then 
    gelt:=g`element;
    ginv:=Parent(g)!<gelt[1]^-1, (gelt[1]`element)*(gelt[2]^-1)*((gelt[1]`element)^-1) >;
    return ginv;
  elif exp le 2 then 
    gelt:=g`element;
    ginv:=<gelt[1]^-1, (gelt[1]`element)*(gelt[2]^-1)*((gelt[1]`element)^-1)>;
    gi:=ginv;
    for i in [1..exp-1] do 
      gi:= gi*ginv;
    end for;
    return Parent(g)!gi;
  end if;

end intrinsic;


intrinsic Order(x::AlgQuatProjElt) -> Any
  {order of element}
  BxmodQx:=x`parent;
  B:=BxmodQx`quaternionalgebra;
  for n in [1..24] do 
    if x^n eq BxmodQx!(B!1) then 
      return Integers()!n;
    end if;
  end for;
  return "infinity";
end intrinsic;

intrinsic Order(g::AlgQuatEnhElt) -> Any
  {order of element}
  Ocirc:=g`parent;
  for n in [1..24] do 
    if g^n eq Ocirc!(<Ocirc`lhs!(Ocirc`quaternionalgebra!1),Ocirc`rhs!1>) then 
      return Integers()!n;
    end if;
  end for;
  return "infinity";
end intrinsic;

intrinsic Norm(x::AlgQuatEnhElt) -> RngIntResElt
{Norm of the element of the enhanced semidirect product as an element of (Z/N)^x}
    return Norm(x`element[2]);
end intrinsic;

intrinsic PrimitiveElement(x::AlgQuatElt) -> AlgQuatProjElt
  {We consider the coset of x in B^x/Q^x: this coset has a unique representative
  b of squarefree and integral norm. Return b.}

  num:=Integers()!Numerator(Norm(x));
  den:=Integers()!Denominator(Norm(x));
  _,squarepart_num:=SquarefreeFactorization(num);
  sqfree_den,squarepart_den:=SquarefreeFactorization(den);
  b:=x*(sqfree_den*squarepart_den/squarepart_num);
  assert IsSquarefree(Integers()!Norm(b));
  return QuaternionAlgebraModuloScalars(Parent(x))!b;
end intrinsic;

intrinsic PrimitiveElement(x::AlgQuatProjElt) -> AlgQuatProjElt
  {We consider the coset of x in B>0^x/Q^x: this coset has a unique representative
  b of squarefree and integral norm. Return b.}

  return PrimitiveElement(x`element);
end intrinsic;




  
intrinsic Parent(elt::AlgQuatOrdResElt) -> AlgQuatOrdRes
  {.}
  return elt`parent;    
end intrinsic;

intrinsic Parent(elt::AlgQuatProjElt) -> AlgQuatProj
  {.}
  return elt`parent;    
end intrinsic;

intrinsic Parent(elt::AlgQuatEnhElt) -> AlgQuatProj
  {.}
  return elt`parent;    
end intrinsic;

intrinsic quo(O::AlgQuatOrd, N::RngIntElt) -> AlgQuatOrdRes
  {.}
  M := New(AlgQuatOrdRes);
  M`quaternionideal := N;
  M`quaternionorder := O;
  projection := map < O -> M | x :-> OmodNElement(M,x) >;
  return M, projection;
end intrinsic;

intrinsic QuaternionAlgebraModuloScalars(B::AlgQuat) -> AlgQuatProj 
  {Create B^x/F^x}
  BxmodFx:=New(AlgQuatProj);
  BxmodFx`quaternionalgebra := B;
  return BxmodFx;
end intrinsic;

intrinsic EnhancedSemidirectProduct(O::AlgQuatOrd: N:=0) -> AlgQuatEnh
  {create Autmu(O)\rtimesO^x or Autmu(O)\rtimes(O/N)^x}
  Ocirc:=New(AlgQuatEnh);
  Ocirc`quaternionorder:=O;
  B:=QuaternionAlgebra(O);
  Ocirc`quaternionalgebra:=B;
  if N eq 0 then 
    Ocirc`basering := Integers();
    Ocirc`rhs:=O;
  else 
    Ocirc`basering:=ResidueClassRing(N);
    Ocirc`rhs:=quo(O,N);
  end if;
  BxmodQx:=QuaternionAlgebraModuloScalars(B);
  Ocirc`lhs:=BxmodQx;

  return Ocirc;
end intrinsic;

intrinsic IsCoercible(OmodN::AlgQuatOrdRes, x::Any) -> BoolElt, .
{.}
  if Type(x) eq AlgQuatOrdResElt then
    if Parent(x) eq OmodN then
      return true, x;
    else
      return false, "Illegal Coercion";
    end if;
  elif Type(x) eq AlgQuatOrdElt then
    if Parent(x) eq OmodN`quaternionorder then 
      return true,OmodNElement(OmodN,x);
    else 
      return false, "Illegal Coercion";
    end if;
  elif Type(x) eq AlgQuatElt then 
    if x in OmodN`quaternionorder then 
      return true, OmodNElement(OmodN,(OmodN`quaternionorder)!x);
    else 
      return false, "Illegal Coercion";  
    end if;  
  elif IsCoercible(OmodN`quaternionorder,x) then 
    return true, OmodNElement(OmodN,(OmodN`quaternionorder)!x);
  else
    return false, "Illegal Coercion";
  end if;
end intrinsic;


intrinsic IsCoercible(BxmodFx::AlgQuatProj, x::Any) -> BoolElt, .
{.}
 if Type(x) eq AlgQuatProjElt then
    if Parent(x) eq BxmodFx then
      return true, x;
    else
      return false, "Illegal Coercion";
    end if;
  elif Type(x) eq AlgQuatElt then 
    if Parent(x) eq BxmodFx`quaternionalgebra then 
      return true, ElementModuloScalars(BxmodFx,x);
    else   
      return false, "Illegal Coercion";   
    end if;
  elif IsCoercible(BxmodFx`quaternionalgebra,x) then 
    return true, ElementModuloScalars(BxmodFx,(BxmodFx`quaternionalgebra)!x);
  else
    return false, "Illegal Coercion";
  end if;

end intrinsic;


intrinsic IsCoercible(Ocirc::AlgQuatEnh, g::Any) -> BoolElt, .
{.}
  
  if Type(g) eq AlgQuatEnhElt then 
    h:=g`element;
    assert Type(h) eq Tup;
    assert #h eq 2;
    w:=h[1];
    x:=h[2];
    BxmodQx:=Ocirc`lhs;
    U:=Ocirc`rhs;

    if IsCoercible(Ocirc`lhs,w) and IsCoercible(Ocirc`rhs,x) then 
      return true, EnhancedElement(Ocirc,<w,x>);
    else 
      return false, "Illegal Coercion";
    end if;   
  elif Type(g) eq Tup then 
    assert #g eq 2;
    w:=g[1];
    x:=g[2];
    BxmodQx:=Ocirc`lhs;
    U:=Ocirc`rhs;

    if IsCoercible(Ocirc`lhs,w) and IsCoercible(Ocirc`rhs,x) then 
      return true, EnhancedElement(Ocirc,<w,x>);
    else 
      return false, "Illegal Coercion";
    end if;
  else 
    return false;
  end if;
end intrinsic;
 



intrinsic IsUnit(x::AlgQuatOrdResElt) -> BoolElt
  {return whether x \in O/N is a unit}
  x0:=x`element;
  OmodN:=Parent(x);
  N:=OmodN`quaternionideal;
  nm:=Norm(x0);
  ZmodN:=ResidueClassRing(N);

  return IsUnit(ZmodN!nm);
end intrinsic;


intrinsic Norm(x::AlgQuatOrdResElt) -> RngIntResElt
{Norm of the element of the enhanced semidirect product as an element of (Z/N)^x}
    N := Modulus(Parent(x));
    return Integers(N)!Norm(x`element);
end intrinsic;

intrinsic Set(OmodN::AlgQuatOrdRes) -> Set 
  {return the set of elements O/N}

  O:=OmodN`quaternionorder;
  N:=OmodN`quaternionideal;
  ON,piN:=quo(O,N);
  basis:=Basis(O);
  set:={  O!(a*basis[1] + b*basis[2] + c*basis[3] + d*basis[4]) : a,b,c,d in [0..N-1]  };
  return { OmodN!piN(x) : x in set };
end intrinsic;

intrinsic Modulus(OmodN::AlgQuatOrdRes) -> RngIntElt
{Return the level N of OmodN}
    return OmodN`quaternionideal;
end intrinsic;

intrinsic UnitGroup(OmodN::AlgQuatOrdRes) -> GrpMat, Map
  {return (O/N)^x as a permutation group G, the second value is the isomorphism G ->(O/N)^x}
  //Need to make this much more efficient.

  O:=OmodN`quaternionorder;
  ONgens, GL4gens := UnitGroupGens(OmodN);
  subONx := sub< Universe(GL4gens) | GL4gens>;
  phi := map< subONx -> OmodN | s :-> OmodN!GL4ToUnitGroup(s, O), x :-> UnitGroupToGL4modN(x) >;
  return subONx, phi;
end intrinsic;



intrinsic UnitGroup(O::AlgQuatOrd,N::RngIntElt) -> GrpMat, Map
  {return (O/N)^x as a permutation group G, the second value is the isomorphism G ->(O/N)^x}

  return UnitGroup(quo(O,N));
end intrinsic;





intrinsic Print(elt::AlgQuatOrdResElt)
{.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(OmodN::AlgQuatOrdRes)
{.}
  printf "Quotient of %o by %o", OmodN`quaternionorder, OmodN`quaternionideal;
end intrinsic;

intrinsic Print(elt::AlgQuatProjElt)
{.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(BxmodFx::AlgQuatProj)
{.}
  printf "Quotient by scalars of %o", BxmodFx`quaternionalgebra;
end intrinsic;


intrinsic Print(elt::AlgQuatEnhElt)
{.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(Ocirc::AlgQuatEnh)
{.}
  printf "Semidirect product of Aut(O) and O^x or (O/N)^x where O is %o", Ocirc`quaternionorder;
end intrinsic;





