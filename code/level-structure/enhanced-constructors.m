import "enumerate-H.m" : getDeterminantImage;

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
  mu,
  N,
  basering, // Zmod(N)
  lhs, // BxmodQx
  rhs, // O/N

  GL4sub, // Semidirect product as a subgroup of GL(4,Zmod(N)) (except when N=1, when it is just Aut_mu(O))
  AutmuO, // Aut_mu(O) as a PC group
  AtoBx, // A -> B^x / Q^x (AutFull)
  AtoGL4, // A -> GL(4,Zmod(N)) (Ahom)
  Bxelts, // sequence of elements of Bx / Qx: the image of AtoBx

  ONx, // (O/N)^x as a subgroup of GL(4,Zmod(N))

  G1plus, // the index 2 subgroup of positive norm elements
  NormalizerKernel, // The kernel of the map from the semidirect product to the normalizer in B^x of O
  NormalizerKernelGL4, // The normalizer kernel, as a subgroup of GL(4, Z/NZ)
  G1plusmodKG, // the quotient of the previous two attributes
  G1plusmodKGmap, // the map from G1plus to the quotient
  EllipticElements,
  EllipticElementsGL4,
  NormalizerPlusGenerators,
  Lats;

declare attributes AlgQuatEnhElt :
  element,
  parent;

// The following type collates structures from different levels together
declare type AlgQuatEnhSys;

declare attributes AlgQuatEnhSys :
  quaternionorder,
  mu,
  Ns_maximal, // These Ns will be computed first (to save computation time: computing at level 12 gives level 6 as a consequence
  Enh, // Associative array; Enh[N] is an AlgQuatEnh object at level N
  Lat, // Associative array; Lat[N] is a SubgroupLat object containing subgroups at levels dividing N with surjective determinant
  Lat1, // Associative array; Lat1[N] is a SubgroupLat object containing subgroups at levels dividing N with determinant 1
  Transfer; // Associative array; Transfer[<N,p>] is the reduction homomorphism from GL4sub(Enh[N]) to GL4sub(Enh[N/p])

intrinsic OmodNElement(OmodN::AlgQuatOrdRes, x::AlgQuatOrdElt) -> AlgQuatOrdResElt
  {Construct an element of the OmodN whose underlying element is x in O}
  elt := New(AlgQuatOrdResElt);
  elt`element := x;
  elt`parent := OmodN;

  return elt;
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

  if StandardForm(QuaternionAlgebra(O1)) eq StandardForm(QuaternionAlgebra(O2))
     and [ Eltseq(b) : b in Basis(O1) ] eq [ Eltseq(b) : b in Basis(O2) ]
     and N1 eq N2 then
    return true;
  else 
    return false;
  end if;
end intrinsic;


intrinsic 'eq'(BxmodFx1::AlgQuatProj,BxmodFx2::AlgQuatProj) -> BoolElt 
  {Decide if BxmodFx1 equals BxmodFx2}
 
  B1:=BxmodFx1`quaternionalgebra;
  B2:=BxmodFx2`quaternionalgebra;

  if StandardForm(B1) eq StandardForm(B2)
     and BaseRing(B1) eq BaseRing(B2) then
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

  if StandardForm(QuaternionAlgebra(O1)) eq StandardForm(QuaternionAlgebra(O2))
     and [ Eltseq(b) : b in Basis(O1) ] eq [ Eltseq(b) : b in Basis(O2) ]
     and R1 eq R2 then
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
  if exp ge 0 then 
    return OmodN!(x0^exp);
  else 
    order := Order(x);
    xinv := OmodN!(x0^(order-1));
    return xinv^(-exp);
  end if;
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
    ginv:=Parent(g)!<gelt[1]^-1, (gelt[1]`element)*((gelt[2]^-1)`element)*((gelt[1]`element)^-1) >;
    return ginv;
  elif exp le -2 then
    gelt:=g`element;
    ginv:=Parent(g)!<gelt[1]^-1, (gelt[1]`element)*((gelt[2]^-1)`element)*((gelt[1]`element)^-1)>;
    gi:=ginv;
    for i in [1..exp+1] do 
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


intrinsic Order(x::AlgQuatOrdResElt) -> RngIntElt
  {order of element}
  OmodN:=x`parent;
  for n in [1..12] do
    if x^n eq OmodN!1 then
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

intrinsic EnhancedSemidirectProduct(O::AlgQuatOrd, mu::AlgQuatElt : N:=0) -> AlgQuatEnh
  {create Autmu(O)\rtimesO^x or Autmu(O)\rtimes(O/N)^x}
  Ocirc:=New(AlgQuatEnh);
  Ocirc`quaternionorder:=O;
  B:=QuaternionAlgebra(O);
  Ocirc`quaternionalgebra:=B;
  Ocirc`N:=N;
  Ocirc`mu:=mu;
  if N eq 0 then
    Ocirc`basering := Integers();
    Ocirc`rhs:=O;
  elif N eq 1 then
    Ocirc`rhs:=ONx(Ocirc);
  else
    Ocirc`basering:=ResidueClassRing(N);
    Ocirc`rhs:=quo(O,N);
  end if;
  BxmodQx:=QuaternionAlgebraModuloScalars(B);
  Ocirc`lhs:=BxmodQx;

  return Ocirc;
end intrinsic;


intrinsic GL4sub(Enh::AlgQuatEnh) -> GrpMat
{Returns the semidirect product as a subgroup of GL(4,Zmod(N))}
    if not assigned Enh`GL4sub then
        Enh`GL4sub, Enh`ONx, Enh`AtoGL4 := EnhancedImageGL4(Enh);
    end if;
    return Enh`GL4sub;
end intrinsic;

intrinsic ONx(Enh::AlgQuatEnh) -> GrpMat
{Returns (O/N)^x as a subgroup of GL(4,Zmod(N))}
    if not assigned Enh`ONx then
        Enh`GL4sub, Enh`ONx, Enh`AtoGL4 := EnhancedImageGL4(Enh);
    end if;
    return Enh`ONx;
end intrinsic;

intrinsic AtoGL4(Enh::AlgQuatEnh) -> GrpHom
{Returns the inclusion A -> GL(4,Zmod(N)), where A is the PC group Aut_mu(O)}
    if not assigned Enh`AtoGL4 then
        Enh`GL4sub, Enh`ONx, Enh`AtoGL4 := EnhancedImageGL4(Enh);
    end if;
    return Enh`AtoGL4;
end intrinsic;

intrinsic G1plus(Enh::AlgQuatEnh) -> GrpMat
{Returns the index-2 subgroup of positive norm elements}
    if assigned Enh`G1plus then return Enh`G1plus; end if;
    t0 := Cputime();
    O := Enh`quaternionorder;
    mu := Enh`mu;
    N := Enh`N;
    G := GL4sub(Enh);
    NBOplusgens_enhanced := NormalizerPlusGenerators(Enh);
    NBOplusgensGL4 := [ EnhancedElementInGL4(g) : g in NBOplusgens_enhanced ];
    G1plus := sub< G | NBOplusgensGL4 >;
    if Enh`N gt 2 then
        assert #G/#G1plus eq 2;
    end if;
    Enh`G1plus := G1plus;
    vprint User1: "G1plus", Cputime() - t0;
    return G1plus;
end intrinsic;

intrinsic NormalizerKernel(Enh::AlgQuatEnh) -> SeqEnum[AlgQuatEnh]
{return the kernel of the map form the enhanced semidirect product to N_B^x(O).
  It is necessarily cyclic and the second value is the generator of the group}
    if not assigned Enh`NormalizerKernel then
        B := Enh`quaternionalgebra;
        O := Enh`quaternionorder;
        autmuOseq := Bxelts(Enh);
        Oxcyc := [ (1/Integers()!Sqrt(Norm(a`element)))*a`element : a in autmuOseq | IsSquare(Norm(a`element)) ];
        ker := [ Enh!<x,x^-1> : x in Oxcyc ];
        assert #ker in [1,2,3];
        assert &and[Norm(e) eq 1 : e in Oxcyc];
        if #ker eq 1 then
            assert ker[1] eq Enh!<B!1,O!1> or ker[1] eq Enh!<B!1,-O!1>;
            Enh`NormalizerKernel := [ Enh!<B!1,O!1>, Enh!<B!1,-O!1> ];
        else
            gen := [ e : e in ker | Order(e) eq 2 * #ker ];
            assert #gen eq 1;
            gen := gen[1];
            newker := [ gen^i : i in [0..Order(gen) - 1] ];
            // assert #Set(newker) eq Order(gen);
            //assert its cyclic in GL4
            Enh`NormalizerKernel := newker;
        end if;
    end if;
    return Enh`NormalizerKernel;
end intrinsic;

intrinsic NormalizerKernelGen(Enh::AlgQuatEnh) -> AlgQuatEnh
{The generator of the normalizer kernel}
    return NormalizerKernel(Enh)[2];
end intrinsic;

intrinsic NormalizerKernelGL4(Enh::AlgQuatEnh) -> GrpMat
{The kernel of the map from the semidirect product to the normalizer in B^x of O, as a subgroup of GL(4,Zmod(N))}
    if not assigned Enh`NormalizerKernelGL4 then
        t0 := Cputime();
        O := Enh`quaternionorder;
        K := NormalizerKernel(Enh);
        Enh`NormalizerKernelGL4 := sub< G1plus(Enh) | [ EnhancedElementInGL4(k) : k in K ] >;
        if Enh`N gt 2 then
            assert #(Enh`NormalizerKernelGL4) eq #K;
        end if;
        vprint User1: "NormalizerKernelGL4", Cputime() - t0;
    end if;
    return Enh`NormalizerKernelGL4;
end intrinsic;

intrinsic G1plusmodKG(Enh::AlgQuatEnh) -> GrpPerm // TODO: worry about what happens if this quotient is too big
{The quotient of the positive norm elements by the kernel of the map to the normalizer}
    if not assigned Enh`G1plusmodKG then
        Enh`G1plusmodKG, Enh`G1plusmodKGmap := quo<G1plus(Enh) | NormalizerKernelGL4(Enh)>;
    end if;
    return Enh`G1plusmodKG;
end intrinsic;

intrinsic G1plusmodKGmap(Enh::AlgQuatEnh) -> HomGrp
{The projection map from the positive norm elements to its quotient by the kernel of the map to the normalizer}
    if not assigned Enh`G1plusmodKGmap then
        Enh`G1plusmodKG, Enh`G1plusmodKGmap := quo<G1plus(Enh) | NormalizerKernelGL4(Enh)>;
    end if;
    return Enh`G1plusmodKGmap;
end intrinsic;

intrinsic AutmuO(Enh::AlgQuatEnh) -> GrpPC
{The abstract group Aut_mu(O), either cyclic or dihedral}
    if not assigned Enh`AutmuO then
        Enh`AutmuO := Domain(AtoBx(Enh));
    end if;
    return Enh`AutmuO;
end intrinsic;

intrinsic AtoBx(Enh::AlgQuatEnh) -> Map
{The map A -> B^x / Q^x, where A is Aut_mu(O) as an abstract group}
    if not assigned Enh`AtoBx then
        Enh`AtoBx := Aut(Enh`quaternionorder, Enh`mu);
    end if;
    return Enh`AtoBx;
end intrinsic;

intrinsic Bxelts(Enh::AlgQuatEnh) -> SeqEnum
{The image of AtoBx as a sequence of elements}
    if not assigned Enh`Bxelts then
        Bxhom := AtoBx(Enh);
        Enh`Bxelts := [Bxhom(a) : a in Domain(Bxhom)];
    end if;
    return Enh`Bxelts;
end intrinsic;

intrinsic EllipticElements(Enh::AlgQuatEnh) -> SeqEnum
{The elliptic elements}
    // TODO: This is currently the same as NormalizerPlusGenerators(Enh)
    if not assigned Enh`EllipticElements then
        B := Enh`quaternionalgebra;
        O := Enh`quaternionorder;
        Enh`EllipticElements := [Enh!NormalizerToAutmuO(Enh, B!a) : a in NormalizerPlusGenerators(O)];
    end if;
    return Enh`EllipticElements;
end intrinsic;

intrinsic EllipticElementsGL4(Enh::AlgQuatEnh) -> SeqEnum
{The elliptic elements of the associated Shimura curve as elements in GL4(Z/NZ)}
    if not assigned Enh`EllipticElementsGL4 then
        t0 := Cputime();
        N := Enh`N;
        elliptic_elements_enhanced := EllipticElements(Enh);
        //assert forall(u){ <u,v> : u,v in elliptic_elements_enhanced |
        //    EnhancedElementInGL4(u)*EnhancedElementInGL4(v) eq EnhancedElementInGL4(u*v) };
        Enh`EllipticElementsGL4 := [ EnhancedElementInGL4(e) : e in elliptic_elements_enhanced ];
        vprint User1: "EllipticElementsGL4", Cputime() - t0;
    end if;
    return Enh`EllipticElementsGL4;
end intrinsic;

intrinsic IsCoercible(OmodN::AlgQuatOrdRes, x::Any) -> BoolElt, .
{.}
  N:=OmodN`quaternionideal;
  O:=OmodN`quaternionorder;
  ZmodN:=ResidueClassRing(N);
  if Type(x) eq AlgQuatOrdResElt then
    if Parent(x) eq OmodN then
      x0:=Eltseq(x`element);
      x1 := [ Integers()!(ZmodN!a) : a in x0 ];
      return true, OmodNElement(OmodN,O!x1);
    else
      return false, "Illegal Coercion";
    end if;
  elif Type(x) eq AlgQuatOrdElt then
    if Parent(x) eq O then
      x0:=Eltseq(x);
      x1 := [ Integers()!(ZmodN!a) : a in x0 ];
      return true, OmodNElement(OmodN,O!x1);
    else
      return false, "Illegal Coercion";
    end if;
  elif Type(x) eq AlgQuatElt then
    if x in OmodN`quaternionorder then
      x0:=Eltseq(O!x);
      x1 := [ Integers()!(ZmodN!a) : a in x0 ];
      return true, OmodNElement(OmodN,O!x1);
    else
      return false, "Illegal Coercion";
    end if;
  elif IsCoercible(O,x) then
    x0:=Eltseq(O!x);
    x1 := [ Integers()!(ZmodN!a) : a in x0 ];
    return true, OmodNElement(OmodN,O!x1);
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

intrinsic SemidirectSystem(O::AlgQuatOrd, mu::AlgQuatElt, Ns_maximal::SeqEnum[RngIntElt]) -> AlgQuatEnhSys
{Constructor from a quaternion order, a polarization mu, and a sequence of desired levels (which will be augmented to be closed under taking divisors}
    X := New(AlgQuatEnhSys);
    X`quaternionorder := O;
    X`mu := mu;
    X`Ns_maximal := Ns_maximal;
    X`Enh := AssociativeArray();
    X`Lat := AssociativeArray();
    X`Lat1 := AssociativeArray();
    X`Transfer := AssociativeArray();
    return X;
end intrinsic;

intrinsic EnhancedSemidirectProduct(X::AlgQuatEnhSys, N::RngIntElt) -> AlgQuatEnh
{Return the semidirect product at level N}
    if not IsDefined(X`Enh, N) then
        X`Enh[N] := EnhancedSemidirectProduct(X`quaternionorder, X`mu : N:=N);
    end if;
    return X`Enh[N];
end intrinsic;

intrinsic ComputeSubs(X::AlgQuatEnhSys, N::RngIntElt) -> SeqEnum
{Compute subgroups at level n for all divisors n of N}
    Enh := EnhancedSemidirectProduct(X, N);
    G := GL4sub(Enh);

    // TODO: map to a permutation group instead of computing in G
    t0 := Cputime();
    subs := Subgroups(G);
    vprint User1: "MagmaSubgroups", Cputime() - t0;
    return subs;
end intrinsic;

intrinsic ComputeLats(X::AlgQuatEnhSys, M::RngIntElt)
{}
    N := 0;
    for mm in X`Ns_maximal do
        if IsDivisibleBy(mm, M) then
            N := mm;
            break;
        end if;
    end for;
    if N eq 0 then
        Append(~X`Ns_maxial, M);
        N := M;
    end if;
    Enh := EnhancedSemidirectProduct(X, N);
    G := GL4sub(Enh);
    Gsubs := ComputeSubs(X, N);

    O := X`quaternionorder;
    Ahom := AtoGL4(Enh);
    KG := NormalizerKernelGL4(Enh);
    t0 := Cputime();
    detimages := [#getDeterminantImage(H`subgroup, O, Ahom) : H in subs];
    vprint User1: "DeterminantImages", Cputime() - t0; t0 := Cputime();

    phiN := EulerPhi(N);
    surjH := [subs[i] : i in [1..#subs] | detimages[i] eq phiN];
    trivH := [subs[i] : i in [1..#subs] | detimages[i] eq 1];

    t0 := Cputime();
    surj_gerby_H := [H : H in surjH | KG subset H`subgroup];
    //print "Gerbysurj", #surj_gerby_H, #surjH;
    triv_gerby_H := [H : H in trivH | KG subset H`subgroup];
    //print "Gerbytriv", #triv_gerby_H, #surjH;
    vprint User1: "Gerby", Cputime() - t0; t0 := Cputime();

    ker_reds := getGLReductionKernels(X, N);
    surjLevel := [getLevel(H, ker_reds) : H in surj_gerby_H];
    ker1_reds := getSLReductionKernels(ker_reds, N);
    trivLevel := [getLevel(H, ker1_reds) : H in triv_gerby_H];

    primes := PrimeDivisors(N);
    divN := Divisors(N);
    needed := [m : m in divN | not IsDefined(X`Lat, m)];
    Reverse(~needed);
    msubs := AssociativeArray();
    m1subs := AssociativeArray();
    for m in needed do
        
        Gm := GL4sub(EnhancedSemidirectProduct(X, m));
        fake_label := Sprintf("%o.a", #Gm); // The FiniteGroup code expects a label, but only the order is actually used
        GGm := NewLMFDBGrp(Gm, fake_label);
        L := New(SubgroupLat);
        L`Grp := GGm;
        L`outer_equivalence := false; // We want subgroups up to conjugacy, not up to automorphism
        L`inclusions_known := true; // We want to compute inclusion relations
        L`index_bound := 0; // Even though we are restricting subgroups, it's not correctly modeled by an index bound
        if m eq N then
            L`subs := [SubgroupLatElement(L, surj_gerby_H[i]`subgroup : i:=i, subgroup_count:=surj_gerby_H[i]`length) : i in [1..#surj_gerby_H]];
        else
            p := Representative({p : p in primes | IsDivisibleBy(N, m*p)});
            reduction_map := Transfer(X, m*p, p);
            // We construct subgroups at level m from subgroups at level m*p
            // mpsubs := [
            //L`subs := [X`Lat[m*p]`subs[i] @ reduction_map : 
            msubs[m] := [i : i in [1..#surjLevel] | IsDivisibleBy(m, surjLevel[i])];
            m1subs[m] := [i : i in [1..#trivLevel] | IsDivisibleBy(m, trivLevel[i])];
        end if;
    end for;
    //for m in divN do
        

end intrinsic;

intrinsic Lat(X::AlgQuatEnhSys, N::RngIntElt) -> SubgroupLat
{Return the lattice of surjective subgroups for levels dividing N}
    if not IsDefined(X`Lat, N) then
        ComputeLats(X, N);
    end if;
    return X`Lat[N];
end intrinsic;

intrinsic Lat1(X::AlgQuatEnhSys, N::RngIntElt) -> SubgroupLat
{Return the lattice of determinant 1 subgroups for levels dividing N}
    if not IsDefined(X`Lat1, N) then
        ComputeLats(X, N);
    end if;
    return X`Lat1[N];
end intrinsic;

intrinsic Transfer(X::AlgQuatEnhSys, N::RngIntElt, p::RngIntElt) -> HomGrp
{Return the reduction homomorphism from GL4sub(Enh[N]) to GL4sub(Enh[N/p]), where p is a prime dividing N}
    if not IsDefined(X`Transfer, <N,p>) then
        if not IsPrime(p) and IsDivisibleBy(N, p) then
            error Sprintf("%o must be a prime dividing %o", p, N);
        end if;
        EnhN := EnhancedSemidirectProduct(X, N);
        G := GL4sub(EnhN);
        if N eq p then
            X`Transfer[<N,p>] := GL4ToAutmu(EnhN);
        else
            H := GL4sub(EnhancedSemidirectProduct(X, N div p));
            Ggens := [G.i : i in [1..Ngens(G)]];
            X`Transfer[<N,p>] := hom<G -> H | [<g, ChangeRing(g, Integers(N div p))> : g in Ggens]>;
        end if;
    end if;
    return X`Transfer[<N,p>];
end intrinsic;

intrinsic getGLReductionKernels(X::AlgQuatEnhSys, N::RngIntElt) -> Assoc
{Return the prime-power kernels of reduction from level N to N/q}
    ker_reds := AssociativeArray();
    for p in PrimeDivisors(N) do
        // !!! TODO - change this !!!
        // At the moment we are only using reduction modulo p, so we only populate 
        // a single kernel of reduction (modulo p)
        // ker_reds[p] := [Kernel(Transfer(X, N, p^k)) : k in [1..Valuation(N, p)]];
        ker_reds[p] :=  [Kernel(Transfer(X, N, p))];
    end for;
    return ker_reds;
end intrinsic;

intrinsic getSLReductionKernels(GLkers::Assoc, N::RngIntElt) -> Assoc
{Intersects with SL(4, Zmod(N))}
    SLkers := AssociativeArray();
    G1 := SL(4, Integers(N));
    for p in PrimeDivisors(N) do
        SLkers[p] := [H meet G1 : H in GLkers[p]];
    end for;
    return SLkers;
end intrinsic;

intrinsic getLevel(H::GrpMat, ker_reds::Assoc) -> RngIntElt
{Find the level of a given subgroup given the kernels of reduction}
    N := Modulus(BaseRing(H));
    level := N;
    for p in PrimeDivisors(N) do
        for K in ker_reds[p] do
            if K subset H then
                level := level div p;
            end if;
        end for;
    end for;
    return level;
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





