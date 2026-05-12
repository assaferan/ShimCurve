function find_q(D, N)
  pD := PrimeDivisors(D);
  pN := PrimeDivisors(N);
  resD := [(p eq 2) select 5 else Integers()!Nonsquare(GF(p))  : p in pD];
  resN := [1 : p in pN];
  ps := pD cat pN;
  res := resD cat resN;
  if 2 notin ps then
    ps := [2] cat ps;
    res := [1] cat res;
  end if;
  for i->p in ps do
    if p eq 2 then ps[i] := 8; end if;
  end for;
  q := CRT(res, ps);
  assert &and[KroneckerSymbol(q,p) eq -1 : p in pD];
  assert &and[KroneckerSymbol(q,p) eq 1 : p in pN];
  assert q mod 4 eq 1;
  return q;
end function;

function eichler_order(D,N)
  // This is needed for the construction below, I think
  assert IsSquarefree(N);
  q := find_q(D, N);
  is_sqr, a := IsSquare((Integers(q)!(D*N))^(-1));
  assert is_sqr;
  a := Integers()!a;
  Q := Rationals();
  B<i,j> := QuaternionAlgebra(Q, D*N, q);
  assert Discriminant(B) eq D;
  basisO := [1, (1+j)/2, (i+i*j)/2, (a*D*N*j+i*j)/q];
  O := QuaternionOrder(basisO);
  assert IsEichler(O);
  assert Level(O) eq N;
  return O, basisO;
end function;

function normalizing_element_of_norm(O, basisO, d)
  B := Algebra(O);
  if d eq 1 then return true, O!1; end if;
  Qx<[x]> := FunctionField(Rationals(), 4);
  Bx, B_to_Bx := ChangeRing(B, Qx);
  mu := &+[x[i]*B_to_Bx(basisO[i]) : i in [1..4]];
  RHS := Matrix([Eltseq(B_to_Bx(b) * mu) : b in basisO]);
  LHS := Matrix([Eltseq(mu * B_to_Bx(b)) : b in basisO]);
  A := RHS^(-1)*LHS;
  assert Denominator(A) eq Norm(mu);
  nums := [Numerator(a) : a in Eltseq(A) | Denominator(a) eq Norm(mu)];
  eqns := nums cat [Numerator(Norm(mu))];
  dens := [LCM([Denominator(x) : x in Coefficients(eqn)]) : eqn in eqns];
  int_eqns := [dens[i]*eqns[i] : i in [1..#eqns]];
  An := AffineSpace(Universe(int_eqns));
  S := Scheme(An, int_eqns);
  pts_mod_p := AssociativeArray();
  for p in PrimeDivisors(d) do
    Sp := ChangeRing(S, GF(p));
    pts_mod_p[p] := [[Integers() | x : x in Eltseq(P)] : P in Points(Sp)];
  end for;
  for p in PrimeDivisors(LCM(dens)) do
    if (d mod p eq 0) then continue; end if; // think later how to handle p = 2
    S := Scheme(An, [int_eqns[i] : i in [1..#dens] | dens[i] mod p eq 0]);
    Sp := ChangeRing(S, GF(p));
    pts_mod_p[p] := [[Integers() | x : x in Eltseq(P)] : P in Points(Sp)];
  end for;
  ps := [x : x in Keys(pts_mod_p)];
  X := CartesianProduct([pts_mod_p[p] : p in ps]);
  nrd := Norm(mu);
  for x in X do
    coords := [];
    for i in [1..Dimension(An)] do
      res := [Integers()!x[j][i] : j->p in ps];
      Append(~coords, CRT(res, ps));
    end for;
    assert &and[IsIntegral(Evaluate(eqn, coords)) : eqn in eqns];
    ev_nrd := Evaluate(nrd, coords);
    assert IsIntegral(ev_nrd);
    ev_nrd := Integers()!ev_nrd;
    assert ev_nrd mod d eq 0;
    if IsSquare(ev_nrd div d) and (ev_nrd ne 0) then
      mu := &+[coords[i]*basisO[i] : i in [1..4]];
      nrd_mu := Norm(mu);
      assert IsIntegral(nrd_mu);
      nrd_mu := Integers()!nrd_mu;
      assert nrd_mu mod d eq 0;
      assert IsSquare(nrd_mu div d);
      assert mu in O;
      print "d = ", d, "mu = ", mu, "T = ", Trace(mu)^2 / Norm(mu);
      // We add this because it seems we want elliptic elements
      if Trace(mu)^2 lt 4*Norm(mu) then
        return true, O!mu;
      end if;
    end if;
  end for;
  return false, _;
end function;

intrinsic NormalizerPlusGenerators(O::AlgQuatOrd) -> SeqEnum 
{return generators of the positive norm elements which normalize O}
  require IsEichler(O) : "Only implemented for Eichler orders";
  D := Discriminant(Algebra(O));
  N := Level(O);
  // It seems the code assumes more than is stated here.
  // One wants these elements to be of finite order in Bx/Qx
  // Is this a real requirement or an artifact?
  mus := [mu where _, mu := normalizing_element_of_norm(O, Basis(O), d) : d in HallDivisors(D*N) | d ne 1];
  return mus;
end intrinsic;

intrinsic SemidirectToNormalizer(O::AlgQuatOrd,mu::AlgQuatOrdElt,h::AlgQuatEnhElt) -> AlgQuatProjElt
  {the map from the semidirect product to the normalizer.}
  w:=(h`element[1])`element;
  x:=h`element[2];
  return Parent(h`element[1])!(w*x);
end intrinsic;

intrinsic SemidirectToNormalizerKernel(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> SeqEnum 
  {return the kernel of the map from the enhanced semidirect product to N_B^x(O). 
  It is necessarily cyclic and the second value is the generator of the group}
  B:=QuaternionAlgebra(O);
  Ocirc:=EnhancedSemidirectProduct(O);
  AutFull, autmuOseq := Aut(O,mu);
  Oxcyc_cand:= [ (1/Integers()!Sqrt(Norm(a`element)))*a`element : a in autmuOseq | IsSquare(Norm(a`element)) ];
  //ker:=[ Ocirc!<x,x^-1> : x in Oxcyc ];
  Oxcyc := [x : x in Oxcyc_cand | x in O];
  ker:=[ Ocirc!<x,x^-1> : x in Oxcyc];
  assert #ker in [1,2,3];
  assert Set([ Norm(e) eq 1 : e in Oxcyc ]) eq Set([true]);
  if #ker eq 1 then 
    assert ker[1] eq Ocirc!<B!1,O!1> or ker[1] eq Ocirc!<B!1,-O!1>;
    return [ Ocirc!<B!1,O!1>,Ocirc!<B!1,-O!1> ],Ocirc!<B!1,-O!1>;
  else 
    gen:=[ e : e in ker | Order(e) eq 2*#ker ];
    assert #gen eq 1;
    gen:=gen[1];
    newker:=[ gen^i : i in [1..Order(gen)] ];
    assert #Set(newker) eq Order(gen);
    //assert its cyclic in GL4
    return newker,gen;
  end if;
end intrinsic;

intrinsic SemidirectToNormalizerKernel(O::AlgQuatOrd,mu::AlgQuatElt) -> SeqEnum 
  {return the kernel of the map form the enhanced semidirect product to N_B^x(O). 
  It is necessarily cyclic and the second value is the generator of the group}
  return SemidirectToNormalizerKernel(O,O!mu);
end intrinsic;

intrinsic NormalizerToAutmuO(O::AlgQuatOrd,mu::AlgQuatOrdElt,a::AlgQuatOrdElt) -> AlgQuatEnhElt 
  {Lift an element a of the Normalizer of O to the enhanced semidirect product, which is well defined up to 
  the kernel of this map (given by SemidirectToNormalizerKernel)}
  Ocirc:=EnhancedSemidirectProduct(O);
  AutFull,autmuOseq:=Aut(O,mu);

  //[ elt : elt in autmuOseq | elt in ker ];

  assert a^2/Norm(a) in O;
  assert Norm(a) gt 0;
  
  for w in autmuOseq do 
    if IsSquare(Rationals()!Abs(Norm((w`element)^-1*a))) then
      tr,c:=IsSquare(Rationals()!Abs(Norm((w`element)^-1*a)));
      x:=(1/c)*((w`element)^-1)*a;
      assert x in O;
      assert Norm(x) in {1,-1};
      ell:=Ocirc!<w,O!x>;
      return ell;
    end if;
  end for;
  
end intrinsic;

intrinsic NormalizerToAutmuO(O::AlgQuatOrd,mu::AlgQuatElt,a::AlgQuatElt) -> AlgQuatEnhElt 
  {Lift an element a of the Normalizer of O to the enhanced semidirect product, which is well defined up to 
  the kernel of this map (given by SemidirectToNormalizerKernel)}
  return NormalizerToAutmuO(O,O!mu,O!a);
end intrinsic;


intrinsic NormalizerToAutmuO(O::AlgQuatOrd,mu::AlgQuatElt,a::AlgQuatOrdElt) -> AlgQuatEnhElt 
  {Lift an element a of the Normalizer of O to the enhanced semidirect product, which is well defined up to 
  the kernel of this map (given by SemidirectToNormalizerKernel)}
  return NormalizerToAutmuO(O,O!mu,a);
end intrinsic;

intrinsic NormalizerToAutmuO(O::AlgQuatOrd,mu::AlgQuatOrdElt,a::AlgQuatElt) -> AlgQuatEnhElt 
  {Lift an element a of the Normalizer of O to the enhanced semidirect product, which is well defined up to 
  the kernel of this map (given by SemidirectToNormalizerKernel)}
  return NormalizerToAutmuO(O,mu,O!a);
end intrinsic;




intrinsic NormalizerPlusGeneratorsEnhanced(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> Tup 
  {return generators of the positive norm elements which normalize O in the enhanced semidirect product}
  ker,kergen:=SemidirectToNormalizerKernel(O,mu);
  Ocirc:=EnhancedSemidirectProduct(O);
  Nplus:=NormalizerPlusGenerators(O);
  return [ Ocirc!NormalizerToAutmuO(O,O!mu,O!a) : a in NormalizerPlusGenerators(O) ] cat [Ocirc!kergen];
end intrinsic;

intrinsic NormalizerPlusGeneratorsEnhanced(O::AlgQuatOrd,mu::AlgQuatElt) -> Tup 
  {return generators of the positive norm elements which normalize O in the enhanced semidirect product}
  return NormalizerPlusGeneratorsEnhanced(O,O!mu);
end intrinsic;

intrinsic NormalizerPlusGeneratorsEnhanced(O::AlgQuatOrd,del::RngIntElt) -> Tup 
  {return generators of the positive norm elements which normalize O in the enhanced semidirect product}
  tr,mu:=HasPolarizedElementOfDegree(O,del);
  return NormalizerPlusGeneratorsEnhanced(O,O!mu);
end intrinsic;



intrinsic NormalizerPlusGeneratorsGL4modN(O::AlgQuatOrd,mu::AlgQuatOrdElt,N::RngIntElt) -> SeqEnum 
  {return generators of the positive norm elements which normalize O in the enhanced semidirect product}
  return [ EnhancedElementInGL4modN(g,N) : g in NormalizerPlusGeneratorsEnhanced(O,mu) ];
end intrinsic;

intrinsic NormalizerPlusGeneratorsGL4modN(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt) -> SeqEnum 
  {return generators of the positive norm elements which normalize O in the enhanced semidirect product}
  return [ EnhancedElementInGL4modN(g,N) : g in NormalizerPlusGeneratorsEnhanced(O,O!mu) ];
end intrinsic;


intrinsic NormalizerPlusGeneratorsGL4modN(O::AlgQuatOrd,del::RngIntElt,N::RngIntElt) -> SeqEnum 
  {return generators of the positive norm elements which normalize O in the enhanced semidirect product}
  tr,mu:=HasPolarizedElementOfDegree(O,del);
  return [ EnhancedElementInGL4modN(g,N) : g in NormalizerPlusGeneratorsEnhanced(O,mu) ];
end intrinsic;

intrinsic EnhancedEllipticElements(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> SeqEnum 
  {return the elliptic elements}
  Ocirc:=EnhancedSemidirectProduct(O);
  return [ Ocirc!NormalizerToAutmuO(O,mu,a) : a in NormalizerPlusGenerators(O) ];
end intrinsic;

intrinsic EnhancedEllipticElements(O::AlgQuatOrd,mu::AlgQuatElt) -> SeqEnum
  {return the elliptic elements of the enhanced semidirect product}

  return EnhancedEllipticElements(O,O!mu);
end intrinsic;





