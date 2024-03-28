
  

intrinsic HasPolarizedElementOfDegree(O::AlgQuatOrd,d::RngIntElt) -> BoolElt, AlgQuatElt 
  {return an element mu of O such that mu^2 + d*disc(O) = 0 if it exists.}
  assert IsSquarefree(d);
  disc:=Discriminant(O);
  B:=QuaternionAlgebra(O);
  Rx<x>:=PolynomialRing(Rationals());
  Em<v>:=NumberField(x^2+d*disc);
  if IsSplittingField(Em,QuaternionAlgebra(O)) then 
/*    cyc,Czeta,zeta:=IsCyclotomic(Em);
    if cyc eq true then      
      Zzeta:=Integers(Czeta);
      z:=Zzeta.2;
      zO,emb:=Embed(Zzeta,O);
      if CyclotomicOrder(Czeta) eq 4 then 
        assert zO^4 eq 1;
        tr,c:=IsSquare(Integers()!d*disc);
        mu:=zO/c;
        assert mu^2+d/disc eq 0;
        assert d*mu in O;
        return true, B!mu;
      else 
        assert zO^3 eq 1;
        tr,c:=IsSquare(Integers()!d*disc/3);
        mu:=(2*zO+1)*c;
        assert mu^2+d*disc eq 0;
        assert d*mu in O;
        return true,B!mu;
      end if;
    else */
    Rm:=Order([1,v]);
    mu,emb:=Embed(Rm,O);
    assert mu^2+d*disc eq 0;
    return true, B!(mu);   
  else 
    return false;
  end if;
end intrinsic;


intrinsic DegreeOfPolarizedElement(O::AlgQuatOrd,mu:AlgQuatOrdElt) -> RngIntElt
  {degree of mu}
  tr,nmu:= IsScalar(mu^2);
  assert tr;
  disc:=Discriminant(O);
  del:=SquarefreeFactorization(-nmu/disc);
  assert IsCoercible(Integers(),del);
  assert IsSquarefree(Integers()!del);
  return Integers()!del;
end intrinsic;

intrinsic IsTwisting(O::AlgQuatOrd,mu::AlgQuatElt) -> BoolElt
  {(O,mu) is twisting (of degree del = -mu^2/disc(O)) if there exists chi in O and N_Bx(O)
   such that chi^2 = m, m|Disc(O) and mu*chi = -chi*mu. Return true or false; if true 
   return [mu, chi] up to scaling}

  //assert IsMaximal(O);
  Rx<x>:=PolynomialRing(Rationals());
  tr,nmu:= IsScalar(mu^2);
  assert tr;
  //assert IsSquarefree(Integers()!nmu);
  disc:=Discriminant(O);
  del:=DegreeOfPolarizedElement(O,mu);
  B:=QuaternionAlgebra(O);
  ram:=Divisors(disc);

  //consider the map a |-> mu^-1*a*mu
  mu_GL4:=NormalizingElementToGL4(mu,O);
  basisO:=Basis(O);

  //this is equal to V = { v \in O | mu^-1vmu = -v }
  skew_commuters:=Eigenspace(mu_GL4,-1);
  skew_commuters_gens:=Basis(skew_commuters);
  assert Dimension(skew_commuters) eq 2;
  //The skew-commute set V is equal to Z*v_1 + Z*v_2 for v_1,v_2 in skew_commute_basis
  skew_commute_basis:=[ &+[ Eltseq(skew_commuters_gens[j])[i]*basisO[i] : i in [1..4] ] : j in [1..2] ];
  assert forall(e){ b : b in skew_commute_basis | mu^-1*b*mu eq -b };

  //nrd(x*v_1 + y*v_2) = nrd(v_1)*x^2 + trd(v1\bar{v_2})*x*y + nrd(v_2)*y^2
  // hence we will q(x,y) = -nrd(x*v_1 + y*v_2) be the quadratic form which 
  //we will see if it has any solutions such that q(x,y) | disc(O).
  //TODO: not sure if this is enough when O is not maximal to conclude element is in normalizer
  a:=-Integers()!Norm(skew_commute_basis[1]);
  b:=-Integers()!Trace(skew_commute_basis[1]*Conjugate(skew_commute_basis[2]));
  c:=-Integers()!Norm(skew_commute_basis[2]);
  Dform:=b^2-4*a*c;
  assert Dform lt 0;
  Q:=QuadraticForms(Dform);
  q := Q![a,b,c];
  L:=Lattice(q);
  
  //We loop over short vectors of size <= disc to see if any divide disc
  solns:=ShortVectors(L,disc);
  if #solns eq 0 then 
    return false, [mu];
  end if;


//Note that there might be many candidates for chi.
//Does this mean that there are multiple possibilities for Aut_mu(O) or they generate the same group!?!?
  for soln in solns do 
    if IsDivisibleBy(disc,soln[2]) then
      x,y:=Explode(Eltseq(soln[1]));
      chi:=x*skew_commute_basis[1] + y*skew_commute_basis[2];
      assert IsDivisibleBy(disc,Norm(chi));
      assert chi in O;
      assert mu*chi eq -chi*mu;
      assert forall(e){ b : b in Basis(O) | chi^-1*b*chi in O };
      return true, [mu,chi];
    end if;
  end for;

  return false;

end intrinsic;




