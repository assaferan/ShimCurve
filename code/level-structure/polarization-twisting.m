
  

intrinsic HasPolarizedElementOfDegree(O::AlgQuatOrd,d::RngIntElt) -> BoolElt, AlgQuatElt 
  {return an element mu of O such that mu^2 + d*disc(O) = 0 if it exists.}
  disc:=Discriminant(O);
  B:=QuaternionAlgebra(O);
  Rx<x>:=PolynomialRing(Rationals());
  Em<v>:=NumberField(x^2+d*disc);
  if IsSplittingField(Em,QuaternionAlgebra(O)) then 
    cyc,Czeta,zeta:=IsCyclotomic(Em);
    if cyc eq true then      
      Zzeta:=Integers(Czeta);
      z:=Zzeta.2;
      zO,emb:=Embed(Zzeta,O);
      if CyclotomicOrder(Czeta) eq 4 then 
        assert zO^4 eq 1;
        tr,c:=IsSquare(Integers()!d*disc);
        mu:=c*zO;
        assert mu^2+d*disc eq 0;
        assert mu in O;
        return true, B!mu;
      else 
        assert zO^3 eq 1;
        tr,c:=IsSquare(Integers()!d*disc/3);
        mu:=(2*zO+1)*c;
        assert mu^2+d*disc eq 0;
        assert mu in O;
        return true,B!mu;
      end if;
    else 
      Rm:=Order([1,v]);
      mu,emb:=Embed(Rm,O);
      assert mu^2+d*disc eq 0;
      return true, B!mu;
    end if;
  else 
    return false;
  end if;
end intrinsic;


intrinsic DegreeOfPolarizedElement(O::AlgQuatOrd,mu:AlgQuatOrdElt) -> RngIntElt
  {degree of mu}
  tr,nmu:= IsScalar(mu^2);
  //assert IsSquarefree(Integers()!nmu);
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

  assert IsMaximal(O);
  Rx<x>:=PolynomialRing(Rationals());
  tr,nmu:= IsScalar(mu^2);
  //assert IsSquarefree(Integers()!nmu);
  disc:=Discriminant(O);
  del:=DegreeOfPolarizedElement(O,mu);
  B:=QuaternionAlgebra(O);
  ram:=Divisors(disc);

  //consider the map a |-> mu^-1*a*mu
  mu_GL4:=NormalizingElementToGL4(mu,O);
  basisO:=Basis(O);
  skew_commuters:=Eigenspace(mu_GL4,-1);
  skew_commuters_gens:=Basis(skew_commuters);
  assert Dimension(skew_commuters) eq 2;
  skew_commute_basis:=[ &+[ Eltseq(skew_commuters_gens[j])[i]*basisO[i] : i in [1..4] ] : j in [1..2] ];
  assert forall(e){ b : b in skew_commute_basis | mu^-1*b*mu eq -b };

  a:=-Integers()!Norm(skew_commute_basis[1]);
  b:=-Integers()!Trace(skew_commute_basis[1]*Conjugate(skew_commute_basis[2]));
  c:=-Integers()!Norm(skew_commute_basis[2]);
  Dform:=b^2-4*a*c;
  assert Dform lt 0;
  Q:=QuadraticForms(Dform);
  q := Q![a,b,c];
  L:=Lattice(q);
  
  solns:=ShortVectors(L,disc);
  if #solns eq 0 then 
    return false, [mu];
  end if;

  for soln in solns do 
    if IsDivisibleBy(disc,soln[2]) then
      x,y:=Explode(Eltseq(soln[1]));
      chi:=x*skew_commute_basis[1] + y*skew_commute_basis[2];
      assert IsDivisibleBy(disc,Norm(chi));
      assert chi in O;
      assert mu*chi eq -chi*mu;
      return true, [mu,chi];
    end if;
  end for;

  return false;



  /*flag:=false;
  while flag eq false do 
    if IsDivisibleBy(disc,Norm(a*skew_commute_basis[1] + b*skew_commute_basis[2])) then 
      soln:=[a,b];
      flag:=true;
    end if;
  end while;*/
  


  //[ [Norm(a*skew_commute_basis[1] + b*skew_commute_basis[2]),a,b] : a,b in [-2..2] ];
  
  //First we find twisting elements for an isomorphic quaternion algebra to B given by 
  //Bram<i,j> = (-D*del,m | Q). Then we find an isomorphism phi: Bram -> B. Otwisted_basis 
  // is the phi(Basis(MaximalOrder(Bram))). This defines an order of B and phi(i), phi(j) 
  //will define twisting elements mu and chi for this Otwisted_inB. However, Otwisted_inB is 
  //not necessarily the same as O so we have to find an isomorphism Otwisted_inB --> O
  //and map the twisting elements to get mu and chi and O. We should find that this mu is 
  //plus or minus the original mu.  

  /*
  Bdisc:=QuaternionAlgebra(Discriminant(B));
  Odisc:=MaximalOrder(Bdisc);
  for m in ram do
    Bram<i1,j1>:=QuaternionAlgebra< Rationals() | -disc*del, m>;
    if Discriminant(Bram) eq Discriminant(B) then 
      Otwisted:=MaximalOrder(Bram);
      assert i1 in Otwisted and j1 in Otwisted and i1*j1 eq -j1*i1;
      //Bnumfld<i,j>:=QuaternionAlgebra< RationalsAsNumberField() | -disc*del, m>;    
      break;
    end if;
  end for;

  tr,map:=IsIsomorphic(Bram,B : Isomorphism:=true);
  Otwisted_basis:=[ map(elt) : elt in Basis(Otwisted) ];
  Otwisted_inB:=QuaternionOrder(Otwisted_basis);

  Otwisted_muchi:= [ map(i1), map(j1) ];
  assert Otwisted_muchi[1] in Otwisted_inB and Otwisted_muchi[1] in Otwisted_inB 
    and Otwisted_muchi[1]*Otwisted_muchi[2] eq -Otwisted_muchi[2]*Otwisted_muchi[1];

  //now we have to make them associative orders to retreive the isomorphism
  Bnumfld:=ChangeRing(B,RationalsAsNumberField());
  Onumfld:=Order([ Bnumfld!Eltseq(ChangeRing(b,RationalsAsNumberField())) : b in Basis(O) ]);
  Otwisted_numfld:=Order([ Bnumfld!Eltseq(ChangeRing(b,RationalsAsNumberField())) : b in Basis(Otwisted_inB) ]);
  
  _,_,gamma:=IsIsomorphic(Otwisted_numfld,Onumfld : FindElement:=true);
  gammaQ:=B!Eltseq(ChangeRing(gamma,Rationals()));

  Omuchi:=[ (gammaQ^(-1))*x*gammaQ : x in Otwisted_muchi ];
  */

  /*Omuchi := [];
  for x in Otwisted_muchi do
    xfld_twst := ChangeRing(B!x,RationalsAsNumberField());
    xfld_Btwst_elt := Bnumfld!xfld_twst;
    //xfld_Oelt := Onumfld!xfld_Belt;
    xfld := (gamma^(-1))*(xfld_Btwst_elt)*gamma;
    xQ := ChangeRing(xfld,Rationals());
    xZ := O!xQ;
    Append(Omuchi,xZ);
  end for;*/


  //Omuchi_numfld:=[ gamma(Bnumfld!Eltseq(ChangeRing(x,RationalsAsNumberField()))) : x in Otwisted_muchi];
  //Omuchi := [ B!Eltseq(ChangeRing(Bnumfld!x,Rationals())) : x in Omuchi_numfld ];

  //make sure its twisting


end intrinsic;




