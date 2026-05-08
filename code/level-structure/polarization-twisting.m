declare type QuaternionLatticeData;
declare attributes QuaternionLatticeData: D, N, Q, O, L, Ldual, Qinv, basis_L, disc_grp, to_disc;

function get_lattice_data(D, N, O)
    B := QuaternionAlgebra(D);
    O_max := MaximalOrder(B);
    basis_O := Basis(O);
    L_space := Kernel(Transpose(Matrix(Integers(),[[Trace(x) : x in basis_O]])));
    basis_L := [&+[b[i]*basis_O[i] : i in [1..4]] : b in Basis(L_space)];
    BM_L := Matrix([Eltseq(b) : b in basis_L]);
    Q := Matrix([[Norm(x+y)-Norm(x)-Norm(y) : y in basis_L] : x in basis_L]);
    BM_Ldual := Q^(-1)*BM_L;
    // L := LatticeWithGram(Q : CheckPositive := false);
    // return L;
    denom := Denominator(BM_Ldual);
    // We are modifying it to be always with respect to the basis of L.
    // Ldual := RSpaceWithBasis(ChangeRing(denom*BM_Ldual,Integers()));
    Ldual := RSpaceWithBasis(ChangeRing(denom*Q^(-1), Integers()));
    // L := RSpaceWithBasis(ChangeRing(denom*BM_L,Integers()));
    L := RSpaceWithBasis(ScalarMatrix(3,denom));
    disc_grp, to_disc := Ldual / L;
    return L, Ldual, disc_grp, to_disc, Q^(-1), Q, O, basis_L;
end function;

intrinsic ShimuraCurveLattice(D::RngIntElt, N::RngIntElt, O::AlgQuatOrd) -> QuaternionLatticeData
{Return the quaternion lattice data for the lattice of trace zero elements in the
 Eichler order of level N in the quaternion algebra of discriminant D.}
    L, Ldual, disc_grp, to_disc, Qinv, Q, O, basis_L := get_lattice_data(D,N,O);
    data := New(QuaternionLatticeData);
    data`D := D;
    data`N := N;
    data`L := L;
    data`Ldual := Ldual;
    data`Q := Q;
    data`Qinv := Qinv;
    data`O := O;
    data`basis_L := basis_L;
    data`disc_grp := disc_grp;
    data`to_disc := to_disc;
    return data;
end intrinsic;

intrinsic FindLambda(Q::AlgMatElt, d::RngIntElt, Order::AlgQuatOrd, basis_L::SeqEnum : bound := 10)-> BoolElt, ModTupRngElt
{.}
    require d gt 0: "d must be positive";

    Q := ChangeRing(Q, Integers());
    n := Nrows(Q);
    idxs := CartesianPower([-bound..bound], n);
    for idx in idxs do
        v := Vector([idx[j] : j in [1..n]]);
        v := ChangeRing(v, BaseRing(Q));
        if (v*Q,v) eq 2*d then
            // checking whether this is an optimal embedding of the order of discriminant d
            elt := &+[v[i]*basis_L[i] : i in [1..#basis_L]];
            if d mod 4 ne 3 then
                assert d mod 4 eq 0;
                if elt/2 in Order then
                    return true, v;
                end if;
            end if;
            // d mod 4 eq 3
            if (1+elt)/2 in Order then
                return true, v;
            end if;
        end if;
    end for;
    return false, _;
end intrinsic;

intrinsic HasPolarizedElementOfDegree(O::AlgQuatOrd,d::RngIntElt) -> BoolElt, AlgQuatElt 
  {return an element mu of O such that mu^2 + d*disc(O) = 0 if it exists.}
  assert IsSquarefree(d);
  disc:=Discriminant(O);
  B:=QuaternionAlgebra(O);
  D := Discriminant(B);
  N := disc div D;
  Rx<x>:=PolynomialRing(Rationals());
  Em<v>:=NumberField(x^2+d*disc);
  Rm:=Order([1,v]);
  if IsSplittingField(Em,QuaternionAlgebra(O)) then 
    //Rm:=Order([1,v]);
    //if N eq 1 then
    //mu,emb:=Embed(Rm,O);
    mu, _ := Embed(Em, B);
    _, nu := InternalConjugatingElement(O, mu);
    mu := O!(nu*mu*nu^(-1));
    /*
    else
      Ldata := ShimuraCurveLattice(D,N,O);
      Q := Ldata`Q;
      basis_L := Ldata`basis_L;
      f := DefiningPolynomial(Conic(Q));
      found_point := false;
      g := f - d*disc;
      mu := B!1;
      bound := 10;
      while not found_point and bound le 100000 do
        bound *:= 10;
        for x in [-bound..bound] do
            for y in [-bound..bound] do
                for z in [-bound..bound] do
                    if Evaluate(g, [x,y,z]) eq 0 then
                       mu := x*basis_L[1] + y*basis_L[2] + z*basis_L[3];
                       assert Trace(mu) eq 0; assert Norm(mu) eq d*disc; assert mu in O;
                       return true, B!(mu);
                    end if;
                end for;
            end for;
        end for;
      end while;
    end if;
    */
    if not (&and[AbsoluteValue(x) le 2147483647 : x in Eltseq(O!mu)]) then 
      num_try := 1;
      mu, emb := Embed(Rm, O: Al:="Search");
      while not (&and[AbsoluteValue(x) le 2147483647 : x in Eltseq(O!mu)]) and num_try le 10 do 
        mu, emb := Embed(Rm, O: Al:="Search");
        num_try +:=1; 
      end while;
      if &and[AbsoluteValue(x) le 2147483647 : x in Eltseq(O!mu)] then 
        assert mu^2+d*disc eq 0;
        return true, B!(mu);
      else 
        a, b, _, _ := StandardForm(B);
        C := Conic([Em| 1, -a, -b]);
        CA := AffinePatch(C, 1);
        CA_Q, CA_Q_to_CA := RestrictionOfScalars(CA, Rationals());
        bound := 100;
        pts := PointSearch(CA_Q, bound);
        while #pts eq 0 and bound le 10000 do 
          bound *:= 10;
          pts := PointSearch(CA_Q, bound);
        end while;
        if #pts eq 0 then return false, "unable to find mu by naive point search"; end if;
        CA_Q_K := Domain(CA_Q_to_CA);
        sol := C!(CA_Q_to_CA(CA_Q_K!Eltseq(pts[1])));
        g := [Eltseq(sol[1]), Eltseq(sol[2])];
        mu := B![g[1][1],g[2][1],1,0] / B![g[1][2],g[2][2],0,0];
        bl, nu := InternalConjugatingElement(O, mu);
        assert bl;
        mu := O!(nu*mu*nu^(-1));
      end if;
    end if;
    assert mu in O;
    assert mu^2+d*disc eq 0;
    return true, B!(mu);   
  else 
    return false, _;
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
  assert mu in O;
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
      //assert IsDivisibleBy(disc,Norm(chi));
      //assert chi in O;
      //assert mu*chi eq -chi*mu;
      //assert forall(e){ b : b in Basis(O) | chi^-1*b*chi in O };
      //return true, [mu,chi];
      if IsDivisibleBy(disc,Norm(chi)) and (chi in O) and (mu*chi eq -chi*mu) and forall(e){ b : b in Basis(O) | chi^-1*b*chi in O } then 
        return true, [mu,chi];
      end if;
    end if;
  end for;

  return false;

end intrinsic;




