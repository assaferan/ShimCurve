

intrinsic Mod2GaloisMapPQM(X::CrvHyp : prec:=30) -> Any 
  {Given X/F such that Jac(X) is a PQM surface, the 2-torsion 
  A[2] is free of rank 1 as an O/2-module. Let Q be an O/2-basis element. 
  Then we can write Q^sigma = a_sigma * Q for any sigma \in GalF. We return the map 
            GalF --> (O/2)^x,   sigma |--> a_sigma   
  where it factors through adjoining the 2-torsion field 
  and the endomorphism field to F.}

  CC:=ComplexFieldExtra(prec);
  //CC`epscomp:=10^-Floor(prec/2);
  assert BaseRing(X) eq Rationals();
  assert IsSimplifiedModel(X);
  B1,B2,B3:=HeuristicEndomorphismAlgebra( X : CC:=true);
  assert IsQuaternionAlgebra(B2);

  f:=HyperellipticPolynomials(X);
  XR:=RiemannSurface(f,2 : Precision:=prec);
  //assert that the basepoint is of the form (x,0)
  assert Coordinates(XR`BasePoint)[2] eq 0;


  //We just use Polredbest since combining with Polredabs often runs out of memory.
	QA2:=SplittingField(f);
  QA2:=NumberField(Polredbest(DefiningPolynomial(QA2)));
	L:=HeuristicEndomorphismFieldOfDefinition(X);
  L:=NumberField(Polredbest(DefiningPolynomial(L)));

	M:=Compositum(QA2,L);
  Mdef:=DefiningPolynomial(M);
  Mdefred:=Polredbest(Mdef);
  M:=NumberField(Mdefred);

  if Degree(M) eq Degree(QA2) then 
    print "L is a subsfield of QA2";
  else 
    print "L is not a subfield of QA2";
  end if;

	ooplaces:=InfinitePlaces(M);
  //CAREFUL: we choose an embedding here which affects the final output.
	embC:=ooplaces[1];
  Gal,auts,map:=AutomorphismGroup(M);

  //These are the roots a_i of the hyperelliptic polynomial
  // [(a_2,0)] - [(a_1,0)] will be an O/2O-basis element of A[2](C)
  //after apply the Abel-Jacobi map. assert a1 is rational.
  frootsM:=[ a[1] : a in Roots(ChangeRing(f,M))];
  frootsC:=[ CC!Evaluate(a,embC) : a in frootsM ];
  //Let's find which element x0 of frootsM corresponds to the basepoint (x0,0) of the Riemann surface. 
  exists(x0){ z : z in frootsM | Abs(Evaluate(z,embC)-Coordinates(XR`BasePoint)[1]) lt RealField(20)!0.00000000000000001 };
  

  //This shows that the action of Gal on frootsM is a RIGHT action.
  assert forall(elt){ <g,h,r> : g,h in Gal, r in frootsM | map(h)(map(g)(r)) eq map(g*h)(r) };
  //Let's make a Gset out of the roots:
  frootsMset:=Set(frootsM);
  assert #frootsMset eq #frootsM;
  Gmap := map< CartesianProduct(frootsMset,Gal) -> frootsMset | x :-> map(x[2])(x[1]) >;
  Galaction:=GSet(Gal,frootsMset,Gmap); 
  //assert forall(elt){ <g,h,r> : g,h in Gal, r in Galaction | Image(g,Galaction,r) eq map(g*h)(r) };

  //We were previously choosing a rational root as the base point of the Riemann surface,
  //Now we use the default basepoint and see which root in M corresponds to this basepoint so that we can act on it by Galois. 

	BPM:=ChangeRing(BigPeriodMatrix(XR),CC);

  GL4Z:=GL(4,Integers());
  //endos:=HeuristicEndomorphismRepresentation( X : CC:=true);
  endos := GeometricEndomorphismRepresentationCC(BPM);
  endosM2:=[ ChangeRing(m[1],CC) : m in endos ];
  endosM4:=[ ChangeRing(m[2],Rationals()) : m in endos ]; 
  Bmat:=MatrixAlgebra< Rationals(), 4 | endosM4 >;
  tr, B, maptoB := IsQuaternionAlgebra(Bmat);
  //assert maptoB is indeed an algebra-hom
  assert forall(b){ [Bmat.u,Bmat.v] : u,v in [1..4] | maptoB(Bmat.u*Bmat.v) eq maptoB(Bmat.u)*maptoB(Bmat.v) };

  Obasis:=[ maptoB(b) : b in endosM4 ];
  O:=QuaternionOrder(Obasis : IsBasis:=true);
  assert Basis(O) eq Obasis;
  a,b,c,d:=Explode(endosM2);
  OtoM2C := map< O -> KMatrixSpace(CC,2,2) | a :-> &+[ Eltseq(O!a)[i]*endosM2[i] : i in [1..4] ] >;
  assert forall(e){ Basis(O)[i] : i in [1..4] | OtoM2C(Basis(O)[i]) eq endosM2[i] };
  //assert forall(e) { [b1,b2] : b1,b2 in Obasis | (OtoM2C(b1*b2) eq OtoM2C(b1)*OtoM2C(b2)) and (OtoM2C(b1+b2) eq OtoM2C(b1) + OtoM2C(b2)) };

  //AbelJacobi() uses BPM = BigPeriodMatrix whereas the endomorphisms package uses PM = PeriodMatrix
  //PM := ChangeRing(PeriodMatrix(X),CC);
  //printf "PM is a %ox%o matrix = \n%o\n\n",  NumberOfRows(PM), NumberOfColumns(PM), PM;

  //printf "BPM is a %ox%o matrix = \n%o\n\n",  NumberOfRows(BPM), NumberOfColumns(BPM), BPM;
	P1:=ColumnSubmatrix(BPM,1,2);
  P2 := ColumnSubmatrix(BPM,3,2);
  SPM:=ChangeRing(SmallPeriodMatrix(XR),CC);
  //according to the magma documentation SPM = P1^-1*P2, which we assert here. Note BPM = [ P1 P2 ]
  assert NumericalRank(SPM - P1^-1*P2 : Epsilon := RealField(prec)!10^(-Floor(prec/2))) eq 0;

  //printf "P1 is a %ox%o matrix = \n%o\n\n",  NumberOfRows(P1), NumberOfColumns(P1), P1;

  //Check that M*PM = PM*R in the notation of Costa-Mascot-Sijsling-Voight.
  assert forall(e){ endo : endo in endos | NumericalRank(ChangeRing(endo[1],CC)*ChangeRing(BPM,CC) - ChangeRing(BPM,CC)*ChangeRing(endo[2],CC) : Epsilon := RealField(prec)!10^(-Floor(prec/5))) eq 0 };

	Latendo:=RealLatticeOfPeriodMatrix(BPM);

  //The columns of PM and 1/2*BPM are the same, but not necessarily in the same order, which we assert here.
  //Infact if 1/2BPM = [ S1 S2 ] then PM = [ S2 S1 ].
  //assert NumericalRank(2*PM - HorizontalJoin(P2,P1) : Epsilon:=RealField(prec)!10^(-Floor(prec/5))) eq 0;

  //PM_cols:=Set(Rows(Transpose(PM)));
  //BPM_halfcols:=Set(Rows(Transpose(1/2*BPM)));
  //assert forall(v){ col : col in BPM_halfcols | IsCoercible(Latendo,Eltseq(RealVector(col))) };
  //assert forall(v){ col : col in BPM_halfcols | Coordinates(Latendo!Eltseq(RealVector(col))) in Rows(IdentityMatrix(Integers(),4)) };

  //PM_cols:=Rows(Transpose(PM));
  //BPM_halfcols:=Rows(Transpose(1/2*BPM));
  //assert forall(v){ col : col in BPM_halfcols | IsCoercible(Latendo,Eltseq(RealVector(col))) };
  //assert forall(v){ col : col in BPM_halfcols | Coordinates(Latendo!Eltseq(RealVector(col))) in Rows(IdentityMatrix(Integers(),4)) };

  /*
  swap_mat := Matrix(Integers(),4,4,[Coordinates(Latendo!Eltseq(RealVector(col))) : col in BPM_halfcols])^-1;
  newendosM4 := [swap_mat*endosM4[i]*swap_mat^-1 : i in [1..#endosM4]];

  print [x in Bmat : x in newendosM4];
  newendosM2 := [&+[Eltseq(O!maptoB(Bmat!newendosM4[i]))[j]*endosM2[j] : j in [1..4]] : i in [1..4]];
  OtoM2C := map< O -> KMatrixSpace(CC,2,2) | a :-> &+[ Eltseq(O!a)[i]*newendosM2[i] : i in [1..4] ] >;
  assert forall(e){ Basis(O)[i] : i in [1..4] | OtoM2C(Basis(O)[i]) eq newendosM2[i] };
  printf "Modified OtoM2C to work with BigPeriodMatrix\n";
  */

  Omod2:=quo(O,2);
  coefs := [ [w,x,y,z] : w,x,y,z in [0,1] ];
  //Omod2_eltsCC:=[ (coef[1]*a + coef[2]*b + coef[3]*c + coef[4]*d) : coef in coefs ];
  O_elts:=[ O!(coef[1]*Obasis[1] + coef[2]*Obasis[2] + coef[3]*Obasis[3] + coef[4]*Obasis[4]) : coef in coefs ];
  

  cyclic_module:=[];
  k:=1;
  while #cyclic_module lt 16 do
    //Q is an O/2O basis element coming from the roots of X after applying Abel-Jacobi 
    Q:=AbelJacobi(XR![frootsC[k],0],XR`BasePoint);
    //1/2*P1 because this is the change of basis required from the small period matrix lattice to Latendo
    k:=k+1;
    twotorsion_points:=[ OtoM2C(a)*Q : a in O_elts ];
    //this is O_Q: the O-cyclic module generated by Q. 
    twotorsion_points_real:= [ RealVector(v) : v in twotorsion_points ];
    cyclic_module := [ twotorsion_points[i] : i in [1..#twotorsion_points] 
    | not(exists(e){ twotorsion_points[j] : j in [1..#twotorsion_points] | j lt i and IsCoercible(Latendo,Eltseq(twotorsion_points_real[i]-twotorsion_points_real[j])) }) ];
  end while;

  //check that they are all 2-torsion points, only the identity is already 2-torsion
  //and that O_Q is all of the two torsion
  assert forall(e){ x : x in twotorsion_points_real | IsCoercible(Latendo,Eltseq(2*x)) };
  assert #{ x : x in twotorsion_points_real | IsCoercible(Latendo,Eltseq(x)) } eq 1;
  assert not(exists(t){ [T1,T2] : T1,T2 in twotorsion_points_real | IsCoercible(Latendo,Eltseq(T1-T2)) and (T1 ne T2) });
  //cyclic_module := [ twotorsion_points[i] : i in [1..#twotorsion_points] 
    //| not(exists(e){ twotorsion_points[j] : j in [1..#twotorsion_points] | j lt i and IsCoercible(Latendo,Eltseq(twotorsion_points_real[i]-twotorsion_points_real[j])) }) ];



  map_init:=[];
  for sigma in Gal do
    //Qsigma is what we get when we act on Q by the Galois element sigma. It is still a two torsion point.
    Qsigma := (P1)*(AbelJacobi(XR![Evaluate(map(sigma)(frootsM[k-1]),embC),0], XR`BasePoint) - AbelJacobi(XR![Evaluate(map(sigma)(x0),embC),0], XR`BasePoint));
    cyclic_coefficients:=[ a : a in O_elts | IsCoercible(Latendo,Eltseq(RealVector(OtoM2C(a)*Q - Qsigma))) ];
    assert #cyclic_coefficients eq 1;
    //index:=Index(Omod2_eltsCC,cyclic_coefficients[1]);
    a_sigma := Omod2!cyclic_coefficients[1];
    Append(~map_init,<sigma,a_sigma>);
  end for;
  
  Omod2_elts := [ Omod2!elt : elt in O_elts ];
  enhancedmap:=map< Gal -> Omod2_elts | map_init >;
  assert enhancedmap(Id(Gal)) eq Omod2![1,0,0,0];
  //enhancedmap:=map< Gal -> Omod2_elts | sigma :-> 
  //Omod2_elts[[ i : i in [1..#twotorsion_points] | IsCoercible(Latendo,Eltseq(RealVector(twotorsion_points[i] - 1/2*(P1)*AbelJacobi(XR![Evaluate(map(sigma)(frootsM[2]),embC),0])))) ][1]] >;

  return Gal,map,enhancedmap,O;
 end intrinsic;




 
 //R<x> := PolynomialRing(Rationals()); C := HyperellipticCurve(R![-1, 5, -8, 4, -1, 1], R![]);
 //X:=C;
 intrinsic EndomorphismRepresentationPQM(X::CrvHyp : prec:=30,endo_prec:=500, quaternionorder:=[]) -> Any 
  {}

  if Type(quaternionorder) ne AlgQuatOrd then
    CC:=ComplexField(prec);
    assert BaseRing(X) eq Rationals();
    assert IsSimplifiedModel(X);
    B1,B2,B3:=HeuristicEndomorphismAlgebra( X : CC:=true);
    assert IsQuaternionAlgebra(B2);

    endos:=HeuristicEndomorphismRepresentation( X : CC:=true);
    endosM2:=[ ChangeRing(m[1],CC) : m in endos ];
    endosM4:=[ ChangeRing(m[2],Rationals()) : m in endos ]; 
    Bmat:=MatrixAlgebra< Rationals(), 4 | endosM4 >;
    tr, B, maptoB := IsQuaternionAlgebra(Bmat);
    Obasis:=[ maptoB(b) : b in endosM4 ];
    O:=QuaternionOrder(Obasis : IsBasis:=true);
    //assert IsMaximal(O);
    //O:=MaximalOrder(QuaternionAlgebra(Discriminant(Oquat)));
  else 
    O:=quaternionorder;
  end if;

  tr,mu:=HasPolarizedElementOfDegree(O,1);
  L:=HeuristicEndomorphismFieldOfDefinition(X);
  L:=OptimizedRepresentation(L);
  GalL,auts,GalLmap:=AutomorphismGroup(L);
  autsL:=[ FieldAutomorphism(L,phi) : phi in Automorphisms(L) ];
  //assert GroupName(Gal) eq "C2^2";
  //assert IsAbelian(GalL); //because there might be an issue with automorphisms being the opposite group

  AutFull:=Aut(O,mu);
  wchi:=[ a : a in Generators(Domain(AutFull)) | Sprint(a) eq "w_chi" ][1];
  wmu:=[ a : a in Generators(Domain(AutFull)) | Sprint(a) eq "w_mu" ][1];  

  if IsCyclic(GalL) then 
    if #GalL in [4,6] then 
      sigma_mu:=GalL.1;
      elts:= [ <sigma_mu^l, wmu^l> : l in [0..#GalL/2-1] ];
      galmap_init:=map< GalL -> Domain(AutFull) | elts >;
      endomorphism_rep := galmap_init*AutFull;
      assert MapIsHomomorphism(endomorphism_rep);
    else
      Kprec:=BaseNumberFieldExtra(DefiningPolynomial(L),endo_prec);
      Kprec:=RationalsExtra(endo_prec);
      XK:=ChangeRing(X,Kprec);
      A1,A2,A3:=HeuristicEndomorphismAlgebra(XK);
      tr,E:=IsNumberField(A2);
      assert tr;
      assert Degree(E) le 2;
      exists(elt){ elt : elt in [wmu,wchi,wmu*wchi] | SquarefreeFactorization(Discriminant(E)) eq SquarefreeFactorization(Rationals()!((AutFull(elt)^2)`element)) };

      sigma_elt := GalL.1;
      aut_elt:=autsL!FieldAutomorphism(L,GalLmap(sigma_elt));
      elts:= [ <aut_elt^l, elt^l> : l in [0,1] ];
      galmap_init:=map< autsL -> Domain(AutFull) | elts >;
      GalLmap2:=map< GalL -> autsL | mp :-> autsL!FieldAutomorphism(L,GalLmap(mp)) >;
      endomorphism_rep := GalLmap2*galmap_init*AutFull;

      assert MapIsHomomorphism(endomorphism_rep);
      return GalL, GalLmap2, endomorphism_rep, O;
    end if;
  end if;

  tr,muchi:=IsTwisting(O,mu);
  chi:=muchi[2];
  assert Parent(AutFull(wchi))!chi eq AutFull(wchi);
  
  cycsubs_init := [ H`subgroup : H in Subgroups(GalL : IsCyclic:=true) | H`order in [2,#GalL/2] ]; 
  cycsubs := [ H : H  in cycsubs_init | forall(e){ G : G in Exclude(cycsubs_init,H) | H notin [ N`subgroup : N in Subgroups(G) ] } ];
  //maybe_muchi are the generators of the maximal cyclic sybgroups.
  maybe_muchi := [ H.1 : H in cycsubs ];

  endos := [];
  for sigma in maybe_muchi do 
    //for each generator of the maximal cyclic subgroups, 
    //we first find the fixed field Ksigma.
    //Then we compute the endomorphism ring of Jac(X) over 
    //Ksigma. It should be a quadratic field E = Q(sqrt(m)).
    //We append the tuple <sigma, Ksigma, m>.
    Ksigma:=FixedField(L,[GalLmap(sigma)]);
    assert Degree(Ksigma) in [2,#GalL/2];
    Kprec:=BaseNumberFieldExtra(DefiningPolynomial(Ksigma),endo_prec);

    XK:=ChangeRing(X,Kprec);
    A1,A2,A3:=HeuristicEndomorphismAlgebra(XK);
    tr,E:=IsNumberField(A2);
    assert tr;
    assert Degree(E) le 2;
    Append(~endos, <sigma, Ksigma,SquarefreeFactorization(Discriminant(E)) >);
  end for;


  //End(Jac(X)) over Ksigma is equal to Q(sqrt(m)), which means it is fixed by an 
  //element in Autmu(O) of norm m (up to squares).
  //We map sigma to this element in Autmu(O).
  tup_mu:=[ tup : tup in endos | SquarefreeFactorization(Rationals()!(mu^2)) eq tup[3] ];
  assert #tup_mu eq 1;
  sigma_mu := tup_mu[1][1];
  aut_mu:=autsL!FieldAutomorphism(L,GalLmap(sigma_mu));

  tup_chi:=[ tup : tup in endos | SquarefreeFactorization(Rationals()!(chi^2)) eq tup[3] ];
  assert #tup_chi eq 1;
  sigma_chi := tup_chi[1][1];
  aut_chi:=autsL!FieldAutomorphism(L,GalLmap(sigma_chi));

  assert GalL eq sub< GalL | sigma_mu, sigma_chi >;

  //MAGMA composes from left to right, need to think about what it means for this map!!
  elts:= [ <autsL!(aut_mu^l*aut_chi^k), wmu^l*wchi^k> : l in [0..#GalL/2-1], k in [0..1] ];
  galmap_init:=map< autsL -> Domain(AutFull) | elts >;
  GalLmap2:=map< GalL -> autsL | mp :-> autsL!FieldAutomorphism(L,GalLmap(mp)) >;
  endomorphism_rep := GalLmap2*galmap_init*AutFull;
  assert MapIsHomomorphism(endomorphism_rep);

  return GalL, GalLmap2, endomorphism_rep, O;

end intrinsic;



intrinsic EnhancedRepresentationMod2PQM(X::CrvHyp : prec:=30,endo_prec := 500) -> Any 
  {return 1. the Galois group of the compositum of the two torsion field and the endomorphism field
          2. A map from the Galois group in S_n to automorphisms of the field
          3. the enhanced representation as a map from automorphisms of the field to elements of the enhanced semidirect product.
          4. the endomorphism ring}

  Galgrp2,Galmap2,mod2map,O1:=Mod2GaloisMapPQM(X : prec:=prec);
  Galgrp_end,Galmap_end,rho_end:=EndomorphismRepresentationPQM(X : prec:=prec,endo_prec:=endo_prec, quaternionorder:=O1);

 
  M:=Domain(Galmap2(Galgrp2.1));
  L:=Galmap_end(Galgrp_end.1)`L;


  rho_end_components:=Components(rho_end);
  autsL:=Codomain(rho_end_components[1]);
  //first we define the restriction map Galgrp2 --> Gal(L|Q)
  //then we can define the compositum Galgrp2 --> Gal(L|Q) --> GrpPC --> Aut(O,mu) 
  restrict_Galmap2 := map< Domain(Galmap2) -> autsL | elt :-> RestrictFieldAutomorphism(M,L,FieldAutomorphism(M,Galmap2(elt))) >;
  restrict_rho_end:= restrict_Galmap2*rho_end_components[2]*rho_end_components[3];
  assert MapIsHomomorphism(restrict_Galmap2);
  assert MapIsHomomorphism(restrict_rho_end);

  Oenh:=EnhancedSemidirectProduct(O1 : N:=2);
  rho_enhanced:=map< Galgrp2 -> Oenh | sigma :-> Oenh!< restrict_rho_end(sigma), mod2map(sigma) >  >;

  assert MapIsHomomorphism(rho_enhanced : injective:=true);
  return Galgrp2, Galmap2, rho_enhanced, O1;
end intrinsic;
  

//Rx<x>:=PolynomialRing(Rationals()); fx:=-x^5+4*x^4-10*x^3+8*x^2-2*x; X:=HyperellipticCurve(fx);



