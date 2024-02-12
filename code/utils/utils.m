
/*intrinsic ReplaceAll(string::MonStgElt, char1::MonStgElt, char2::MonStgElt) -> MonStgElt
  {Replace all instances of the string char1 with char2 in string}
  return Pipe(Sprintf("sed \"s/%o/%o/g\"", char1, char2), string);
end intrinsic;
*/


intrinsic ReplaceString(s::MonStgElt,c::MonStgElt,d::MonStgElt) -> MonStgElt
{ Greedily replace each occurrence of string c in s with the string d. }
    require #c ge 1: "The string to be replaced cannot be empty.";
    m := #c;
    t := "";
    n := Index(s,c);
    while n gt 0 do
        t cat:= s[1..n-1] cat d;
        s := s[n+m..#s];
        n := Index(s,c);
    end while;
    return t cat s;
end intrinsic;


intrinsic getLines(file::MonStgElt) -> Any
  {turn text file into lines}
  F := Open(file, "r");
  Ls := [];
  while true do
    s := Gets(F);
    if IsEof(s) then break; end if;
    Append(~Ls,s);
  end while;
  return Ls;
end intrinsic;


intrinsic IsNumberField(A::AlgAss) -> BoolElt, FldNum
  {Take the associative algebra over Q and make a number field}
  if BaseRing(A) eq Rationals() and IsCommutative(A) then 
    B:=Basis(A); 
    pols:=[ MinimalPolynomial(b) : b in B ];
    F:=NumberField(pols);
    return true,F;
  else 
   return false;
  end if;
end intrinsic;


intrinsic SquarefreeFactorization(x::FldRatElt) -> FldRatElt
  {x = a*q^2 where a is a squarefree integer, return a, q}
  numx:=Numerator(x);
  denx:=Denominator(x);

  numa,c:=SquarefreeFactorization(numx);
  dena,d:=SquarefreeFactorization(denx);

  a:=numa*dena;
  assert IsSquarefree(a);
  assert a in Integers();
  tr,q:=IsSquare(x/a);
  assert tr;
  assert x eq a*q^2;
  return a, q;
end intrinsic;


intrinsic RepresentativeModuloSquares(x::FldRatElt) -> RngIntElt
  {x = q^2*a where a is a squarefree integer, return a}

  numx:=Numerator(x);
  denx:=Denominator(x);

  numa,c:=SquarefreeFactorization(numx);
  dena,d:=SquarefreeFactorization(denx);
  
  a:=numa*dena;
  assert IsSquarefree(a);
  assert IsSquare(x/a);
  return numa*dena;
end intrinsic;


intrinsic TrialRepresentativeModuloSquares(x::FldRatElt : divisionbound:=1000000000) -> RngIntElt
  {x = q^2*a where a is a squarefree integer, return a}

  if x eq 0 then 
    return x;
  else 
    numx:=Numerator(x);
    denx:=Denominator(x);

    trinum1,trinum2:=TrialDivision(numx,divisionbound);
    Append(~trinum1,<1,1>);
    trinum2:=trinum2 cat [1];
    assert (&*[ a[1]^a[2] : a in trinum1 ])*trinum2[1] eq Abs(numx);

    triden1,triden2:=TrialDivision(denx,divisionbound);
    Append(~triden1,<1,1>);
    triden2:=triden2 cat [1];
    assert (&*[ a[1]^a[2] : a in triden1 ])*triden2[1] eq Abs(denx);

    newnum:=(&*[ a[1]^(a[2] mod 2) : a in trinum1 ])*trinum2[1];
    newden:=(&*[ a[1]^(a[2] mod 2) : a in triden1 ])*triden2[1];

    newx:=Sign(x)*newnum*newden;

    return newx;
  end if;
end intrinsic;



/*
intrinsic SquarefreeFactorization(phi::FldFunFracSchElt[Crv[FldRat]]) -> FldFunFracSchElt[CrvEll[FldRat]]
  {If phi(x) = f(x)/g(x) and f = c^2*f0, g = d^2*g0 with f0, g0 irreducible; return f0/g0.}
  
  KX<x>:=Parent(phi);
  phi_num:=KX!Numerator(phi);
  phi_den:=KX!Denominator(phi);

  Rz<z>:=PolynomialRing(Rationals());
  phi_numz:=Rz!eval(ReplaceAll(Sprint(phi_num),"x","z"));
  phi_denz:=Rz!eval(ReplaceAll(Sprint(phi_den),"x","z"));

  fac_numz:=Factorization(phi_numz);
  fac_denz:=Factorization(phi_denz);

  fac_l1:=Factorization(LeadingCoefficient(phi_numz)) cat [ <1,1> ];
  fac_l2:=Factorization(LeadingCoefficient(phi_denz)) cat [ <1,1> ];

  newnumz:=(&*[ a[1]^(a[2] mod 2) : a in fac_l1 ])*(&*[ a[1]^(a[2] mod 2) : a in fac_numz ]);
  newdenz:=(&*[ a[1]^(a[2] mod 2) : a in fac_l2 ])*(&*[ a[1]^(a[2] mod 2) : a in fac_denz ]);

  c:=(&*[ a[1]^Integers()!((a[2]-(a[2] mod 2))/2) : a in fac_l1 ])*(&*[ a[1]^Integers()!((a[2]-(a[2] mod 2))/2) : a in fac_numz ]);
  d:=(&*[ a[1]^Integers()!((a[2]-(a[2] mod 2))/2) : a in fac_l2 ])*(&*[ a[1]^Integers()!((a[2]-(a[2] mod 2))/2) : a in fac_denz ]);

  phi_sqfree:=KX!((KX!Evaluate(newnumz,x))/(KX!Evaluate(newdenz,x)));
  //phi = (c/d)^2*(f/g);
  c:=KX!Evaluate(c,x);
  d:=KX!Evaluate(d,x);
  cdivd:=KX!(c/d);
  //assert Sprint(phi) eq Sprint(cdivd^2*phi_sqfree);

  return phi_sqfree, c/d;
end intrinsic;*/

intrinsic remove_whitespace(X::MonStgElt) -> MonStgElt
{ Strips spaces and carraige returns from string; much faster than StripWhiteSpace. }
    return Join(Split(Join(Split(X," "),""),"\n"),"");
end intrinsic;

intrinsic sprint(X::.) -> MonStgElt
{ Sprints object X with spaces and carraige returns stripped. }
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return remove_whitespace(Sprintf("%o",X));
end intrinsic;

intrinsic RealVector(v::ModTupFldElt) -> ModTupFldElt
  {Given the complex vector v = v1 + I*v2 of dimension g return it as a real vector 
   (v1  v2)^T of dimension 2g}

  vector:=Eltseq(v);
  real_part:= [ Real(a) : a in vector ];
  imaginary_part := [ Imaginary(a) : a in vector ];
  real_vector := real_part cat imaginary_part;

  prec:=Precision(BaseRing(Parent(v)));
  dim:=#vector;
  RRRR:= RealField(prec);
  return VectorSpace(RRRR,2*dim)!real_vector;
end intrinsic;


intrinsic RealVector(v::ModMatFldElt) -> ModMatFldElt
  {Given the complex vector v = v1 + I*v2 of dimension g return it as a real vector 
   (v1  v2)^T of dimension 2g}

  vector:=Eltseq(v);
  real_part:= [ Real(a) : a in vector ];
  imaginary_part := [ Imaginary(a) : a in vector ];
  real_vector := real_part cat imaginary_part;

  prec:=Precision(BaseRing(Parent(v)));
  dim:=#vector;
  RRRR:= RealField(prec);
  return Matrix(RRRR,2*dim,1,[ [a] : a in real_vector]);
end intrinsic;



intrinsic BasisOfBigPeriodMatrix(PM::ModMatFldElt) -> SeqEnum 
  {Given a period matrix PM which is an element of M_gx2g, return the columns of PM}

  columns:= [ A : A in Rows(Transpose(PM)) ];
  matrices := [ Transpose(Matrix(BaseRing(PM),1,2, Eltseq(c))) : c in columns ];
  return matrices;
end intrinsic;



intrinsic BasisOfBigPeriodMatrixReal(PM::ModMatFldElt) -> SeqEnum 
  {Given a period matrix PM which is an element of M_gx2g, return the columns of PM}

  columns:= [ A : A in Rows(Transpose(PM)) ];
  matrices := [ Transpose(Matrix(BaseRing(PM),1,2, Eltseq(c))) : c in columns ];
  matrices_real:= [ RealVector(v) : v in matrices ];
  return matrices_real;
end intrinsic;



intrinsic BasisOfSmallPeriodMatrix(PM::AlgMatElt) -> SeqEnum 
  {Given a period matrix PM which is an element of M_gx2g, return the columns of PM}

  columns:= [ A : A in Rows(Transpose(PM)) ];
  matrices := [ Transpose(Matrix(BaseRing(PM),1,2, Eltseq(c))) : c in columns ] cat 
  [ Matrix(BaseRing(PM),2,1,[[1],[0]]), Matrix(BaseRing(PM),2,1,[[0],[1]]) ] ;
  return matrices;
end intrinsic;




intrinsic RealLatticeOfPeriodMatrix(PM::ModMatFldElt) -> Lat 
  {Given a period matrix PM which is an element of M_gx2g, create the real lattice 
  whose basis is the columns of PM after a real embedding.}
  assert NumberOfRows(Transpose(PM)) eq  2*NumberOfRows(PM);

  Lambda_basisCC:=Rows(Transpose(PM));
  real_basis:= [ RealVector(v) : v in Lambda_basisCC ];

  real_basis_matrix:=Matrix(BaseRing(real_basis[1]),[ Eltseq(a) : a in real_basis]);
  Lambda:=LatticeWithBasis(real_basis_matrix);

  return Lambda;
end intrinsic;



 

intrinsic MapIsHomomorphism(AutmuO::. : injective:=true) -> BoolElt
  {Check whether the map AutmuO : C -> B^x/Q^x is an injective homomorphism}
  for x,y in Domain(AutmuO) do 
    if not(AutmuO(x*y) eq AutmuO(x)*AutmuO(y)) then 
      return false;
    end if;
    if injective eq true then 
      if ((AutmuO(x) eq AutmuO(y)) and (x ne y)) then 
        return false;
      end if;
    end if;
  end for;
  return true;
end intrinsic 


intrinsic FixedSubspace(H::GrpMat) -> GrpAb
{}
  N := #BaseRing(H);
  M4R := MatrixAlgebra(Integers(N), 4);
  Hgens := [H.i : i in [1..NumberOfGenerators(H)]];
  A := AbelianGroup([N,N,N,N]);
  if #Hgens eq 0 then
    return A;
  end if;
  V := &meet[Kernel(M4R!h-1) : h in Hgens];
  // Need to convert to abelian group
  return sub<A | [Eltseq(v) : v in Generators(V)]>;
end intrinsic;
