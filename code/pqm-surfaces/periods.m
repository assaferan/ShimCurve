
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


