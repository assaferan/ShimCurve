
intrinsic Norm(g::AlgQuatEnhElt) -> RngIntElt
  {Returns the norm of the AlgQuatEnhElt g}
  return Norm((g`element)[1]`element);
end intrinsic;

//Prints the data to algdat.dat, where you are given the order O and the subgroup H.
intrinsic PrepPictureDataH(O::AlgQuatOrd, Henhgens :: Tup) -> RngIntElt
  {Saves the data to the data to a file, to be read by PARI/GP to compute the fundamental domain}
  SetOutputFile("ShimCurve/pictures/algdat.dat" : Overwrite := true);
  B := Algebra(O);//Retrieve the algebra
  a, b := StandardForm(B);//Find a, b where B=[a, b / Q]
  printf "[%o, %o]\n", a, b;
  M := BasisMatrix(O);
  printf "[";
  for i := 1 to 4 do
    R := M[i];
    printf "[%o, %o, %o, %o]", R[1], R[2], R[3], R[4];
    if i lt 4 then
      printf ", ";
    else
      print "]";
    end if;
  end for;
  nms := Set([ Abs(SquarefreeFactorization(Integers()!Norm(w))) : w in Henhgens ]);
  nms := [x : x in nms];
  printf "[";
  for i := 1 to #nms do
    printf "%o", nms[i];
    if i lt #nms then
      printf ", ";
    else
      print "]";
    end if;
  end for;
  UnsetOutputFile();
  return 1;
end intrinsic;

//Does PrepPictureDataH for the full group H, i.e. the largest Atkin-Lehner quotient that we will consider.
intrinsic PrepPictureDataMaximalH(O::AlgQuatOrd, mu::AlgQuatElt) -> RngIntElt
  {Saves the data to the data to a file, to be read by PARI/GP to compute the fundamental domain, for the maximal group H.}
  AutmuO := Aut(O, mu);
  G, Gelts := EnhancedImageGL4(AutmuO, O, 1);
  Genh := [ g`enhanced : g in Gelts];
  GGL4gens := Generators(G);
  Genhgens := < g`enhanced : g in Gelts | g`GL4 in GGL4gens >;
  return PrepPictureDataH(O, Genhgens);
end intrinsic;





