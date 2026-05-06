
/*
L<y>:=PolynomialRing(Rationals());
L<x>:=L;
Lq:=FieldOfFractions(L);
Kext:=Rationals();
*/


//////////////////////////
//j_2=-16/27, j_4:=0, j_6=oo

intrinsic LFT02_14_oo6(F::FldFunFracSchElt) -> FldFunFracSchElt
  {0,1,oo --> j_2, j_4,j_6}
  return (-F+1)/(-27/16);
end intrinsic;

intrinsic LFT04_12_oo6(F::FldFunFracSchElt) -> FldFunFracSchElt
  {0,1,oo --> j_4, j_2, j_6}
  return (-F)/(27/16);
end intrinsic;

intrinsic LFT06_12_oo4(F::FldFunFracSchElt) -> FldFunFracSchElt
  {0,1,oo --> j_6, j_2, j_4}
  return (-16/27)*(1/F);
end intrinsic;

intrinsic LFT06_14_oo2(F::FldFunFracSchElt) -> FldFunFracSchElt
  {0,1,oo --> j_6, j_4, j_2}
  return (F-1)/(-27/16*F);
end intrinsic;

intrinsic LFT04_16_oo2(F::FldFunFracSchElt) -> FldFunFracSchElt
  {0,1,oo --> j_4, j_6, j_2}
  return (F)/(27/16*(-F+1));
end intrinsic;

intrinsic LFT02_16_oo4(F::FldFunFracSchElt) -> FldFunFracSchElt
  {0,1,oo --> j_2, j_6, j_4}
  return 1/(27/16*(F-1));
end intrinsic;


intrinsic LFT(F::FldFunFracSchElt,A::SeqEnum) -> FldFunFracSchElt
  {return the S3 action on phi determined by the sequence}
  if A eq [1,2,3] then
    return LFT02_14_oo6(F);
  elif A eq [1,3,2] then
    return LFT02_16_oo4(F);
  elif A eq [2,1,3] then
    return LFT04_12_oo6(F);
  elif A eq [2,3,1] then
    return LFT04_16_oo2(F);
  elif A eq [3,1,2] then
    return LFT06_12_oo4(F);
  elif A eq [3,2,1] then
    return LFT06_14_oo2(F);
  end if;
end intrinsic;
