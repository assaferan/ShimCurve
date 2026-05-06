
intrinsic PQMIgusaClebschDisc6(j::FldRatElt : LinYang:=true) -> SeqEnum
  {Given j from Baba-Granaths discriminant 6 family,
  create the Igusa-Clebsch invariants of the curve associated to j.}

  // The Igusa invariants from Baba-Granath for D=6
  if LinYang eq false then
    J2:=12*(j+1);
    J4:=6*(j^2+j+1);
    J6:=4*(j^3-2*j^2+1);
    J8:=(J2*J6-J4^2)/4;
    J10:=j^3;
    BG6Igusa:=[J2,J4,J6,J8,J10];

    //The Igusa-Clebsch invariants are
    I2:=8*J2;
    I4:=-96*J4+4*J2^2;
    I6:=-(576*J6-8*J2^3+160*J2*J4);
    I10:=4096*J10;
    IgusaClebsch:=[I2,I4,I6,I10];

  else
    s2:=j;
    s3:=j^2;
    s5:=j^3;
    s6:=j^3*(j+1);

    psi4:=s2;
    psi6:=s3;
    chi10:=s5/(2^12*3^5);
    chi12:=s6/(2^12*3^6);

    J2:=-3*chi12/chi10;
    J4:=1/24*(J2^2-psi4);
    J6:=1/216*(-J2^3+36*J2*J4+psi6);
    J8:=(J2*J6-J4^2)/4;
    J10:=-4*chi10;

    I2:=8*J2;
    I4:=-96*J4+4*J2^2;
    I6:=-(576*J6-8*J2^3+160*J2*J4);
    I10:=4096*J10;
    IgusaClebsch:=[I2,I4,I6,I10];
  end if;

  return IgusaClebsch;
end intrinsic;


intrinsic PQMIgusaClebschDisc10(j::FldRatElt) -> SeqEnum
  {Given j from Baba-Granath's discriminant 10 family,
  create the Igusa-Clebsch invariants of the curve associated to j.}
  J2:=12*j^2-16*j+12;
  J4:=6*j^4-16*j^3+6*j^2-16*j+6;
  J6:=4*j^6-16*j^5+32*j^3-8*j^2-16*j+4;
  J8:=(J2*J6-J4^2)/4;
  J10:=j^4;
  BGIgusa:=[J2,J4,J6,J8,J10];

  //The Igusa-Clebsch invariants are
  I2:=8*J2;
  I4:=-96*J4+4*J2^2;
  I6:=-(576*J6-8*J2^3+160*J2*J4);
  I10:=4096*J10;
  BGIC:=[I2,I4,I6,I10];

  return BGIC;
end intrinsic;



intrinsic PQMIgusaClebschDisc15(j::FldRatElt : LinYang:=true) -> SeqEnum
  {Given j from Baba-Granaths discriminant 15 family,
  create the Igusa-Clebsch invariants of the curve associated to j.}

  //The Igusa-Clebsch invariants are

  // From X(15,1)/<w_15>
  /*I2:=12*(j^4+15*j^3+105*j^2+125*j+10);
  I4:=45*(4*j+1)*(j+3)^2*(j-1)^4;
  I6:=9*(84*j^5+1414*j^4+8865*j^3+11157*j^2+3895*j+185)*(j+3)^2*(j-1)^4;
  I10:=2*(j+3)^6*(j-1)^12;
  BGIC:=[I2,I4,I6,I10];*/


  /*s2:=5^2;  //First in Lin-Yang
  s3:=4*j^2+64*j+121;
  s5:=2^6*(j-1)^2*j;
  s6:=2^4*(j^4+72*j^3+174*j^2+8*j+1);*/

  s2:=5*(4*j+1);  //Second in Lin-Yang
  s3:=4*j^2+190*j-5;
  s5:=2^4*(j-1)^2*(j+3);
  s6:=2^4*(j^4+15*j^3+105*j^2+125*j+10);

  psi4:=s2;
  psi6:=s3;
  chi10:=s5/(2^12*3^5);
  chi12:=s6/(2^12*3^6);

  J2:=-3*chi12/chi10;
  J4:=1/24*(J2^2-psi4);
  J6:=1/216*(-J2^3+36*J2*J4+psi6);
  J8:=(J2*J6-J4^2)/4;
  J10:=-4*chi10;

  I2:=8*J2;
  I4:=-96*J4+4*J2^2;
  I6:=-(576*J6-8*J2^3+160*J2*J4);
  I10:=4096*J10;
  IgusaClebsch:=[I2,I4,I6,I10];

  //JVs family from Budapest
  /*I2:=  -24*(j^4-15*j^3+105*j^2-125*j+10)/((j-3)*(j+1)^2);
  I4:=  180*(1-4*j);
  I6:=  72*(84*j^5-1414*j^4+8865*j^3-11157*j^2+3895*j-185) / ((j-3)*(j+1)^2);
  I10:=  -64 * (j-3) * (j+1)^2;*/

  IgusaClebsch:=[I2,I4,I6,I10];

  return IgusaClebsch;
end intrinsic;




intrinsic PQMIgusaClebschDisc26(j::FldRatElt : LinYang:=true) -> SeqEnum
  {Given j from Baba-Granath's discriminant 26 family,
  create the Igusa-Clebsch invariants of the curve associated to j.}


  s2:=25*j^2 - 306*j +1305;
  s3:=2*(29*j^3+27*j^2-5913*j+23085);
  s5:=2^2*3^5*(j-1)^2*(j+3)^2;
  s6:=3^5*(3*j^6-2*j^5+13*j^4-92*j^3+2733*j^2+7038*j+2595);

  psi4:=s2;
  psi6:=s3;
  chi10:=s5/(2^12*3^5);
  chi12:=s6/(2^12*3^6);

  J2:=-3*chi12/chi10;
  J4:=1/24*(J2^2-psi4);
  J6:=1/216*(-J2^3+36*J2*J4+psi6);
  J8:=(J2*J6-J4^2)/4;
  J10:=-4*chi10;

  I2:=8*J2;
  I4:=-96*J4+4*J2^2;
  I6:=-(576*J6-8*J2^3+160*J2*J4);
  I10:=4096*J10;
  IgusaClebsch:=[I2,I4,I6,I10];

  return IgusaClebsch;
end intrinsic;


intrinsic PQMIgusaClebschDisc38(j::FldRatElt : LinYang:=true) -> SeqEnum
  {Given j from Lin-Yang's discriminant 38 family,
  create the Igusa-Clebsch invariants of the curve associated to j.}


  s2:=9*j^6 - 60*j^5 + 346*j^4 - 240*j^3 + 153*j^2 - 180*j + 36;
  s3:=675*j^8-2016*j^7+2600*j^6-8064*j^5+11610*j^4-6048*j^3+3240*j^2 +243;
  s5:=3^5*(j + 1)^2*( j^2 + 1)^2*( j^2 + 3)^2*( j^2 + j + 2)^2;
  s6:=3^5*(3*j^18 + 12*j^17 + 61*j^16 + 160*j^15 + 525*j^14 + 1068*j^13 + 2612*j^12 +
  4032*j^11 + 7533*j^10 + 8548*j^9 + 12532*j^8 + 9984*j^7 + 11971*j^6 +
  6180*j^5 + 6792*j^4 + 2208*j^3 + 2592*j^2 + 576*j + 435);

  psi4:=s2;
  psi6:=s3;
  chi10:=s5/(2^12*3^5);
  chi12:=s6/(2^12*3^6);

  J2:=-3*chi12/chi10;
  J4:=1/24*(J2^2-psi4);
  J6:=1/216*(-J2^3+36*J2*J4+psi6);
  J8:=(J2*J6-J4^2)/4;
  J10:=-4*chi10;

  I2:=8*J2;
  I4:=-96*J4+4*J2^2;
  I6:=-(576*J6-8*J2^3+160*J2*J4);
  I10:=4096*J10;
  IgusaClebsch:=[I2,I4,I6,I10];
  return IgusaClebsch;
end intrinsic;



intrinsic PQMIgusaClebsch(D::RngIntElt, j::FldRatElt : LinYang:=true) -> SeqEnum
  {Given a discriminant D and rational j, create the associated Igusa Clebsch
  of a PQM surface}

  if D eq 6 then
    return PQMIgusaClebschDisc6(j : LinYang:=LinYang);
  elif D eq 10 then
    return PQMIgusaClebschDisc10(j);
  elif D eq 15 then
    return PQMIgusaClebschDisc15(j : LinYang:=LinYang);
  elif D eq 26 then
    return PQMIgusaClebschDisc26(j : LinYang:=LinYang);
  elif D eq 38 then
    return PQMIgusaClebschDisc38(j : LinYang:=LinYang);
  end if;

end intrinsic;


intrinsic MestreObstructionIsSplit(D::RngIntElt, j::FldRatElt : LinYang:=true) -> BoolElt
  {Mestre obstruction}

  if D eq 6 then 
    assert LinYang eq false;
    a:=TrialRepresentativeModuloSquares(-6*j);
    b:=TrialRepresentativeModuloSquares(-2*(27*j+16));
    if a*b ne 0 then 
      H:=QuaternionAlgebra<Rationals() | a , b >;
      //return Discriminant(H) eq 1;
      return IsMatrixRing(H);
    else 
      return false;
    end if;    
  elif D eq 15 then
    a:=-15*j;
    b:=-3*(j+3)*(27*j+1);
    if a*b ne 0 then 
      H:=QuaternionAlgebra<Rationals() | a , b >;
      return Discriminant(H) eq 1;
    else 
      return false;
    end if;
  elif D eq 26 then
    H:=QuaternionAlgebra<Rationals() | -26*j, -13*(2*j^3-19*j^2+24*j+169) >;
    return Discriminant(H) eq 1;
  elif D eq 38 then
    H:=QuaternionAlgebra<Rationals() | -38*j, -2*(16*j^3+59*j^2+82*j+19) >;
    return Discriminant(H) eq 1;
  end if;

end intrinsic;


intrinsic SplitMestreObstructionSearch(D::RngIntElt : bound:=100 ) -> SeqEnum
  {}
  P<j,X,Y>:=PolynomialRing(Rationals(),3);
  if D eq 26 then
    a:=-26*j;
    b:=-13*(2*j^3-19*j^2+24*j+169);
  elif D eq 38 then
    a:=-38*j;
    b:=-2*(16*j^3+59*j^2+82*j+19);
  end if;

  A3:=AffineSpace(Rationals(),3);
  H:=a*X^2+b*Y^2-1;
  C:=Scheme(A3,H);

  pts:=PointSearch(C, bound : Dimension:=2);
  js:= Setseq(Set([ Eltseq(A)[1] : A in pts ]));
  return ChangeUniverse(js,Rationals());

end intrinsic;
