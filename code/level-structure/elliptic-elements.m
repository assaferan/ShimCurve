
intrinsic NormalizerPlusGenerators(O::AlgQuatOrd) -> SeqEnum
  {return generators of the positive norm elements which normalize O}
  if Discriminant(O) eq 6 then 
    B6<i6,j6>:=QuaternionAlgebra<Rationals() | -1,3 >;
    B:=QuaternionAlgebra(O);
    tr,map:=IsIsomorphic(B6,B : Isomorphism:=true);
    assert tr;
    B6elliptic_elts:=[3*i6 + i6*j6, 1+i6, 3+3*i6+j6+i6*j6];
    Oelliptic_elts:=[ O!map(a) : a in B6elliptic_elts ];
    assert Set([ Norm(a) : a in Oelliptic_elts ]) eq {2,6,12};

    e2,e4,e6:=Explode(Oelliptic_elts);
    assert IsScalar(e6^6); assert IsScalar(e4^4); assert IsScalar(e2^2);
    assert IsScalar(&*Oelliptic_elts);
    return Oelliptic_elts;
  elif Discriminant(O) eq 10 then 
    //Elkies 
    B10<b,e>:=QuaternionAlgebra<Rationals() | -2,5 >;
    s2:=b;
    s2p:=2*e+5*b-b*e;
    s2pp:=5*b-b*e;
    s3:=2*b-e-1;

    B:=QuaternionAlgebra(O);
    tr,map:=IsIsomorphic(B10,B : Isomorphism:=true);
    assert tr;
    B10elliptic_elts:=[ s2,s2p,s2pp,s3];
    assert IsScalar(&*B10elliptic_elts);
    assert IsScalar(s2^2); assert IsScalar(s2p^2); assert IsScalar(s2pp^2); assert IsScalar(s3^3);
    Oelliptic_elts:=[ O!map(a) : a in B10elliptic_elts ];
    //assert Set([ Norm(a) : a in Oelliptic_elts ]) eq {2,6,12};
    return Oelliptic_elts;
  elif Discriminant(O) eq 15 then 
    B15<c,e>:=QuaternionAlgebra<Rationals() | -3,5 >;
    s2:=4*c-3*e;
    s2p:=5*c-3*e-c*e;
    s2pp:=20*c-9*e-7*c*e;
    s6:=3+c;

    B:=QuaternionAlgebra(O);
    tr,map:=IsIsomorphic(B15,B : Isomorphism:=true);
    assert tr;
    B15elliptic_elts:=[ s2,s2p,s2pp,s6 ];
    assert IsScalar(&*B15elliptic_elts);
    assert IsScalar(s2^2); assert IsScalar(s2p^2); assert IsScalar(s2pp^2); assert IsScalar(s6^6);

    Oelliptic_elts:=[ O!map(a) : a in B15elliptic_elts ];
    //assert Set([ Norm(a) : a in Oelliptic_elts ]) eq {2,6,12};
    return Oelliptic_elts;

  else
    return "oops, not written for this discriminant yet";
  end if;
end intrinsic;


intrinsic NormalizerToAutmuO(Enh::AlgQuatEnh, a::AlgQuatElt) -> AlgQuatEnhElt
  {Lift an element a of the Normalizer of O to the enhanced semidirect product, which is well defined up to 
  the kernel of this map (given by NormalizerKernel(Enh))}
  O := Enh`quaternionorder;
  mu := Enh`mu;
  ker := NormalizerKernel(Enh);

  B:=QuaternionAlgebra(O);
  BxmodQx:=QuaternionAlgebraModuloScalars(B);
  proja:=BxmodQx!(B!a);
  orda:=Order(proja);

  //[ elt : elt in Bxelts(Enh) | elt in ker ];

  assert a^2/Norm(a) in O;
  assert Norm(a) gt 0;
  //W:=[];
  for w in Bxelts(Enh) do
    if IsSquare(Rationals()!Abs(Norm((w`element)^-1*a))) then
      tr,c:=IsSquare(Rationals()!Abs(Norm((w`element)^-1*a)));
      x:=(1/c)*((w`element)^-1)*a;
      assert x in O;
      assert Norm(x) in {1,-1};
      ell := Enh!<w,O!x>;
      if Min([ i : i in [1..orda] | ell^i in ker]) eq orda then
        //Append(~W,ell);
        return ell;
      end if;
    end if;
  end for;
  //return W[1];
end intrinsic;

intrinsic NormalizerPlusGenerators(Enh::AlgQuatEnh) -> SeqEnum
{return generators of the positive norm elements which normalize O in the enhanced semidirect product}
    if not assigned Enh`NormalizerPlusGenerators then
        t0 := Cputime();
        O := Enh`quaternionorder;
        B := Enh`quaternionalgebra;
        Nplus := NormalizerPlusGenerators(O);
        gens := [ Enh!NormalizerToAutmuO(Enh, B!a) : a in Nplus ];
        vprint User1: "NBOplusgens_enhanced", Cputime() - t0;
        Enh`NormalizerPlusGenerators := gens;
    end if;
    return Enh`NormalizerPlusGenerators;
end intrinsic;
