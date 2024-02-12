
/*
label, text, label of the order D.d-?
i_square, integer, i^2
j_square, integer, j^2
discO, integer, (reduced) discriminant (O)
discB, integer, discriminant(B)
gens_numerators, integer[], a list L of lists such that L[j] are the coefficients of 1,i,j,k of the numerator of an element of B.
gens_denominators, integer[], a list of denominators, so that gensOnumerators[j] / gensOdenominators[j] is a generator of O for all j.
*/

intrinsic LMFDBLabel(O::AlgQuatOrd) -> MonStgElt
  {Given a quaternion order O, generate its LMFDB label}
  
  if IsMaximal(O) then 
    B := QuaternionAlgebra(O);
    D := Discriminant(B);
    return Sprintf("%o",D);
  else 
    print "Only works for O maximal at the moment";
  end if;
  
end intrinsic;


intrinsic LMFDBRowEntry(O::AlgQuatOrd) -> MonStgElt
  {return the row of data associated to O which will become part of the LMFDB schema.
  The schema is (for O maximal):
  LMFDBLabel(O) ? a ? b ? disc(O) ? disc(B) ? coefficients of Basis(O) in terms of i,j,k scaled to be integral ? 1/b where b multiplied by the corresponding element in the previous column is the basis element}

  if not(IsMaximal(O)) then 
    return "Only works for O maximal at the moment";
  end if;

  B:=QuaternionAlgebra(O);
  D:=Discriminant(B);
  d:= Discriminant(O);
  gensO:=Generators(O);
  gensOijk:=[ Eltseq(elt) : elt in gensO ];

  denominatorsLCM:=[ LCM([Denominator(a) : a in seq]) : seq in gensOijk ];
  denominatorsLCM_str:=Sprint(denominatorsLCM);
  denominatorsLCM_str := ReplaceString(denominatorsLCM_str,"[","{");
  denominatorsLCM_str := ReplaceString(denominatorsLCM_str,"]","}");

  gensOijk_integral:=[ [ (denominatorsLCM[i])*gensOijk[i][j] : j in [1..4] ] : i in [1..4] ];
  gensOijk_integral_str := [ Sprintf("%o",lst) : lst in gensOijk_integral ];
  gensOijk_integral_str := Sprint(gensOijk_integral_str);
  gensOijk_integral_str := ReplaceString(gensOijk_integral_str,"[","{");
  gensOijk_integral_str := ReplaceString(gensOijk_integral_str,"]","}");
  

  label:=LMFDBLabel(O);
  a,b:=StandardForm(B);

  return Sprintf("%o?%o?%o?%o?%o?%o?%o",label,a,b,D,d,gensOijk_integral_str,denominatorsLCM_str);
end intrinsic;



intrinsic EnumerateO(bound::RngIntElt : verbose:=true,write:=false) -> Any
  {loop over maximal orders of discriminant up to bound and output their lmfdb row entry}
  
  if write eq true then 
    filename:=Sprintf("ShimCurve/data/quaternion-orders/quaternion-orders.m");
    fprintf filename, "label ? i_square ? j_square ? discO ? discB ? gens_numerators ? gens_denominators\n";
    fprintf filename, "text ? integer ? integer ? integer ? integer ? integer[] ? integer[]\n";
    fprintf filename, "\n";
  end if;

  for D in [6..bound] do 
    if IsSquarefree(D) and IsEven(#PrimeDivisors(D)) then 
      B:=QuaternionAlgebra(D);
      O:=MaximalOrder(B);
      row:=LMFDBRowEntry(O);
      if verbose eq true then 
        row;
      end if;
      if write eq true then 
        filename:=Sprintf("ShimCurve/data/quaternion-orders/quaternion-orders.m");
        fprintf filename, "%o\n",row;   
      end if;
    end if;
  end for;
  return "";
end intrinsic;




intrinsic LMFDBLabel(O::AlgQuatOrd,mu::AlgQuatElt) -> MonStgElt
  {Given a quaternion order O, generate its LMFDB label}
  
  
  if IsMaximal(O) then 
    B := QuaternionAlgebra(O);
    D := Discriminant(B);
    del:=DegreeOfPolarizedElement(O,mu);
    return Sprintf("%o.%o",D,del);
  else 
    print "Only works for O maximal at the moment";
  end if;
  
end intrinsic;




/*
label, label of (O,mu)
order_label, text, label of the order D.d-?
mu, integer[], coefficients of the basis of O that describe mu
deg_mu, integer, the degree of the associated polarization
nrd_mu, integer, the reduced norm of mu
Glabel, text, label of Aut_mu(O) as an abstract group
is_cyclic, boolean, whether Aut_mu(O) is cyclic or not
generators, integer[], list of lists (of length 1 or 2) representing the elements of O generating Aut_mu(O) (coefficients in O)
*/



intrinsic LMFDBRowEntry(O::AlgQuatOrd, mu::AlgQuatElt) -> MonStgElt
  {the row of data that makes up the LMFDB table associated to (O,mu)}
  B:=QuaternionAlgebra(O);
  D:=Discriminant(B);
  d:= Discriminant(O);

  label:=LMFDBLabel(O,mu);
  labelO:=LMFDBLabel(O);

  muO:=Eltseq(O!mu);
  muO_str:=Sprint(muO);
  muO_str:=ReplaceString(muO_str,"[","{");
  muO_str:=ReplaceString(muO_str,"]","}"); 

  deg_mu := DegreeOfPolarizedElement(O,mu);
  nrd_mu := SquarefreeFactorization(Norm(mu));

  AutmuO := Aut(O,mu);
  AutmuO_label := GroupName(Domain(AutmuO));

  is_cyclic := IsCyclic(Domain(AutmuO)) select "t" else "f";
  if IsCyclic(Domain(AutmuO)) then
    AutmuO_generators := Sprint([ O!(AutmuO(Domain(AutmuO).1)`element) ]);
  else 
    AutmuO_generators := Sprint([ O!(AutmuO(Domain(AutmuO).i)`element) : i in [1,2] ]);
  end if;

  AutmuO_generators_str := ReplaceString(AutmuO_generators,"[","{");
  AutmuO_generators_str := ReplaceString(AutmuO_generators_str,"]","}");

  K,Kgen:=SemidirectToNormalizerKernel(O,mu);
  Kgen := [ O!((Kgen`element)[1]`element), O!(Kgen`element[2]) ];
  Kgen_str:=ReplaceString(Sprint(Kgen),"[","{");
  Kgen_str:=ReplaceString(Kgen_str,"]","}");


  return Sprintf("%o?%o?%o?%o?%o?%o?%o?%o?%o?%o",label,labelO,muO_str,deg_mu,nrd_mu,#Domain(AutmuO),AutmuO_label,is_cyclic,AutmuO_generators_str,Kgen_str);
end intrinsic;


  

intrinsic EnumerateOmu(boundO::RngIntElt: verbose:=true,write:=false) -> Any
  {loop over polarized maximal orders (O,mu) of discriminant up to boundO 
  and polarization up to boundmu and output their lmfdb row entry}
  
  if write eq true then 
    filename:=Sprintf("ShimCurve/data/quaternion-orders/quaternion-orders-polarized.m");
    fprintf filename, "label ? order_label ? mu ? deg_mu ? nrd_mu ? AutmuO_size ? AutmuO_label ? AutmuO_is_cyclic ? AutmuO_generators ? Gerby_gen \n";
    fprintf filename, "text ? text ? integer[] ? integer ? integer ? integer ? text ? boolean ? integer[] ? integer[]\n";
    fprintf filename, "\n";
  end if;

  for D in [6..boundO] do
    if IsSquarefree(D) and IsEven(#PrimeDivisors(D)) then
      for deg in Divisors(D) do
        B:=QuaternionAlgebra(D);
        O:=MaximalOrder(B); 
        if HasPolarizedElementOfDegree(O,deg) then 
          tr,mu := HasPolarizedElementOfDegree(O,deg);
          row:=LMFDBRowEntry(O,mu);
          if verbose eq true then 
            printf "%o\n",row;
          end if;
          if write eq true then 
            filename:=Sprintf("ShimCurve/data/quaternion-orders/quaternion-orders-polarized.m");
            fprintf filename, "%o\n",row;   
          end if;
        end if;
      end for;
    end if;
  end for;

  return "";
end intrinsic;





