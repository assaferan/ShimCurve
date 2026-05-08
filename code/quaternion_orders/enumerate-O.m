
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
  B := QuaternionAlgebra(O);
  D := Discriminant(B);
  if IsMaximal(O) then
    return Sprintf("%o", D);
  else
    return Sprintf("%o.%o", D, Discriminant(O));
  end if;
end intrinsic;

intrinsic DedekindPsi(N::RngIntElt) -> RngIntElt
  {Dedekind psi function: N * prod_(p | N) (1 + 1/p)}
  result := 1;
  for fac in Factorization(N) do
    p := fac[1]; e := fac[2];
    result *:= p^(e-1) * (p+1);
  end for;
  return result;
end intrinsic;


intrinsic Area(O::AlgQuatOrd) -> FldRatElt
  {Compute the Area of X_O}
  //assert IsMaximal(O);
  discO := Discriminant(O);

  D:=Discriminant(QuaternionAlgebra(O));
  M := Integers()!(discO/D);
  //area:=EulerPhi(D)/6;
  area := (EulerPhi(D)*DedekindPsi(M))/12; // stores area/4pi
  return area;
end intrinsic;


intrinsic LMFDBRowEntry(O::AlgQuatOrd) -> MonStgElt
  {return the row of data associated to O which will become part of the LMFDB schema.
  The schema is (for O maximal):
  LMFDBLabel(O) ? a ? b ? disc(O) ? disc(B) ? coefficients of Basis(O) in terms of i,j,k scaled to be integral ? 1/b where b multiplied by the corresponding element in the previous column is the basis element}

  //if not(IsMaximal(O)) then 
  //  return "Only works for O maximal at the moment";
  //end if;

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

  areaO := Area(O);
  area_numerator:=Numerator(areaO);
  area_denominator := Denominator(areaO);
  
  label:=LMFDBLabel(O);
  a,b:=StandardForm(B);

  return Sprintf("%o?%o?%o?%o?%o?%o?%o?%o?%o",label,a,b,D,d,gensOijk_integral_str,denominatorsLCM_str,area_numerator,area_denominator);
end intrinsic;

intrinsic LMFDBRowEntryTxt(O::AlgQuatOrd) -> MonStgElt
  {return the row of data associated to O which will become part of the LMFDB schema.
  The schema is (for O maximal):
  LMFDBLabel(O) ? a ? b ? disc(O) ? disc(B) ? coefficients of Basis(O) in terms of i,j,k scaled to be integral ? 1/b where b multiplied by the corresponding element in the previous column is the basis element}

  //if not(IsMaximal(O)) then
  //  return "Only works for O maximal at the moment";
  //end if;

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

  areaO := Area(O);
  area_numerator:=Numerator(areaO);
  area_denominator := Denominator(areaO);
  
  label:=LMFDBLabel(O);
  a,b:=StandardForm(B);

  return Sprintf("%o|%o|%o|%o|%o|%o|%o|%o|%o",label,a,b,D,d,gensOijk_integral_str,denominatorsLCM_str,area_numerator,area_denominator);
end intrinsic;



intrinsic EnumerateO(bound::RngIntElt : verbose:=true,write:=false) -> Any
  {loop over Eichler orders of reduced discriminant up to bound and output their lmfdb row entry}
  
  if write eq true then 
    filename:=Sprintf("ShimCurve/data/quaternion-orders/quaternion-orders.m");
    fprintf filename, "label ? i_square ? j_square ? discO ? discB ? gens_numerators ? gens_denominators\n";
    fprintf filename, "text ? integer ? integer ? integer ? integer ? integer[] ? integer[]\n";
    fprintf filename, "\n";
  end if;

  for D in [6..bound] do 
    for M in [1..Floor(bound/D)] do 
      if (Gcd(D, M) eq 1) and (D*M lt bound) and IsSquarefree(D) and IsEven(#PrimeDivisors(D)) then 
        B:=QuaternionAlgebra(D);
        O:= Order(MaximalOrder(B), M);
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
  end for;
  return "";
end intrinsic;

intrinsic EnumerateOTxt(bound::RngIntElt : verbose:=true,write:=false) -> Any
  {loop over Eichler orders of reduced discriminant up to bound and output their lmfdb row entry}

  if write eq true then
    filename:=Sprintf("./data/quaternion-orders/quaternion-orders.txt");
    fprintf filename, "label | i_square | j_square | discO | discB | gens_numerators | gens_denominators | area_numerator | area_denominator \n";
    fprintf filename, "text | integer | integer | integer | integer | integer[] | integer[] | integer | integer\n";
    fprintf filename, "\n";
  end if;

  for D in [6..bound] do
    for M in [1..Floor(bound/D)] do
      if (Gcd(D, M) eq 1) and (D*M lt bound) and IsSquarefree(D) and IsEven(#PrimeDivisors(D)) then
        B:=QuaternionAlgebra(D);
        O:= Order(MaximalOrder(B), M);
        row:=LMFDBRowEntryTxt(O);
        if verbose eq true then
          row;
        end if;
        if write eq true then
          filename:=Sprintf("./data/quaternion-orders/quaternion-orders.txt");
          fprintf filename, "%o\n",row;
        end if;
      end if;
    end for;
  end for;
  return "";
end intrinsic;

intrinsic EnumerateOTxt(bound::RngIntElt : verbose:=true,write:=false) -> Any
  {loop over maximal orders of discriminant up to bound and output their lmfdb row entry}
  
  if write eq true then 
    filename:=Sprintf("./data/quaternion-orders/quaternion-orders.txt");
    fprintf filename, "label | i_square | j_square | discO | discB | gens_numerators | gens_denominators | area_numerator | area_denominator \n";
    fprintf filename, "text | integer | integer | integer | integer | integer[] | integer[] | integer | integer\n";
    fprintf filename, "\n";
  end if;

  for D in [6..bound] do 
    if IsSquarefree(D) and IsEven(#PrimeDivisors(D)) then 
      B:=QuaternionAlgebra(D);
      O:=MaximalOrder(B);
      row:=LMFDBRowEntryTxt(O);
      if verbose eq true then 
        row;
      end if;
      if write eq true then 
        filename:=Sprintf("./data/quaternion-orders/quaternion-orders.txt");
        fprintf filename, "%o\n",row;   
      end if;
    end if;
  end for;
  return "";
end intrinsic;




intrinsic LMFDBLabel(O::AlgQuatOrd,mu::AlgQuatElt) -> MonStgElt
  {Given a quaternion order O, generate its LMFDB label}
  B := QuaternionAlgebra(O);
  D := Discriminant(B);
  del := DegreeOfPolarizedElement(O, mu);
  if IsMaximal(O) then
    return Sprintf("%o.%o", D, del);
  else
    return Sprintf("%o.%o.%o", D, Discriminant(O), del);
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
  assert mu in O;

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

  // gerbiness = 1 because f: Aut_{±mu}(O) --> N_{B^x}(O)/Q^x is injective
  // this is only correct when the degree of polarization is 1! 
  // TODO: handle this more generally
  Kgen := [Eltseq(O!1)];
  Kgen_str := [ Sprintf("%o",lst) : lst in Kgen ];
  Kgen_str := Sprint(Kgen_str);
  Kgen_str:=ReplaceString(Sprint(Kgen_str),"[","{");
  Kgen_str:=ReplaceString(Kgen_str,"]","}");

  is_cyclic := IsCyclic(Domain(AutmuO)) select "t" else "f";
  if IsCyclic(Domain(AutmuO)) then
    //AutmuO_generators := [ Eltseq(O!(AutmuO(Domain(AutmuO).1)`element)) ];
    AutmuO_generators := [ Eltseq(B!(AutmuO(Domain(AutmuO).1)`element)) ];
  else 
    //AutmuO_generators := [ Eltseq(O!(AutmuO(Domain(AutmuO).i)`element)) : i in [1,2] ];
    AutmuO_generators := [ Eltseq(B!(AutmuO(Domain(AutmuO).i)`element)) : i in [1,2] ];;
  end if;


  AutmuO_generators_str := [ Sprintf("%o",lst) : lst in AutmuO_generators ];
  AutmuO_generators_str := Sprint(AutmuO_generators_str);
  AutmuO_generators_str := ReplaceString(AutmuO_generators_str,"[","{");
  AutmuO_generators_str := ReplaceString(AutmuO_generators_str,"]","}");
  //AutmuO_generators_str := Sprintf("%o",AutmuO_generators);

  


  return Sprintf("%o|%o|%o|%o|%o|%o|%o|%o|%o|%o",label,labelO,muO_str,deg_mu,nrd_mu,#Domain(AutmuO),AutmuO_label,is_cyclic,AutmuO_generators_str,Kgen_str);
end intrinsic;


  

intrinsic EnumerateOmu(boundO::RngIntElt: verbose:=true,write:=false) -> Any
  {loop over polarized Eichler orders (O,mu) of discriminant up to boundO
  and output their lmfdb row entry}

  if write eq true then
    filename:=Sprintf("ShimCurve/data/quaternion-orders/quaternion-orders-polarized.m");
    fprintf filename, "label ? order_label ? mu ? deg_mu ? nrd_mu ? AutmuO_size ? AutmuO_label ? AutmuO_is_cyclic ? AutmuO_generators ? Gerby_gen \n";
    fprintf filename, "text ? text ? integer[] ? integer ? integer ? integer ? text ? boolean ? integer[] ? integer[]\n";
    fprintf filename, "\n";
  end if;

  for D in [6..boundO] do
    for M in [1..Floor(boundO/D)] do
      if (Gcd(D, M) eq 1) and (D*M lt boundO) and IsSquarefree(D) and IsEven(#PrimeDivisors(D)) then
        B:=QuaternionAlgebra(D);
        O:= Order(MaximalOrder(B), M);
        for deg in Divisors(D*M) do // want mu to be in N_(B^x)(O)
          tr,mu := HasPolarizedElementOfDegree(O,deg);
          if not tr then continue; end if;
          row:=LMFDBRowEntry(O,mu);
          if verbose eq true then
            printf "%o\n",row;
          end if;
          if write eq true then
            filename:=Sprintf("ShimCurve/data/quaternion-orders/quaternion-orders-polarized.m");
            fprintf filename, "%o\n",row;
          end if;
        end for;
      end if;
    end for;
  end for;

  return "";
end intrinsic;


intrinsic EnumerateOmuTxt(boundO::RngIntElt: verbose:=true,write:=false) -> Any
  {loop over polarized Eichler orders (O,mu) of discriminant up to boundO
  and output their lmfdb row entry}

  filename_eichler := "./data/quaternion-orders/quaternion-Eichler-orders-polarized.txt";
  filename_maximal := "./data/quaternion-orders/quaternion-maximal-orders-polarized.txt";

  // Build set of already-computed labels from both files so we can resume.
  // Maximal orders (M=1) use "D.del"; Eichler orders (M>=2) use "D.DM.del".
  done_labels := {};
  if write then
    for fname in [filename_maximal, filename_eichler] do
      file_exists := false;
      try
        f := Open(fname, "r"); delete f;
        file_exists := true;
      catch e
        file_exists := false;
      end try;
      if file_exists then
        f := Open(fname, "r");
        line := Gets(f);
        while not IsEof(line) do
          parts := Split(line, "|");
          if #parts ge 2 and #parts[1] gt 0 and parts[1][1] ge "0" and parts[1][1] le "9" then
            Include(~done_labels, parts[1]);
          end if;
          line := Gets(f);
        end while;
        delete f;
      elif fname eq filename_eichler then
        f := Open(fname, "w"); delete f;
        fprintf fname, "label | order_label | mu | deg_mu | nrd_mu | AutmuO_size | AutmuO_label | AutmuO_is_cyclic | AutmuO_generators | Gerby_gen \n";
        fprintf fname, "text | text | integer[] | integer | integer | integer | text | boolean | integer[] | integer[]\n";
        fprintf fname, "\n";
      end if;
    end for;
  end if;

  // Preload order basis data from quaternion-orders.txt (keyed by label "D.DM") so that
  // Eichler orders (M>1) are reconstructed from the stored basis rather than recomputed.
  ord_data := AssociativeArray();
  try
    f := Open("./data/quaternion-orders/quaternion-orders.txt", "r"); delete f;
    f := Open("./data/quaternion-orders/quaternion-orders.txt", "r");
    _ := Gets(f); _ := Gets(f); _ := Gets(f); // header, types, blank
    line := Gets(f);
    while not IsEof(line) do
      if #line gt 0 then
        fields := Split(line, "|");
        if #fields ge 7 and #fields[1] gt 0 and fields[1][1] ge "0" and fields[1][1] le "9" then
          ord_data[fields[1]] := <fields[2], fields[3], fields[6], fields[7]>;
        end if;
      end if;
      line := Gets(f);
    end while;
    delete f;
  catch e
    ord_data := AssociativeArray(); // file absent; will fall back to Order(MaximalOrder(B), M)
  end try;

  for D in [6..boundO] do
    for M in [1..Floor(boundO/D)] do
      if IsSquarefree(M) and (Gcd(D, M) eq 1) and (D*M lt boundO) and IsSquarefree(D) and IsEven(#PrimeDivisors(D)) then
        print(<D, M>);
        ord_label := Sprintf("%o.%o", D, D*M);
        if M gt 1 and IsDefined(ord_data, ord_label) then
          dat := ord_data[ord_label];
          i_sq := StringToInteger(dat[1]);
          j_sq := StringToInteger(dat[2]);
          B := QuaternionAlgebra(Rationals(), i_sq, j_sq);
          nums   := eval ReplaceString(ReplaceString(dat[3], "{", "["), "}", "]");
          denoms := eval ReplaceString(ReplaceString(dat[4], "{", "["), "}", "]");
          bas := Basis(B);
          gens := [&+[nums[k][c]*bas[c] : c in [1..4]] / denoms[k] : k in [1..4]];
          print("found basis of O");
          O := QuaternionOrder(gens);
        else
          B := QuaternionAlgebra(D);
          O := QuaternionOrder(B, M);
        end if;
        deg_pol := IsMaximal(O) select D*M else 1;
        for deg in Divisors(deg_pol) do
          // Label format: maximal (M=1) "D.del", Eichler (M>=2) "D.DM.del"
          lbl := M eq 1 select Sprintf("%o.%o", D, deg)
                            else Sprintf("%o.%o.%o", D, D*M, deg);
          if lbl in done_labels then
            if verbose then printf "Skipping %o (already computed)\n", lbl; end if;
            continue;
          end if;
          tr, mu := HasPolarizedElementOfDegree(O, deg);
          if not tr then continue; end if;
          row := LMFDBRowEntry(O, mu);
          if verbose then
            printf "%o\n", row;
          end if;
          if write then
            // Maximal orders go to filename_maximal, Eichler to filename_eichler
            target := M eq 1 select filename_maximal else filename_eichler;
            fprintf target, "%o\n", row;
          end if;
        end for;
      end if;
    end for;
  end for;

  return "";
end intrinsic;

intrinsic EnumerateOmuTxt(boundO::RngIntElt: verbose:=true,write:=false) -> Any
  {loop over polarized maximal orders (O,mu) of discriminant up to boundO 
  and polarization up to boundmu and output their lmfdb row entry}
  
  if write eq true then 
    filename:=Sprintf("./data/quaternion-orders/quaternion-orders-polarized.txt");
    fprintf filename, "label | order_label | mu | deg_mu | nrd_mu | AutmuO_size | AutmuO_label | AutmuO_is_cyclic | AutmuO_generators | Gerby_gen \n";
    fprintf filename, "text | text | integer[] | integer | integer | integer | text | boolean | integer[] | integer[]\n";
    fprintf filename, "\n";
  end if;

  for D in [6..boundO] do
    if IsSquarefree(D) and IsEven(#PrimeDivisors(D)) then
      for deg in Divisors(D) do
        B:=QuaternionAlgebra(D);
        O:=MaximalOrder(B); 
        if HasPolarizedElementOfDegree(O,deg) then 
          tr,mu := HasPolarizedElementOfDegree(O,deg);
          if verbose eq true then 
            print(<D,deg>);
          end if;
          row:=LMFDBRowEntry(O,mu);
          if verbose eq true then 
            printf "%o\n",row;
          end if;
          if write eq true then 
            filename:=Sprintf("./data/quaternion-orders/quaternion-orders-polarized.txt");
            fprintf filename, "%o\n",row;   
          end if;
        end if;
      end for;
    end if;
  end for;

  return "";
end intrinsic;





