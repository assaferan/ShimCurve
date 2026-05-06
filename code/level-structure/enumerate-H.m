
// This should work for small groups
function GroupLabel(grp)
  if CanIdentifyGroup(#grp) then
    a, b := Explode(IdentifyGroup(grp));
    return Sprintf("%o.%o", a, b);
  end if;
  // For now, we give up.
  return "\\N";
end function;

function getDeterminantImage(H, O, Ahom)
  R := BaseRing(H);
  GL1 := GL(1, R);
  gens := [H.i : i in [1..Ngens(H)]];
  if IsEmpty(gens) then
    return sub<GL1 | >;
  end if;
  ONparts := [GL4ToPair(h, O, Ahom)[2] : h in gens];
  return sub<GL1 | [[[Norm(x)]] : x in ONparts]>;
end function;

function getKernelOfReduction(OmodN, p, G)
  N := Modulus(OmodN);
  assert IsDivisibleBy(N, p);
  if (p eq N) then
    return G;
  end if;
  gens := [G.i : i in [1..Ngens(G)]];
  R := Integers(N div p);
  phom := hom<G -> GL(4, R) | [<g, ChangeRing(g, R)> : g in gens]>;
  return Kernel(phom);
end function;

function getAllReductionKernels(OmodN, G)
  N := Modulus(OmodN);
  ker_reds := AssociativeArray();
  for p in PrimeDivisors(N) do
    ker_reds[p] := getKernelOfReduction(OmodN, p, G);
  end for;
  return ker_reds;
end function;

function EnumerateGerbiestAttachPrimeData(OmodN, G, ONx, surj_gerby_H, O1_subs)
  if #O1_subs eq 0 then
    Error(
    "EnumerateGerbiestAttachPrimeData: O1_subs is empty; use full Subgroups(G) for det-trivial subgroups, not Subgroups(G,KG) alone."
    );
  end if;

  ker_reds := getAllReductionKernels(OmodN, G meet ONx);

  ker_reds_O1 := AssociativeArray(Keys(ker_reds));

  for p in Keys(ker_reds) do
    ker_reds_O1[p] := ker_reds[p] meet O1_subs[#O1_subs]`subgroup;
  end for;

  prime_kernels_in_H := [[] : H in surj_gerby_H];

  prime_kernels_in_H_O1 := [[] : H in O1_subs];

  for p in Keys(ker_reds) do
    for i->H in surj_gerby_H do
      if ker_reds[p] subset H`subgroup then
        Append(~prime_kernels_in_H[i], p);
      end if;
    end for;
    for i->H in O1_subs do
      if ker_reds_O1[p] subset H`subgroup then
        Append(~prime_kernels_in_H_O1[i], p);
      end if;
    end for;
  end for;

  return surj_gerby_H, prime_kernels_in_H, O1_subs, prime_kernels_in_H_O1;
end function;

function EnumerateGerbiestFromSubgroupLattice(subs, OmodN, G, ONx, Ahom, KG, surjRequireKG)
  O := OmodN`quaternionorder;
  N := Modulus(BaseRing(G));
  euler_phi_N := EulerPhi(N);

  surj_gerby_H := [];
  O1_subs := [];
  for H in subs do
    d := #getDeterminantImage(H`subgroup, O, Ahom);
    if d eq 1 then
      Append(~O1_subs, H);
    end if;
    if d eq euler_phi_N then
      if surjRequireKG then
        if KG subset H`subgroup then
          Append(~surj_gerby_H, H);
        end if;
      else
        Append(~surj_gerby_H, H);
      end if;
    end if;
  end for;

  return EnumerateGerbiestAttachPrimeData(OmodN, G, ONx, surj_gerby_H, O1_subs);
end function;

function EnumerateGerbiestHybrid(OmodN, G, ONx, Ahom, KG)
  assert IsNormal(G, KG);
  O := OmodN`quaternionorder;
  N := Modulus(BaseRing(G));
  euler_phi_N := EulerPhi(N);

  subs_full := Subgroups(G);
  O1_subs := [];
  for H in subs_full do
    if #getDeterminantImage(H`subgroup, O, Ahom) eq 1 then
      Append(~O1_subs, H);
    end if;
  end for;

  surj_gerby_H := [];
  for H in Subgroups(G, KG) do
    if #getDeterminantImage(H`subgroup, O, Ahom) eq euler_phi_N then
      Append(~surj_gerby_H, H);
    end if;
  end for;

  return EnumerateGerbiestAttachPrimeData(OmodN, G, ONx, surj_gerby_H, O1_subs);
end function;

function SubgroupPrimeFingerprint(subgrp_recs, prime_rows)
  seq := [];
  for i in [1..#subgrp_recs] do
    Append(~seq, <subgrp_recs[i]`order, Sort(prime_rows[i])>);
  end for;
  return Sort(seq);
end function;

intrinsic GetG1plus(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt,G::GrpMat) -> GrpMat
  {Returns G1plus given G.}
  NBOplusgens_enhanced:=NormalizerPlusGeneratorsEnhanced(O,mu);
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens_enhanced ];
  G1plus:=sub< G | NBOplusgensGL4 >;
  assert #G/#G1plus eq 2;
  return G1plus;
end intrinsic;

intrinsic GetKernelAsSubgroup(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt,G1plus::GrpMat) -> GrpMat
  {Returns the kernel of the semidirect to normalizer map, as a subgroup of G.}
  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  KGlist:=[ EnhancedElementInGL4modN(k,N) : k in K ];
  KG:=sub< G1plus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;
  assert #KG eq #K;
  return KG;
end intrinsic;

intrinsic EnumerateGerbiestSurjectiveH(OmodN::AlgQuatOrdRes, AutFull::Map, G::GrpMat, ONx::GrpMat, Ahom::HomGrp, KG::GrpMat) -> SeqEnum[Rec], SeqEnum, SeqEnum[Rec], SeqEnum
  {return all of the enhanced subgroups which contain the entire kernel (maximal size of gerbe, hence gerbisest), and having surjective reduced norm, in a list with each one being a record (rethink it).}

  assert IsNormal(G, KG);
  // surj_gerby_H from Subgroups(G,KG); O1_subs from full Subgroups(G) (det-trivial subgroups need
  // not contain KG, e.g. the trivial subgroup). See VerifyGerbiestKGSubgroupEnumeration.
  return EnumerateGerbiestHybrid(OmodN, G, ONx, Ahom, KG);
end intrinsic;

intrinsic VerifyGerbiestKGSubgroupEnumeration(O::AlgQuatOrd, mu::AlgQuatElt, N::RngIntElt) -> BoolElt, MonStgElt
  {Reference implementation uses one Subgroups(G) pass (EnumerateGerbiestFromSubgroupLattice with
  surjRequireKG true). Production uses Subgroups(G,KG) for surj rows and full Subgroups(G) for O1.
  Returns true when both agree: identical O1 lists (hence same O1_subs[#] / ker_reds_O1), same
  surj multiset fingerprint (subgroup order + sorted prime rows).}
  assert N gt 2;
  AutFull := Aut(O,mu);
  assert MapIsHomomorphism(AutFull : injective:=true);
  OmodN := quo(O,N);
  G, ONxinGL4, Ahom := EnhancedImageGL4(AutFull,O,N);
  assert -G!1 in G;
  G1plus := GetG1plus(O, mu, N, G);
  KG := GetKernelAsSubgroup(O, mu, N, G1plus);

  if not IsNormal(G, KG) then
    return false, "KG is not normal in G";
  end if;

  Oq := OmodN`quaternionorder;
  euler_phi_N := EulerPhi(Modulus(BaseRing(G)));

  subs_full := Subgroups(G);
  ref_surj, ref_pfH, ref_O1, ref_pfO1 :=
  EnumerateGerbiestFromSubgroupLattice(subs_full, OmodN, G, ONxinGL4, Ahom, KG, true);

  hyb_surj := [];
  for H in Subgroups(G, KG) do
    if #getDeterminantImage(H`subgroup, Oq, Ahom) eq euler_phi_N then
      Append(~hyb_surj, H);
    end if;
  end for;
  hyb_O1 := [];
  for H in subs_full do
    if #getDeterminantImage(H`subgroup, Oq, Ahom) eq 1 then
      Append(~hyb_O1, H);
    end if;
  end for;
  hyb_surj, hyb_pfH, hyb_O1, hyb_pfO1 :=
  EnumerateGerbiestAttachPrimeData(OmodN, G, ONxinGL4, hyb_surj, hyb_O1);

  if #ref_O1 ne #hyb_O1 then
    return false, Sprintf("O1_subs length mismatch ref=%o hybrid=%o", #ref_O1, #hyb_O1);
  end if;
  for i in [1..#ref_O1] do
    if ref_O1[i]`subgroup ne hyb_O1[i]`subgroup then
      return false, Sprintf("O1_subs[%o] subgroup differs between reference and hybrid", i);
    end if;
    if Sort(ref_pfO1[i]) ne Sort(hyb_pfO1[i]) then
      return false, Sprintf("prime_kernels_in_H_O1 row %o differs", i);
    end if;
  end for;

  if #ref_surj ne #hyb_surj then
    return false, Sprintf("surj_gerby_H count mismatch ref=%o hybrid=%o", #ref_surj, #hyb_surj);
  end if;

  fp_ref := SubgroupPrimeFingerprint(ref_surj, ref_pfH);
  fp_hyb := SubgroupPrimeFingerprint(hyb_surj, hyb_pfH);
  if fp_ref ne fp_hyb then
    return false, "Fingerprint mismatch on surj_gerby_H between reference and hybrid";
  end if;

  return true, "";
end intrinsic;

intrinsic EnumerateGerbiestSurjectiveH(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt : prime_kernel := []) -> SeqEnum[Rec]
  {return all of the enhanced subgroups which contain the entire kernel (maximal size of gerbe, hence gerbisest), and having surjective reduced norm, in a list with each one being a record (rethink it).}

  assert N gt 2;
  AutFull := Aut(O,mu);
  assert MapIsHomomorphism(AutFull : injective:=true);

  G, ONxinGL4, Ahom := EnhancedImageGL4(AutFull,O,N);

  assert -G!1 in G;

  G1plus := GetG1plus(O, mu, N, G);

  KG := GetKernelAsSubgroup(O, mu, N, G1plus);

  subs, prime_kernels := EnumerateGerbiestSurjectiveH(quo(O,N), AutFull, G, ONxinGL4, Ahom, KG);

  // For now, we simply return the subgroups that have minimal level N
  return [subs[i] : i in [1..#subs] | prime_kernels[i] eq prime_kernel];

end intrinsic;

intrinsic EllipticElementsGL4(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt) -> SeqEnum
  {return the elliptic elements of the associated Shimura curve as elements in GL4(Z/NZ).}
  elliptic_elements_enhanced:=EnhancedEllipticElements(O,mu);
  assert forall(u){ <u,v> : u,v in elliptic_elements_enhanced | 
  EnhancedElementInGL4modN(u,N)*EnhancedElementInGL4modN(v,N) eq EnhancedElementInGL4modN(u*v,N) };
  elliptic_eltsGL4:= [ EnhancedElementInGL4modN(e,N) : e in elliptic_elements_enhanced ];
  return elliptic_eltsGL4;
end intrinsic;

function Base26Encode(n)
  strip := "abcdefghijklmnopqrstuvwxyz";
  assert n gt 0;
  x := n - 1;
  s := "";
  repeat
    digit := x mod 26;
    s cat:= strip[digit+1];
    x div:= 26;
  until x eq 0;
  return Reverse(s);
end function;

intrinsic GetH1plusquo(H::GrpMat[RngIntRes], G1plus::GrpMat[RngIntRes], KG::GrpMat[RngIntRes], G1plusmodKG::GrpPerm, Gmap::Map[GrpMat[RngIntRes], GrpPerm]) -> GrpPerm
  {}
  H1plus := sub< G1plus | H meet G1plus >;
  H1plusKG:= sub< G1plus | H1plus, KG >;
  H1plusKGmodKG:= quo< H1plusKG | KG >;

  H1plusquo:=Gmap(H1plus);
  //if not IsIsomorphic(H1plusquo,H1plusKGmodKG) then
  //    Error("This should not happen, something is not right - maybe this subgroup is not coarsest?");
  //end if;
  return H1plusquo;
end intrinsic;

intrinsic FuchsianIndex(G1plusmodKG::GrpPerm, H1plusquo::GrpPerm) -> RngIntElt
  {Returns the index of H as a fuchsian group acting on the upper half plane.}

  return #G1plusmodKG/#H1plusquo;
end intrinsic;

intrinsic RamificationData(G1plusmodKG::GrpPerm, H1plusquo::GrpPerm, Gmap::Map[GrpMat[RngIntRes], GrpPerm], ells::SeqEnum[GrpMatElt[RngIntRes]]) -> SeqEnum[GrpPermElt]
  {return the genus of the Shimura curve corresponding to H.}

  T:=CosetTable(G1plusmodKG,H1plusquo);
  piH:=CosetTableToRepresentation(G1plusmodKG,T);

  sigma := [ piH(Gmap(v)) : v in ells ];
  assert &*(sigma) eq Id(Parent(sigma[1]));

  return sigma;
end intrinsic;

GP_SHIM_RF := recformat< level : Integers(),
subgroup,
genus,
order,
index,
fuchsian_index,
torsion,
generators,
is_split,
galEnd,
autmuO_norms,
ram_data_elts,
discB,
discO,
deg_mu,
order_label,
mu_label,
label,
coarse_label,
Glabel,
nu2,
nu3,
nu4,
nu6,
coarse_class,
coarse_class_num,
coarse_num,
coarse_index,
fine_label,
gerbiness,
aut_gerbiness,
is_coarse,
psl2label,
scalar_label
>;	  

// Minimal record shape for createRecord (needs subgroup + order only).
SUBMEET_RF := recformat<subgroup : GrpMat, order : Integers()>;

function createRecord(H, G1plus, KG, G1plusmodKG, Gmap, ells, ONxinGL4, 
  Ahom, AutFull, O, N, OmodN, G, mu, level)
  s := rec< GP_SHIM_RF | >;
  Hgp:=H`subgroup;
  fixedspace:=FixedSubspace(Hgp);
  order:=H`order;

  H1plusquo := GetH1plusquo(Hgp, G1plus, KG, G1plusmodKG, Gmap);

  fuchsian_index:=FuchsianIndex(G1plusmodKG, H1plusquo);
  sigma := RamificationData(G1plusmodKG, H1plusquo, Gmap, ells);
  genus := EnhancedGenus(sigma);

  is_split := (order eq #(Hgp meet Image(Ahom)) * #(Hgp meet ONxinGL4));
  Henhgens := [GL4ToPair(Hgp.i, O, Ahom) : i in [1..Ngens(Hgp)]];
  aut_mu_norms := [Abs(SquarefreeFactorization(Integers()!Norm(AutFull(pair[1])`element))) : pair in Henhgens];

  s`subgroup:=Hgp;
  s`level := level;
  s`genus:=genus;
  s`order:=order;
  s`index:=Order(G) div order;
  s`coarse_index := s`index;
  s`fuchsian_index:=fuchsian_index;
  s`gerbiness:=#KG;
  s`aut_gerbiness:=#{GL4ToPair(x, O, Ahom)[1] : x in KG};
  s`torsion:=PrimaryAbelianInvariants(fixedspace);
  s`Glabel:= N eq level select GroupLabel(Hgp) else 
  GroupLabel(Hgp / getKernelOfReduction(OmodN, N div level, G meet ONxinGL4));
  s`galEnd:=GroupLabel(Domain(Ahom));
  s`autmuO_norms:=aut_mu_norms;
  s`is_split:=is_split;
  s`generators:= N eq level select [<AutFull(g[1]),g[2]> : g in Henhgens] else 
  [<AutFull(g[1]),[Integers()!x mod level : x in Eltseq(g[2])]> : g in Henhgens];
  s`generators:= [g : g in Set(s`generators)];
  s`ram_data_elts:=sigma;
  s`discO := Discriminant(O);
  s`discB := Discriminant(Algebra(O));
  if IsMaximal(O) then 
    s`order_label := Sprintf("%o", s`discO);
  elif IsEichler(O) then
    s`order_label := Sprintf("%o.%o", s`discB, s`discO);
  else
    Error("Not implemented for non-Eichler orders at the moment");
  end if;
  s`deg_mu := Integers()!Norm(mu) div Discriminant(O);
  s`mu_label := Sprintf("%o.%o", s`order_label, s`deg_mu);
  s`coarse_label := Sprintf("%o.%o.%o", s`level, s`index, s`genus);
  s`fine_label := s`coarse_label;
  s`is_coarse := true;

  nu := EnhancedEllipticPoints(s`ram_data_elts);
  s`nu2 := nu[2];
  s`nu3 := nu[3];
  s`nu4 := nu[4];
  s`nu6 := nu[6];

  return s;
end function;

procedure updateLabels(~subs, G)
  labels := {s`coarse_label : s in subs};
  for label in labels do
    label_subs := [i : i in [1..#subs] | subs[i]`coarse_label eq label];
    perm_chars := [<Eltseq(PermutationCharacter(G,subs[i]`subgroup)),i> : i in label_subs];
    perm_chars_sorted := Sort(perm_chars);
    n := 0;
    idx := 0;
    prev_char := [];
    tiebreaker := 0;
    while idx lt #perm_chars do
      idx +:= 1;
      perm_char := perm_chars_sorted[idx][1];
      if (perm_char ne prev_char) then
        n +:= 1;
        tiebreaker := 0;
      else
        tiebreaker +:= 1;
      end if;
      class := Base26Encode(n);
      sub_idx := perm_chars_sorted[idx][2];
      subs[sub_idx]`coarse_label cat:= Sprintf(".%o.%o", class, tiebreaker+1);
      subs[sub_idx]`coarse_class_num := n;
      subs[sub_idx]`coarse_class := class;
      subs[sub_idx]`coarse_num := tiebreaker+1;
    end while;
  end for;
  for i in [1..#subs] do
    subs[i]`label := Sprintf("%o.%o", subs[i]`mu_label, subs[i]`coarse_label);
    subs[i]`fine_label := subs[i]`coarse_label;
  end for;
end procedure;

intrinsic GenerateDataForGerbiestSurjectiveH(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt) -> SeqEnum[Rec]
  {Returns a list of records, each representing a line to be added to the database gps_shimura_test.}

  level := N;
  if N le 2 then
    N := 3*N;
    prime_kernel := [3];
  else
    prime_kernel := [];
  end if;
  assert N gt 2;
  OmodN := quo(O,N);
  AutFull:=Aut(O,mu);

  G, ONxinGL4, Ahom :=EnhancedImageGL4(AutFull,O,N);

  assert -G!1 in G;

  G1plus := GetG1plus(O, mu, N, G);

  KG := GetKernelAsSubgroup(O, mu, N, G1plus);

  subs, prime_kernels, O1_subs, O1_prime_kernels := EnumerateGerbiestSurjectiveH(OmodN, AutFull, G, ONxinGL4, Ahom, KG);
  vprintf ShimuraCurves, 1 : "subs %o\n", #subs;
  vprintf ShimuraCurves, 1 : "O1_subs %o\n", #O1_subs;

  subs := [subs[i] : i in [1..#subs] | prime_kernels[i] eq prime_kernel];
  vprintf ShimuraCurves, 1 : "#filtered %o\n", #subs;
  O1_subs := [O1_subs[i] : i in [1..#O1_subs] | O1_prime_kernels[i] eq prime_kernel];
  vprintf ShimuraCurves, 1 : "#O1 filtered %o\n", #O1_subs;
  if #O1_subs eq 0 then
    Error("GenerateDataForGerbiestSurjectiveH: empty O1_subs after prime_kernel filter");
  end if;

  ells := EllipticElementsGL4(O, mu, N);

  G1plusmodKG,Gmap:= quo< G1plus | KG >;

  ret_subs := [createRecord(H, G1plus, KG, G1plusmodKG, Gmap, ells, ONxinGL4, 
  Ahom, AutFull, O, N, OmodN, G, mu, level) : H in subs];

  updateLabels(~ret_subs, G);

  G1 := O1_subs[#O1_subs]`subgroup;
  // Only coarse intersections H meet G1 occur in psl2label matching; build one record per
  // G-conjugacy class of such intersections (instead of every det-trivial subgroup of G).
  meet_subgroups := [ H`subgroup meet G1 : H in subs ];
  meet_class_reps := [];
  for M in meet_subgroups do
    if not exists(R){ R : R in meet_class_reps | IsConjugate(G, M, R) } then
      Append(~meet_class_reps, M);
    end if;
  end for;
  O1_needed := [ rec<SUBMEET_RF | subgroup := R, order := #R> : R in meet_class_reps ];
  vprintf ShimuraCurves, 1 : "#O1 PSL2 reps (meet classes) %o (filtered O1_subs %o)\n",
  #O1_needed, #O1_subs;

  ret_O1_subs := [createRecord(H, G1plus, KG, G1plusmodKG, Gmap, ells, ONxinGL4, 
  Ahom, AutFull, O, N, OmodN, G, mu, level) : H in O1_needed];

  updateLabels(~ret_O1_subs, G);

  for idx->H in ret_subs do
    H1 := H`subgroup meet G1;
    assert exists(H_O1){H_O1 : H_O1 in ret_O1_subs | IsConjugate(G, H1, H_O1`subgroup)};
    ret_subs[idx]`psl2label := H_O1`label;
    scalar_index := Index(H`subgroup, H1);
    // At the moment we are not sure how to label the scalar subgroup, leaving 1 in the end
    ret_subs[idx]`scalar_label := Sprintf("%o.%o.1", level, scalar_index);
  end for;

  return ret_subs;
end intrinsic;

function writeSeqEnum(seq)
  str := "{";
  for i->elt in seq do
    if i gt 1 then
      str cat:= Sprintf(",");
    end if;
    str cat:= Sprintf("%o", elt);
  end for;
  str cat:= "}";
  return str;
end function;

function writeBoolean(b)
  ret := b select "T" else "F";
  return ret;
end function;

function strJoin(char, strings)
  s := "";
  for i->st in strings do
    if (i gt 1) then s cat:=char; end if;
    s cat:= st;
  end for;
  return s;
end function;

/*
List below produced in sage using:

from lmfdb import db
sage: for k in sorted(db.gps_shimura_test.col_type.keys()):
print('<"%s","%s">,'%(k,db.gps_shimura_test.col_type[k]))

but note that we leave out id and put label first (for update_from_file)
*/
GPS_SHIMURA_FIELDS := [
<"label","text">,
<"Glabel","text">,
<"all_degree1_points_known","boolean">,
<"aut_gerbiness","integer">,
<"autmuO_norms","integer[]">,
<"bad_primes","integer[]">,
<"cm_discriminants","integer[]">,
<"coarse_class","text">,
<"coarse_class_num","integer">,
<"coarse_index","integer">,
<"coarse_label","text">,
<"coarse_num","integer">,
<"conductor","integer[]">,
<"curve_label","text">,
<"deg_mu","integer">,
<"dims","integer[]">,
<"discB","integer">,
<"discO","integer">,
<"fine_label","text">,
<"fine_num","integer">,
<"fuchsian_index","integer">,
<"galEnd","text">,
<"generators","integer[]">,
<"genus","integer">,
<"genus_minus_rank","integer">,
<"gerbiness","integer">,
<"has_obstruction","smallint">,
<"index","integer">,
<"is_coarse","boolean">,
<"is_split","boolean">,
<"lattice_labels","text[]">,
<"lattice_x","integer[]">,
<"level","integer">,
<"level_is_squarefree","boolean">,
<"level_radical","integer">,
<"log_conductor","numeric">,
<"models","smallint">,
<"mu_label","text">,
<"mults","integer[]">,
<"name","text">,
<"newforms","text[]">,
<"nu2","integer">,
<"nu3","integer">,
<"nu4","integer">,
<"nu6","integer">,
<"num_bad_primes","integer">,
<"num_known_degree1_noncm_points","integer">,
<"num_known_degree1_points","integer">,
<"obstructions","integer[]">,
<"order_label","text">,
<"parents","text[]">,
<"parents_conj","integer[]">,
<"pointless","boolean">,
<"power","boolean">,
<"psl2label","text">,
<"q_gonality","integer">,
<"q_gonality_bounds","integer[]">,
<"qbar_gonality","integer">,
<"qbar_gonality_bounds","integer[]">,
<"ram_data_elts","numeric[]">,
<"rank","integer">,
<"reductions","text[]">,
<"scalar_label","text">,
<"simple","boolean">,
<"squarefree","boolean">,
<"torsion","integer[]">,
<"trace_hash","bigint">,
<"traces","integer[]">
];

intrinsic WriteHeaderToFile(file::IO)
  {Write the header to a file.}
  /*
  fields := ["Glabel", "all_degree1_points_known", "autmuO_norms", "bad_primes", "cm_discriminants", "coarse_class", "coarse_class_num", "coarse_index", "coarse_label", "coarse_num", "conductor", "curve_label", "deg_mu", "dims", "discB", "discO", "fine_label", "fine_num", "fuchsian_index", "galEnd", "generators", "genus", "genus_minus_rank", "gerbiness", "aut_gerbiness", "has_obstruction", "index", "is_coarse", "is_split", "label", "lattice_labels", "lattice_x", "level", "level_is_squarefree", "level_radical", "log_conductor", "models", "mu_label", "mults", "name", "newforms", "nu2", "nu3", "nu4", "nu6", "num_bad_primes", "num_known_degree1_noncm_points", "num_known_degree1_points", "obstructions", "order_label", "parents", "parents_conj", "pointless", "power", "psl2label", "q_gonality", "q_gonality_bounds", "qbar_gonality", "qbar_gonality_bounds", "ram_data_elts", "rank", "reductions", "scalar_label", "simple", "squarefree", "torsion", "trace_hash", "traces"];

  types := ["text", "boolean", "integer[]", "integer[]", "integer[]", "text", "integer", "integer", "text", "integer", "integer[]", "text", "integer", "integer[]", "integer", "integer", "text", "integer", "integer", "text", "integer[]", "integer", "integer", "integer", "smallint", "integer", "boolean", "boolean", "text", "text[]", "integer[]", "integer", "boolean", "integer", "numeric", "smallint", "text", "integer[]", "text", "text[]", "integer", "integer", "integer", "integer", "integer", "integer", "integer", "integer[]", "text", "text[]", "integer[]", "boolean", "boolean", "text", "integer", "integer[]", "integer", "integer[]", "numeric[]", "integer", "text[]", "text", "boolean", "boolean", "integer[]", "bigint", "integer[]"];
  */
  fields := [x[1] : x in GPS_SHIMURA_FIELDS];
  types := [x[2] : x in GPS_SHIMURA_FIELDS];

  assert #types eq #fields;

  labels_header := strJoin("?", fields) cat "\n";

  fprintf file, labels_header;

  types_header := strJoin("?", types) cat "\n\n";

  fprintf file, types_header;

  return;
end intrinsic;

intrinsic WriteSubgroupsDataToFile(file::IO, subs::SeqEnum[Rec], O::AlgQuatOrd)
  {Write the list of subgroup records to a file, without the header}
  for s in subs do 
    gens_readable:= [ writeSeqEnum(Eltseq(O!g[1]`element) cat Eltseq(O!g[2])) : g in s`generators ];
    perms_readable:=[ EncodePerm(p):  p in s`ram_data_elts];

    bad_primes := PrimeDivisors(s`discO * s`level);

    if (s`genus in [0,1]) then
      // These q-bounds only hold when the bottom curve is genus 0
      q_gon_bounds := [1, 2*s`index];
      if s`genus eq 0 then
        q_gon_bounds := [1,2];
      end if;
      qbar_gon_bounds := [1,2];
    else
      q_gon_bounds := [1, 2*(s`genus - 1)];
      // These could be better - maybe (g+3)/2 ? Ask Oana and Freddy
      qbar_gon_bounds := [1, 2*(s`genus-1)];
    end if;

    s_fields_assoc := AssociativeArray();
    s_fields_assoc["Glabel"] := s`Glabel;
    s_fields_assoc["all_degree1_points_known"] := "F";
    s_fields_assoc["aut_gerbiness"] := s`aut_gerbiness;
    s_fields_assoc["autmuO_norms"] := writeSeqEnum(s`autmuO_norms);
    s_fields_assoc["bad_primes"] := writeSeqEnum(bad_primes);
    s_fields_assoc["cm_discriminants"] := "\\N";
    s_fields_assoc["coarse_class"] := s`coarse_class;
    s_fields_assoc["coarse_class_num"] := s`coarse_class_num;
    s_fields_assoc["coarse_index"] := s`coarse_index;
    s_fields_assoc["coarse_label"] := s`coarse_label;
    s_fields_assoc["coarse_num"] := s`coarse_num;
    s_fields_assoc["conductor"] := "\\N";
    s_fields_assoc["curve_label"] := "\\N";
    s_fields_assoc["deg_mu"] := s`deg_mu;
    s_fields_assoc["dims"] := "\\N";
    s_fields_assoc["discB"] := s`discB;
    s_fields_assoc["discO"] := s`discO;
    s_fields_assoc["fine_label"] := s`fine_label;
    s_fields_assoc["fine_num"] := "\\N";
    s_fields_assoc["fuchsian_index"] := s`fuchsian_index;
    s_fields_assoc["galEnd"] := s`galEnd;
    s_fields_assoc["generators"] := writeSeqEnum(gens_readable);
    s_fields_assoc["genus"] := s`genus;
    s_fields_assoc["genus_minus_rank"] := "\\N";
    s_fields_assoc["gerbiness"] := s`gerbiness;
    s_fields_assoc["has_obstruction"] := "\\N";
    s_fields_assoc["index"] := s`index;
    s_fields_assoc["is_coarse"] := writeBoolean(s`is_coarse);
    s_fields_assoc["is_split"] := writeBoolean(s`is_split);
    s_fields_assoc["label"] := s`label;
    s_fields_assoc["lattice_labels"] := "\\N";
    s_fields_assoc["lattice_x"] := "\\N";
    s_fields_assoc["level"] := s`level;
    s_fields_assoc["level_is_squarefree"] := writeBoolean(IsSquarefree(s`level));
    s_fields_assoc["level_radical"] := &*PrimeDivisors(s`level);
    s_fields_assoc["log_conductor"] := "\\N";
    s_fields_assoc["models"] := "\\N";
    s_fields_assoc["mu_label"] := s`mu_label;
    s_fields_assoc["mults"] := "\\N";
    s_fields_assoc["name"] := "\\N";
    s_fields_assoc["newforms"] := "\\N";
    s_fields_assoc["nu2"] := s`nu2;
    s_fields_assoc["nu3"] := s`nu3;
    s_fields_assoc["nu4"] := s`nu4;
    s_fields_assoc["nu6"] := s`nu6;
    s_fields_assoc["num_bad_primes"] := #bad_primes;
    s_fields_assoc["num_known_degree1_noncm_points"] := "\\N";
    s_fields_assoc["num_known_degree1_points"] := "\\N";
    s_fields_assoc["obstructions"] := "\\N";
    s_fields_assoc["order_label"] := s`order_label;
    s_fields_assoc["parents"] := "{}";
    s_fields_assoc["parents_conj"] := "\\N";
    s_fields_assoc["pointless"] := "\\N";
    s_fields_assoc["power"] := "\\N";
    s_fields_assoc["psl2label"] := s`psl2label;
    s_fields_assoc["q_gonality"] := "\\N";
    s_fields_assoc["q_gonality_bounds"] := writeSeqEnum(q_gon_bounds);
    s_fields_assoc["qbar_gonality"] := "\\N";
    s_fields_assoc["qbar_gonality_bounds"] := writeSeqEnum(qbar_gon_bounds);
    s_fields_assoc["ram_data_elts"] := writeSeqEnum(perms_readable);
    s_fields_assoc["rank"] := "\\N";
    s_fields_assoc["reductions"] := "\\N";
    s_fields_assoc["scalar_label"] := s`scalar_label;
    s_fields_assoc["simple"] := "\\N";
    s_fields_assoc["squarefree"] := "\\N";
    s_fields_assoc["torsion"] := writeSeqEnum(s`torsion);
    s_fields_assoc["trace_hash"] := "\\N";
    s_fields_assoc["traces"] := "\\N";

    s_fields := [* s_fields_assoc[fld[1]] : fld in GPS_SHIMURA_FIELDS *];

    assert #s_fields eq 68;
    fprintf file, strJoin("?", [Sprintf("%o", f) : f in s_fields]) cat "\n";
  end for;
  return;
end intrinsic;

intrinsic WriteHeaderAndSubgroupsDataToFile(subs::SeqEnum[Rec], O::AlgQuatOrd)
  {Write the list of subgroup records to a file, together with the header.}
  assert #subs gt 0;
  filename:=Sprintf("data/genera-tables/genera-D%o-deg%o-N%o.m",subs[1]`discO,subs[1]`deg_mu,subs[1]`level);
  file := Open(filename, "w");
  WriteHeaderToFile(file);
  WriteSubgroupsDataToFile(file, subs, O);
  return;
end intrinsic;

intrinsic EnumerateH(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false, profile:=false) -> Any
  {return all of the enhanced subgroups in a list with each one being a record}
  t0 := Cputime();
  if write eq true then
    assert verbose eq true;
    assert minimal eq false;
  end if;
  assert N gt 2;
  B:=QuaternionAlgebra(O);
  BxmodQx:=QuaternionAlgebraModuloScalars(B);
  OmodN:=quo(O,N);
  possible_tors:=[   [3], [2,3], [3,3], [4], [2,4], [2,2,2], [2,2,3],[3,4],[4,4], [2,2,4],[2,3,3] ];
  D:=Discriminant(B);
  del:=DegreeOfPolarizedElement(O,mu);
  //if profile then print "Setup", Cputime() - t0; end if;
  t0 := Cputime();

  //mu:=PolarizedElementOfDegree(O,1);
  AutFull:=Aut(O,mu);
  if profile then print "Aut(O,mu)", Cputime() - t0; t0 := Cputime(); end if;

  RF := recformat< n : Integers(),
  subgroup,
  genus,
  order,
  index,
  torsion,
  generators,
  is_split,
  endomorphism_representation,
  AutmuO_norms,
  ramification_data
  >
  ;

  NBOplusgens_enhanced:=NormalizerPlusGeneratorsEnhanced(O,mu);
  if profile then print "NBOplusgens_enhanced", Cputime() - t0; t0 := Cputime(); end if;
  NBOplusgensGL4:=[ EnhancedElementInGL4modN(g,N) : g in NBOplusgens_enhanced ];
  //if profile then print "NBOplusgensGL4", Cputime() - t0; end if;
  t0 := Cputime();

  G, ONxinGL4, Ahom := EnhancedImageGL4(AutFull,O,N);
  //print "Group:", GroupToString(G : use_id:=false);
  if profile then print "EnhancedImageGL4", Cputime() - t0; t0 := Cputime(); end if;
  assert -G!1 in G;
  G1plus:=sub< G | NBOplusgensGL4 >;
  if profile then print "G1plus", Cputime() - t0; t0 := Cputime(); end if;
  // This assertion fails for N = 5, D = 6. Do we understand why?
  assert #G/#G1plus eq 2;
  GO:= G meet sub< GL(4,ResidueClassRing(N)) | UnitGroup(O,N) >;
  if profile then print "GO", Cputime() - t0; t0 := Cputime(); end if;
  //assert #G/4 eq #GO; //if twisting

  ZmodN:=ResidueClassRing(N);

  elliptic_elements_enhanced:=EnhancedEllipticElements(O,mu);
  if profile then print "elliptic_elements_enhanced", Cputime() - t0; t0 := Cputime(); end if;
  //assert forall(u){ <u,v> : u,v in elliptic_elements_enhanced |
  //EnhancedElementInGL4modN(u,N)*EnhancedElementInGL4modN(v,N) eq EnhancedElementInGL4modN(u*v,N) };
  //if profile then print "assertion", Cputime() - t0; t0 := Cputime(); end if;
  elliptic_eltsGL4:= [ EnhancedElementInGL4modN(e,N) : e in elliptic_elements_enhanced ];
  //if profile then print "elliptic_eltsGL4", Cputime() - t0; end if;
  t0 := Cputime();
  K:=[ k : k in SemidirectToNormalizerKernel(O,mu) ];
  if profile then print "K", Cputime() - t0; t0 := Cputime(); end if;
  KGlist:=[ EnhancedElementInGL4modN(k,N) : k in K ];
  KG:=sub< G1plus | [ EnhancedElementInGL4modN(k,N) : k in K ] >;
  assert #KG eq #K;

  G1plusmodKG,Gmap:= quo< G1plus | KG >;

  minimal_subs_init:=<>;
  //if profile then print "G1plusmodKG", Cputime() - t0; end if;
  t0 := Cputime();
  subs:=Subgroups(G);
  if profile then print "Subgroups(G)", Cputime() - t0; t0 := Cputime(); end if;

  for H in subs do
    Hgp:=H`subgroup;
    fixedspace:=FixedSubspace(Hgp);
    order:=H`order;
    //index:=Order(G)/order;

    H1plus := sub< G1plus | Hgp meet G1plus >;
    H1plusKG:= sub< G1plus | H1plus, KG >;
    H1plusKGmodKG:= quo< H1plusKG | KG >;

    H1plusquo:=Gmap(H1plus);
    //if not IsIsomorphic(H1plusquo,H1plusKGmodKG) then 
    //  break;
    //end if;

    index:=#G1plusmodKG/#H1plusquo;

    T:=CosetTable(G1plusmodKG,H1plusquo);
    piH:=CosetTableToRepresentation(G1plusmodKG,T);
    //piH := EnhancedCosetRepresentation(G,Hgp,Gammastar_plus);
    sigma := [ piH(Gmap(v)) : v in elliptic_eltsGL4 ];
    assert &*(sigma) eq Id(Parent(sigma[1]));
    genus:=EnhancedGenus(sigma);

    is_split := (order eq #(Hgp meet Image(Ahom)) * #(Hgp meet ONxinGL4));
    Henhgens := [GL4ToPair(Hgp.i, O, Ahom) : i in [1..NumberOfGenerators(Hgp)]];
    aut_mu_norms := [Abs(SquarefreeFactorization(Integers()!Norm(AutFull(pair[1])`element))) : pair in Henhgens];
    rho_end := sub<GL(4,ZmodN)|[Ahom(pair[1]) : pair in Henhgens]>;

    s := rec< RF | >;
    s`subgroup:=Hgp;
    s`genus:=genus;
    s`order:=order;
    s`index:=index;
    s`torsion:=PrimaryAbelianInvariants(fixedspace);
    s`endomorphism_representation:=GroupName(rho_end);
    s`AutmuO_norms:=aut_mu_norms;
    s`split:=is_split;
    s`generators:=Henhgens;
    s`ramification_data:=sigma;

    if PQMtorsion eq true then 
      if s`endomorphism_representation ne "C1" and s`fixedsubspace in possible_tors then
        if lowgenus eq true then  
          if genus le 1 then 
            Append(~minimal_subs_init,s);
          end if;
        else 
          Append(~minimal_subs_init,s);
        end if;
      end if;
    else 
      if lowgenus eq true then  
        if genus le 1 then 
          Append(~minimal_subs_init,s);
        end if;
      else 
        Append(~minimal_subs_init,s);
      end if;
    end if;
  end for;

  if profile then print "Subloop", Cputime() - t0; t0 := Cputime(); end if;
  if minimal eq false then 
    if verbose eq true then 
      printf "Quaternion algebra of discriminant %o with presentation\n",Discriminant(O);
      print B : Magma;
      printf "Basis of O is %o\n", Basis(O);
      printf "Level N = %o\n", N;
      printf "Polarized Element \\mu=%o of degree %o and norm %o\n", mu, DegreeOfPolarizedElement(O,mu),Norm(mu);
      print "Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data \n";
      for s in minimal_subs_init do 
        printf "%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o \n", s`genus, s`index, s`order, s`torsion, s`endomorphism_representation, s`AutmuO_norms, s`split, s`generators, sprint(s`ramification_data);
      end for;
      if write eq true then 
        filename:=Sprintf("ShimCurve/data/genera-tables/genera-D%o-deg%o-N%o.m",D,del,N);
        Write(filename,Sprintf("%m;",B));
        Write(filename,Sprintf("%o;",Basis(O)));
        Write(filename,Sprintf("%o;",N));
        Write(filename,Sprintf("%o;",Eltseq(O!mu)));
        //Write(filename,Sprintf("Discriminant %o",Discriminant(O)));
        //Write(filename,Sprintf("Basis of O is %o", Basis(O)));
        //Write(filename,Sprintf("Level N = %o", N));
        Write(filename,Sprintf("Polarized Element \\mu=%o of degree %o and norm %o", mu, DegreeOfPolarizedElement(O,mu),Norm(mu)));
        Write(filename,"Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data");

        for s in minimal_subs_init do 
          gens_readable:=[ Sprintf("<%o, %o>", g[1], Eltseq(g[2])) : g in s`generators ];
          //gens_readable;
          Write(filename,Sprintf("%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o ? %o", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, gens_readable, sprint(s`ramification_data)));
        end for;
      end if;
    end if;
    if profile then print "Minimal", Cputime() - t0; t0 := Cputime(); end if;
    return minimal_subs_init;
  else 
    minimal_subs:=<>;
    for s in minimal_subs_init do  
      F:=s`subgroup;
      tors:=s`fixedsubspace;
      //endorep:=s`endomorphism_representation;
      //AL:=s`atkin_lehners;
      if exists(e){ N : N in minimal_subs_init | F subset N`subgroup and 
      tors eq N`fixedsubspace and F ne N`subgroup }
      //or exists(e){ N : N in minimal_subs_init | IsGLConjugate(F,N`subgroup) } 
      then 
      ;
    else 
      Append(~minimal_subs,s);
    end if;
  end for;
  if verbose eq true then
    printf "Quaternion algebra of discriminant %o with presentation\n",Discriminant(O);
    print B : Magma;
    printf "Basis of O is %o\n", Basis(O);
    printf "Level N = %o\n", N;
    printf "Polarized Element \\mu=%o of degree %o and norm %o\n", mu, DegreeOfPolarizedElement(O,mu),Norm(mu);
    print "Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data\n";
    for s in minimal_subs do 
      printf "%o ? %o ? %o ? %o ? %o ? %o ? %o ? %o \n", s`genus, s`index, s`order, s`fixedsubspace, s`endomorphism_representation, s`AutmuO_norms, s`split, sprint(s`generators), sprint(s`ramification_data);
    end for;
  end if;
  if profile then print "Nonminimal", Cputime() - t0; t0 := Cputime(); end if;
  return minimal_subs;
end if;

end intrinsic;


intrinsic EnumerateH(B::AlgQuat,mu::AlgQuatOrdElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  return EnumerateH(MaximalOrder(B),mu,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
end intrinsic;

intrinsic EnumerateH(O::AlgQuatOrd,del::RngIntElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  if HasPolarizedElementOfDegree(O,del) then 
    tr,mu:=HasPolarizedElementOfDegree(O,del);
    return EnumerateH(O,mu,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
  else 
    printf "No polarization of degree %o\n", del;
    return "";
  end if;
end intrinsic;

intrinsic EnumerateH(B::AlgQuat,del::RngIntElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  O:=MaximalOrder(B);
  return EnumerateH(O,del,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
end intrinsic;

intrinsic EnumerateH(D::RngIntElt,del::RngIntElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {}
  B:=QuaternionAlgebra(D);
  O:=MaximalOrder(B);
  return EnumerateH(O,del,N : minimal:=minimal, verbose:=verbose, PQMtorsion:=PQMtorsion, lowgenus:=lowgenus, write:=write);
end intrinsic;






intrinsic EnhancedPermutationRepresentationMod2(O::AlgQuatOrd,mu::AlgQuatElt) -> Any
  {return the permutation representation Autmu(O) \ltimes (O/N)^x -> S_n}

  Omod2:=quo(O,2);
  Oenh:=EnhancedSemidirectProduct(O : N:=2);

  Omod2_elements := Setseq(Set(Omod2));
  Omod2_units := [ a : a in Omod2_elements | IsUnit(a) ];

  autmuO := Aut(O,mu);
  autmuOelts := [ autmuO(x) : x in Domain(autmuO) ];

  enhanced_elements:= [ Oenh!<a,b> : a in autmuOelts, b in Omod2_units ];
  assert #Set(enhanced_elements) eq #enhanced_elements;
  enhanced_elements := Set(enhanced_elements);
  enhanced_elements := SetToIndexedSet(enhanced_elements);

  n:=#enhanced_elements;
  SymX:=Sym(enhanced_elements);
  permrep := map< enhanced_elements -> SymX | g :-> SymX![ g*x : x in enhanced_elements ] >; 

  permrep_elts:= [ permrep(g) : g in enhanced_elements ];
  Gperm:= sub< SymX | permrep_elts >;

  idG := Oenh!<1, [1,0,0,0]>;
  embedG := map< Oenh -> Gperm | g :-> Gperm!permrep(g), p :-> Image(p,idG) >;

  return embedG;
end intrinsic;


/*
subsGperm:=Subgroups(Codomain(Gperm));
subsGpermD4 := [ subs : subs in subsGperm | GroupName(subs`subgroup) eq "D4" ]; 
D4enh:=[ [ <Order(p), Inverse(Gperm)(p)> : p in Set(sub`subgroup) ] : sub in subsGpermD4 ];


Genh,mapenh,rho_enh:=EnhancedRepresentationMod2PQM(X);
rho2_elts:=[ a : a in ]


EnumerateHmod2(O::AlgQuatOrd,mu::AlgQuatElt,N::RngIntElt) -> Any
{return the subgroups of the enhanced semidirect product with N=2}


*/

intrinsic Print(elt::AlgQuatOrdResElt)
  {.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(OmodN::AlgQuatOrdRes)
  {.}
  printf "Quotient of %o by %o", OmodN`quaternionorder, OmodN`quaternionideal;
end intrinsic;

intrinsic Print(elt::AlgQuatProjElt)
  {.}
  printf "%o", elt`element;
end intrinsic;

intrinsic Print(BxmodFx::AlgQuatProj)
  {.}
  printf "Quotient by scalars of %o", BxmodFx`quaternionalgebra;
end intrinsic;





