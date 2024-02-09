
declare attributes SubgroupLatElt:
  level,
  index,
  shimura_label,
  sigma,
  genus,
  H1plusquo,
  Enh;

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
    N := Modulus(BaseRing(H));
    gens := [H.i : i in [1..Ngens(H)]];
    ONparts := [GL4ToPair(h, O, Ahom)[2] : h in gens];
    return sub<GL(1, Integers(N)) | [[[Norm(x)]] : x in ONparts]>;
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

function aaa(L, key) // {key: L} in Python
    aa := AssociativeArray(); aa[key] := L; return aa;
end function;

function SortGClass(L)
    ans := [];
    Lat := L[1]`Lat;
    f := func<x|Sort([Lat`subs[y]`shimura_pieces : y in Keys(x, "overs")])>;
    by_supergroups := IndexFibers(L, f);
    for supers in Sort([k : k in Keys(by_supergroups)]) do
        subs := by_supergroups[supers];
        if #subs gt 1 then
            sorter := [sort_key(s, false) : s in subs];
            ParallelSort(~sorter, ~subs);
        end if;
        ans cat:= subs;
    end for;
    return ans;
end function;

intrinsic FromLowerLevel(Lat::SubgroupLat, Enh::AlgQuatEnh : naive:=false)
{}
    N := Enh`N;
    ambord := #Enh`GL4sub;
    ker_reds := getAllReductionKernels(Enh`rhs, ONx(Enh));
    label_lower := {};
    for i in [1..#Lat] do
        H := Lat`subs[i];
        H`Enh := Enh;
        H`level := N; // default; overridden below if from lower level
        H`index := ambord div H`order;
        for p -> kerp in ker_reds do
            if kerp subset H`subgroup then
                if IsDefined(Enh`Lats, N div p) then
                    pLat := Enh`Lats[N div p];
                    Hi := SubgroupIdentify(pLat, H`subgroup);
                    HH := pLat`subs[Hi];
                    H`level := HH`level;
                    H`shimura_label := HH`shimura_label;
                    break;
                else
                    // TODO: Handle the shimura_level correctly
                    assert IsDivisibleBy(H`level, p);
                    assert IsSquarefree(N); // Must compute prior level N separately
                    H`level := H`level div p;
                    Include(~label_lower, H`level);
                end if;
            end if;
        end for;
        H`genus := EnhancedGenus(RamificationData(H));
    end for;
    for lower in label_lower do
        // We need to deal with level 1 and 2 specially
        ComputeLevelsLabels(Lat, Enh : N:=lower, naive:=naive);
    end for;
end intrinsic;

intrinsic ComputeLevelsLabels(Lat::SubgroupLat, Enh::AlgQuatEnh : N:=0, naive:=false)
{}
    if N eq 0 then
        N := Enh`N;
        FromLowerLevel(Lat, Enh : naive:=naive);
    end if;
    this_level := [H : H in Lat`subs | H`level eq N];
    by_ig := IndexFibers(this_level, func<x|<x`level, x`index, x`genus>>);
    for ig -> Hs in by_ig do
        if #Hs eq 1 then
            by_gassman := aaa(Hs, 0);
        else
            gcodes := {@ Get(x, "gassman_vec") : x in Hs @};
            Sort(~gcodes);
            by_gassman := IndexFibers(Hs, func<x|Index(gcodes, Get(x, "gassman_vec"))-1>);
        end if;
        for gcode -> gsubs in by_gassman do
            if #gsubs eq 1 or naive then
                by_gnum := gsubs;
            else
                by_gnum := SortGClass(gsubs, false);
            end if;
            for gnum in [1..#by_gnum] do
                H := by_gnum[gnum];
                H`shimura_label := Sprintf("%o.%o.%o.%o.%o", H`level, H`index, H`genus, CremonaCode(gcode), gnum);
            end for;
        end for;
    end for;
end intrinsic;

intrinsic EnumerateGerbiestSurjectiveH(Enh::AlgQuatEnh) -> SeqEnum[Re] // OmodN::AlgQuatOrdRes, AutFull::Map, G::GrpMat, ONx::GrpMat, Ahom::HomGrp, KG::GrpMat) -> SeqEnum[Rec]
{return all of the enhanced subgroups which contain the entire kernel (maximal size of gerbe, hence gerbisest), and having surjective reduced norm, in a list with each one being a record (rethink it).}

  OmodN := Enh`rhs;
  Ahom := AtoGL4(Enh);
  G := GL4sub(Enh);
  KG := NormalizerKernelGL4(Enh);

  fake_label := Sprintf("%o.a", #G); // The FiniteGroup code expects a label, but only the order is actually used
  GG := NewLMFDBGrp(G, fake_label);
  AssignBasicAttributes(GG); // Computes basic invariants (like solvable, nilpotent) which are expected by the finite group code

  Lat := New(SubgroupLat);
  Lat`Grp := GG;
  Lat`outer_equivalence := false; // We want subgroups up to conjugacy, not up to automorphism
  Lat`inclusions_known := true; // We want to compute inclusion relations
  Lat`index_bound := 0; // We don't impose an index bound

  t0 := Cputime();
  subs:=Subgroups(G);
  vprint User1: "MagmaSubgroups", Cputime() - t0;
  O := OmodN`quaternionorder;
  N := Modulus(BaseRing(G));
  t0 := Cputime();
  surjH := [H : H in subs | #getDeterminantImage(H`subgroup, O, Ahom) eq EulerPhi(N)];
  vprint User1: "DeterminantImages", Cputime() - t0; t0 := Cputime();
  surj_gerby_H := [H : H in surjH | KG subset H`subgroup];
  vprint User1: "Gerby", Cputime() - t0; t0 := Cputime();
  Reverse(~surj_gerby_H); // FiniteGroup code prefers lower index earlier
  Lat`subs := [SubgroupLatElement(Lat, surj_gerby_H[i]`subgroup : i:=i, subgroup_count:=surj_gerby_H[i]`length) : i in [1..#surj_gerby_H]];

  t0 := Cputime();
  // This needs to be sped up (lattice edges are hard); we turn it off for now.
  //ComputeLatticeEdges(Lat, G, IdentityHomomorphism(G));
  //vprint User1: "ComputeLatticeEdges", Cputime() - t0; t0 := Cputime();

  // This requires the lattice edges, so we have to replace it with another, more naive labeling
  //ComputeLevelsLabels(Lat, Enh);
  //vprint User1: "ComputeLevelsLabels", Cputime() - t0; t0 := Cputime();

  ComputeLevelsLabels(Lat, Enh : naive:=true);
  vprint User1: "ComputeLevelsLabelsNaive", Cputime() - t0;

  return Lat;
end intrinsic;

intrinsic H1plusquo(H::GrpMat, Enh::AlgQuatEnh) -> GrpPerm
{}
    // Note that this version doesn't cache; the one below does
    G1plus := G1plus(Enh);
    KG := NormalizerKernelGL4(Enh);
    Gmap := G1plusmodKGmap(Enh);

    H1plus := sub< G1plus | H meet G1plus >;
    //H1plusgens := [H1plus.i : i in [1..Ngens(H1plus)]];
    H1plusKG := sub< G1plus | H1plus, KG >;
    H1plusKGmodKG := quo< H1plusKG | KG >;

    H1plusquo := Gmap(H1plus);
    //if not IsIsomorphic(H1plusquo, H1plusKGmodKG) then
    //    Error("This should not happen, something is not right - maybe this subgroup is not coarsest?");
    //end if;
    return H1plusquo;
end intrinsic;

intrinsic H1plusquo(H::SubgroupLatElt) -> GrpPerm
{}
    if not assigned H`H1plusquo then
        H`H1plusquo := H1plusquo(H`subgroup, H`Enh);
    end if;
    return H`H1plusquo;
end intrinsic;

intrinsic FuchsianIndex(H::SubgroupLatElt) -> RngIntElt
{Returns the index of H as a fuchsian group acting on the upper half plane.}

    return #G1plusmodKG(H`Enh) / #H1plusquo(H);
end intrinsic;

function RamData(H, Enh)
    G1KG := G1plusmodKG(Enh);
    Gmap := G1plusmodKGmap(Enh);
    ells := EllipticElementsGL4(Enh);
    if Type(H) eq SubgroupLatElt then
        Hpq := H1plusquo(H);
    else
        Hpq := H1plusquo(H, Enh);
    end if;
    T := CosetTable(G1KG, Hpq);
    piH := CosetTableToRepresentation(G1KG, T);

    sigma := [ piH(Gmap(v)) : v in ells ];
    assert &*(sigma) eq Id(Parent(sigma[1]));
    return sigma;
end function;

intrinsic RamificationData(H::SubgroupLatElt) -> SeqEnum[GrpPermElt]
{return the genus of the Shimura curve corresponding to H.}
    if not assigned H`sigma then
        H`sigma := RamData(H, H`Enh);
    end if;
    return H`sigma;
end intrinsic;

intrinsic RamificationData(H::GrpMag, Enh::AlgQuatEnh) -> SeqEnum[GrpPermElt]
{return the genus of the Shimura curve corresponding to H.}
    return RamData(H, Enh);
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
			 Glabel
		       >;

function createRecord(H)
    s := rec< GP_SHIM_RF | >;
    Hgp := H`subgroup;
    order := H`order;
    Enh := H`Enh; // Set in ComputeLevelsLabels
    mu := Enh`mu;
    Ahom := AtoGL4(Enh);
    homtoB := AtoBx(Enh);
    G := GL4sub(Enh);
    O := Enh`quaternionorder;

    Henhgens := [GL4ToPair(Hgp.i, O, Ahom) : i in [1..Ngens(Hgp)]];
    aut_mu_norms := [Abs(SquarefreeFactorization(Integers()!Norm(homtoB(pair[1])`element))) : pair in Henhgens];

    s`subgroup:=Hgp;
    s`level := H`level;
    s`genus:=H`genus;
    s`order:=order;
    s`index:=Order(G) div order;
    s`fuchsian_index:=FuchsianIndex(H);
    s`torsion:=PrimaryAbelianInvariants(FixedSubspace(Hgp));
    s`Glabel:=GroupLabel(Hgp);
    s`galEnd:=GroupLabel(Domain(Ahom));
    s`autmuO_norms:=aut_mu_norms;
    s`is_split:=(order eq #(Hgp meet Image(Ahom)) * #(Hgp meet ONx(Enh)));
    s`generators:=Henhgens;
    s`ram_data_elts:=H`sigma;
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
    s`coarse_label := H`shimura_label;
    s`label := Sprintf("%o-%o-%o", s`order_label, s`mu_label, s`coarse_label);

    return s;
end function;

intrinsic GenerateDataForGerbiestSurjectiveH(O::AlgQuatOrd,mu::AlgQuatElt,Ns::SeqEnum[RngIntElt],LatLookup::Assoc) -> SeqEnum[Rec], Assoc
{Returns a list of records, each representing a line to be added to the database gps_shimura_test, together with an updated LatLookup.
If N in Ns, then the every integer m dividing N should be in Ns}

  levels := {N : N in Ns};
  if 2 in Ns and not (6 in Ns) then
    Ns := [6] cat Ns;
  elif Ns eq [1] then
    Ns := [3];
  end if;
  seen := {};
  records := [];
  for N in Ns do
    if N le 2 then continue; end if;
    Enh := EnhancedSemidirectProduct(O, mu : N:=N);
    Enh`Lats := LatLookup;
    Lat := EnumerateGerbiestSurjectiveH(Enh);
    print "subs", N, #Lat;
    Latlevels := {H`level : H in Lat`subs};
    new_levels := Latlevels diff seen;
    subs := [H : H in Lat`subs | H`level in new_levels];
    print "#filtered", N, #subs;
    for M in new_levels do
      // Usually just one, but sometimes also adds 1 and 2
      LatLookup[M] := Lat;
    end for;

    t0 := Cputime();
    records cat:= [createRecord(H) : H in subs];
    vprint User1: "createRecord", Cputime() - t0;
    seen join:= Latlevels;
  end for;
  return records;
end intrinsic;

function writeSeqEnum(seq)
    return "{" * Join([Sprint(x) : x in seq], ",") * "}";
end function;

intrinsic WriteSubgroupsDataToFile(subs::SeqEnum[Rec])
{}
    t0 := Cputime();
    assert #subs gt 0;
    filename:=Sprintf("data/genera-tables/genera-D%o-deg%o-N%o.m",subs[1]`discO,subs[1]`deg_mu,subs[1]`level);
    file := Open(filename, "w");
    header := "genus?fuchsian_index?index?torsion?galEnd?autmuO_norms?is_split?generators?ram_data_elts\n";
    fprintf file, header;

    for s in subs do
        gens_readable:=[ writeSeqEnum(Eltseq(g`element[1]`element) cat Eltseq((g`element[2])`element)) : g in s`generators ];
	perms_readable:=[ EncodePerm(p):  p in s`ram_data_elts];
        fprintf file, Sprintf("%o?%o?%o?%o?%o?%o?%o?%o?%o\n", s`genus, s`fuchsian_index, s`index, s`torsion, s`galEnd, s`autmuO_norms, s`is_split, writeSeqEnum(gens_readable), writeSeqEnum(perms_readable));
    end for;
    vprint User1: "WriteSubgroups", Cputime() - t0;
end intrinsic;


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





