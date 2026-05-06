
declare attributes SubgroupLatElt:
  level,
  index,
  shimura_label,
  sigma,
  genus,
  H1plusquo,
  i_at_level, // This lattice element may be stored modulo N, where N is a multiple of the level.  In this case, we want to remember which lattice element modulo the level corresponds to this one
  Enh;

declare attributes SubgroupLat:
  LowerLevels;
  // Subgroup lattices, as an associative array indexed by N.
  // Lats[N] only contains subgroups with surjective norm (and currently only the gerbiest ones),
  // but there will be overlap since subgroups of level dividing N will be included (in order to get the containment relations correct)

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

  N := Enh`N;
  OmodN := Enh`rhs;
  O := OmodN`quaternionorder;
  Ahom := AtoGL4(Enh);
  G := GL4sub(Enh);
  KG := NormalizerKernelGL4(Enh);

  fake_label := Sprintf("%o.a", #G); // The FiniteGroup code expects a label, but only the order is actually used
  GG := NewLMFDBGrp(G, fake_label);
  AssignBasicAttributes(GG); // Computes basic invariants (like solvable, nilpotent) which are expected by the finite group code

  Latfull := New(SubgroupLat);
  Latfull`Grp := GG;
  Latfull`outer_equivalence := false; // We want subgroups up to conjugacy, not up to automorphism
  Latfull`inclusions_known := true; // We want to compute inclusion relations
  Latfull`index_bound := 0; // Even though we are restricting subgroups, it's not correctly modeled by an index bound

  Lat1 := New(SubgroupLat);
  Lat1`Grp := GG; // Even though all the subgroups here will be contained in G1, the equivalence relation is under conjugacy in GG
  Lat1`outer_equivalence := false; // We want subgroups up to GG-conjugacy, not up to automorphism
  Lat1`inclusions_known := false; // We don't need inclusion relationship for the G1-subgroups
  Lat1`index_bound := 0; // Even though we are restricting subgroups, it's not correctly modeled by an index bound

  // Compute the list of subgroups
  t0 := Cputime();
  subs := Subgroups(G);
  vprint User1: "MagmaSubgroups", Cputime() - t0;

  t0 := Cputime();
  detimages := [#getDeterminantImage(H`subgroup, O, Ahom) : H in subs];
  vprint User1: "DeterminantImages", Cputime() - t0; t0 := Cputime();

  phiN := EulerPhi(N);
  surjH := [H[i] : i in [1..#subs] | detimages[i] eq phiN];
  trivH := [H[i] : i in [1..#subs] | detimages[i] eq 1];

  t0 := Cputime();
  surj_gerby_H := [H : H in surjH | KG subset H`subgroup];
  print "Gerbysurj", #surj_gerby_H, #surjH;
  triv_gerby_H := [H : H in trivH | KG subset H`subgroup];
  print "Gerbytriv", #triv_gerby_H, #surjH;
  vprint User1: "Gerby", Cputime() - t0; t0 := Cputime();

  // FiniteGroup code prefers lower index earlier
  Reverse(~surj_gerby_H); Reverse(~trivH);

  // Create lattices
  Latfull`subs := [SubgroupLatElement(Latfull, surj_gerby_H[i]`subgroup : i:=i, subgroup_count:=surj_gerby_H[i]`length) : i in [1..#surj_gerby_H]];
  Lat1`subs := [SubgroupLatElement(Lat1, triv_gerby_H[i]`subgroup : i:=i, subgroup_count:=triv_gerby_H[i]`length) : i in [1..#triv_gerby_H]];

  t0 := Cputime();
  // This needs to be sped up (lattice edges are hard); we turn it off for now.
  //ComputeLatticeEdges(Latfull, G, IdentityHomomorphism(G));
  //vprint User1: "ComputeLatticeEdges", Cputime() - t0; t0 := Cputime();

  // This requires the lattice edges, so we have to replace it with another, more naive labeling
  //ComputeLevelsLabels(Latfull, Enh);
  //vprint User1: "ComputeLevelsLabels", Cputime() - t0; t0 := Cputime();

  ComputeLevelsLabels(Latfull, Enh : naive:=true);
  vprint User1: "ComputeLevelsLabelsNaive", Cputime() - t0; t0 := Cputime();
  ComputeLevelsLabels(Lat1, Enh : naive:=true);
  vprint User1: "ComputeLevelsLabels1Naive", Cputime() - t0; t0 := Cputime();

  return Latfull, Lat1;
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
			 is_coarse,
			 psl2label
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
    s`coarse_index := s`index;
    s`fuchsian_index:=FuchsianIndex(H);
    s`gerbiness:=#NormalizerKernelGL4(Enh);
    s`torsion:=PrimaryAbelianInvariants(FixedSubspace(Hgp));
    s`Glabel:=GroupLabel(Hgp);
    s`galEnd:=GroupLabel(Domain(Ahom));
    s`autmuO_norms:=aut_mu_norms;
    s`is_split:=(order eq #(Hgp meet Image(Ahom)) * #(Hgp meet ONx(Enh)));
    s`generators:=[<homtoB(g[1]),g[2]> : g in Henhgens];
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
    s`fine_label := s`coarse_label;
    s`label := Sprintf("%o-%o-%o", s`order_label, s`mu_label, s`coarse_label);
    s`is_coarse := true;

    nu := EnhancedEllipticPoints(H`sigma);
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
    Latfull, Lat1 := EnumerateGerbiestSurjectiveH(Enh);
    print "subs", N, #Latfull;
    Latlevels := {H`level : H in Latfull`subs};
    new_levels := Latlevels diff seen;
    subs := [H : H in Latfull`subs | H`level in new_levels];
    print "#filtered", N, #subs;
    for M in new_levels do
      // Usually just one, but sometimes also adds 1 and 2
      LatLookup[M] := Lat;
    end for;

    // TODO: Need to fix handling of lower levels, especially with regard to subgroups of G1
    // Also need to set psl2label on the returned records

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

function writeBoolean(b)
    return b select "t" else "f";
end function;

function strJoin(char, strings)
    s := "";
    for i->st in strings do
	if (i gt 1) then s cat:=char; end if;
	s cat:= st;
    end for;
    return s;
end function;

intrinsic WriteHeaderToFile(file::IO)
{Write the header to a file.}
    fields := ["Glabel", "all_degree1_points_known", "autmuO_norms", "bad_primes", "cm_discriminants", "coarse_class", "coarse_class_num", "coarse_index", "coarse_label", "coarse_num", "conductor", "curve_label", "deg_mu", "dims", "discB", "discO", "fine_label", "fine_num", "fuchsian_index", "galEnd", "generators", "genus", "genus_minus_rank", "gerbiness", "has_obstruction", "index", "is_coarse", "is_split", "label", "lattice_labels", "lattice_x", "level", "level_is_squarefree", "level_radical", "log_conductor", "models", "mu_label", "mults", "name", "newforms", "nu2", "nu3", "nu4", "nu6", "num_bad_primes", "num_known_degree1_noncm_points", "num_known_degree1_points", "obstructions", "order_label", "parents", "parents_conj", "pointless", "power", "psl2label", "q_gonality", "q_gonality_bounds", "qbar_gonality", "qbar_gonality_bounds", "ram_data_elts", "rank", "reductions", "scalar_label", "simple", "squarefree", "torsion", "trace_hash", "traces"];

    types := ["text", "boolean", "integer[]", "integer[]", "integer[]", "text", "integer", "integer", "text", "integer", "integer[]", "text", "integer", "integer[]", "integer", "integer", "text", "integer", "integer", "text", "integer[]", "integer", "integer", "integer", "smallint", "integer", "boolean", "boolean", "text", "text[]", "integer[]", "integer", "boolean", "integer", "numeric", "smallint", "text", "integer[]", "text", "text[]", "integer", "integer", "integer", "integer", "integer", "integer", "integer", "integer[]", "text", "text[]", "integer[]", "boolean", "boolean", "text", "integer", "integer[]", "integer", "integer[]", "numeric[]", "integer", "text[]", "text", "boolean", "boolean", "integer[]", "bigint", "integer[]"];

    assert #types eq #fields;

    labels_header := strJoin("?", fields) cat "\n";

    fprintf file, labels_header;

    types_header := strJoin("?", types) cat "\n\n";

    fprintf file, types_header;

    return;
end intrinsic;

intrinsic WriteSubgroupsDataToFile(file::IO, subs::SeqEnum[Rec])
{Write the list of subgroup records to a file, without the header}
    for s in subs do
        gens_readable:= [ writeSeqEnum(Eltseq(g[1]`element) cat Eltseq(g[2])) : g in s`generators ];
	perms_readable:=[ EncodePerm(p):  p in s`ram_data_elts];

	bad_primes := PrimeDivisors(s`discO * s`level);

	// These q-bounds only hold when the bottom curve is genus 0
	q_gon_bounds := [1, 2*s`index];

	if (s`genus in [0,1]) then
	    qbar_gon_bounds := [1,2];
	else
	    qbar_gon_bounds := [1, 2*(s`genus-1)];
	end if;

	s_fields := [* s`Glabel,
		       "F",
		       writeSeqEnum(s`autmuO_norms),
		       writeSeqEnum(bad_primes),
		       "\\N",
		       s`coarse_class,
		       s`coarse_class_num,
		       s`coarse_index,
		       s`coarse_label,
		       s`coarse_num,
		       "\\N",
		       "\\N",
		       s`deg_mu,
		       "\\N",
		       s`discB,
		       s`discO,
		       s`fine_label,
		       "\\N",
		       s`fuchsian_index,
		       s`galEnd,
		       writeSeqEnum(gens_readable),
		       s`genus,
		       "\\N",
		       s`gerbiness,
		       "\\N",
		       s`index,
		       writeBoolean(s`is_coarse),
		       writeBoolean(s`is_split),
		       s`label,
		       "\\N",
		       "\\N",
		       s`level,
		       writeBoolean(IsSquarefree(s`level)),
		       &*PrimeDivisors(s`level),
		       "\\N",
		       "\\N",
		       s`mu_label,
		       "\\N",
		       "\\N",
		       "{}",
		       s`nu2,
		       s`nu3,
		       s`nu4,
		       s`nu6,
		       #bad_primes,
		       "\\N",
		       "\\N",
		       "\\N",
		       s`order_label,
		       "{}",
		       "\\N",
		       "\\N",
		       "\\N",
		       "\\N",
		       "\\N",
		       writeSeqEnum(q_gon_bounds),
		       "\\N",
		       writeSeqEnum(qbar_gon_bounds),
		       writeSeqEnum(perms_readable),
		       "\\N",
		       "\\N",
		       "1.1.1",
		       "\\N",
		       "\\N",
		       writeSeqEnum(s`torsion),
		       "\\N",
		       "\\N" *];

	assert #s_fields eq 67;
        fprintf file, strJoin("?", [Sprintf("%o", f) : f in s_fields]) cat "\n";
    end for;
    return;
end intrinsic;

intrinsic WriteHeaderAndSubgroupsDataToFile(subs::SeqEnum[Rec])
{Write the list of subgroup records to a file, together with the header.}
    assert #subs gt 0;
    filename:=Sprintf("data/genera-tables/genera-D%o-deg%o-N%o.m",subs[1]`discO,subs[1]`deg_mu,subs[1]`level);
    file := Open(filename, "w");
    WriteHeaderToFile(file);
    WriteSubgroupsDataToFile(file, subs);
    return;
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





