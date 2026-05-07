AttachSpec("spec");
import "code/level-structure/enumerate-H.m" : createRecord, getDeterminantImage, SetLevel;

D := 6;
B := QuaternionAlgebra(D);
O := MaximalOrder(B);
deg := 1;
tr,mu := HasPolarizedElementOfDegree(O,deg);
assert tr;
Ns := [1,2,3,4,6];
LatLookup := AssociativeArray();
levels := {N : N in Ns};
if 2 in Ns and not (6 in Ns) then
  Ns := [6] cat Ns;
elif Ns eq [1] then
  Ns := [3];
end if;
seen := {};
records := [];
for N in Ns[1..4] do
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
      // !! TODO - is this the right thing, or should we just take the sublattice
      // corresponding to the new level M ???
      LatLookup[M] := Latfull;
    end for;

    // TODO: Need to fix handling of lower levels, especially with regard to subgroups of G1
    // Also need to set psl2label on the returned records

    t0 := Cputime();
    records cat:= [createRecord(H) : H in subs];
    vprint User1: "createRecord", Cputime() - t0;
    seen join:= Latlevels;
end for;
N := 6;
Enh := EnhancedSemidirectProduct(O, mu : N:=N);
Enh`Lats := LatLookup;
N := Enh`N;
OmodN := Enh`rhs;
O := OmodN`quaternionorder;
Ahom := AtoGL4(Enh);
G := GL4sub(Enh);
KG := NormalizerKernelGL4(Enh);
assert IsNormal(G, KG);
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
subs := Subgroups(G, KG);
vprint User1: "MagmaSubgroups", Cputime() - t0;

t0 := Cputime();
detimages := [#getDeterminantImage(H`subgroup, O, Ahom) : H in subs];
vprint User1: "DeterminantImages", Cputime() - t0; t0 := Cputime();

phiN := EulerPhi(N);
surjH := [subs[i] : i in [1..#subs] | detimages[i] eq phiN];
trivH := [subs[i] : i in [1..#subs] | detimages[i] eq 1];

// FiniteGroup code prefers lower index earlier
Reverse(~surjH); Reverse(~trivH);

// Create lattices
Latfull`subs := [SubgroupLatElement(Latfull, surjH[i]`subgroup : i:=i, subgroup_count:=surjH[i]`length) : i in [1..#surjH]];
Lat1`subs := [SubgroupLatElement(Lat1, trivH[i]`subgroup : i:=i, subgroup_count:=trivH[i]`length) : i in [1..#trivH]];

Lat := Latfull;
naive := true;
N := Enh`N;
ambord := #Enh`GL4sub;
X := SemidirectSystem(Enh`quaternionorder, Enh`mu, [N]);
X`Enh[N] := Enh;
ker_reds := getGLReductionKernels(X, N);
label_lower := {};
for i in [1..#Lat] do
    SetLevel(Lat, i, X, ker_reds, N, ambord, ~label_lower);
end for;