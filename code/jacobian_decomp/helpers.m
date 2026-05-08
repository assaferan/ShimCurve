// Helper functions for computing trace formulas and loading CMF data.

// local utilities
function strip(s) return Join(Split(Join(Split(s," "),""),"\n"),""); end function;

function sprint(X)
    if Type(X) eq Assoc then return Join(Sort([ $$(k) cat "=" cat $$(X[k]) : k in Keys(X)]),":"); end if;
    return strip(Sprintf("%o",X));
end function;

function atoi(s) return StringToInteger(s); end function;

cmfrec := recformat<
    label:MonStgElt,
    level:RngIntElt,
    cond:RngIntElt,
    dim:RngIntElt,
    rank:RngIntElt,
    traces:SeqEnum>;


intrinsic ClassNumberTable(N::RngIntElt) -> SeqEnum
{Returns a table whose (-D)th entry is h(-D) for D up to N, using cached data xgclassnumbers.dat if present.}
    try
        fp := Open("xgclassnumbers.dat","r");
        htab := ReadObject(fp);
    catch e
        htab := [];
    end try;
    N := Abs(N);
    if #htab lt N then
        htab := [d mod 4 in [0,3] select ClassNumber(-d) else 0 : d in [1..N]];
        fp := Open("xgclassnumbers.dat","w");
        WriteObject(fp,htab);
        delete fp;
    end if;
    fp := Open("xgclassnumbers.dat","r");
    htab := ReadObject(fp);
    return htab[1..N];
end intrinsic;


intrinsic GetClassNumber(htab::SeqEnum, D::RngIntElt) -> RngIntElt
{Returns h(D) using precomputed table htab where available.}
    return -D le #htab select htab[-D] else ClassNumber(D);
end intrinsic;


intrinsic GL2PermutationCharacter(H::GrpMat) -> .
{Returns the permutation character of GL2 acting on cosets of H.}
    R := BaseRing(H);
    pi := CosetAction(GL(Degree(H), R), H);
    return func<g|#Fix(pi(g))>;
end intrinsic;


intrinsic HPermutationCharacter(G::., H::.) -> .
{Returns the permutation character of G acting on cosets of H, via PCGroup.}
    G_pc, map_G := PCGroup(G);
    pi := CosetAction(G_pc, map_G(H));
    return func<g|#Fix(pi(map_G(g)))>;
end intrinsic;


// expected file format: label:level:cond:dim:rank:traces
intrinsic CMFLoad(D::RngIntElt, N::RngIntElt : cmfdatafile:="cmfdata.txt", levelbound:=-1) -> Assoc
{Loads CMF records from cmfdatafile whose level divides levelbound (default D*N^2).}
    if levelbound eq -1 then levelbound := D*N^2; end if;
    S := [Split(s,":"): s in Split(Read(cmfdatafile))];
    S := [r:r in S|IsDivisibleBy(levelbound, level) where level:=atoi(r[2]) ];
    S := [rec<cmfrec|label:=r[1],level:=atoi(r[2]),cond:=atoi(r[3]),dim:=atoi(r[4]),rank:=atoi(r[5]),traces:=eval(r[6])> : r in S];
    X := AssociativeArray();
    for r in S do X[r`label] := r; end for;
    return X;
end intrinsic;


intrinsic CMFLabelCompare(s::MonStgElt, t::MonStgElt) -> RngIntElt
{Comparison function for LMFDB newform labels, for use with Sort.}
    a := Split(s,".");  b := Split(t,".");
    if a[1] ne b[1] then return atoi(a[1]) - atoi(b[1]); end if;
    if a[2] ne b[2] then return atoi(a[2]) - atoi(b[2]); end if;
    if a[3] ne b[3] then return a[3] lt b[3] select -1 else 1; end if;
    if a[4] ne b[4] then return  a[4] lt b[4] select -1 else 1; end if;
    return 0;
end intrinsic;
