import !"Geometry/GrpPSL2/GrpPSL2Shim/domain.m" : HistoricShimuraReduceUnit;

// returns matrix that translates i to z 
Translation := function(z);
    x := Real(z);
    y := Imaginary(z);
    Re := Parent(x);
    return Matrix(Re,2,2,[[y^0.5,x*y^(-0.5)],[0,y^(-0.5)]]);
end function;

// returns matrix that translates a vertex of (2,3,7) to z
TranslationMatrix := function(z);
    tri_group := ArithmeticTriangleGroup(2,3,7);
    vertex := FundamentalDomain(tri_group)[3];
    return Translation(z)*Inverse(Translation(vertex));
end function;

// Mobius action
MobiusTransformation := function(M,z);
    return (M[1,1]*z+M[1,2])/(M[2,1]*z+M[2,2]);
end function;

EmbeddingGenerators := function(a,b,c);
    pi := Pi(RealField());
    cosa := Cos(pi/a);
    cosb := Cos(pi/b);
    cosc := Cos(pi/c);
    sina := Sin(pi/a);
    sinb := Sin(pi/b);
    sinc := Sin(pi/c);

    l := (cosa*cosb+cosc)/(sina*sinb);
    t := l+Sqrt(l^2-1);

    da := Matrix([[cosa,sina],[-sina,cosa]]);
    db := Matrix([[cosb,t*sinb],[-sinb/t,cosb]]);
    dc := Inverse((da*db));
  
    return da,db,dc;

end function;

InitVertex := function(a,b,c);
    RR := RealField();
    l := (Cos(Pi(RR)/a)*Cos(Pi(RR)/b)+Cos(Pi(RR)/c))/(Sin(Pi(RR)/a)*Sin(Pi(RR)/b));
    t := l+Sqrt(l^2-1);
    x := ((t^2)-1)/(2*(Cot(Pi(RR)/a) + t*Cot(Pi(RR)/b)));
    y := Sqrt(Cosec(Pi(RR)/a)^2 - (x - Cot(Pi(RR)/a))^2);
    I := Sqrt(RR!-1);
    return t*I, x+y*I, -x+y*I;
end function;

MapToUnitDisc := function(z,center);
// Maps points in the upper half plane to the unit disc where center is mapped to the origin
    return (z-center)/(z-ComplexConjugate(center));
end function;

pt1, pt2, pt3 := InitVertex(2,3,7); //pt3 is mapped to the origin
D := UnitDisc(:Center:=pt3);
zeropt := D!0;
r_hept := Distance(D!MapToUnitDisc(pt1,pt3), zeropt);
A,B,C := EmbeddingGenerators(2,3,7);
prec := 30;
CC<I> := ComplexField(prec);
RR := RealField(prec);

HeptTilingTable := function(N);
    // function that creates a hash table for centers of heptagonal tiling up to layer N
    // N = number of (C^i*A) in the word generating centers
    // i-th element = [(theta,r,z,n,index): theta=Arg(z), r=AbsoluteValue(z), z is a center in the i-th layer, n=layer]

    Matrix_list := {IdentityMatrix(CC,2)};
    allpts := [];
    Append(~allpts,[<RR!0,RR!0,CC!0,1,1>]);
    tmp := [CC!0];
    count := 1;
    for layer in [2..N] do
        Matrix_list := {C^i*A*M: i in [0..6], M in Matrix_list};
        newpts := {MapToUnitDisc(MobiusTransformation(M,pt3), pt3): M in Matrix_list};
        tmp2 := [];
        for pt in newpts do
            if AbsoluteValue(ChangePrecision(pt,10)) gt 10^(-10) and (not (ChangePrecision(pt,10) in tmp)) then
                Include(~tmp, ChangePrecision(pt,10));
                Include(~tmp2,<Argument(pt), AbsoluteValue(pt), pt, layer>);
            end if;
        end for;
        tmp3 := Sort(tmp2, func<x,y|(x[1] ne y[1]) select x[1]-y[1] else x[2]-y[2]>);
        to_store := [Append(tmp3[i], i+count): i in [1..#tmp3]];
        Append(~allpts, to_store);
        count := count + #tmp2;
    end for;
    return allpts;
end function;

AddAttribute(GrpPSL2, "HeptCoverCenters");
AddAttribute(GrpPSL2, "LayeredHeptCover");

intrinsic HeptagonalCovering(Gamma::GrpPSL2, z::SpcHypElt) -> SeqEnum[RngIntElt]
  {Takes as input a Fuchsian group Gamma, returns as output
  the sequence of integers indexing the centers of the heptagonal cover of the Dirichlet domain of Gamma}
    D := UnitDisc(:Center:=z);
    zeropt := D!0;
    fd := FundamentalDomain(Gamma,D);
    fd_radius := Maximum({Distance(x, zeropt): x in fd});
    N := Ceiling(fd_radius/r_hept);
    Gamma`LayeredHeptCover := HeptTilingTable(N);
    centers := &cat Gamma`LayeredHeptCover;

    O := BaseRing(Gamma);
    B := Algebra(O);
    gammagens := Gamma`ShimFDSidepairsDomain;
    prunecenters := [centers[1]];
    indices := [1];
    for i := 2 to #centers do
        c := centers[i][3];
        euc_circle := HyperbolicToEuclideanCircle(c,r_hept);
        euc_radius := euc_circle[2];
        boundary_pt := D!(c-euc_radius/AbsoluteValue(c)*c);
        gg := HistoricShimuraReduceUnit(O!1, gammagens, Gamma, D : z0 := boundary_pt);
        if gg[1][1] eq O!1 then
            Append(~indices,i);
            Append(~prunecenters,centers[i]);
        end if;
    end for;
    Gamma`HeptCoverCenters := prunecenters;
    return indices;
end intrinsic;


function Locate(elt,L);
    // given a sorted list L, find index i such that L[i] <= elt <= L[i+1]
    Lnew := Sort(Append(L,elt));
    return Index(Lnew,elt)-1;
end function;


function LocateLayer(r,radii_minandmax);
    // given a list of tuples [r_min, r_max] of minimum and maximum radii of each layer of heptagonal tiling,
    // return the layers closest to r
    L1 := {i : i in [1..#radii_minandmax] | radii_minandmax[i,1] lt r and r lt radii_minandmax[i,2]};
    L2 := &join[{i, i+1} : i in [1..#radii_minandmax-1] | radii_minandmax[i,2] lt r and r lt radii_minandmax[i+1,1]];
    return Sort(Setseq(L1 join L2));
end function;

function LocatePoint(z, tiling_centers : brute_force := false);
// tiling centers is a sequence of sequence of triples [argument, absolute value, complex number] by layer.
// returns the centers of the heptagonal discs containing z
    
    if Distance(D!z, zeropt) lt r_hept then return tiling_centers[1,1]; end if;
    radii_minandmax := [[Minimum([y[2] : y in x]), Maximum([y[2] : y in x])] : x in tiling_centers];
//    print radii_minandmax;
    allradii := [{ChangePrecision(y[2],5) : y in x} : x in tiling_centers];
//    print allradii;
    r := AbsoluteValue(z);
    theta := Argument(z);
    L := LocateLayer(r,radii_minandmax);
    if L eq [] then
        print "Not enough layers";
        return false;
    end if;
//    print L;
//    print [#x : x in tiling_centers];
    Exclude(~L,1);
    output_centers := [];
    for l in L do
//        print l;
        if l gt #tiling_centers then
            print "Not enough layers";
            return false;
        end if;
        if brute_force then
            possibilities := tiling_centers[l];
            for x in possibilities do
                center := D ! x[3];
                if Distance(center,D ! z) le r_hept then
                    Append(~output_centers, x);
                end if;
            end for;
        end if;
        thetas_l := [x[1] : x in tiling_centers[l]];
        j1 := Locate(theta,thetas_l);
//        print j1;
        if j1 mod #tiling_centers[l] eq 0 then
            two_possibilities := [tiling_centers[l,1],tiling_centers[l,#tiling_centers[l]]];
        else
            two_possibilities := [tiling_centers[l,j1],tiling_centers[l,j1+1]];
        end if;
//        print two_possibilities;
        for x in two_possibilities do
            center := D ! x[3];
            dist := Distance(center,D ! z);
//            print dist, r_hept;
            if dist le r_hept then
                Append(~output_centers, x);
            end if;
        end for;
        if output_centers ne [] then 
            output := Sort(output_centers, func<x,y| Distance(D!x[3],z)-Distance(D!y[3],z)>)[1];
            return output;
        end if;
    end for;
    return Sort(output_centers, func<x,y| Distance(D!x[3],z)-Distance(D!y[3],z)>)[1];
end function;


intrinsic HeptagonalWhichCenter(Gamma::GrpPSL2, w::SpcHydElt) -> RngIntElt, GrpPSL2Elt, SpcHydElt
    {Takes as input a Fuchsian group Gamma and
    w a point in the mother unit disc, and returns as output
    the index of the ball it belongs to (as output by HeptagonalCovering),
    an element delta in Gamma, and a point w` in the mother unit disc
    such that w` = delta*w and w` belongs to the indexed ball.}

    O := BaseRing(Gamma);
    B := Algebra(O);
    gammagens := Gamma`ShimFDSidepairsDomain;
    deltaH := HistoricShimuraReduceUnit(O!1, gammagens, Gamma, D : z0 := w)[1,1];
    wp := (Gamma!deltaH)*w;
    nearest_center := LocatePoint(wp, Gamma`LayeredHeptCover);

    return nearest_center[5], deltaH, wp;
end intrinsic;


intrinsic HyperbolicToEuclideanCircle(w::FldComElt,r::FldReElt) -> Tup
    {returns the Euclidean center and Euclidean radius of a circle in 
    hyperbolic unit disc with hyperbolic center w and hyperbolic radius r.
    Uses Eq 33.7.5 from John Voight - Quaternion Algebras}
    c := (Cosh(r)-1)/2;
    A := 1+c-c*AbsoluteValue(w)^2;
    B := (1+c)*AbsoluteValue(w)^2-c;
    z0 := w/A;
    r0 := (AbsoluteValue(z0)^2-B/A)^(1/2);
    return <z0, r0>;
end intrinsic;

intrinsic HyperbolicToEuclideanCircle(ws::SeqEnum,r::FldReElt) -> SeqEnum
    {returns the Euclidean center and Euclidean radius of the circles in 
    hyperbolic unit disc with hyperbolic center given by ws and fixed hyperbolic radius r.
    Uses Eq 33.7.5 from John Voight - Quaternion Algebras}
    return [HyperbolicToEuclideanCircle(w,r) : w in ws];
end intrinsic;

intrinsic NumberOfHeptagonsInCover(O :: AlgQuatOrd) -> RngIntElt, RngIntElt
{given an order O in a quaternion algebra B, first computes the associated Fuchsian group G, 
and a CM point z corresponding to an imaginary quadratic subring with fundamental discriminant 
-d < -4, and |d| smallest.
returns number of heptagons in an (almost-)cover of the fundamental domain of G centered at z, and -d.}
    B<i,j,ij> := QuaternionAlgebra(O);
    G := FuchsianGroup(B);
    d := 5;
    while true do
        if IsFundamentalDiscriminant(-d) then
            try
                ZK := Integers(QuadraticField(-d));
                nu := Embed(ZK,O);
                break;
            catch e;
                d := d+1;
            end try;
        else
            d := d+1;
        end if;
    end while;
    z := FixedPoints(G!nu, UpperHalfPlane())[1];
    DD := UnitDisc(:Center:=z);
    fd := FundamentalDomain(G,DD);
    _ := Group(G);
    heptcoverindices := HeptagonalCovering(G,z);
    return #heptcoverindices, -d;
end intrinsic;

intrinsic AreaRatio(O :: AlgQuatOrd) -> FldReElt, RngIntElt
{given an order O in a quaternion algebra B, first computes the associated Fuchsian group G, 
and a CM point z corresponding to an imaginary quadratic subring with fundamental discriminant 
-d < -4, and |d| smallest.
returns the ratio of the area of fundamental domain of G centered at z wrt area of a heptagonal disc, and -d.}
    B<i,j,ij> := QuaternionAlgebra(O);
    G := FuchsianGroup(B);
    d := 5;
    while true do
        if IsFundamentalDiscriminant(-d) then
            try
                ZK := Integers(QuadraticField(-d));
                nu := Embed(ZK,O);
                break;
            catch e;
                d := d+1;
            end try;
        else
            d := d+1;
        end if;
    end while;
    z := FixedPoints(G!nu, UpperHalfPlane())[1];
    DD := UnitDisc(:Center:=z);
    fd := FundamentalDomain(G,DD);

    RR := RealField();
    A := ArithmeticVolume(fd)*2*Pi(RR);
    a := (1-1/2-1/3-1/7)*2*Pi(RR)*7;
    return A/a, -d;
end intrinsic;

intrinsic AreaRatio_SingleDisc(O :: AlgQuatOrd) -> FldReElt, RngIntElt
{given an order O in a quaternion algebra B, first computes the associated Fuchsian group G, 
and a CM point z corresponding to an imaginary quadratic subring with fundamental discriminant 
-d < -4, and |d| smallest.
returns the ratio of the area of a single disc centered at 0 covering the fundamental domain of G centered at z
wrt the area of fundamental domain, and -d.}
    B<i,j,ij> := QuaternionAlgebra(O);
    G := FuchsianGroup(B);
    d := 5;
    while true do
        if IsFundamentalDiscriminant(-d) then
            try
                ZK := Integers(QuadraticField(-d));
                nu := Embed(ZK,O);
                break;
            catch e;
                d := d+1;
            end try;
        else
            d := d+1;
        end if;
    end while;
    z := FixedPoints(G!nu, UpperHalfPlane())[1];
    DD := UnitDisc(:Center:=z);
    fd := FundamentalDomain(G,DD);
    rho := Maximum([Distance(DD!0,DD!x) : x in fd]);

    RR := RealField();
    A := ArithmeticVolume(fd)*2*Pi(RR);
    a := 4*Pi(RR)*Sinh(rho/2)^2;

    return a/A, -d;
end intrinsic;

PrintFDCovering := procedure(L, Gamma, D);
// L: List of tuples <center, radius>
    printf "\\begin{center}\n\\psset{unit=2.5in}\n\\begin{pspicture}(-1,-1)(1,1)\n\\pscircle[fillstyle=solid,fillcolor=lightgray](0,0){1}\n\n";

    deltas := ChangeUniverse(Gamma`ShimFDSidepairsDomain,Gamma);
    for delta in deltas do
        c,r := IsometricCircle(delta,D);
        printf "\\psclip{\\pscircle(0,0){1}} \\pscircle[fillstyle=solid,fillcolor=white](%o,%o){%o} \\endpsclip\n", 
        RealField(6)!Re(c), RealField(6)!Im(c), Max(RealField(6)!r,0.001);
    end for;

    printf "\n";

    for delta in deltas do
        c,r := IsometricCircle(delta,D);
        printf "\\psclip{\\pscircle(0,0){1}} \\pscircle(%o,%o){%o} \\endpsclip\n", 
        RealField(6)!Re(c), RealField(6)!Im(c), Max(RealField(6)!r,0.001);
    end for;

    for ele in L do
        printf "\\pscircle[](%o,%o){%o}\n", 
        RealField(6)!Re(ele[1]), RealField(6)!Im(ele[1]), RealField(6)!ele[2];
    end for;

    printf "\\pscircle(0,0){1}\n\\end{pspicture}\n\\end{center}\n\n\\end{document}\n";
end procedure;

/*
PrintDomain := procedure(deltas, D);
  printf "\\begin{center}\n\\psset{unit=2.5in}\n\\begin{pspicture}(-1,-1)(1,1)\n\\pscircle[fillstyle=solid,fillcolor=lightgray](0,0){1}\n\n";

  for delta in deltas do
    c,r := IsometricCircle(delta,D);
    printf "\\psclip{\\pscircle(0,0){1}} \\pscircle[fillstyle=solid,fillcolor=white](%o,%o){%o} \\endpsclip\n",
      RealField(6)!Re(c), RealField(6)!Im(c), Max(RealField(6)!r,0.001);
  end for;

  printf "\n";

  for delta in deltas do
    c,r := IsometricCircle(delta,D);
    printf "\\psclip{\\pscircle(0,0){1}} \\pscircle(%o,%o){%o} \\endpsclip\n",
      RealField(6)!Re(c), RealField(6)!Im(c), Max(RealField(6)!r,0.001);
  end for;

  printf "\\pscircle(0,0){1}\n\\end{pspicture}\n\\end{center}\n\n\\end{document}\n";
end procedure;
*/

HepCoveringPicture := procedure(O);
    B := QuaternionAlgebra(O);
    G := FuchsianGroup(B);
    d := 5;
    while true do
        if IsFundamentalDiscriminant(-d) then
            try
                ZK := Integers(QuadraticField(-d));
                nu := Embed(ZK,O);
                break;
            catch e;
                d := d+1;
            end try;
        else
            d := d+1;
        end if;
    end while;
    z := FixedPoints(G!nu, UpperHalfPlane())[1];
    DD := UnitDisc(:Center:=z);
    fd := FundamentalDomain(G,DD);
    _ := Group(G);
    _ := HeptagonalCovering(G,z);
    L1 := [x[3] : x in G`HeptCoverCenters];
    L2 := HyperbolicToEuclideanCircle(L1,r_hept);
    PrintFDCovering(L2,G,DD);
end procedure;
