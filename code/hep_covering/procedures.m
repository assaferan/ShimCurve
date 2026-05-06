Attach("hep_utils.m");

PrintFDCovering := procedure(L, Gamma, D);
// L: List of tuples <center, radius>
    printf "\\begin{center}\n\\psset{unit=2.5in}\n\\begin{pspicture}(-1,-1)(1,1)\n\\pscircle[fillstyle=solid,fillcolor=lightgray](0,0){1}\n\n";

    deltas := ChangeUniverse(Gamma`ShimFDSidepairsDomain,Gamma);
    for delta in deltas do
        c,r := IsometricCircle(delta,D);
        re_c := (AbsoluteValue(Re(c)) lt 10^-10) select 0 else RealField(6)!Re(c);
        im_c := (AbsoluteValue(Im(c)) lt 10^-10) select 0 else RealField(6)!Im(c);
        printf "\\psclip{\\pscircle(0,0){1}} \\pscircle[fillstyle=solid,fillcolor=white](%o,%o){%o} \\endpsclip\n", 
        re_c, im_c, Max(RealField(6)!r,0.001);
    end for;

    printf "\n";

    for delta in deltas do
        c,r := IsometricCircle(delta,D);
        re_c := (AbsoluteValue(Re(c)) lt 10^-10) select 0 else RealField(6)!Re(c);
        im_c := (AbsoluteValue(Im(c)) lt 10^-10) select 0 else RealField(6)!Im(c);
        printf "\\psclip{\\pscircle(0,0){1}} \\pscircle(%o,%o){%o} \\endpsclip\n", 
        re_c, im_c, Max(RealField(6)!r,0.001);
    end for;

    for ele in L do
        printf "\\pscircle[](%o,%o){%o}\n", 
        RealField(6)!Re(ele[1]), RealField(6)!Im(ele[1]), RealField(6)!ele[2];
    end for;

    printf "\\pscircle(0,0){1}\n\\end{pspicture}\n\\end{center}\n\n";
end procedure;

HepCoveringPicture := procedure(O);
    B := QuaternionAlgebra(O);
    //G := FuchsianGroup(B);
    G := FuchsianGroup(O);
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
    print(d);
    z := FixedPoints(G!nu, UpperHalfPlane())[1];
    print(z);
    DD := UnitDisc(:Center:=z);
    fd := FundamentalDomain(G,DD);
    _ := Group(G);
    _ := HeptagonalCovering(G,z);
    L1 := [x[3] : x in G`HeptCoverCenters];
    L2 := HyperbolicToEuclideanCircle(L1,r_hept);
    PrintFDCovering(L2,G,DD);
end procedure;