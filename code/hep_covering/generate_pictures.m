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
print r_hept;

///////////////////////////////////////////////////////////////

Attach("hep_utils.m");
SetColumns(0);

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

    printf "\\pscircle(0,0){1}\n\\end{pspicture}\n\\end{center}\n\n";
end procedure;

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

for N in [6..50] do
    if IsSquarefree(N) and #PrimeFactors(N) mod 2 eq 0 then
        try
            B := QuaternionAlgebra(N);
            O := MaximalOrder(B);
            HepCoveringPicture(O);
            printf "\\newpage\n\n\n";
        catch e;
        end try;
    end if;
end for;
printf "\\end{document}";

