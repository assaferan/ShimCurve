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
QQ := Rationals();
B<i,j,ij> := QuaternionAlgebra<QQ|-3,5>;
O := MaximalOrder(B);
ZK := Integers(QuadraticField(-7));
nu := Embed(ZK,O);
G := FuchsianGroup(B);
z := FixedPoints(G!nu, UpperHalfPlane())[1];
DD := UnitDisc(:Center:=z);
fd := FundamentalDomain(G,DD);
_ := Group(G);

/*
// to print fundamental domain
SetColumns(0);
import !"Geometry/GrpPSL2/GrpPSL2Shim/domain.m" : PrintDomain;
PrintDomain(ChangeUniverse(G`ShimFDSidepairsDomain,G), DD);
*/

CC<I> := ComplexField(DD`prec);
_ := HeptagonalCovering(G,z);
HeptagonalWhichCenter(G, DD!(-0.655492752372111787627614081399 - 0.437818211925444596389788823719*I));

/*
// to print fundamental domain with heptagonal covering
SetColumns(0);
L1 := [x[3] : x in G`HeptCoverCenters];
L2 := HyperbolicToEuclideanCircle(L1,r_hept);
// Copy Procedure PrintFDCovering from hep_utils.m
PrintFDCovering(L2,G,DD);
*/