Attach("hep_utils.m");

QQ := Rationals();
B<i,j,ij> := QuaternionAlgebra<QQ|-3,5>;
O := MaximalOrder(B);
ZK := Integers(QuadraticField(-7));
nu := Embed(ZK,O);
Gamma := FuchsianGroup(B);
_ := Group(Gamma);
z := FixedPoints(Gamma!nu, UpperHalfPlane())[1];
DD := UnitDisc( : Center := z);

/* 
test HeptagonalCovering and HeptagonalWhichCenter
CC<I> := ComplexField(DD`prec);
pi := Pi(CC);
_ := HeptagonalCovering(Gamma, z);
HeptagonalWhichCenter(Gamma, DD!(1/2*Exp(2*pi*I*45/110)));
HeptagonalWhichCenter(Gamma, DD!(0.31*Exp(2*pi*I/69)));
HeptagonalWhichCenter(Gamma, DD!(-0.309678738830485547090702735959 - 0.0141095257312187148410792542418*));
*/

