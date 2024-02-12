The code in this repo is for Shimura curves with level structure. It can be used to compute invariants such as the genus, write the invariants to a formatted string and read data directly into MAGMA from text files if stored for those paramaters.

Fix $(O,\pm \mu,N)$ where $O$ is (a maximal) order in an indefinite rational quaternion algebra $B$, $\mu$ is a polarized element and $N$ is an integer. 

In analogy with the $H < \mathrm{GL}_2(\mathbb{Z}/N\mathbb{Z})$ for modular curves, there is an $H$ which depends on on the triple above and has an associated Shimura curve $X_H$. This requires some more explanation: 
- Let $\mathrm{Aut}_{\pm \mu}(O)$ be the automorphisms of $O$ which preserve $\pm \mu$.
- $(O/N)^\times$ is just the units of the ring $O/N$.
- $G = \mathrm{Aut}_{\pm \mu}(O) \ltimes (O/N)^\times$, with the semidirect product naturally defined.

$G$ plays the role of $\mathrm{GL}_2(\mathbb{Z}/N\mathbb{Z})$, $(O/N)^\times$ is where the Galois representation lives if the surface has QM defined already and $\mathrm{Aut}_{\pm \mu}(O)$ is like refined Atkin-Lehner involutions. A **PQM surface** has its Galois representatin contained in $G$, this is called the enhanced representation, see section 3.5 of https://arxiv.org/abs/2308.15193 for more details.

Make sure you are working one directory above this repository. To load the intrinsics do
```
AttachSpec("ShimCurve/spec");
```

# Types

Since it is not straightforward to work with $G$ directly in MAGMA, new 'types' have been created to support it. These are:
```
- AlgQuatProj :: B^x/Q^x, the quaternion algebra modulo scalars :: QuaternionAlgebraModuloScalars(B::AlgQuat)
- AlgQuatProjElt :: an element of AlgQuatProj :: ElementModuloScalars(BxmodFx::AlgQuatProj, x::AlgQuatElt)
- AlgOrdRes :: O/N :: quo(O::AlgQuatOrd, N::RngIntElt)
- AlgOrdResElt :: an element of AlgOrdRes :: OmodNElement(OmodN::AlgQuatOrdRes, x::AlgQuatOrdElt)
- AlgQuatEnh :: the semidirect product G, allows for N=0 :: EnhancedSemidirectProduct(O::AlgQuatOrd: N:=0) // TODO: mu
- AlgQuatEnhElt :: an element of G :: EnhancedElement(Ocirc::AlgQuatEnh, tup::<>)
```

## Example
```
B<i,j>:=QuaternionAlgebra<RationalField() | 3, -1>;
O:=MaximalOrder(B);
BxmodQx:=QuaternionAlgebraModuloScalars(B);
OmodN:=quo(O,3);
w:=BxmodQx!(-3*j+3*i*j);
w^2;
18
w^2 eq BxmodQx!1;
true 18
Genh:=EnhancedSemidirectProduct(O: N:=3); // TODO: mu
x:=OmodN!2;
Genh!<w,x>
;
<-3*j + 3*k, [2 0 0 0]>
Genh!<1,1> eq (Genh!<w,x>)^2;
true
```

## Main Intrinsics

```
intrinsic HasPolarizedElementOfDegree(O::AlgQuatOrd,d::RngIntElt) -> BoolElt, AlgQuatElt 
  {return an element mu of O such that mu^2 + d*disc(O) = 0 if it exists.}

intrinsic IsTwisting(O::AlgQuatOrd,mu::AlgQuatElt) -> BoolElt
  {(O,mu) is twisting (of degree del = -mu^2/disc(O)) if there exists chi in O and N_Bx(O)
   such that chi^2 = m, m|Disc(O) and mu*chi = -chi*mu. Return true or false; if true 
   return [mu, chi] up to scaling}
   
intrinsic Aut(O::AlgQuatOrd,mu::AlgQuatElt) -> Any
  {Return Aut_{\pm mu}(O). It will be a map from D_n to B^x/Q^x where the codomain 
  is Aut_{\pm mu}(O)}

intrinsic NormalizingElementToGL4(w::AlgQuatElt,O::AlgQuatOrd) -> GrpMatElt 
intrinsic NormalizingElementToGL4modN(w::AlgQuatElt,O::AlgQuatOrd, N::RngIntElt) -> GrpMatElt 
  {O is an order over R. For an element g \in N_Bx(O) the map phi_g : b |--> g^-1bg
  is R-linear hence [g] is an element of M_4(R) after fixing a basis
  this function computes [g] and also returns the R-basis of O.}

intrinsic UnitGroupToGL4(x::AlgQuatOrdElt) -> GrpMatElt 
intrinsic UnitGroupToGL4modN(x::AlgQuatOrdElt,N::RngIntElt) -> GrpMatElt 
  {O is an order over R, this returns a matrix [lambda_g] wrt to a basis
  which is the right regular representation
  lambda_x : y --> y*x where g \in GL_1(O)}

intrinsic EnhancedSemidirectInGL4(Ocirc::AlgQuatEnh) -> Map 
  {create the map from the semidirect product to GL4(R). R depends on the base 
  ring of Ocirc.}

intrinsic EnhancedElementInGL4(g::AlgQuatEnhElt) -> GrpMatElt
  {the enhanced element in GL4(R), R depends on the base ring of g}

intrinsic EnhancedElementRecord(elt::AlgQuatEnhElt) -> Any
  {given <w,x> in Autmu(O) \rtimes (O/N)^x or Autmu(O) \rtimes O^x  return <w,x> as a 
  record along with its embedding in GL_4xGL_4 and just GL_4}

intrinsic EnhancedImageGL4(Enh::AlgQuatEnh) -> GrpMat, GrpMat, GrpHom
  {return the image of the enhanced semidirect product group G in GL4(Z/NZ).

intrinsic NormalizerPlusGenerators(O::AlgQuatOrd) -> SeqEnum
  {return generators of the positive norm elements which normalize O}

intrinsic NormalizerKernel(O::AlgQuatOrd,mu::AlgQuatOrdElt) -> SeqEnum // TODO: Enh
  {return the kernel of the map form the enhanced semidirect product to N_B^x(O). 
  It is necessarily cyclic and the second value is the generator of the group}

intrinsic NormalizerPlusGenerators(Enh::AlgQuatEnh) -> SeqEnum
  {return generators of the positive norm elements which normalize O in the enhanced semidirect product}

intrinsic EnhancedRamificationData(H::GrpMat, G::GrpMat,O::AlgQuatOrd,mu::AlgQuatElt) -> Any // TODO: Enh
  {return the image of the elliptic elements under the monodromy map}

intrinsic EnhancedGenus(sigma::SeqEnum) -> RngIntElt
  {Compute genus from permutation triple
   f:X -> Y. 2gX-2 = deg(f)*(2gY-2) + sum_x\inX (ex -1). 
   ex is the ramification degree of x. An element of S_n acts on sheets of the cover. 
  x is ramified if x is sent to another point under the action of an isotropy subgroup,
  i.e. the cycle type corresponding to x has length >1. The length is the ramification degree.}

intrinsic EnumerateH(O::AlgQuatOrd,mu::AlgQuatOrdElt,N::RngIntElt : minimal:=false,PQMtorsion:=false,verbose:=true, lowgenus:=false, write:=false) -> Any
  {return all of the enhanced subgroups in a list with each one being a record}
```

## Example

```
B<i,j,k>:=QuaternionAlgebra< Rationals() | 3,-1 >;
O:=QuaternionOrder([ 1, 1/2 + 1/2*i + 1/2*j + 1/2*k, 1/2 - 1/2*i + 1/2*j - 1/2*k, 1/2 - 1/2*i - 1/2*j + 1/2*k\
 ]);
N:=4;
Ocirc:=EnhancedSemidirectProduct(O : N:=4); // TODO: mu
 
tr,mu:=HasPolarizedElementOfDegree(O,1);
mu;
-3*j + k
assert mu^2 eq -6;
IsTwisting(O,mu);
true [ -3*j + k, -j + k ]
AutmuO:=Aut(O,mu);
AutmuO;
Mapping from: GrpPC to Quotient by scalars of Quaternion Algebra with base ring Rational Field, defined by i^2 = 3, j^2 = -1
<Id($), 1>
<$.1, -3*j + k>
<$.2, -j + k>
<$.1 * $.2, -2*i>
 
 
Hgens:=[ Ocirc!< 1, [ 1, 0, 2, 0 ] >, Ocirc!< 1, [ 3, 1, 0, 1 ] >, Ocirc!< 1, [ 1, 2, 2, 0 ] >, Ocirc!< 1, [ \
3, 0, 3, 3 ] >, Ocirc!< 1, [ 3, 2, 3, 1 ] >, Ocirc!< 1, [ 3, 0, 0, 0 ] >, Ocirc!< -3*j + k, [ 2, 0, 1, 0 ] > ];
HgensGL4:=[ EnhancedElementInGL4(g) : g in Hgens ];
HGL4:=sub< GL(4,ResidueClassRing(N)) | HgensGL4 >;
 
EnhancedElementRecord(Hgens[2]);
rec<recformat<n: IntegerRing(), enhanced, GL4xGL4, GL4> | 
enhanced := <1, [3 1 0 1]>,
GL4xGL4 := <
[1 0 0 0]
[0 1 0 0]
[0 0 1 0]
[0 0 0 1],

[3 1 0 1]
[0 2 1 0]
[0 3 2 0]
[2 3 3 1]
>,
GL4 := [3 1 0 1]
[0 2 1 0]
[0 3 2 0]
[2 3 3 1]>
 
FixedSubspace(HGL4);
Abelian Group isomorphic to Z/2
Defined on 1 generator in supergroup:
$.1 = 2*$.2 + 2*$.4
Relations:
2*$.1 = 0

G:=EnhancedImageGL4(AutmuO,O,N); // TODO: Enh
elliptic:=EllipticElements(O,mu); // TODO: Enh
elliptic; 
[
<-3*j + k, [1 0 0 0]>,
<-j + k, [ 0  0 -1  0]>,
<-2*i, [-1  0  0  1]>
]
 
mon:=EnhancedRamificationData(HGL4,G,O,mu); // TODO: Enh
mon;
[
(1, 2)(3, 4),
(1, 3)(2, 5)(4, 6),
(1, 4, 6, 3, 2, 5)
]
Genus(mon);
0
```

## Data

The list of $H$ for each triple $(O,\pm \mu, N)$ is currently stored as a string in data/genera-tables with the following columns:
```
Genus ? (Fuchsian) Index ? #H ? Torsion ? Gal(L|Q) ? AutmuO norms ? Split semidirect ? Generators ? Ramification Data
```

To load the data type:
```
list := GeneraTableToRecords(6,1,3);
list[50];
rec<recformat<n: IntegerRing(), genus, fuchsindex, torsioninvariants, endogroup, AutmuOnorms, Hsplit, generators, ramification_data> | 
genus := 1,
fuchsindex := 12,
torsioninvariants := [],
endogroup :=  C1 ,
AutmuOnorms := { 1 },
Hsplit := true,
generators :=  [ < 1, [ 2, 0, 0, 0 ] >, < 1, [ 2, 0, 2, 2 ] >, < 1, [ 0, 0, 1, 2 ] > ] ,
ramification_data := [
(1, 2)(3, 4)(5, 6)(7, 9)(8, 10)(11, 12),
(1, 3)(2, 5)(4, 7, 11, 10)(6, 9, 12, 8),
(1, 4, 8, 11, 9, 5)(2, 6, 10, 12, 7, 3)
]>
```





