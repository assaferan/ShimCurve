177,0
T,AlgQuatOrdRes,AlgQuatOrdResElt,0
A,AlgQuatOrdRes,2,quaternionorder,quaternionideal
A,AlgQuatOrdResElt,2,element,parent
T,AlgQuatProj,AlgQuatProjElt,0
A,AlgQuatProj,1,quaternionalgebra
A,AlgQuatProjElt,2,element,parent
T,AlgQuatEnh,AlgQuatEnhElt,0
A,AlgQuatEnh,5,quaternionalgebra,quaternionorder,basering,lhs,rhs
A,AlgQuatEnhElt,2,element,parent
S,OmodNElement,Construct an element of the OmodN whose underlying element is x in O,0,2,0,0,0,0,0,0,0,20,,0,0,AlgQuatOrdRes,,AlgQuatOrdResElt,-38,-38,-38,-38,-38
S,ElementModuloScalars,Construct an element of B^x/F^x whose underlying element is x in B,0,2,0,0,0,0,0,0,0,18,,0,0,AlgQuatProj,,AlgQuatProjElt,-38,-38,-38,-38,-38
S,EnhancedElement,Construct and element of the enhances semidirect product whose underling element is a tuple in Autmu(O)x(O)^x or Autmu(O)x(O/N)^x,0,2,0,0,0,0,0,0,0,303,,0,0,AlgQuatEnh,,AlgQuatEnhElt,-38,-38,-38,-38,-38
S,eq,Decide if x equals y in OmodN,0,2,0,0,0,0,0,0,0,AlgQuatOrdResElt,,0,0,AlgQuatOrdResElt,,36,-38,-38,-38,-38,-38
S,eq,Decide if x equals y in OmodN,0,2,0,0,0,0,0,0,0,AlgQuatProjElt,,0,0,AlgQuatProjElt,,36,-38,-38,-38,-38,-38
S,eq,decide if g1 eq g2 in enhanced semidirect product,0,2,0,0,0,0,0,0,0,AlgQuatEnhElt,,0,0,AlgQuatEnhElt,,36,-38,-38,-38,-38,-38
S,eq,Decide if OmodN1 equals OmodN2,0,2,0,0,0,0,0,0,0,AlgQuatOrdRes,,0,0,AlgQuatOrdRes,,36,-38,-38,-38,-38,-38
S,eq,Decide if BxmodFx1 equals BxmodFx2,0,2,0,0,0,0,0,0,0,AlgQuatProj,,0,0,AlgQuatProj,,36,-38,-38,-38,-38,-38
S,eq,Decide if Ocirc1 equals Ocirc2,0,2,0,0,0,0,0,0,0,AlgQuatEnh,,0,0,AlgQuatEnh,,36,-38,-38,-38,-38,-38
S,*,compute x*y in OmodN,0,2,0,0,0,0,0,0,0,AlgQuatOrdResElt,,0,0,AlgQuatOrdResElt,,AlgQuatOrdResElt,-38,-38,-38,-38,-38
S,*,compute x*y in B^x/F^x,0,2,0,0,0,0,0,0,0,AlgQuatProjElt,,0,0,AlgQuatProjElt,,AlgQuatProjElt,-38,-38,-38,-38,-38
S,*,compute x*y in enhanced semidirect produt,0,2,0,0,0,0,0,0,0,AlgQuatEnhElt,,0,0,AlgQuatEnhElt,,AlgQuatEnhElt,-38,-38,-38,-38,-38
S,^,compute x^y in (O/N)^x,0,2,0,0,0,0,0,0,0,148,,0,0,AlgQuatOrdResElt,,AlgQuatOrdResElt,-38,-38,-38,-38,-38
S,^,compute x^y in B^x/F^x,0,2,0,0,0,0,0,0,0,148,,0,0,AlgQuatProjElt,,AlgQuatProjElt,-38,-38,-38,-38,-38
S,^,g^exp in enhanced semidirect product,0,2,0,0,0,0,0,0,0,148,,0,0,AlgQuatEnhElt,,AlgQuatEnhElt,-38,-38,-38,-38,-38
S,Order,order of element,0,1,0,0,0,0,0,0,0,AlgQuatProjElt,,-1,-38,-38,-38,-38,-38
S,Order,order of element,0,1,0,0,0,0,0,0,0,AlgQuatEnhElt,,-1,-38,-38,-38,-38,-38
S,Norm,Norm of the element of the enhanced semidirect product as an element of (Z/N)^x,0,1,0,0,0,0,0,0,0,AlgQuatEnhElt,,321,-38,-38,-38,-38,-38
S,PrimitiveElement,We consider the coset of x in B^x/Q^x: this coset has a unique representative b of squarefree and integral norm. Return b,0,1,0,0,0,0,0,0,0,18,,AlgQuatProjElt,-38,-38,-38,-38,-38
S,PrimitiveElement,We consider the coset of x in B>0^x/Q^x: this coset has a unique representative b of squarefree and integral norm. Return b,0,1,0,0,0,0,0,0,0,AlgQuatProjElt,,AlgQuatProjElt,-38,-38,-38,-38,-38
S,Parent,,0,1,0,0,0,0,0,0,0,AlgQuatOrdResElt,,AlgQuatOrdRes,-38,-38,-38,-38,-38
S,Parent,,0,1,0,0,0,0,0,0,0,AlgQuatProjElt,,AlgQuatProj,-38,-38,-38,-38,-38
S,Parent,,0,1,0,0,0,0,0,0,0,AlgQuatEnhElt,,AlgQuatProj,-38,-38,-38,-38,-38
S,quo,,0,2,0,0,0,0,0,0,0,148,,0,0,19,,AlgQuatOrdRes,-38,-38,-38,-38,-38
S,QuaternionAlgebraModuloScalars,Create B^x/F^x,0,1,0,0,0,0,0,0,0,17,,AlgQuatProj,-38,-38,-38,-38,-38
S,EnhancedSemidirectProduct,create Autmu(O)rtimesO^x or Autmu(O)rtimes(O/N)^x,0,1,0,0,0,0,0,0,0,19,,AlgQuatEnh,-38,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,AlgQuatOrdRes,,36,-1,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,AlgQuatProj,,36,-1,-38,-38,-38,-38
S,IsCoercible,,0,2,0,0,0,0,0,0,0,-1,,0,0,AlgQuatEnh,,36,-1,-38,-38,-38,-38
S,IsUnit,return whether x in O/N is a unit,0,1,0,0,0,0,0,0,0,AlgQuatOrdResElt,,36,-38,-38,-38,-38,-38
S,Norm,Norm of the element of the enhanced semidirect product as an element of (Z/N)^x,0,1,0,0,0,0,0,0,0,AlgQuatOrdResElt,,321,-38,-38,-38,-38,-38
S,Set,return the set of elements O/N,0,1,0,0,0,0,0,0,0,AlgQuatOrdRes,,-50,-38,-38,-38,-38,-38
S,Modulus,Return the level N of OmodN,0,1,0,0,0,0,0,0,0,AlgQuatOrdRes,,148,-38,-38,-38,-38,-38
S,UnitGroup,"return (O/N)^x as a permutation group G, the second value is the isomorphism G ->(O/N)^x",0,1,0,0,0,0,0,0,0,AlgQuatOrdRes,,178,175,-38,-38,-38,-38
S,UnitGroup,"return (O/N)^x as a permutation group G, the second value is the isomorphism G ->(O/N)^x",0,2,0,0,0,0,0,0,0,148,,0,0,19,,178,175,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,AlgQuatOrdResElt,,-38,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,AlgQuatOrdRes,,-38,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,AlgQuatProjElt,,-38,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,AlgQuatProj,,-38,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,AlgQuatEnhElt,,-38,-38,-38,-38,-38,-38
S,Print,,0,1,0,0,1,0,0,0,0,AlgQuatEnh,,-38,-38,-38,-38,-38,-38
