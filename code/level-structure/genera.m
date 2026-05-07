

intrinsic EnhancedGenus(sigma::SeqEnum) -> RngIntElt
  {Compute genus from permutation triple
   f:X -> Y. 2gX-2 = deg(f)*(2gY-2) + sum_x\inX (ex -1). 
   ex is the ramification degree of x. An element of S_n acts on sheets of the cover. 
  x is ramified if x is sent to another point under the action of an isotropy subgroup,
  i.e. the cycle type corresponding to x has length >1. The length is the ramification degree.}
  d := Degree(Parent(sigma[1]));
  // Riemann-Hurwitz formula
  rhs := -2*d + &+[ &+[ e[2]*(e[1]-1) : e in CycleStructure(sig) ] : sig in sigma ];
  assert rhs mod 2 eq 0;
  g := Integers()!((rhs+2)/2);
  return g;
end intrinsic;

intrinsic EnhancedEllipticPoints(sigma::SeqEnum) -> Assoc
{Only works for discriminant 6!}
  ells := AssociativeArray([2,3,4,6]);
  for n in [2,3,4,6] do
      ells[n] := 0;
  end for;
  // sigma is ordered as the cycles above 2, 4, 6
  bottom := [2,4,6];
  for i->sig in sigma do
      for e in CycleStructure(sig) do
	  n := bottom[i] div e[1];
	  if (n gt 1) then
	      assert IsDefined(ells, n);
	      ells[n] +:= e[2];
	  end if;
      end for;
  end for;
  return ells;
end intrinsic;



