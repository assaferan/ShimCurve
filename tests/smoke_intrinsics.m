load "tests/test_helpers.m";

print "== smoke_intrinsics ==";

B := QuaternionAlgebra(6);
O := MaximalOrder(B);

tr, mu := HasPolarizedElementOfDegree(O, 1);
TestAssert(tr, "Has polarized element for (D,del)=(6,1)");

if tr then
  TestAssertEq(mu^2, -Discriminant(B), "Polarization relation mu^2 = -del*D");

  // Aut map should be defined and nontrivial enough to evaluate generators.
  Autmu := Aut(O, mu);
  A := Domain(Autmu);
  TestAssert(#Generators(A) gt 0, "Aut(O,mu) has at least one generator");
  for g in Generators(A) do
    w := Autmu(g);
    M := NormalizingElementToGL4modN(w, O, 3);
    TestAssert(Determinant(M) ne 0, "Aut image embeds in GL4 mod N");
  end for;

  // Unit group -> GL4 -> unit round-trip modulo N.
  Omod3 := quo(O, 3);
  U, Umap := UnitGroup(O, 3);
  if #Generators(U) gt 0 then
    u := Umap(U.1);
    Mu := UnitGroupToGL4modN(u, 3);
    ub := GL4ToUnitGroup(Mu, O);
    TestAssertEq(Omod3!ub, Omod3!u, "UnitGroupToGL4modN / GL4ToUnitGroup round-trip");
  else
    TestSkip("UnitGroup(O,3) returned no generators");
  end if;

  // Enhanced embedding should respect multiplication.
  Ocirc := EnhancedSemidirectProduct(O : N := 3);
  x := Omod3!2;
  e := Omod3!1;
  g1 := Ocirc!<1, x>;
  g2 := Ocirc!<1, e>;
  lhs := EnhancedElementInGL4modN(g1 * g2, 3);
  rhs := EnhancedElementInGL4modN(g1, 3) * EnhancedElementInGL4modN(g2, 3);
  TestAssertEq(lhs, rhs, "EnhancedElementInGL4modN is multiplicative");
end if;
