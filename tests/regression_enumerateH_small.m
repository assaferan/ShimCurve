load "tests/test_helpers.m";

print "== regression_enumerateH_small ==";

// Keep this case reasonably small while still exercising the full pipeline.
D := 6;
del := 1;
N := 3;

B := QuaternionAlgebra(D);
O := MaximalOrder(B);
tr, mu := HasPolarizedElementOfDegree(O, del);
TestAssert(tr, "Polarized element exists for regression case");

if tr then
  calc := GenerateDataForGerbiestSurjectiveH(O, mu, N);
  TestAssert(#calc gt 0, "GenerateDataForGerbiestSurjectiveH produced records");

  top := Minimum(#calc, 10);
  for i in [1..top] do
    s := calc[i];
    if assigned s`ram_data_elts then
      TestAssertEq(EnhancedGenus(s`ram_data_elts), s`genus, Sprintf("Genus from ramification matches record (%o)", i));
    else
      TestSkip(Sprintf("Record %o has no ram_data_elts field", i));
    end if;
  end for;
end if;
