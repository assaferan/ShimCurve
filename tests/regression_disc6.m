AttachSpec("spec");
SetVerbose("ShimuraCurves", 1);

D := 6;
B := QuaternionAlgebra(D);
O := MaximalOrder(B);
for deg in Divisors(D) do
  tr,mu := HasPolarizedElementOfDegree(O,deg);
  if not tr then continue; end if;
  Ns := [1,2,3,4,6];
  print "deg = ", deg;
  time subs := GenerateDataForGerbiestSurjectiveH(O,mu,Ns);
  WriteHeaderAndSubgroupsDataToFile(subs, O);
end for;