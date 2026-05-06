load "tests/test_helpers.m";

procedure CleanupGeneraFixture(fn::MonStgElt);
  System(Sprintf("rm -f %o", fn));
end procedure;

print "== data_roundtrip ==";

// Create a deterministic legacy-format fixture that GeneraTableToRecords can parse.
D := 99991;
del := 7;
N := 11;
filename := Sprintf("data/genera-tables/genera-D%o-deg%o-N%o.m", D, del, N);

try
  f := Open(filename, "w");
  Puts(f, "fixture header");
  Puts(f, "0?12?24?[2]?C1?{1}?true?<g1>?[1,2,3]");
  Puts(f, "1?18?36?[2,2]?D2?{1,6}?false?<g2>?[3,2,1]");
  delete f;

  recs := GeneraTableToRecords(D, del, N : sort := false);
  TestAssertEq(#recs, 2, "Parser reads two fixture records");
  TestAssertEq(recs[1]`genus, 0, "First fixture genus parsed");
  TestAssertEq(recs[2]`fuchsindex, 18, "Second fixture fuchsindex parsed");
  TestAssertEq(recs[2]`torsioninvariants, [2,2], "Second fixture torsion parsed");

  g0 := GeneraTableToRecords(D, del, N : genus := 0, sort := false);
  TestAssertEq(#g0, 1, "Genus filter keeps only genus 0 fixture record");
  TestAssert(forall{ r : r in g0 | r`genus eq 0 }, "Genus filter output is consistent");
catch e
  CleanupGeneraFixture(filename);
  error e;
end try;

CleanupGeneraFixture(filename);
