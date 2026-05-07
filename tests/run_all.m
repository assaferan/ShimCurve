AttachSpec("spec");
AttachSpec("../CHIMP/CHIMP.spec");
load "tests/test_helpers.m";

TestReset();
print "";
print "Running tests/smoke_intrinsics.m";
load "tests/smoke_intrinsics.m";

print "";
print "Running tests/regression_enumerateH_small.m";
load "tests/regression_enumerateH_small.m";

print "";
print "Running tests/data_roundtrip.m";
load "tests/data_roundtrip.m";

print "";
print "Running tests/regression_mod2_image.m";
load "tests/regression_mod2_image.m";

print "";
printf "Test run complete: %o failure(s), %o skip(s)\n", TestFailureCount(), TestSkipCount();

if TestFailureCount() gt 0 then
  error Sprintf("ShimCurve tests failed with %o failure(s).", TestFailureCount());
end if;
