load "tests/test_helpers.m";

print "== regression_mod2_image ==";

Rx<x> := PolynomialRing(Rationals());

// One curated curve from the existing mod2-hom test set.
f := x^5 + 8*x^4 + 19*x^3 + 16*x^2 - 4*x;
X := HyperellipticCurve(f);

// timing_steps:=true prints cumulative CPU after each phase of Mod2GaloisMapPQM (locate stalls).
GalM, mapM, rho2, O := EnhancedRepresentationMod2PQM(X : prec := 30, timing_steps := true);
rho2_image_gens := [ rho2(a) : a in Generators(GalM) ];
rho2_image_GL4gens := [ GL(4,2)!EnhancedElementInGL4modN(a, 2) : a in rho2_image_gens ];
rho2_image_GL4grp := sub< GL(4,2) | rho2_image_GL4gens >;

mod2rep := mod2Galoisimage(X);
TestAssert(IsGLConjugate(mod2rep, rho2_image_GL4grp), "Enhanced mod-2 image is GL-conjugate to mod2Galoisimage");

