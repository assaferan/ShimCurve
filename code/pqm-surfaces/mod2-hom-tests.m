//magma ShimCurve/code/pqm-surfaces/mod2-hom-tests.m > ShimCurve/code/pqm-surfaces/log-mod2-hom-tests.txt &
//disown -h %1
/////////////////////////////
//We test some examples to see if the mod 2 enhanced representation works 
//and is bug free by computing the enhanced representation, embedding in GL4 and then 
//checking the image is conjugate to the mod 2 representation which Shiva's code computes
/////////////////////////////


Rx<x>:=PolynomialRing(Rationals());


print "LIPSCHITZ EXAMPLES";


for t in [19,20,21,22,24,25,26,27,28] do
    try 

        f:=x^5 + 8*x^4 + t*x^3 + 16*x^2-4*x;

        X:=HyperellipticCurve(f);
        prec:=30;
        CC:=ComplexField(prec);

        f:=HyperellipticPolynomials(X);
        XR:=RiemannSurface(f,2 : Precision:=prec);

        printf "The endomorphism package base point is %o\n", SmallBasePoint(X);
        printf "The magma base point is %o\n", XR`BasePoint;

        Galgrp_end,Galmap_end,rho_end:=EndomorphismRepresentationPQM(X : prec:=prec, quaternionorder:=[]);

        printf "The group name of the image of the endomorphism representation is %o\n",GroupName(Galgrp_end);
        printf "The norms of elements in the image of the endomorphism representation are %o\n", Set([ SquarefreeFactorization(Norm(rho_end(g)`element)) : g in Galgrp_end ]);
    

        GalM,mapM,rho2,O :=EnhancedRepresentationMod2PQM(X : prec:=prec);
        //create the permutation representation so we can work with the semidirect product as a group
        //perm_rep:=EnhancedPermutationRepresentationMod2(O,mu);

        rho2_image_gens := [ rho2(a) : a in Generators(GalM) ];
        rho2_image_GL4gens := [ GL(4,2)!EnhancedElementInGL4modN(a,2) : a in rho2_image_gens ];
        rho2_image_GL4grp := sub< GL(4,2) | rho2_image_GL4gens >;

        //check with Mod2EnhancedImage();
        mod2rep:=mod2Galoisimage(X);

        assert IsGLConjugate(mod2rep,rho2_image_GL4grp); 



        X;
        rho2_image_gens;
        rho2_image_GL4gens;
        Basis(O);
        Discriminant(O);
        printf "The group name of the image in GL(4,2) is %o\n",GroupName(rho2_image_GL4grp);
        print "==============================";
    catch e  
        X;
        e;
        print "==============================";
    end try;

end for;


/*
PQM6curves := 
[
[-x^5+4*x^4-10*x^3+8*x^2-2*x,0],
[x^5-3*x^4-2*x-1,x^3+x^2+x+1],
[3*x^5+3*x^4-4*x^3+3*x-1,0],
[x^6-4*x^5-2*x^4+12*x^3+8*x^2-8*x-8,0],
[2*x^6+9*x^5+6*x^4+2*x^3-6*x-4,0],
[-x^6-9*x^5-12*x^4-14*x^3-6*x^2+6*x+4,0],
[-x^6+6*x^5-20*x^3-12*x^2+8,0],
[-x^6-8*x^5-2*x^4+36*x^3-16*x^2+8*x+8,0],
[3*x^6-8*x^5-42*x^4-38*x^3+39*x^2+37*x-18,x^3+x^2+x+1],
[9*x^6-18*x^5-27*x^4+12*x^3-9*x^2-18*x+11,0],
[x^6+30*x^5+207*x^4+414*x^3+51*x^2+18*x+1,0],
[8*x^6+16*x^5-12*x^4-16*x^3-42*x^2+36*x+23,0],
[-x^6+12*x^5-42*x^4-48*x^3+276*x^2+432*x+136,0],
[-2*x^6+15*x^5-15*x^4-100*x^3+150*x^2+375*x+125,0],
[-x^6+15*x^5-90*x^4+100*x^3-75*x^2+31,1],
[x^6+12*x^5+78*x^4-16*x^3+12*x^2+48*x-24,0]
];

print "PQM6 EXAMPLES";

for elt in PQM6curves do  
    try
        C:=HyperellipticCurve(elt);
        X:=SimplifiedModel(C);
        prec:=30;
        CC:=ComplexField(prec);

        f:=HyperellipticPolynomials(X);
        XR:=RiemannSurface(f,2 : Precision:=prec);

        printf "The endomorphism package base point is %o\n", SmallBasePoint(X);
        printf "The magma base point is %o\n", XR`BasePoint;

        Galgrp_end,Galmap_end,rho_end:=EndomorphismRepresentationPQM(X : prec:=prec, quaternionorder:=[]);

        printf "The group name of the image of the endomorphism representation is %o\n",GroupName(Galgrp_end);
        printf "The norms of elements in the image of the endomorphism representation are %o\n", Set([ SquarefreeFactorization(Norm(rho_end(g)`element)) : g in Galgrp_end ]);
    

        GalM,mapM,rho2,O :=EnhancedRepresentationMod2PQM(X : prec:=prec);
        //create the permutation representation so we can work with the semidirect product as a group
        //perm_rep:=EnhancedPermutationRepresentationMod2(O,mu);

        rho2_image_gens := [ rho2(a) : a in Generators(GalM) ];
        rho2_image_GL4gens := [ GL(4,2)!EnhancedElementInGL4modN(a,2) : a in rho2_image_gens ];
        rho2_image_GL4grp := sub< GL(4,2) | rho2_image_GL4gens >;

        //check with Mod2EnhancedImage();
        mod2rep:=mod2Galoisimage(X);

        assert IsGLConjugate(mod2rep,rho2_image_GL4grp); 



        X;
        rho2_image_gens;
        rho2_image_GL4gens;
        Basis(O);
        Discriminant(O);
        printf "The group name of the image in GL(4,2) is %o\n",GroupName(rho2_image_GL4grp);
        print "==============================";
    catch e  
        X;
        e;
        print "==============================";
    end try;
end for;



PQM10curves:=
[
[-x^5-5*x^3-5*x,0],
[x^6-5*x^5+15*x^3-9*x,0],
[8*x^6-42*x^5+36*x^4+67*x^3-42*x^2-54*x-12,0],
[3*x^6+23*x^5-55*x^3+31*x-9,0],
[x^6-9*x^5+70*x^3-147*x-86,1],
[x^6-9*x^4-16*x^3+27*x^2+48*x+101,0],
[-63*x^6+229*x^5-555*x^3+477*x+189,0],
[-18*x^6+74*x^5-210*x^3+198*x+81,0],
[-8*x^6+8*x^5-20*x^4+64*x^3-34*x^2+2*x-21,0],
[2*x^6+25*x^5-560*x^3+4361*x-5145,x^3],
[-5*x^6-4*x^5-75*x^4+40*x^3-135*x^2-20*x-1,0],
[3*x^6-25*x^5+300*x^3-1125*x-844,1],
[-5*x^6-61*x^5-155*x^4+225*x^3+290*x^2-430*x+128,0],
[17*x^6-44*x^5+75*x^4+40*x^3-45*x^2+20*x+25,0],
[-x^6+16*x^5-55*x^4-64*x^3-299*x^2-208*x-117,0],
[8*x^6+32*x^5+12*x^4+32*x^3+198*x^2-248*x+97,0]
];


print "PQM10 EXAMPLES";

for elt in PQM10curves do  
    try
        C:=HyperellipticCurve(elt);
        X:=SimplifiedModel(C);
        prec:=30;
        CC:=ComplexField(prec);

        f:=HyperellipticPolynomials(X);
        XR:=RiemannSurface(f,2 : Precision:=prec);

        printf "The endomorphism package base point is %o\n", SmallBasePoint(X);
        printf "The magma base point is %o\n", XR`BasePoint;

        Galgrp_end,Galmap_end,rho_end:=EndomorphismRepresentationPQM(X : prec:=prec, quaternionorder:=[]);

        printf "The group name of the image of the endomorphism representation is %o\n",GroupName(Galgrp_end);
        printf "The norms of elements in the image of the endomorphism representation are %o\n", Set([ SquarefreeFactorization(Norm(rho_end(g)`element)) : g in Galgrp_end ]);
    

        GalM,mapM,rho2,O :=EnhancedRepresentationMod2PQM(X : prec:=prec);
        //create the permutation representation so we can work with the semidirect product as a group
        //perm_rep:=EnhancedPermutationRepresentationMod2(O,mu);

        rho2_image_gens := [ rho2(a) : a in Generators(GalM) ];
        rho2_image_GL4gens := [ GL(4,2)!EnhancedElementInGL4modN(a,2) : a in rho2_image_gens ];
        rho2_image_GL4grp := sub< GL(4,2) | rho2_image_GL4gens >;

        //check with Mod2EnhancedImage();
        mod2rep:=mod2Galoisimage(X);

        assert IsGLConjugate(mod2rep,rho2_image_GL4grp); 



        X;
        rho2_image_gens;
        rho2_image_GL4gens;
        Basis(O);
        Discriminant(O);
        printf "The group name of the image in GL(4,2) is %o\n",GroupName(rho2_image_GL4grp);
        print "==============================";
    catch e  
        X;
        e;
        print "==============================";
    end try;
end for;
