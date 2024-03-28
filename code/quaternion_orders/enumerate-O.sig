177,0
S,LMFDBLabel,"Given a quaternion order O, generate its LMFDB label",0,1,0,0,0,0,0,0,0,19,,298,-38,-38,-38,-38,-38
S,Area,Compute the Area of X_O,0,1,0,0,0,0,0,0,0,19,,267,-38,-38,-38,-38,-38
S,LMFDBRowEntry,"return the row of data associated to O which will become part of the LMFDB schema. The schema is (for O maximal): LMFDBLabel(O) ? a ? b ? disc(O) ? disc(B) ? coefficients of Basis(O) in terms of i,j,k scaled to be integral ? 1/b where b multiplied by the corresponding element in the previous column is the basis element",0,1,0,0,0,0,0,0,0,19,,298,-38,-38,-38,-38,-38
S,EnumerateO,loop over maximal orders of discriminant up to bound and output their lmfdb row entry,0,1,0,0,0,0,0,0,0,148,,-1,-38,-38,-38,-38,-38
S,LMFDBLabel,"Given a quaternion order O, generate its LMFDB label",0,2,0,0,0,0,0,0,0,18,,0,0,19,,298,-38,-38,-38,-38,-38
S,LMFDBRowEntry,"the row of data that makes up the LMFDB table associated to (O,mu)",0,2,0,0,0,0,0,0,0,18,,0,0,19,,298,-38,-38,-38,-38,-38
S,EnumerateOmu,"loop over polarized maximal orders (O,mu) of discriminant up to boundO and polarization up to boundmu and output their lmfdb row entry",0,1,0,0,0,0,0,0,0,148,,-1,-38,-38,-38,-38,-38
