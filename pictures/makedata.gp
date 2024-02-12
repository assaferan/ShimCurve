
/*Processes the vertices from the file algdat.dat*/
loadcurvefromfile() = {
  my(v);
  v = readvec("algdat.dat");
  return(processvertices(v[1], v[2], v[3]));
}



/*Inputs 
ab: pair [a, b]
Obasis: vector of basis elements of the (maximal) order O where each element is of the form [e, f, g, h] representing a basis element of e+fi+gj+hk (maximal order)
norms: vector of the norms of elements of Aut_{+/- mu}(O). Must be a set of positive integers that are divisors of D = discriminant of A.

Output: fundamental domain for the correct Shimura curve.
*/

processdomain(ab, Obasis, norms) = {
  my(F, A, Or, X, alnorms, mat);
  F = nfinit(y);
  A = alginit(F, ab);
  Or = matrix(4, 4);
  for (i = 1, 4, Or[,i] = alg1ijktobasis(A, Obasis[i]));/*Make the order*/
  X = afuchinit(A, Or, 3);/*Compute the full domain.*/
  alnorms = afuchnormalizernorms(X)[2];/*Only relevant entry.*/
  mat = matrix(#alnorms, #norms);
  for (i = 1, #norms,
    for (j = 1, #alnorms,
      if (norms[i] % alnorms[j] == 0, mat[j, i] = 1);
    );
  );
  X = afuchnewtype(X, mat);
  return(X);
}


