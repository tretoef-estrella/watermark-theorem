\\ c3.gp -- read after data_m{m}.gp. Exact integer lattice computations (PARI/gp).
n = #G; vm(x) = if(x==0, "0", valuation(x, m));
K = matkerint(G);                         \\ Z-basis of K = ker G (saturated)
printf("m=%d n=%d rank G=%d  rank K=%d (paper 9m-7=%d)\n", m, n, matrank(G), #K, 9*m-7);
S = SATg~;                                \\ columns = s_Z(basis of Src_Z)
printf("  rank SAT=%d; G*SAT==0: %d\n", matrank(S), G*S == matrix(n, #S));
C = matinverseimage(K, S);                \\ S = K*C
printf("  C integral: %d; [K:SAT]=|det C| = m^%s (paper 12)\n", denominator(C)==1, vm(abs(matdet(C))));
L = Lg~;
printf("  [Z^P:L_fam] = m^%s (paper (m^2+m+2)/2=%d)\n", vm(abs(matdet(L))), (m^2+m+2)/2);
Fb = Fr~;
printf("  rank F=%d (paper %d); F cap K = 0: %d\n", matrank(Fb), 3*(m-2)*(m-1)+1, matrank(concat(Fb,K)) == #Fb + #K);
iFK = abs(matdet(concat(Fb, K)));
printf("  [A:F+K] = m^%s (paper 3(m^2+m+2)/2-12=%d); other primes: %d\n", vm(iFK), 3*(m^2+m+2)/2-12, iFK/m^valuation(iFK,m));
GF = Fb~*G*Fb;
dGF = matdet(GF);
printf("  det Gram(F basis c) = %s m^%s (paper m^%d)\n", sign(dGF), vm(abs(dGF)), 3*(m-2)*(2*m-1)+3);
dV = dGF / iFK^2;
printf("  paper route: det Gram(V) = det Gram_c/[V:phi F]^2 = %s m^%s; paper m^%d\n", sign(dV), vm(abs(dV)), 3*(m-3)^2);
\\ independent route: Smith normal form of G
D = matsnf(G); nz = select(x -> x != 0, D);
pr = prod(i=1, #nz, nz[i]);
printf("  INDEPENDENT (SNF of G): #nonzero divisors=%d, product = m^%s, other primes: %d\n", #nz, vm(pr), pr/m^valuation(pr,m));
\\ (|det Gram V| = product of the non-zero elementary divisors of G, because K is saturated: A = K + C, G ~ 0 + Gram(V).)
\\ addendum (08:09): exact equalities, not only valuations
printf("  EXACT: |det L|==m^((m^2+m+2)/2): %d; det Gram_c==m^(3(m-2)(2m-1)+3): %d; det Gram V == m^(3(m-3)^2): %d; prod SNF == m^(3(m-3)^2): %d\n", abs(matdet(L))==m^((m^2+m+2)/2), dGF==m^(3*(m-2)*(2*m-1)+3), dV==m^(3*(m-3)^2), pr==m^(3*(m-3)^2));
