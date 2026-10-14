\\ c4.gp -- read after data_m{m}.gp: Smith profile of G.
D = matsnf(G); n = #G;
c0 = #select(x->x==0, D); c1 = #select(x->x==1, D); cm = #select(x->x==m, D); cm2 = #select(x->x==m^2, D);
oth = n - c0 - c1 - cm - cm2;
printf("m=%d Smith profile of G: 0^%d 1^%d %d^%d %d^%d, other=%d\n", m, c0, c1, m, cm, m^2, cm2, oth);
if(m==5, printf("   Theorem 2 (m=5): 1^26 5^10 25^1\n"), printf("   Theorem 2: 1^%d %d^%d %d^%d\n", 12*(m-3), m, 3*m^2-24*m+59, m^2, 3*m-16));
