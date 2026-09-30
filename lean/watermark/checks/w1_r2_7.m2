load "G7.m2";
m = 7; n = numRows G;
K = gens kernel G;   -- saturated kernel over ZZ
print("m=" | toString m | " rank K = " | toString numColumns K | " (want " | toString(9*m-7) | ")");
fam = j -> matrix{toList apply(n, i -> if floor(i/(m*m)) == j then 1 else 0)};
augs = apply(3, j -> fam j * K);
tot = augs#0 + augs#1 + augs#2;
print("sum of augs zero on K: " | toString(tot == 0));
print("m | aug_j on K: " | toString(all(3, j -> all(flatten entries augs#j, a -> a % m == 0))));
half = matrix{toList apply(n, i -> if i < (m*m) and (i % m) < 2 then 1 else 0)};
print("control (partial fibre functional divisible by m on K?): " | toString(all(flatten entries(half*K), a -> a % m == 0)));
(D,P,Q) = smithNormalForm G;
d = select(apply(n, i -> abs D_(i,i)), x -> x != 0);
print("rank V = " | toString(#d) | " (want " | toString(3*(m-1)*(m-2)+1) | ")");
prodd = product d;
print("prod nonzero elementary divisors = m^" | toString(if prodd == 1 then 0 else (log prodd)/(log m)) | " exact? " | toString(prodd == m^(3*(m-3)^2)));
print "FIN-OK";
exit 0;
