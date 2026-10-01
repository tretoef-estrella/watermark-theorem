-- Cold reader's own M2 script: Hilbert function of the ring in (C) and the formula of Theorem 3(b).
-- usage: M2 --script cold_ringC.m2 k p char     (char = p or 0)
clK = value (scriptCommandLine#1); clP = value (scriptCommandLine#2); clCh = value (scriptCommandLine#3);
clN = 2*clK+2;
clF = if clCh == 0 then QQ else ZZ/clCh;
clR = clF[clX_0..clX_(clN-1)];
clT = clR[clTT];
clE = product(clN, i -> 1 + clTT*sub(clX_i, clT));
clCo = j -> sub((coefficients(clE, Monomials => {clTT^j}))#1_(0,0), clR);
clI = ideal(apply(select(toList(1..clN), j -> odd j), clCo)) + ideal(apply(clN, i -> clX_i^(clP-1)));
clTop = clN*(clP-2);
clA = apply(clTop+1, d -> hilbertFunction(d, module clI));   -- HF of the ideal as a module
clS = apply(clTop+1, d -> binomial(d+clN-1, clN-1));
clH = apply(clTop+1, d -> hilbertFunction(d, clR/clI));
clDim = sum clH;
clLast = max select(toList(0..clTop), d -> clH#d != 0);
clB = clDim // (clP-1);
clKap = 2*clK*(clP-2)-1;
clE1 = 1 + clKap*clB - 2*sum(clTop+1, i -> (i // (clP-1))*clH#i);
clh = j -> sum(select(toList(0..j), i -> (j-i) % (clP-1) == 0), i -> clH#i);
clE2 = 1 - clB + 2*sum(clK*(clP-2), j -> clh j);
<< "k=" << clK << " p=" << clP << " char=" << clCh << "  dim=" << clDim << "  top degree=" << clLast << " (expected " << (clK+1)*(clP-2) << ")" << endl;
<< "a(i) = " << toString take(clH, clLast+1) << endl;
<< "h(j) = " << toString apply(clK*(clP-2)+1, clh) << "  B=" << clB << endl;
<< "E first form = " << clE1 << "   E second form = " << clE2 << endl << "COLD-DONE" << endl;
