-- Cold reader: Lemma 4.4. Hilbert function of S/(e_odd(x_0..x_{N-1}), x_nu^{p-1} - x_0^{p-1}) with x_0 = -(x_1+...+x_r).
clK = value (scriptCommandLine#1); clP = value (scriptCommandLine#2);
clN = 2*clK+2; clRr = clN-1;
clR = ZZ/clP[clX_1..clX_clRr];
clX0 = -sum(clRr, i -> clX_(i+1));
clVars = {clX0} | apply(clRr, i -> clX_(i+1));
clT = clR[clTT];
clE = product(clVars, v -> 1 + clTT*sub(v, clT));
clCo = j -> sub((coefficients(clE, Monomials => {clTT^j}))#1_(0,0), clR);
clI = ideal(apply(select(toList(3..clN-1), j -> odd j), clCo)) + ideal(apply(clRr, i -> clX_(i+1)^(clP-1) - clX0^(clP-1)));
clTop = (clK+1)*(clP-2) + 3;
<< "k=" << clK << " p=" << clP << "  HF of S/(generators of Lemma 4.4), degrees 0.." << clTop << ": " << toString apply(clTop+1, d -> hilbertFunction(d, clR/clI)) << endl;
<< "   dim = " << dim(clR/clI) << ", degree = " << degree(clR/clI) << ", e_1(x_0..) = " << toString clCo(1) << endl << "COLD-DONE" << endl;
