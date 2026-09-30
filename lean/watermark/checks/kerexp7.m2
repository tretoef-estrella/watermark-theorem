load "G7.m2";
K = gens ker G;
"kerG7.txt" << toString entries transpose K << close;
exit 0
