load "G5.m2";
K = gens ker G;
"kerG5.txt" << toString entries transpose K << close;
exit 0
