/ http://rosalind.info/problems/iprb/    (mendel's first law (probability))
/ (assume D and R are dominant and recessive forms of an allele.)

kmn: 27    17    27                      / k organisms have DD,  m have DR,  n have RR
prD: 1.0  0.5  0.0                       / probability of inheriting D from this parent.
tpop: %% +/kmn                           / total population

iden: {i:!x; i=/:i}                      / x -> x*x identity matrix

pMom: kmn % tpop                         / P(choosing mother from each group.) (1x3)
pDad: {+(0|x-iden[#x]) % tpop-1} kmn     / P(choosing father after mother is removed) (3x3)
pDom: 1-{x */: x} 1-prD                  / P(either has D) = ~(neither has D) (3x3)

+/+/ pDom * pMom * pDad                  / final answer
