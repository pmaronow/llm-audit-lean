# Blind reading of SAP.P004c.T34

Written before opening claims.json or record.json. Source: SAP/P004c/Challenge/Part1.lean:26-34 and every human-readable declaration in closure.json (SAP/P004c/Defs/Part1.lean, Part2.lean, Part5.lean). Generated internal proof auxiliaries at line 0 have no independent prose definition.

## SAP.P004c.T34 (P004-T34)

The statement is a conjunction of four separate claims.

1. For every natural sample size N>0, binary assignment z: Fin N -> Bool, real probability p with 0<p<1, real cross-sum scalar S, and strictly positive treated-arm count T=sum_i 1{z_i=true}, the absolute difference between the two normalized expressions is
|N[(NS)/T^2-(NS)/(N^2 p^2)]|=|N^2/T^2-1/p^2| |S|.
It also factors the denominator error exactly as
|N^2/T^2-1/p^2|=|[(T/N-p)(T/N+p)]/[p^2(T/N)^2]|.
These are algebraic identities for every S, not just a kernel cross-sum.

2. For every N>0, assignment z, real node residuals e_i, real distance array D_ij with D_ij>=0, bandwidth b>0, real kernel K and real bound Kmax such that |K(t)|<=Kmax for all t>=0 and K(t)=0 when t>1, the absolute value of (1/N) times the off-diagonal ordered-pair sum of bit(z_i) bit(z_j) e_i e_j K(D_ij/b) is at most Kmax times M^2 times dmax. Here M=sup_i |e_i|, the finite sample maximum; dmax is max_i of the cardinality of the closed ball {j:D_ij<=b}. The pair sum excludes j=i. There is no triangle or symmetry assumption on D and no statistical interpretation of e built into this clause. Because K vanishes outside radius b and each i has at most dmax terms, it is a deterministic finite bound.

3. For each fixed 0<p<1, assign each of N binary coordinates independently with common Bernoulli probability p. The denominatorError(p,N,z) is |N^2/T^2-1/p^2| when T>0 and zero when T=0. It is BigOp at rate 1/sqrt(N): for every epsilon>0 there is C>0 such that, for all sufficiently large N, the Bernoulli probability of C*(1/sqrt(N))<|denominatorError(p,N,z)| is below epsilon. The definition of probability is the finite sum over all assignments of the product of coordinate coin weights, and BigOp is this explicit in-probability tail condition.

4. Pure scalar arithmetic for N=8, T=5, p=1/2 and S=-1/4 asserts |(64/25-4)|*|-1/4|=9/25, the corresponding signed product is -9/25, and 9/25 <= -9/25 is false. The statement does not assert there exists an eight-node assignment, residual vector or kernel that produces S=-1/4.

Junk-value analysis: The first identities require T>0, N>0 and p>0, so all denominators have their intended nonzero meaning. The kernel bound requires N>0 and b>0, so N and D/b are safe; p is not present there. Its M is real sSup of |e_i| on nonempty finite Fin N, hence an attained finite maximum, not an empty or unbounded supremum. The maxDegree finite-set sup is similarly finite. In the third clause denominatorError explicitly chooses zero at T=0, avoiding a reciprocal of zero; that convention affects the random variable only on the empty-treated event, whose probability (1-p)^N vanishes as N grows. At N=0, sqrt(0) inverse is Lean's totalized zero, but BigOp is an eventual atTop statement and so does not depend on it. The design product is a genuine probability for p in (0,1); there are no nonintegrable Bochner means, toReal infinity, log/rpow, or partial-function defaults in this closure. Natural-to-real casts of N and treated count are harmless under N>0 and T>0.
