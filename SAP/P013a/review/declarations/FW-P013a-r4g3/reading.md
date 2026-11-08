# Blind reading

This file was written before opening `claims.json` or `record.json`. Source locations and the dependency list come from `closure.json`. I read all listed source declarations, constructors and projections, and compiled `scratch/BlindChecks.lean` to print every listed generated `_proof_` declaration. Those auxiliaries certify numeral instances, or positivity and normalization of product laws; they add no substantive assumptions.

## SAP.P013a.T11

Sources: `Challenge/Part2.lean:27–29`, `Defs/Part6.lean:124–134`, `Defs/Part4.lean:83–90` (all paths under `SAP/P013a/`).

For every pair of finite sets (U,B\subseteq\mathbb N), and then every (i,n\in\mathbb N), assume, in order: (i\in U), (B\subseteq U), (i\notin B), \\(|B|=39\\), (1\le n), and (n\le |U|-39), where this last subtraction is natural-number subtraction. Put (M=|U|). Sample uniformly from all (n)-element subsets (S\subseteq U). Define

- (p=\#\{S\subseteq U:|S|=n,\ i\in S,\ S\cap B=\varnothing\}/\binom Mn);
- (q=\#\{S\subseteq U:|S|=n,\ i\notin S,\ S\cap B=\varnothing\}/\binom Mn).

The numerators are finite-set cardinalities cast to real numbers; the denominator is the natural binomial coefficient cast to a real number. The theorem concludes all of

\[
p=\frac{\binom{M-40}{n-1}}{\binom Mn},\qquad
q=\frac{\binom{M-40}{n}}{\binom Mn},\qquad
q=\frac{M-39-n}{n}p.
\]

The numerator (M-39-n) in the third formula is real subtraction, while the binomial arguments use natural subtraction. It further concludes this implication: if (M\le 10n+5), then (a) (q\le9p); (b) if (p\le27/40000), then both (q\le243/40000) and (q<1/100); and (c) if (1/100\le q), then both (1/900\le p) and (27/40000<p). The three counting identities hold without the additional (M\le10n+5) hypothesis. Nothing specifies particular numerical values for (M,n), or an actual network beyond this focal vertex and its 39 distinct neighbors.

The docstring describes this as exact complete-randomization counting demonstrating incompatibility of two probability descriptions.

Junk and boundary checks: `completeProbability` would return zero if its binomial denominator were zero, since real division by zero is zero in Lean. Here (B\cup\{i\}\subseteq U) has 40 elements, so (M\ge40), and (1\le n\le M-39\le M) makes \(\binom Mn>0\). Hence the probability is genuine. The natural subtractions (M-40), (M-39), and (n-1) are not truncated in this domain. A binomial numerator can genuinely be zero, for example (q=0) at (n=M-39). The real denominator (n) is nonzero. The empty-neighbor or empty-population cases contradict the hypotheses. All casts are exact nonnegative integer-to-real casts. No logs, square roots, real powers, integrals, extended-real conversions, extrema, limits, or partial functions occur.

## SAP.P013a.T12

Sources: `Challenge/Part2.lean:31–33`, `Defs/Part6.lean:136–151`, `Defs/Part1.lean:14–19,29–50`, `Defs/Part2.lean:57–84`.

The statement is the conjunction of two negations of universal assertions; it does not explicitly supply witnesses, and the witnesses to the two negations need not coincide.

Here is the full common domain, unfolded. First universally choose a small type (\Omega) with a finite enumeration, natural numbers (N,K), and real weights (w_z>0) for every (z\in\Omega), with \(\sum_z w_z=1\). A population consists of any map (D:\Omega\times\{0,\ldots,N-1\}\to\{0,\ldots,K-1\}) and any fixed real table (y_i(d)). Then assume (N>0); choose an exposure (d\in\{0,\ldots,K-1\}); assume, for every (i),

\[
0<\pi_i=\sum_z w_z\mathbf1\{D(z,i)=d\}<1.
\]

Then universally choose (R\in\mathbb N) and (p_0\in\mathbb R), assume both (\exists i,\pi_i=p_0) and (\forall i,p_0\le\pi_i), and assume the population total \(T=\sum_i y_i(d)\ne0\). No sign restriction is imposed on outcomes, and there is no (R\ge1) condition.

Choose independent (Z,Z_1,\ldots,Z_R\) all with weights (w). More precisely the finite space is \(\Omega\times(\operatorname{Fin}R\to\Omega)\), with weight \(w_z\prod_{r<R}w_{z_r}\). Thus the replicates are mutually independent and independent of the actual assignment. Put

\[
C_i=\sum_{r<R}\mathbf1\{D(Z_r,i)=d\},\quad
\widehat\pi_i=\frac{C_i+1}{R+1},\quad
\widehat T=\sum_i\frac{\mathbf1\{D(Z,i)=d\}\,y_i(D(Z,i))}{\widehat\pi_i}.
\]

Expectation here means precisely the weighted finite sum over the displayed product space. The observed outcome is (y_i(D(Z,i))); on the event selected by its accompanying indicator it equals (y_i(d)).

The first negated universal assertion is that, for all data and hypotheses above,
\[
\left|\frac{E\widehat T-T}{T}\right|\le(1-p_0)^{R+1}.
\]

The second uses the same common quantifier order and hypotheses, then universally chooses (b\in\mathbb R), assumes (b>0) and
\[
R\ge\frac{\log b}{\log(1-p_0)}-1,
\]
and asserts \( |(E\widehat T-T)/T|\le b\). T12 asserts that each universal assertion fails. The docstring calls these refutations of the unrestricted relative-bias bound and logarithmic replicate guarantee on the nonzero-total domain.

Junk and boundary checks: normalization excludes empty (\Omega). (N>0) excludes an empty population; choosing (d) excludes (K=0), and strict marginal positivity plus the upper bound actually excludes a one-label population. The minimum is attained by an explicit existential hypothesis, and yields (0<p_0<1). Thus (0<1-p_0<1) and \(\log(1-p_0)<0\); its use as a denominator is legitimate. (b>0) puts \(\log b\) in its usual domain. (T\ne0) rules out a zero relative-bias denominator. Each (C_i\ge0), and (R+1>0), so every smoothed probability is positive. All exponentiation here has a natural exponent. (R=0) is allowed: the replicate-function space then has one empty function, its product weight is one, the replicate counts are zero, and each smoothed probability is one. This is a meaningful special estimator but may matter to the claimed scope. All moments are finite real sums; no nonintegrability conventions occur. There are no truncated subtractions, extended-real conversions, extrema or limits.

## SAP.P013a.T13

Sources: `Challenge/Part2.lean:35–37`, `Defs/Part6.lean:153–170`, `Defs/Part1.lean:14–24,29–65`. Its listed generated numeral proof is also printed in the blind check.

This is a conjunction of two independently quantified finite-experiment assertions. In each, universally choose an arbitrary finite type (\Omega), a positive normalized real weight function (w), natural (N,K), and arbitrary maps (D(z,i)\in\operatorname{Fin}K) and (y_i(d)\in\mathbb R), for (i\in\operatorname{Fin}N). Assume (N>0). For notation define

\[
I_i^d(z)=\mathbf1\{D(z,i)=d\},\quad
\pi_i^d=\sum_z w_z I_i^d(z),\quad
\pi_{ij}^{de}=\sum_z w_z I_i^d(z)I_j^e(z),\quad
T_d=\sum_i y_i(d),\quad
H_d(z)=\sum_i I_i^d(z)y_i(d)/\pi_i^d.
\]

For any real functions (X,Y\) on (\Omega), (EX=\sum_z w_zX(z)), \(\operatorname{Cov}(X,Y)=E(XY)-(EX)(EY)\), and \(\operatorname{Var}(X)=E(X^2)-(EX)^2\). These are genuine expectation, covariance, and variance for the stated normalized finite probability law.

The first assertion then universally chooses (d\in\operatorname{Fin}K), assumes (0<\pi_i^d<1) for every (i), and concludes

\[
EH_d=T_d,\qquad
\operatorname{Var}(H_d)=\sum_i\pi_i^d(1-\pi_i^d)\left(\frac{y_i(d)}{\pi_i^d}\right)^2+
\sum_i\sum_{j\ne i}(\pi_{ij}^{dd}-\pi_i^d\pi_j^d)\frac{y_i(d)}{\pi_i^d}\frac{y_j(d)}{\pi_j^d}.
\]

The second assertion independently chooses all experiment data again, then exposures (d,e\), assumes (d\ne e), (0<\pi_i^d<1) for every (i), and (0<\pi_i^e<1) for every (i). With \(\widehat\tau=(H_d-H_e)/N\) and \(\tau=T_d/N-T_e/N\), it concludes

\[
E\widehat\tau=\tau,\qquad
\operatorname{Var}(\widehat\tau)=\frac{\operatorname{Var}(H_d)+\operatorname{Var}(H_e)-2\operatorname{Cov}(H_d,H_e)}{N^2},
\]
\[
\operatorname{Cov}(H_d,H_e)=\sum_i\sum_{j\ne i}(\pi_{ij}^{de}-\pi_i^d\pi_j^e)\frac{y_i(d)}{\pi_i^d}\frac{y_j(e)}{\pi_j^e}-\sum_i y_i(d)y_i(e).
\]

All double sums over distinct units are ordered. There are no restrictions on signs, independence across units, or joint exposure positivity. The docstring describes unbiasedness and the variance/covariance formulas for the total and contrast.

Junk and boundary checks: (N>0) and positive marginals guard every division by (N,N^2,\pi_i^d,\pi_i^e). Zero joint probabilities cause no division in this theorem. The zero-size or zero-label cases cannot instantiate its hypotheses; a singleton population is possible and its off-diagonal sums are legitimately empty. A design cannot live on an empty assignment type because its weights must sum to one. Finite real sums make all moments exist. There are no logs, square roots, real powers, natural subtractions, extended-real conversions, extrema, limits, or default partial-function values.

## SAP.P013a.T14

Sources: `Challenge/Part2.lean:39–45`, `Defs/WholeW1.lean:161–218`, `Defs/Part6.lean:172–178`, `Defs/Part1.lean:14–24,29–41,46–47,58–59,67–84`. The structure fields, constructor, and listed generated numeral proofs have also been inspected.

The actual theorem type is `T14WholeStatement`, a conjunction of an exposure assertion and a separate general binary inclusion assertion.

For the exposure assertion, universally choose a finite assignment type (\Omega), strictly positive real weights (w_z) summing to one, natural (N,K), arbitrary exposures (D(z,i)\in\operatorname{Fin}K), and fixed outcomes (y_i(d)\in\mathbb R). Assume (N>0); then choose (d\in\operatorname{Fin}K) and assume (0<\pi_i<1) for every (i). Here

\[
I_i(z)=\mathbf1\{D(z,i)=d\},\quad \pi_i=\sum_z w_zI_i(z),\quad \pi_{ij}=\sum_z w_zI_i(z)I_j(z),\quad H(z)=\sum_i I_i(z)y_i/\pi_i,
\]
where (y_i=y_i(d)), expectation is \(\sum_z w_zX(z)\), and variance is \(E(X^2)-(EX)^2\). Define, literally using real-field totalized division,

\[
V_0(z)=\sum_i I_i(z)(1-\pi_i)(y_i/\pi_i)^2+
\sum_i\sum_{j\ne i}I_i(z)I_j(z)\frac{\pi_{ij}-\pi_i\pi_j}{\pi_{ij}}\frac{y_i}{\pi_i}\frac{y_j}{\pi_j},
\]
\[
A=\sum_i\sum_{j\ne i:\ \pi_{ij}=0}y_i y_j,\qquad
C_2(z)=\sum_i\sum_{j\ne i:\ \pi_{ij}=0}\left(\frac{I_i(z)y_i^2}{2\pi_i}+\frac{I_j(z)y_j^2}{2\pi_j}\right).
\]

It concludes: if (\pi_{ij}>0) for every (i,j), including diagonal pairs, then (EV_0=\operatorname{Var}(H)); always (EV_0=\operatorname{Var}(H)+A); and always \(\operatorname{Var}(H)\le E(V_0+C_2)\).

The second assertion independently universally chooses small finite types (U,\Omega), a real weight function (w_z\ge0\) with \(\sum_z w_z=1\), and arbitrary Boolean inclusion values (s(z,i)\) for each (z\in\Omega,i\in U). Thus zero-weight atoms and certainty inclusions are allowed. Assume (\forall i\in U,\pi_i>0\), and then universally choose (y:U\to\mathbb R). Define

\[
I_i(z)=\begin{cases}1&s(z,i)=\mathrm{true},\\0&s(z,i)=\mathrm{false},\end{cases}\quad
EX=\sum_z w_zX(z),\quad \pi_i=EI_i,\quad \pi_{ij}=E(I_iI_j),
\]
\[
H(z)=\sum_i I_i(z)y_i/\pi_i,\quad \operatorname{Var}(X)=\sum_z w_z(X(z)-EX)^2,
\]
\[
V_0(z)=\sum_{i\in U}\sum_{j\in U:\ \pi_{ij}>0}I_i(z)I_j(z)\frac{\pi_{ij}-\pi_i\pi_j}{\pi_{ij}}\frac{y_i}{\pi_i}\frac{y_j}{\pi_j},
\]
\[
A=\sum_i\sum_{j\ne i:\ \pi_{ij}=0}y_i y_j,\qquad
C_2(z)=\sum_i\sum_{j\ne i:\ \pi_{ij}=0}\left(\frac{I_i(z)y_i^2}{2\pi_i}+\frac{I_j(z)y_j^2}{2\pi_j}\right).
\]

It concludes (EV_0=\operatorname{Var}(H)+A). Next, universally choose real arrays (a,b:U\times U\to\mathbb R). Assume, for every ordered pair with (i\ne j\) and (\pi_{ij}=0), (a_{ij}>0\), (b_{ij}>0\), and (1/a_{ij}+1/b_{ij}=1\). There is no condition on the arrays at other pairs. Put

\[
C_{a,b}(z)=\sum_i\sum_{j\ne i:\ \pi_{ij}=0}\left(\frac{I_i(z)|y_i|^{a_{ij}}}{a_{ij}\pi_i}+\frac{I_j(z)|y_j|^{b_{ij}}}{b_{ij}\pi_j}\right).
\]

The assertion concludes \(\operatorname{Var}(H)\le E(V_0+C_{a,b})\) for every such pair of arrays, and separately \(\operatorname{Var}(H)\le E(V_0+C_2)\). All pair sums are ordered and there is no sign restriction on (y). It does not assert samplewise nonnegativity or samplewise domination of variance. The general branch states its unbiasedness result through the bias identity when the missing-pair sum vanishes. The docstring's 'general' sampling is quantified over finite inclusion populations and finite atom laws.

Junk and boundary checks: in the exposure branch, zero joint probabilities appear as denominators in `pairTerm`. Lean evaluates these quotients as zero, so `varianceHT` omits those pairs. This is an explicit operational convention, not an ordinary quotient at zero. Because all atom weights are positive, (\pi_{ij}=0\) implies (I_i(z)I_j(z)=0\) for every atom; a nonexistent jointly observed pair contributes zero. All marginal and (N\)-based divisions are protected by the hypotheses. In the general branch the estimator explicitly tests (\pi_{ij}>0\) before dividing; zero-joint pairs are omitted even at zero-weight atoms on which both inclusions might be true. Every marginal denominator is positive. The real power in the Young correction has base \(|y_i|\ge0\). At included pairs the conjugate exponents are positive (indeed exceed one), so \(0^a=0\) has its usual meaning. Exponents and denominators outside missing pairs can have arbitrary values, but their terms are omitted. Normalization excludes empty (\Omega). An empty general population (U) is allowed and yields legitimate zero totals, variances and corrections; it does not make the nonempty cases disappear. One certainty unit also gives a legitimate zero variance. Nontrivial multiunit examples are possible. There are no integrals, logs, square roots, truncated natural subtractions, extended-real conversions, extrema or limits.
