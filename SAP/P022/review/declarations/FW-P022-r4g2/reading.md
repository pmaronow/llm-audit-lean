# Blind reading

This file was written before opening `claims.json` or `record.json`. Evidence: the five Challenge docstrings/statements, every entry of their `closure.json` closures, the corresponding definition sources, and `scratch/ClosurePrint.lean` (compiled successfully). No claim or record has been consulted at this stage.

## Common mathematical notation (fully expanded)

All outcomes and thresholds are real. A design is a triple of natural numbers `(N,m,k)` with proofs of `4 ≤ N`, `2 ≤ m`, `2 ≤ k`, and `m+k ≤ N`. An assignment is a bijection of `{0,…,N−1}` with itself. Expectations over assignments mean the arithmetic average over **all N! permutations**, not a probability law supplied by a caller. Writing `Eπ f` means `(1/N!) Σπ f(π)`. Writing `M_s(v)` means `(1/s) Σ_{i=0}^{s−1} v_i`. The actual implementation is `Finset.expect Finset.univ`, namely the inverse of the finite cardinality in the nonnegative rationals, acting on the finite sum in the reals; on a nonempty finite type this is exactly that arithmetic mean. Write `v_s(v)=M_s((v_i−M_s(v))²)` and `s_s²(v)=Σ_i(v_i−M_s(v))²/(s−1)`. All divisions in these formulas are real divisions.

For a population vector `y`, the treatment observation under π is `a_i=y_{π(i)}` for `0≤i<m`; the control observation is `b_j=y_{π(m+j)}` for `0≤j<k`. Thus the two arms are disjoint samples without replacement. Assignment variance is `Eπ[(f(π)−Eπ f)²]`. An empirical CDF is `C_v(x)=M_s(1_{v_i≤x})` (the **right** CDF).

For the quantile statements, sort the list `[v_0,…,v_{s−1}]` in ascending real order using `List.mergeSort` with comparison `decide (a≤b)`. Write `O_v(r)` for its zero-based `List.getD (r−1) 0`, where `r−1` is **natural truncated subtraction**. Write `Q_v(u)=O_v(Nat.ceil(s*u))`. Here natural ceiling is zero for nonpositive real arguments and otherwise the least natural number at least its argument. Consequently `O_v(0)` is the *first* sorted element when `s>0`, not zero; `O_v(r)=0` when `r−1` is beyond the list. On `0<u≤1` with `s>0`, `Q_v` is the usual empirical inverse CDF. Its value at zero is the smallest sample value.

The two-element type of endpoints has constructors H and L, with ordinary structural decidable equality. Put `t_H(u)=u`, `t_L(u)=1−u`, and

`C_B(a,b)=∫₀¹ Q_a(u) Q_b(t_B(u)) du − M_m(a)M_k(b)`.

This is Mathlib's real interval Bochner integral with respect to Lebesgue measure. Put

`V(N,m,k,A,D,C) = [((N−m)/m)A + ((N−k)/k)D + 2C]/(N−1)`

and `A_N(v)=((N−1)/N)s_s²(v)`. The mathematical estimated variance endpoint is the explicit expression

`E_B(N,a,b)=V(N,m,k,A_N(a),A_N(b),C_B(a,b))`.

Partition notation used below is likewise just real arithmetic and finite lists. Let `P=[p_0,…,p_L]` be the ascending sorted, duplicate-free union of `{i/m : i=0,…,m}` and `{j/k : j=0,…,k}`. Formally `L=P.length−1` in natural numbers, `p_r=P.getD r 0`, `w_r=p_{r+1}−p_r`, and `h_r=(p_r+p_{r+1})/2`. For positive m,k, `p_0=0`, `p_L=1`, every actual cell has positive width, and every h_r is strictly inside `(0,1)`. Define

`K_B(a,b)=Σ_{r=0}^{L−1} w_r [Q_a(h_r)−M_m(a)] [Q_b(t_B(h_r))−M_k(b)]`,

`W_ij=max(0,min((i+1)k,(j+1)m)−max(ik,jm))/(mk)` for zero-based `i<m,j<k`.

Every generated declaration with source line zero in the closure was also printed. They are proofs that real scalar arithmetic has characteristic zero, that numeral denominators exceed one, that observed indices are in range, and the generated constructor-index/decidable-equality machinery for H/L. The four-unit design constructor is `(4,2,2)` with the four elementary inequalities. No additional mathematical premise is hidden in these proof declarations. Structure constructors, projections, H/L constructors and recursors are exactly those described above (and the experiment structure described under T10).

## SAP.P022.T4

The theorem has no external parameters; it asserts the following universal proposition. For **every** design `(N,m,k)`, **every** pair of real population vectors `y1,y0 : Fin N → ℝ`, and **every** real x, set `G=C_y1(x)`, `F=C_y0(x)`, `Gh(π)=C_(y1 restricted to treatment under π)(x)`, and `Fh(π)=C_(y0 restricted to control under π)(x)`. All eight conclusions hold simultaneously:

1. `Eπ Gh=G` and `Eπ Fh=F`.
2. `Eπ[(Gh−Eπ Gh)²]=(N−m)G(1−G)/[(N−1)m]` and `Eπ[(Fh−Eπ Fh)²]=(N−k)F(1−F)/[(N−1)k]`.
3. Those variances are respectively at most `(N−m)/[4(N−1)m]` and `(N−k)/[4(N−1)k]`.
4. `M_N((1_{y1_i≤x}−G)²)=G(1−G)` and `M_N((1_{y0_i≤x}−F)²)=F(1−F)`.

This matches its docstring's description of unbiased sampled CDFs, Bernoulli-factor variance formulas, and quarter-factor upper bounds. It has no asymptotic or law-convergence assumptions.

Junk conventions: arithmetic averages of empty finite types are zero, and real division by zero is totalized to zero, but `N≥4,m≥2,k≥2` and the inhabited permutation group prevent both from affecting this statement. `N−m,N−k,N−1` in the displayed ratios are real subtraction after casting, not truncated natural subtraction. The implicit index proofs make all observations genuine population elements. All relevant sums are finite. There are no integrals, logarithms, square roots, real powers, extrema, extended-real conversions or limit operations in this statement.

## SAP.P022.T5

This is a conjunction of unconditional concrete facts, a combinatorial count, and a universal equivalence. In the design `(4,2,2)`, take the population vector identically one and threshold x=0. The population right CDF is zero; the population variance of the zero indicator vector is zero; **every** permutation has treatment-sample right CDF zero; its assignment variance is zero; `(4−2)/[4(4−1)2]=1/12`; and `0≠1/12`. Independently, `Nat.choose 4 2=6`.

Finally, for **every** design `(N,m,k)`, **every** real population vector y and **every** real x,

`Eπ[(C_(treatment observation of y)(x) − Eπ C_(treatment observation of y)(x))²] = (N−m)/[4(N−1)m]`

**if and only if** `C_y(x)=1/2`. This last equivalence is for the treatment arm. No separate control-arm equivalence is asserted.

The docstring calls this a refutation of equation (11), using the constant-one witness, and characterizes equality in the quarter-factor bound. That is a statement about the printed equation which cannot yet be checked during blind reading.

Junk conventions: the same nonempty finite means and strictly positive denominators as T4 apply; the concrete ratios have denominators 12 and 24. The positive factor `N−m` cannot disappear: `k≥2,m+k≤N` implies `N−m≥2`. Natural `choose` is the ordinary binomial coefficient. There are no integral, quantile, supremum, extended-real, or limit conventions involved. The witness uses ordinary real numbers and a valid nonempty randomized design.

## SAP.P022.T8

For **every** natural m,k, then proofs `m≥2,k≥2`, then **every** pair of real sample vectors a,b of those lengths, the following conjunction is asserted:

1. `Σ_{r<L} w_r=1`.
2. For **each** natural `r<L`, then **each** real u strictly between `p_r` and `p_{r+1}`, all three rank identities hold:
   `ceil_nat(m*u)=ceil_nat(m*p_{r+1})`, `ceil_nat(k*u)=ceil_nat(k*p_{r+1})`, and `k+1−ceil_nat(k*u)=ceil_nat(k*p_{L−r})`.
3. `Σ_{r<L} w_r Q_a(h_r)=M_m(a)`.
4. For **each** B in {H,L}, `Σ_{r<L} w_r Q_b(t_B(h_r))=M_k(b)`.
5. For **each** B, the explicit centered midpoint sum `K_B(a,b)` equals the integral covariance `C_B(a,b)`.
6. For **each** natural N satisfying `m+k≤N`, then **each** B, `V(N,m,k,A_N(a),A_N(b),K_B(a,b))=E_B(N,a,b)`.
7. For **each** `i : Fin m`, `Σ_j W_ij=1/m`; for **each** `j : Fin k`, `Σ_i W_ij=1/k`.
8. For **each** B,
   `C_B(a,b)=Σ_i Σ_j W_ij [O_a(i+1)−M_m(a)] [O_b(j+1)−M_k(b)]` for H, and the same expression with `O_b(k−j)` for L.

Every symbol in these formulas is the finite sum/list operation, real arithmetic, or Lebesgue integral defined above. The docstring describes this as using original partition widths and midpoint quantile selections to recover sharp estimates, with rank and overlap-weight identities.

Junk conventions: list lookup outside the knot list returns zero; `L=length−1`, `L−r`, rank `r−1`, `k−j` and `k+1−ceil_nat(k*u)` use natural truncated subtraction. Actual cell indices and positive arm sizes keep all these accesses/subtractions in the intended range. Midpoints are in `(0,1)`; reflected midpoints are too. The quantile convention at 0 differs from an extended inverse-CDF convention but only concerns a Lebesgue-null endpoint of the covariance integral. Sorting never discards multiplicities of outcomes (only the knot union discards duplicate knots). Finite quantile functions on `[0,1]` are bounded measurable step functions, so Bochner's nonintegrable-value-zero convention is unused. The divisions by m,k,mk and (when N is introduced) N,N−1,s−1 have positive denominators. There are no `sInf`, `sSup`, limsup/liminf, `toReal`, logarithm, square-root or real-power values involved.

## SAP.P022.T9

Let `e=1/67108864`. On the partition above set `z_0=e` and `z_r=p_r−e` for every natural `r>0`. Define the literal real-arithmetic code expression

`R_B(N,a,b)=V(N,m,k,A_N(a),A_N(b), Σ_{r<L}(z_{r+1}−z_r)Q_a(z_{r+1})O_b(j_B(r)) − M_m(a)M_k(b))`,

where `j_H(r)=ceil_nat(k*z_{r+1})` and `j_L(r)=k+1−ceil_nat(k*z_{r+1})`. This definition is not a floating-point interpreter.

The theorem is the conjunction of all of the following, without any outside hypotheses:

1. For the four-unit design with both potential-outcome populations identically one, `Eπ[( (M_2(observed y1)−M_2(observed y0)) − Eπ(M_2(observed y1)−M_2(observed y0)))²]=0`. For **each** B, `E_B(4,ones_2,ones_2)=0` but `R_B(4,ones_2,ones_2)=−1/50331648`.
2. For **every** N,m,k with `m≥2,k≥2,m+k≤N`, then **every** real a,b, assuming **every** actual cell satisfies `2e<w_r`, both discrepancies hold:
   `R_H−E_H=−4e O_a(1)O_b(1)/(N−1)` and `R_L−E_L=−4e O_a(1)O_b(k)/(N−1)`.
3. The explicit example details: `choose(4,2)=6`; **every** permutation gives identically-one observed treatment and control samples and mean difference zero; `s_2²(ones)=0`, `A_4(ones)=0`, and `C_B(ones,ones)=0` for both B; the knots for m=k=2 are `[0,1/2,1]`; `z_0=e,z_1=1/2−e,z_2=1−e`; for **every** r<3, `Q_ones(z_r)=1` and `O_ones(3−ceil_nat(2z_r))=1`; the two shifted widths are `1/2−2e` and `1/2`; their sum is `33554431/33554432`; and `−4e/3=−1/50331648<0`.
4. For **every** natural m,k≥2, `Σ_{r<L}(z_{r+1}−z_r)=1−2e`, with **no** cell-width assumption.
5. For **every** N,m,k satisfying the size conditions, **every** real a,b,c and B, `E_B(N,a+c,b+c)=E_B(N,a,b)`.
6. For **every** N,m,k satisfying those conditions and `∀r<L,2e<w_r`, then **every** real a,b,c and B,
   `R_B(N,a+c,b+c)−R_B(N,a,b)=−4e[c(O_a(1)+O_b(1))+c²]/(N−1)` for H; replace `O_b(1)` by `O_b(k)` for L.
7. For **each** B, `R_B(4,zeros_2,zeros_2)=0`, and this differs from `R_B(4,ones_2,ones_2)`.

Its docstring says these facts refute the printed routine's sharp-estimate assertion, in real arithmetic, and describes the explicit cell-width condition and translation defect.

Junk conventions: all means and variance denominators are on nonempty types with sizes at least two; N≥m+k≥4. The concrete shifted points lie inside their proper quantile cells. For the general discrepancy and translation identities, `2e<w_r` forces the shifted selected points into the intended cells, keeps lower ranks between 1 and k, and prevents default order-statistic values or natural subtraction underflow from entering the argument. The knot and rank default conventions are the ones spelled out above. Even without the width condition the telescoping sum in item 4 only reads existing knots. There is no claim that every possible positive m,k satisfies the width hypothesis. The covariance integrals are bounded measurable finite step-function integrals. `e` is a positive exact rational real; it is not Lean's machine floating epsilon. No extrema, extended-real conversions, logarithms, square roots, nonintegrable expectations or limit operations appear.

## SAP.P022.T10

This is a conjunction of three universal propositions:

1. For **every** natural m,k,N satisfying `m≥2,k≥2,m+k≤N`, then **every** real a,b of lengths m,k and B,
   `E_B(N,a,b)=(1/m−1/N)s_m²(a)+(1/k−1/N)s_k²(b)+2C_B(a,b)/(N−1)`.
2. For **every** m,k≥2, then **every** fixed real sample vectors a,b and endpoint B, the real sequence `r↦E_B(r+m+k,a,b)` tends, as natural r→∞, to `s_m²(a)/m+s_k²(b)/k`. Samples and arm lengths are fixed before the limiting parameter is varied.
3. An experiment sequence is a choice of a valid design for every natural q with `N_q=q+4`, and two **fixed infinite real sequences** y1,y0; the q-th population consists of their first N_q terms (not an arbitrary triangular array). For **every** such experiment sequence and then **every** natural m,k≥2, assume eventually `m_q=m`, eventually `k_q=k`, and **there exists one real M** such that **for all q** both population variances `v_{N_q}(y1_0,…,y1_{N_q−1})` and `v_{N_q}(y0_0,…,y0_{N_q−1})` are at most M. Then, as q→∞,
   `Eπ[(D_q(π)−Eπ D_q)²] − [v_{N_q}(y1)/m+v_{N_q}(y0)/k] → 0`,
   where `D_q(π)=M_{m_q}((y1_{π(i)})_{i<m_q})−M_{k_q}((y0_{π(m_q+j)})_{j<k_q})`, and the average at each q is over all permutations of Fin N_q.

No marginal variance convergence, independence of y1 and y0, allocation fraction limit, positive sampling fraction, or conditional-law premise is asserted. In particular the last conclusion approximates a sequence of deterministic variances; it does not claim that either population-variance sequence has its own limit.

The docstring explicitly calls this restricted: it retains the fixed-sample formula and limit and the bounded-variance, eventual-fixed-arm approximation for actual randomization variance. It says it drops the exact actual-variance remainder identity, the `(0,1)` formulas and examples, and R-branch execution assertions.

Junk conventions: m,k≥2 and N≥m+k ensure all divisions and sample variances are meaningful; `r+m+k≥4` in the limiting estimator. Every row in the final clause has N_q≥4 and nonempty assignment type. The eventual arm equalities can hold simultaneously (e.g. m=k=2 for every q); bounded variances are a substantive hypothesis but are not contradictory (zero outcomes give M=0). Averages and variances are finite. The quantile integrals used in the first two clauses are bounded measurable step integrals, including harmless endpoint conventions. The limits are Mathlib `Filter.Tendsto … atTop (nhds …)` on real-valued sequences, not conditionally-complete-order limsup/liminf operations, so unbounded-sequence default extrema play no role. No real powers, logarithms, square roots, partial-function defaults beyond the safe quantile conventions, or `toReal` values are used.
