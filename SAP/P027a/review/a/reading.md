# Blind reading of the challenge statements

This file was written after reading all eight Defs parts and the Challenge files, and before opening either `claims.json` or `record.json`. The mathematical assertions below come from the theorem types, not from their descriptive docstrings. Every theorem has no external hypotheses: each asserts the conjunction defined by its `T…Statement`. Hypotheses and quantifiers inside those conjunctions are recorded below.

## Common definitions and Mathlib semantics

All population and sample-atom types in a `Design U Ω` are finite when expectations are used. A design consists only of real weights (w_\omega) and Boolean selections. Put (I_k(\omega)=1) if selected and (0) otherwise. `Valid` means (w_\omega\ge0) for every atom and (\sum_\omega w_\omega=1); validity is not a field of the structure. `Positive` means every (p_k>0), where

\[
 E_Df=\sum_\omega w_\omega f(\omega),\quad
 p_k=E_DI_k,\quad p_{kl}=E_D(I_kI_l),\quad d_{kl}=p_{kl}-p_kp_l.
\]

Sums are Mathlib `Finset.univ` sums over the indicated finite type; double sums are ordered and include the diagonal unless the condition excludes it. Let

\[
 T_D(y,\omega)=\sum_k I_k(\omega)y_k/p_k,\quad
 M_D=T_D/|U|,\quad
 V_D(f)=E_D[(f-E_Df)^2],
\]
\[
 H_D(y,\omega)=\sum_{k,l:p_{kl}>0}I_kI_l\frac{d_{kl}}{p_{kl}}\frac{y_k}{p_k}\frac{y_l}{p_l}.
\]

For (Z_D=\{(k,l):k\ne l,\ p_{kl}=0\}), define

\[
 A_D(y)=\sum_{Z_D}y_ky_l,\quad
 B_D(y)=\tfrac12\sum_{Z_D}(y_k^2+y_l^2),\quad
 R_D(y,\omega)=\sum_{Z_D}\left(\frac{I_ky_k^2}{2p_k}+\frac{I_ly_l^2}{2p_l}\right),
\]
\[
 C_D=H_D+R_D,\qquad J_D(y)=\tfrac12\sum_{Z_D}(y_k+y_l)^2.
\]

These are respectively `biasA`, `quadraticA`, `quadraticCorrection`, `c2Estimator`, and `squaredZeroPairs`; the word "bias" alone does not impose an identity with a variance. The auxiliary `wrEstimator` for natural (m) is

\[
 W_D(y,m,\omega)=\frac{\sum_k I_k(\omega)[y_k/(p_k/m)-T_D(y,\omega)]^2}{|U|^2m(m-1)}.
\]

Real divisions use Mathlib's total field division (in particular (a/0=0)). Natural subtraction and division use truncated subtraction and integer division. The concrete denominator guards in each assertion therefore matter. There is no global requirement that populations be nonempty, designs be valid, or sample sizes be fixed; those must follow from the particular definitions or hypotheses.

`outcomeE μ f` is the real Bochner integral (\int f\,d\mu). Mathlib `Integrable` means almost-everywhere strong measurability and finite integral of the norm. The integral is zero by convention for nonintegrable functions (`MeasureTheory.integral_undef`, Bochner/Basic.lean:204). `IsProbabilityMeasure μ` means (\mu(\mathrm{univ})=1). `Measure.sum` is the measure sum (on measurable sets it is the extended-nonnegative sum of the measures); `dirac v` is point mass at (v). `ENNReal.ofReal` sends a nonnegative finite real to the same extended real, and clips negative inputs to zero; `toReal` maps infinity to zero. Thus normalization and finiteness assertions in T12 must be taken seriously. All explicit mass coefficients below are positive.

`Tendsto … atTop (𝓝 a)` is the usual limit along natural numbers to (a\) in the real topology, not a limsup. The power ((3/8)^{18/5}) in the mass below is Mathlib real exponentiation, equal here to (\exp((18/5)\log(3/8))). Finite decimal literals denote exact rationals.

For group sizes (n_g\in\mathbb N), the population of `liftDesign D n` is the dependent sum of the sets (\{0,\ldots,n_g-1\}). Its weight is (w\) and its selection of ((g,j)) is the selection of (g\) in (D), including at weight-zero atoms. Write (Y_g=\sum_{j<n_g}y_{gj}) and (Q_g=\sum_{j<n_g}y_{gj}^2). `zeroNeighborCount` is (d_g=\#\{h\ne g:p_{gh}=0\}); `zeroNeighborSize` is (h_g=\sum_{h\ne g:p_{gh}=0}n_h).

For sizes (x_k\) indexed in the natural order of `Fin N`, put (b_k=\sum_{a<k}x_a). `systematicSelected x m u k` means
\[
 \exists j\in\{0,\ldots,m-1\}: b_k\le u+j(\sum_a x_a)/m<b_k+x_k.
\]
`printedPPS m x k` is the real number (mx_k/\sum_a x_a).

For any error process on a probability space, raw outcomes are (\beta x_k+\epsilon_k(\xi)); centered outcomes subtract the population arithmetic mean of those raw outcomes. `NoiseMoments μ ε σ2` says, in order, each error is integrable with integral zero, and each product (\epsilon_k\epsilon_l) is integrable with integral (\sigma^2) if (k=l) and zero otherwise. Here the symbol `σ2` is one real parameter, not a further squaring operation. `UncorrelatedNoise` imposes the same integrability and mean-zero conditions but specifies product integral zero only for distinct indices, leaving diagonal second moments unrestricted in size.

## Shared concrete designs

`fourPhase low high …` has population (0\le k<8), atoms (0\le g<4), weight low for even (g), high for odd (g), and selects (k\equiv g\pmod4). Its constructor takes proofs that both weights are nonnegative and (2\,\mathrm{low}+2\,\mathrm{high}=1). `periodic8` takes weights (1/12,5/12); `random8` takes (1/8,3/8). Their size vectors are respectively (2,10,2,10,2,10,2,10) and (1,3,1,3,1,3,1,3). `alternating8` is (-1,+1,-1,+1,\ldots); `randomOutcome8` is its negative. The interval left endpoints `fourLeft a b` are (0,a,a+b,2a+b).

For integer (r>0), groups are (g=(a,b)\in\{0,\ldots,r-1\}\times\{0,1\}), and
\[
 p_g=\begin{cases}1/(6r)&b=0,\\5/(6r)&b=1.\end{cases}
\]
`phaseGrouped r hr` is the one-draw design whose atom (g) has weight (p_g) and selects exactly group (g). `phaseOriginal r m hr` duplicates each group into (m\) units with the same selection, assigning size (2\) to (b=0) and (10\) to (b=1). Let (q=2r\) and (N=mq). The unit order `phaseIndex` is (2a+b+2rj), and the group start left endpoint is (a_g=12a+(0\text{ if }b=0\text{ else }2)).

## SAP.P027a.T1

This is `Periodic8Witness ∧ AlternatingFamily`.

For the fixed periodic eight-unit design and the alternating outcome (z), it asserts all of the following without hypotheses:

* The design is valid and positive; (p_k=1/12) on even units and (5/12) on odd units. For every ordered pair, (p_{kl}=p_k) if (k\equiv l\pmod4) and zero otherwise; exactly 48 distinct ordered pairs have zero joint probability.
* For every (g<4\) and real (u\), if (u\) lies in ([a_g,a_g+x_g)), with left endpoints (0,2,12,14), then for every unit, `systematicSelected periodicSize8 2 u k` is equivalent to selection by atom (g).
* (\sum_k z_k=0), (A=-16), (B=48). For every (g<4), (M(g)=-3) on even (g) and (3/5) on odd (g); (H(g)/64=33/4) or (21/100); (C(g)/64=21/2) or (33/50); and (W(z,2,g)=0).
* (E M=0), (V(M)=9/5), (E(H/64)=31/20), (E(C/64)=23/10), and (E(H/64)-V(M)=-1/4).

Separately, for every natural (r,m), every proof (r>0), and assuming (m>0), take the phase-original design and the outcome (z_{(a,b),j}=-1) for (b=0), (+1) for (b=1). With (q=2r,N=mq), it asserts (\sum z=0), (A=-qm^2), (V(M)=9/5), and (E(H/N^2)-V(M)=-1/q). No limit or measure identification is asserted by this theorem.

## SAP.P027a.T2

This conjoins the following six independently quantified propositions.

1. `PeriodicStartLaw`: for every natural (r,m), proof (r>0), and assumption (m>0), order the units by `phaseIndex`, define each cumulative left endpoint by summing `phaseSize` over earlier indices, put (L_0=12r), and let (s(u)) select the units hit by (u+jL_0), (j<m). For the measure (\nu=L_0^{-1}\,\mathrm{Leb}|_{[0,L_0)}), assert: (\nu) is a probability measure; every unit left endpoint equals (a_g+L_0j); every (u\in[0,L_0)) belongs to exactly one interval ([a_g,a_g+x_g)); for every group and every (u) in its interval the entire Boolean selection function (s(u)) equals the selection at atom (g) of the phase-original design; each such interval has measure (p_g); and for every real function (F) on all Boolean population selection vectors, (F(s(u))) is integrable and its integral is (E_D[F(D.\mathrm{selected}(g))]).
2. `PeriodicInclusions`: for every natural (r,m) and proof (r>0), with no condition on (m), the phase-original design is valid and positive; for every unit (p_{gj}=p_g); for every pair (p_{gj,hi}=p_g) if (g=h), zero otherwise; selection at atom (g) equals the Boolean decision of (g=h) for a unit in group (h); and two units have equal selections at every atom if and only if their group indices coincide. When (m=0), the unit-quantified conclusions are empty but validity is still asserted on the nonempty group-atom type.
3. `PeriodicBiasClaim`: for all (r,m>0) and every real unit outcome (z) with (\sum z=0), put (Y_g=\sum_{j<m}z_{gj}), (S=\sum_gY_g^2), (V=V_D(T_Dz)). Assert (\sum Y=0), (A=-S), (S\ge0), (S=0\iff\forall g,Y_g=0), (ET=0), (V=\sum_gY_g^2/p_g), (EH=V-S), and for every group (H(g)=(1-p_g)Y_g^2/p_g^2). Also ((EH-V)/N^2=-S/N^2); if (V>0), then (-5/(3q)\le A/V\le-1/(3q)).
4. `PeriodicOutcomeBias`: for every measurable space (\Xi), probability measure (\mu), (r,m>0), reals (\beta,\sigma^2\) with (\sigma^2\ge0), and error family satisfying `NoiseMoments`, form the centered raw size-model outcomes (z). Let (Y_g(\xi)=\sum_jz_{gj}(\xi)), (L=16m^2\beta^2+m\sigma^2(1-1/q)), (V(\xi)=V_D(T_D(z(\xi)))), (H(\xi)=E_DH_D(z(\xi))). Assuming additionally that (V,H,A_D(z)) are all (\mu)-integrable, conclude: each (Y_g^2) is integrable with integral (L); (E_\mu A=-qL); (E_\mu V=(9/5)q^2L); (E_\mu H=E_\mu V-qL); if (L>0), the ratio of those last two expectations' difference to (E_\mu V) equals (-5/(9q)); and (E_\mu(A/N^2)=-16\beta^2/q-\sigma^2(1-1/q)/N).
5. `CalibratedBias`: for every such probability space, (r,m>0), reals (\rho,\beta) with (|\rho|\le1), and errors satisfying `NoiseMoments` with parameter (900(1-\rho^2)), assume (\beta^2=900\rho^2(N-1)/(16N)) and integrability of (A_D(z)/N^2). Its integral equals
   \[
   b(q,\rho,N)=-900\rho^2(N-1)/(qN)-900(1-\rho^2)(q-1)/(qN).
   \]
6. `FixedFractionLimit`: for every natural (r>0) and every real (\rho), with no (|\rho|\) restriction in this component, (b(2r,\rho,(m+1)2r)\to-900\rho^2/(2r)) as natural (m\to\infty).

## SAP.P027a.T3

The three-unit design has two atoms of weight (1/2), selecting respectively ({0,1}) and ({2}). The two-unit design has two atoms of weight (1/2), each selecting its own index. There are no hypotheses.

For outcomes (y=(1,1,1)) and grouped outcomes (Y=(2,1)), the theorem asserts: both designs are positive; units 0 and 1 of the first always have the same indicator; the two estimated totals agree at each atom; original and grouped total variances are both 1; original (A=4), original (B=4), grouped (B=5); original (EC=9) and grouped (EC=10); hence the respective (C)-biases are exactly 8 and 9.

For outcomes (y=(1,1,-1/4)) and (Y=(2,-1/4)), both total variances are (81/16); both (A)'s are (-1); original (B=17/8), grouped (B=65/16); original (EC=99/16), grouped (EC=65/8); and the respective (C)-biases are (9/8) and (49/16). Validity of these explicit designs is not a separate conjunct.

## SAP.P027a.T4

This conjoins four universal propositions.

1. `AEAggregationPreservation`: for every pair of finite types (G,\Omega), positive integer group sizes (n_g), and valid, positive design (D) on the unit fibers, assume for every (g,i,j) that the weighted probability of disagreement between their Boolean selections is zero. For every outcome vector (y), define a group design (D_c) with the same weights and selecting group (g) according to its unit (j=0). Then (D_c) is positive, all unit marginal and joint probabilities equal the corresponding group probabilities, and on every atom with strictly positive weight the original and grouped (T)'s and (H)'s agree. Their total variances and their (A)'s agree. No assertion about those estimator values on weight-zero atoms is made.
2. `AggregationClaim`: for every finite (G,\Omega), valid positive group design (D), every positive integer vector (n), and every unit outcome (y), use the exactly lifted design (D_l). For all atoms, its (T) and (H) equal those of (D) on (Y); total variance and (A) are preserved. Also
   \[
   B_{D_l}(y)=\tfrac12\sum_{g\ne h:p_{gh}=0}(n_hQ_g+n_gQ_h).
   \]
   Define (\Delta=[E C_{D_l}-V_{D_l}(T)]-[E C_D(Y)-V_D(T(Y))]). Assert
   \[
   \Delta=\tfrac12\sum_{g\ne h:p_{gh}=0}(n_hQ_g+n_gQ_h-Y_g^2-Y_h^2).
   \]
   If every zero-joint group pair has equal group sizes, then (\Delta\ge0). For every real (v), if every unit outcome equals (v), then (\Delta=-v^2\sum_{g\ne h:p_{gh}=0}(n_g-n_h)^2/2). Both original and grouped (C)-biases are nonnegative. Finally (\sum_g(h_g-d_gn_g)Q_g\le\Delta).
3. `ConstantAggregationStrict`: for every such valid positive group design, positive integer group sizes, and real (v\ne0), if some distinct zero-joint group pair has unequal sizes, the original lifted-design (C)-bias at the constant outcome (v) is strictly smaller than the grouped (C)-bias.
4. `AggregationSquaredBias`: for every finite (G,\Omega), valid positive group design, every natural group-size vector (n) (zero sizes allowed here), and every outcome (y), the original lifted-design (C)-bias equals (J_{D_l}(y)) and the grouped (C)-bias equals (J_D(Y)).

These universals allow (G) to be empty; validity precludes empty atom types. They also quantify over nonempty examples.

## SAP.P027a.T5

There are three conjoined assertions.

For each row (i=0,1,2,3), and every pair of reals (V,G) satisfying the two independent rounding inequalities (|V-v_i|\le0.005) and (|G-c_i|\le0.005), the conclusion is (V>0) and (G>(1+5(q_i-2)/(3q_i))V). The arrays are (v=(42.55,56.35,23.14,28.58)), (c=(653.92,891.43,622.28,861.11)), (q=(4,20,4,20)). This is a numerical statement about all real pairs in four rectangles, without any assumption connecting (V,G) to a population or an estimator implementation.

For the phase-original design (r=2,m=30), set (z_{(a,b),j}=(-4\text{ if }b=0\text{ else }4)+2j-29), (0\le j<30), and let (Y) be the four group totals. Assert (\sum z=0), (\sum Y_g^2=57600), (\sum z_k^2=37880); (V_D(T)=414720), (EH_D=357120), (EC_D=3766320); and for its phase-grouped design (E C_{D_c}(Y)=529920).

For the same definitions, also assert (V/14400=144/5), (EH_D/14400=124/5), (EC_D/14400=5231/20), (EC_{D_c}/14400=184/5), ((EC_D-V)/V=4655/576), and ((EC_{D_c}-V)/V=5/18). There are no hypotheses on these fixed witnesses.

## SAP.P027a.T6

This conjoins `PeriodicInclusions` (exactly as quantified in T2), `PeriodicCorrectionClaim`, `PeriodicGroupedOutcome`, and a fixed four-group example.

`PeriodicCorrectionClaim`: for every (r,m>0) and unit outcome (z) of zero total, use the phase designs (D,D_c), and set (Y_g=\sum_jz_{gj}), (Q_g=\sum_jz_{gj}^2), (S=\sum_gY_g^2), (Q=\sum_gQ_g), (q=2r,N=mq), (V=V_D(T)), (H=EH_D), (U_c=EC_D), (G_c=EC_{D_c}(Y)). Assert

\[
\begin{gathered}
\sum Y=0,\quad A=-S,\quad S\ge0,\quad(S=0\iff\forall g,Y_g=0),\\
ET=0,\quad V=\sum_gY_g^2/p_g,\quad H=V-S,\\
U_c=V-S+(N-m)Q,\quad G_c=V+(q-2)S.
\end{gathered}
\]

For each group atom (g), assert all six formulas and the sign:
\[
\begin{gathered}
T_D(g)=Y_g/p_g,\quad H_D(g)=(1-p_g)Y_g^2/p_g^2,\\
R_D(g)=(N-m)Q_g/p_g,\quad R_{D_c}(g)=(q-1)Y_g^2/p_g,\\
C_D(g)-C_{D_c}(g)=(q-1)(mQ_g-Y_g^2)/p_g\\
=m(q-1)\sum_{j<m}(z_{gj}-Y_g/m)^2/p_g\ge0.
\end{gathered}
\]

Also (U_c-G_c=(q-1)(mQ-S)), (V\le G_c\le U_c), and ((3q/5)S\le V\le3qS). If (V>0), conclude (-5/(3q)\le A/V\le-1/(3q)) and ((q-2)/(3q)\le(G_c-V)/V\le5(q-2)/(3q)).

`PeriodicGroupedOutcome`: for every measurable space with probability measure (\mu), integers (r,m>0), real (\beta,\sigma^2\ge0) (only (\sigma^2) is constrained nonnegative; (\beta) is arbitrary), and errors satisfying `NoiseMoments`, center the size-model outcomes. Define (Y,L,V) as in T2 and (G_c(\xi)=E_{D_c}C_{D_c}(Y(\xi))). Assuming integrability of (V,G_c), and every (Y_g^2), assert (E_\mu Y_g^2=L) for each (g), (E_\mu V=(9/5)q^2L), (E_\mu G_c=E_\mu V+(q-2)qL), and, if (L>0), ((E_\mu G_c-E_\mu V)/E_\mu V=(5/9)(1-2/q)).

Finally `groupedPeriodic4` is the one-draw design with weights (1/12,5/12,1/12,5/12). For outcomes (Y=(1,0,-1,0)), assert (\sum Y^2=2), (V(T)=24), (EC=28), and ((28-24)/24=1/6). No original eight-unit outcomes occur in this last conjunct.

## SAP.P027a.T10

This is one fixed-witness proposition, `Random8Witness`, with no external hypotheses. The design is `random8`, sizes (x=(1,3,1,3,1,3,1,3)), and outcomes (y=(1,-1,1,-1,1,-1,1,-1)).

It asserts validity and positivity, all (x_k\ge1), (A=-16), (B=48), (ET=0), (V(T)=256/3), (EH=208/3), (EC=352/3); (\sum x=16), (p_k=2x_k/\sum x) for every unit, (V(M)=4/3), (E(H/64)=13/12), (E(H/64)-V(M)=-1/4), and (E(H/64)<V(M)).

For every group atom, (T=16) on even atoms and (-16/3) on odd atoms; (H=224) or (160/9), respectively. For every atom and every (u) in its interval with left endpoints (0,1,4,5) and length (1) or (3), systematic selection of sample size 2 agrees with this atom's Boolean selection for every unit. Finally, for every real outcome vector (y'), if (|y'_k-y_k|<1/8) for every unit, then (A_D(y')\le-13/4). No sampling distribution of (y') or of sizes is asserted.

## SAP.P027a.T11

For every finite population (U), finite atom type (\Omega), measurable error space (\Xi) and probability measure (\mu), valid positive design (D) with (|U|>0), every size vector (x) with (x_k\ge1), every real (\beta), and error family satisfying `UncorrelatedNoise`, form raw (uncentered) outcomes (y_k(\xi)=\beta x_k+\epsilon_k(\xi)). Assume that (A_D(y(\xi))) and
\[
 b(\xi)=E_D[H_D(y(\xi))/|U|^2]-V_D(M_D(y(\xi)))
\]
are both (\mu)-integrable. Then, for all distinct (k,l), (E_\mu[y_ky_l]=\beta^2x_kx_l); (E_\mu A_D(y)=\beta^2 A_D(x)\ge0); and (E_\mu b=\beta^2A_D(x)/|U|^2\ge0). The inequalities are separate asserted conjuncts. Nothing claims (b(\xi)\ge0) for individual outcomes.

Separately and without hypotheses, (A_{\mathrm{random8}}(\mathrm{randomSize8})=176), and ((3/2)^2\cdot176=396).

## SAP.P027a.T12

Put (x_0=30), (x_k=1) for the other seven units. The theorem has five conjoined parts.

1. The size sum is 37, printed sample-size-2 probability at zero is (60/37), all printed probabilities sum to 2, and the excess at zero is (23/37). For every finite atom type and every valid design on the eight units, its inclusion probabilities cannot all equal these printed probabilities.
2. For every unit the printed probability is (60/37) at zero and (2/37) elsewhere. For every valid design on eight units and every unit, its actual inclusion probability is at most one. The count vector (v^*=(29,0,\ldots,0)) satisfies (1+v_k^*=x_k) for all (k).
3. Define for every natural (j)
   \[
   a_j=\frac{\prod_{i=0}^{j-1}(18/5+i)}{j!}(3/8)^{18/5}(5/8)^j.
   \]
   On the discrete count-vector space (\mathbb N^8), define (\mu_8=\sum_v(\prod_ka_{v_k})\delta_v) using extended-nonnegative coefficients. Assert that (\mu_8) is a probability measure; for every coordinate (k) and natural (j), the real probability of (v_k=j) is (a_j); each coordinate has expectation 6 and centered second moment 16; and the atom (v^*) has real probability (a_{29}a_0^7>0).
4. Each coordinate and each squared centered coordinate is explicitly integrable under (\mu_8).
5. For every row of the six arrays
   \[
   N=(8,40,120,600,240,1200),\ m=(2,2,30,30,60,60),\ L=(8,40,5,21,5,21),
   \]
   \[
   p^*=(16/15,80/79,150/124,630/620,300/244,1260/1220),
   \]
   set (v_0=L-1), the other (v_k=0), and (x_k=1+v_k). Assert (N\ge2), (0<m<N), (L=\lfloor(N-1)/(m-1)\rfloor+1) (natural division), (\sum x=L+N-1), (x_0=L) and all other sizes one; there exists an index with value zero and printed probability (p^*>1); the same atomic product measure (\mu_N) on (\mathbb N^N) is a probability measure giving this (v) strictly positive probability; and for every finite atom type, no valid design has all its inclusions equal to these printed probabilities.

## SAP.P027a.T13

This conjoins `PPSFeasibility`, `SystematicConstruction`, and two fixed-witness conjunctions.

`PPSFeasibility`: for every natural (N\ge2), natural (m) with (0<m<N), and real vector (x) with all coordinates positive:

* For every finite atom type and valid design (D), if every (p_k=mx_k/\sum x), then (mx_k\le\sum x) for every (k).
* There exists a real (c>0) with (\sum_k\min(1,cx_k)=m).
* If (mx_k\le\sum x) for every (k), then choosing (c=m/\sum x) gives (\sum_k\min(1,cx_k)=m), and each capped probability equals the printed probability.

`SystematicConstruction`: for every natural (N\ge2), (0<m<N), and real vector (\pi) with (0<\pi_k\le1) for all (k) and (\sum\pi=m), assume every indicator of `systematicSelected π m u k` is integrable with respect to Lebesgue measure restricted to ([0,1)). Then for every real (0\le u<1), exactly (m) distinct unit indices satisfy that selection predicate; and for every (k), the integral of its indicator over ([0,1)) is (\pi_k). This uses cumulative sums of (\pi) and step ((\sum\pi)/m=1).

For the fixed eight-unit (x=(30,1,\ldots,1)), assert (\sum\min(1,x_k/7)=2); naively capping the original printed probabilities gives sum (51/37); and the repaired vector is (1) at zero, (1/7) elsewhere. `certainty8` has seven atoms of weight (1/7), at atom (\omega) selecting zero and unit (\omega+1). Assert it is positive, its marginal probabilities equal the repaired vector, and its joint probabilities equal the marginal on the diagonal, (1/7) off the diagonal if either index is zero, and zero otherwise. Validity of this explicit design and equality of its law to the continuous systematic construction are not separate conclusions.

## Scope of this blind pass

The only theorem declarations found in the Challenge are T1, T2, T3, T4, T5, T6, T10, T11, T12, and T13. No verdict about agreement with a canonical claim or an architect's decision has been made in this file. The Mathlib source checks above establish the semantics of integrability, totalized integral, probability measure, measure sum, real powers, and filter limits; the remaining notation is finite real arithmetic and ordered-set notation.
