# Blind reading

Saved before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`.

I read the five Challenge declarations and their docstrings, every named source declaration in their closures, and used `scratch/ClosurePrint.lean` to print all 33 distinct generated auxiliary declarations in the closures. Those auxiliaries prove only positivity/nonzeroness needed for finite indices and the `OfNat` instances for real numerals; none adds a mathematical hypothesis or an axiom. In particular, coordinate zero in `varianceFactor` exists because its assignment has size `n+1`.

All probabilities and expectations below are finite sums, not Mathlib measure integrals. For a finite type Ω, a real weight function p, a real function X, and an event E:

- `expect p X = Σω p(ω)X(ω)`.
- `prob p E = Σω p(ω)1_E(ω)`.
- `variance p X = Σω p(ω)(X(ω) - Σv p(v)X(v))²`.
- `mean x = (Σi x(i))/(card I)` on a finite type I.
- `condMean p E X = (Σω p(ω)1_E(ω)X(ω))/(Σω p(ω)1_E(ω))`.
- An `Assignment N` is a function `Fin N → Bool`. The mass `bernoulli q(z)` is `Πi (if z(i) then q else 1-q)`, so for q in [0,1] it is the product law of independent identically distributed treatment bits.
- `InProbability p X a` means: for every real ε>0, the real sequence `Σω p_n(ω)1_{ε<|X_n(ω)-a_n|}` tends to 0 as natural n tends to infinity (`Filter.atTop`, usual real neighborhoods). It allows the finite sample space and deterministic target to change with n.

These are complete unfoldings of the shared SAP definitions used below. Subtraction of reals is ordinary subtraction, and every displayed division in real expressions is real division even when the denominator is written using natural-number syntax.

## SAP.P045b.T22

Location: `SAP/P045b/Challenge/Part1.lean:26–29`; definitions `Defs/Part4.lean:83–119` and `Defs/Part1.lean:98–111`.

For every natural n, put N=n+1, Ω_n={false,true}^N, and p_n(z)=2^(-N). Write s_i(z)=1 if z(i)=true and -1 otherwise; define

`S_n(z) = (1/N)Σi s_i(z)`, `A_n(z) = 3/2` if z(0)=true and `1/2` otherwise,
`W_n(z)=A_n(z)²/N`, and `H_n(z)=sqrt(W_n(z))`.

Here `sign`, `signMean`, `varianceFactor`, `varianceWitness`, and `seWitness` are precisely the five definitions just unfolded. The theorem has no external hypotheses. It asserts the following conjunction, with the quantifiers in the indicated order:

1. For every natural n, all of the following hold: E S_n=0; Var S_n=1/N; for every real ε>0, P(ε<|S_n|)≤1/(Nε²); E A_n=1; E A_n²=5/4; for every z, H_n(z)=A_n(z)/sqrt(N); E H_n=1/sqrt(N); E W_n-1/N=1/(4N); P(1/2<|W_n/(1/N)-1|)=1; and for every z, |W_n(z)-1/N|≤5/(4N).
2. S_n converges in probability to 0, in the finite-sum sense above.
3. W_n/(1/N) does not converge in probability to 1 (the negation of the full ε>0 convergence assertion).
4. W_n converges in probability to the changing target 1/N, i.e. its absolute estimation error tends to zero in probability.
5. For every n: P(W_n/(1/N)=1/4)=1/2; P(W_n/(1/N)=9/4)=1/2; for every z, W_n(z)/(1/N)=A_n(z)² and |W_n(z)-1/N|=|A_n(z)²-1|/N; and 0<1/(4N).
6. The deterministic real sequence 5/(4(n+1)) tends to zero.
7. For every n: E H_n=sqrt(Var S_n), and for every z, W_n(z)/(1/N) belongs to the finite set {1/4,9/4}.

The docstring calls these an audit witness, explicitly not either Table 16.1 estimator. It describes exact mean-SE agreement, positive finite-sample variance bias, relative inconsistency, point-estimate consistency, and absolute variance consistency.

Junk-value audit: N is always at least one. Its real cast, 1/N, 4N, and sqrt(N) are strictly positive, and ε²>0 wherever it is a denominator. W_n is positive. Thus neither real division by zero nor `Real.sqrt` at a negative argument can affect any asserted formula. All finite index types are nonempty. No truncating subtraction, logarithms, powers outside their domains, integrals, `toReal`, extrema, limsup/liminf, or partial-function defaults occur. Real powers here are natural squares, and limits are stated by `Tendsto`, not totalized limit operators.

## SAP.P045b.T23

Location: `SAP/P045b/Challenge/Part1.lean:31–33`; definition `Defs/Part4.lean:121–143`. It includes the entire T22 statement, with all definitions, quantifiers, and junk audit as above.

The remaining assertion is a conjunction of:

1. Exact rational comparisons: 3311/2660=473/380; for every real r in the finite set {4594/4532,1033/1045,3407/3666,841/838}, 1-71/1000≤r≤1+71/1000; 244/1000<473/380-1<245/1000; and 164/1000<2509/2155-1<165/1000. These are six numeric ratios altogether. There are no empirical data objects or Monte Carlo replicates in this clause.
2. For every family of types Ω_n, with a finite-type instance for every natural n, every family p_n of `Design (Ω_n)`, and every pair of real statistic families T_n and Vhat_n on Ω_n: assume (in this order) Var_pn(T_n)>0 for every n; Vhat_n(w)≥0 for every n and every w; Var_pn(T_n)→0; and `E_pn sqrt(Vhat_n) - sqrt(Var_pn T_n) →0`. Conclude Vhat_n converges in probability to Var_pn(T_n), using absolute error. A `Design` is exactly a real function p with p(w)≥0 at every w and Σw p(w)=1. It adds no other statistical assumptions. Convergence and moments are the finite sums already unfolded.
3. On the fixed sample space Bool with both masses 1/2, let s(b)=1 for true, -1 for false, and A(b)=3/2 for true, 1/2 for false. Then Var(s)=1, E sqrt(A²)=1, and P(1/2<|A²-1|)=1. Furthermore the constant-in-n sequence Vhat_n(b)=A(b)² does not converge in probability to the constant target 1 under these same two-point laws. There is no assumption of independent draws across n and none is needed for this definition of convergence in probability.
4. For every natural M>0 and every s:Fin M→ℝ with s(i)≥0 for all i, `(M^(-1)Σi s(i))² ≤ M^(-1)Σi s(i)²`.
5. Separately, for every natural M>0, every s:Fin M→ℝ with all entries nonnegative, and every real sd>0, `(mean(s)/sd)² ≤ mean(s²)/sd²`.

The docstring describes corrected finite-sample comparisons, the included witness, the vanishing-variance implication, the nonvanishing-variance counterexample, and the mean-square inequality. It does not explicitly state the general implication's assumptions in its prose.

Junk-value audit: all fixed rational denominators are nonzero. `Design.total` excludes an empty Ω_n, since the empty sum could not equal one. All general square-root arguments Vhat_n and Var(T_n) are nonnegative, the former by an explicit hypothesis and the latter also strictly positive by hypothesis. M>0 and sd>0 exclude the mean and normalized-inequality zero denominators. The implications use no division by a vanishing random variance. The general `InProbability` definition itself has no assumption that p is a probability law, but all its uses here are with normalized nonnegative masses. All other possible conventions listed in T22 are absent here as well.

## SAP.P045b.T24

Location: `SAP/P045b/Challenge/Part1.lean:35–37`; definition `Defs/Part4.lean:145–169`; helpers `Defs/Part1.lean:113–122`.

For any natural G>0, any group-size function n:Fin G→ℕ with n_g>0 for each g, and any real baseline schedule b_gi, define the equally group-weighted baseline

`B=(1/G)Σg [(1/n_g)Σi b_gi]`.

The `dilatedMarginal` schedule assigns values according to (own treatment, high regime): (true,true) gives 2b_gi; (false,true) gives (5/4)b_gi; (true,false) gives (3/2)b_gi; and (false,false) gives b_gi. `regimeMean` averages this schedule first over i in each group, then over groups, without group-size weighting. Denote those four averages by μ(own,high). The five quantities are Dψ=μ(true,true)-μ(false,true), Dφ=μ(true,false)-μ(false,false), I=μ(false,true)-μ(false,false), To=μ(true,true)-μ(false,false), and

`O=(2/3)μ(true,true)+(1/3)μ(false,true)-[(1/3)μ(true,false)+(2/3)μ(false,false)]`.

The first conjunct, universally quantified over G>0, n with all n_g>0, and b as above, asserts Dψ=(3/4)B, Dφ=(1/2)B, I=(1/4)B, To=B, O=(7/12)B; if B>0 then Dφ/Dψ=2/3 and Dφ<Dψ; To=Dψ+I; and if B≠0 then To-I≠Dφ. No sign or distribution assumption on b is made.

The second conjunct universally quantifies independently over G>0, n with positive sizes, and an arbitrary real schedule y_gi(own,high). With μ defined by the same nested means, it asserts μ(true,true)-μ(false,false)=[μ(true,true)-μ(false,true)]+[μ(false,true)-μ(false,false)]. This is a general identity independent of the dilated model.

The third conjunct independently universally quantifies over G>0, positive group sizes n, and real baselines b. For the dilated schedule and B just defined, it asserts `(2/3)μ(true,true)+(1/3)μ(false,true)=(7/4)B`, `(1/3)μ(true,false)+(2/3)μ(false,false)=(7/6)B`, and `(μ(true,true)-μ(false,false))-(μ(false,true)-μ(false,false))=(3/4)B`.

The docstring describes the five model-specific formulas, direct-effect ordering and ratio, and the identity using the high-regime direct effect for arbitrary schedules.

Junk-value audit: G and every n_g are strictly positive, excluding empty means. The only nonconstant denominator involving effects is Dψ in the B>0 implication; the earlier formula makes it strictly positive there. Without B>0 this ratio is not asserted. B≠0 guards the strict inequation that would otherwise fail at zero. Constants 2,3,4,6,12 are nonzero in ℝ. All subtraction is real, and none of the other totalized analytic or partial-function operations listed in the task occurs.

## SAP.P045b.T25

Location: `SAP/P045b/Challenge/Part2.lean:6–9`; definition `Defs/Part5.lean:11–15`; helpers `Defs/Part1.lean:11,18–26,34–40,74–84`.

The theorem is the negation of a universal assertion. The assertion being negated quantifies, in order, over every natural n>0; every real p with 0<p<1; every real schedule y:Fin n→(Fin n→Bool)→ℝ; and every arm label b:Bool. Let Z have mass `Πi (if Z_i then p else 1-p)`. Put

`E_b={z : there exists i with z_i=b}`,
`K_b(z)=Σi 1_{z_i=b}`,
`A_b(z)=[Σi 1_{z_i=b} y_i(z)]/K_b(z)`, and
`m_i(b)=[Σz P(z)1_{z_i=b} y_i(z)]/[Σz P(z)1_{z_i=b}]`.

These unfold `armExists`, `armMean`, and `marginal` (the last through `condMean`). The assertion is

`[Σz P(z)1_Eb(z) A_b(z)]/[Σz P(z)1_Eb(z)] = (1/n)Σi m_i(b)`.

Thus, classically, T25 states that there exist some n>0, interior p, real y, and arm b for which that equality fails. It provides no explicit witness in its statement. It does not quantify over a first-stage design or multiple groups. The docstring explicitly calls this a refutation of the printed within-group assertion and says that refuting this conjunct refutes the printed conjunction.

Junk-value audit: `armMean` as a total real function equals 0 on an empty arm by Lean's x/0=0 convention (its numerator is then also zero). This value is multiplied by zero in the conditional numerator, so it cannot influence the displayed conditional expectation. For n>0 and p strictly between 0 and 1, P(E_b)>0, and P(Z_i=b) is p or 1-p, also positive. All denominators that contribute to the claimed conditional and marginal expectations are therefore nonzero. Every y is finite-valued on a finite set. There are no measure integrals, undefined moments, or other analytic totalizations. The theorem's negation cannot obtain a witness by choosing an empty index type, p=0, or p=1 because those options fail its explicit antecedents.

## SAP.P045b.T26

Location: `SAP/P045b/Challenge/Part2.lean:11–14`; definition `Defs/Part5.lean:17–25`; helpers `Defs/Part1.lean:11,18,28–32,42–43` and `Defs/Part2.lean:16–51`.

This too is a negated universal assertion. Its quantified data, in order, are natural G,C with 2≤C≤G; group-size and treated-count functions n,m:Fin G→ℕ with 0<m_g<n_g for every g; and arbitrary real schedules a_gi,b_gi for individuals i:Fin(n_g). The schedules do not depend on peers' assignments.

`fixedAssignments(n,k)` is the finite set of Bool assignments with exactly k true coordinates. `crMass(n,k)(z)` is 1 divided by the cardinality of that set if z belongs to it, and 0 otherwise. The support is nonempty for the permitted m_g<n_g. `GroupAssignments n` is the dependent function type assigning to each g its own assignment in `Fin(n_g)→Bool`.

A sample point w=(S,z) consists of an arbitrary finite set S of groups and an assignment z_g for every group. `firstStageSets(G,C)` is the finite set of all C-element subsets of Fin G. The law is zero unless |S|=C; otherwise

`P(S,z)=1/(number of C-element group subsets) × Πg crMass(n_g,m_g)(z_g)`.

Thus the first stage selects C groups uniformly, and all within-group complete-randomization assignments are mutually independent and independent of S. Off-support assignments have mass zero.

For a finite set U of indices, write `avg_U(x)=(Σi∈U x_i)/|U|` and `s²_U(x)=[Σi∈U (x_i-avg_U(x))²]/(|U|-1)`, where the subtraction in the last denominator is in ℝ, not ℕ. Put A_g={i:z_g(i)=true} and B_g=(Fin n_g)\A_g. Then

`D_g(z_g)=avg_Ag(a_g)-avg_Bg(b_g)`.

Define

`v_g(z_g) = (if |A_g|≥2 then s²_Ag(a_g)/|A_g| else 0) + (if |B_g|≥2 then s²_Bg(b_g)/|B_g| else 0)`.

The point statistic is `T(S,z)=(1/C)Σg∈S D_g(z_g)`. The variance statistic is

`Vhat(S,z)=[(1-C/G)/C] s²_S(g↦D_g(z_g)) + [1/(CG)]Σg∈S v_g(z_g)`.

The universal assertion being negated is the conjunction:

- If there exists a single real d such that a_gi=b_gi+d for every group and individual, then E(Vhat)=Var(T).
- Var(T)≤E(Vhat).

All expectations and variances use the finite law above. Classically the statement supplies data meeting all count assumptions for which at least one of these two assertions fails; it does not assert failure of each separately. Its prose identifies the statistic as the package statistic with singleton-arm variance contributions dropped, and restricts its claimed refutation to extending the guarantee to that statistic when singleton arms are allowed. It explicitly disclaims refuting the Hudgens–Halloran estimator on the domain where all required arms have at least two units.

Junk-value audit: 2≤C≤G gives G,C>0 and a nonempty first-stage design. The within-group assumptions give n_g≥2 and at least one treated and one control unit on positive-mass assignments. Consequently all contributing group means are defined in ordinary mathematics. First-stage selected-set sample variance has C≥2 on support. For a singleton within-group arm, `rawSampleVar` has denominator zero and Lean returns zero, but `droppedWithin` independently and explicitly replaces the entire contribution by zero. This convention is central to the statistic and can affect the negated guarantee. For an empty set, `average` is zero and `rawSampleVar` has real denominator -1 and zero numerator; these values occur only off support for the means/variances used here. Off-support S of the wrong size also has zero mass. Thus there is no hidden use of empty-arm or wrong-size values in the finite sums. The subtraction |U|-1 is real and not truncated. No square roots, logarithms, `rpow`, integrals, `toReal`, extrema, sequence extrema, or defaults of partial functions occur.
