# Blind reading: SAP.P019b.T22

This reading was saved before opening `claims.json`, `record.json`, `earlier.json`, or `architect-report.md`. The inputs were `closure.json`, the Challenge docstring and declaration, the source of every definition in its closure, and compiled `#print` checks for the generated closure declarations in `scratch/ClosureRead.lean`.

Fingerprint: `72f0a122f3794c3aabec14d321ae7410c086227ec5d5088163c3da1c77cda67e`.

## Objects and definitions, unfolded

The Challenge theorem at `SAP/P019b/Challenge/Part1.lean:102` has type `T22WholeStatement`. There are no arguments or hypotheses outside that proposition. Its first conjunct is the universally quantified proposition `T22Statement`; all remaining conjuncts concern a particular eight-atom model.

For the universal part, first choose a type Ω in `Type`, a `Fintype Ω` instance, and a `Study Ω`. A study contains a finite law and functions W,V : Ω → ℕ and X,Y,Z : Ω → Bool. A finite law contains real weights p(ω), a proof p(ω) ≥ 0 for every ω, and a proof Σω p(ω) = 1. It imposes neither equal weights nor strict positivity of each weight. `FiniteLaw.mk` and `Study.mk` are the ordinary constructors for exactly these fields; the projections in the closure recover the indicated fields.

Write b(true)=1 and b(false)=0 for `bitVal`, and define the following finite sums and real arithmetic:

- E[f] = Σω p(ω)f(ω) (`FiniteLaw.mean`).
- P(D) = Σω p(ω)1_D(ω) (`FiniteLaw.prob`), for a predicate D with a decidability instance.
- E[f | D] = (Σω p(ω)1_D(ω)f(ω))/P(D) (`FiniteLaw.ce`).
- Var(f) = E[f²] − E[f]² (`FiniteLaw.variance`).
- Var(f | D) = E[f² | D] − E[f | D]² (`FiniteLaw.cv`).
- C(z,y) = {ω : Z(ω)=z and Y(ω)=y} (`Study.cell`).
- `Study.monotone` says, for every ω with p(ω)>0, Y(ω)=true implies X(ω)=true.
- `Study.noLiarsDesign` says, for every ω with p(ω)>0, the equality (V(ω):ℝ)=(W(ω):ℝ)+b(X(ω))b(Z(ω)) holds.
- `Study.treatmentIndependent` says, for every function f : ℕ → Bool → Bool → ℝ and every z : Bool,
  Σω p(ω)1_{Z=z}(ω)f(W(ω),X(ω),Y(ω)) = P(Z=z)Σω p(ω)f(W(ω),X(ω),Y(ω)).
  Thus Z is independent of the joint vector (W,X,Y), expressed by full expectation factorization, including zero-mass atoms only through their weights.
- `Study.nondegenerate` is the conjunction of: for every z,y : Bool, P(C(z,y))>0 and Var((V:ℝ) | C(z,y))>0; Var(b(Z))>0; and Var(b(Y))>0.
- δ = E[b(Y) | Z=true] − E[b(Y) | Z=false] (`Study.delta`).

For each n : ℕ the sample space is the type of functions s : Fin n → Ω. Its law (`FiniteLaw.iid`) assigns mass Πi p(s(i)). This is the unconditional ordered product law of n independent, identically distributed subjects; it neither fixes arm sizes nor conditions on occupied arms.

For such an s, set N_z(s)=Σi 1_{Z(s(i))=z}, a natural number (`Study.armCount`). The direct-arm mean M_z(s;c) is c if N_z(s)=0, and otherwise
Σi 1_{Z(s(i))=z}b(Y(s(i)))/(N_z(s):ℝ) (`Study.directArmMean`). Then
δ̂(s;c1,c0)=M_true(s;c1)−M_false(s;c0) (`Study.deltaHat`).

The direct-arm sample variance Q_z(s) is zero when N_z(s)<2; otherwise it is
Σi 1_{Z(s(i))=z}(b(Y(s(i)))−M_z(s;0))² / ((N_z(s):ℝ)−1) (`Study.directArmVariance`). The subtraction by one is in ℝ. The estimated variance D(s;cV) (`Study.deltaVarianceHat`) is Q_true(s)/(N_true(s):ℝ)+Q_false(s)/(N_false(s):ℝ) if both counts are at least two, and is cV otherwise.

Let G be Mathlib's `gaussianReal 0 1`, the real standard normal probability measure. `normalCDF(t)` is (G((−∞,t])).toReal. `normalPValue(e,h,v)` is 2 normalCDF(−|e−h|/Real.sqrt(v)). `WeakLimit P T G` means: for every f : ℝ → ℝ, if f is continuous and there exists C : ℝ with |f(x)|≤C for every x, the sequence
Σs (Πi p(s(i)))f(T(n,s)) converges, as n tends to infinity through natural numbers, to the Bochner integral ∫x f(x) dG. This is weak convergence tested against all bounded continuous real functions, with the sample law freshly defined for each n.

## Exact universal assertion and quantifier order

For every Ω, its finite-type instance, and S : Study Ω, the following two implications both hold:

1. If `S.treatmentIndependent`, P(Z=false)>0, and P(Z=true)>0, then δ=0. There is no monotonicity, no-liars, or nondegeneracy premise in this first implication.
2. If `S.treatmentIndependent` and `S.nondegenerate`, then for every three fixed real constants c1,c0,cV, simultaneously:
   - δ=0;
   - δ̂(s;c1,c0)/Real.sqrt(D(s;cV)) converges weakly under the product sample laws to G as n→∞;
   - for every u : ℝ with 0<u<1, the probability under that product law of
     2 normalCDF(−|δ̂(s;c1,c0)|/Real.sqrt(D(s;cV)))≤u
     converges to u as n→∞.

The completion constants are quantified after the study and its hypotheses and before the convergence assertions; they are constant in n and s. The p-value conclusion is at every interior CDF point, which expresses convergence in distribution to Uniform[0,1]. The second implication also has no monotonicity or no-liars premise. Nondegeneracy supplies positive arm probabilities through positive joint cells.

## Exact additional finite protocol

`WholeOrderAtom` is Bool × (Bool × Bool). Write its coordinates (R,B,Z). `wholeOrderLaw` assigns mass 1/16 to each atom with R=true and 3/16 to each atom with R=false. The four choices of (B,Z) for each R give total mass one. Equivalently R is Bernoulli(1/4), B and Z are fair, and all three coordinates are independent.

`wholeOrderStudy` uses that law and sets W=b(B) as a natural number, X=true, Y=R xor Z, Z equal to the third coordinate, and V=b(B)+b(Z) as a natural number. In particular, Y is R when Z=false and the Boolean complement of R when Z=true.

`WholeOrderEvent` is an inductive type with three distinct tagged constructors, each carrying a Bool: `discloseAssignment`, `recordDirectAnswer`, and `presentList`. `wholeOrderHistory(a,t)` for t : Fin 3 is `discloseAssignment(Z(a))` at t=0, `recordDirectAnswer(Y(a))` at t=1, and `presentList(Z(a))` at t=2. Its source is an explicit schedule; it is not a definition of no anticipation or of a randomized causal intervention.

After the universal assertion, `T22WholeStatement` asserts all of the following, in conjunction, without additional hypotheses:

1. This particular study satisfies monotonicity, the no-liars count equation, and nondegeneracy as defined above.
2. For every f : Bool → Bool → ℝ and z : Bool, E[1_{Z=z}f(R,B)]=P(Z=z)E[f(R,B)].
3. For every z : Bool, P(Z=z)=1/2.
4. For every atom a, Y(a)=if Z(a) then !R(a) else R(a).
5. For every atom a, history at 0,1,2 has respectively the three tagged values described above, and for every t : Fin 3 with t<2 the event is different from `presentList(Z(a))`.
6. The natural-number inequalities 0<1 and 1<2 hold.
7. For every z,y : Bool, P(C(z,y)) is 3/8 if z=y and 1/8 otherwise, and Var((V:ℝ) | C(z,y))=1/4.
8. Var(b(Y))=1/4 and Var(b(Z))=1/4.
9. δ=1/2 and the joint expectation factorization defining `treatmentIndependent` does not hold.

The protocol does not satisfy treatment independence: its direct answer responds to disclosed assignment. The theorem does not apply its universal null assertion to this protocol as though it did.

## Closure coverage, including generated declarations

The above unfolds every substantive declaration listed in `closure.json`: `FiniteLaw`, `FiniteLaw.mk`, `FiniteLaw.mass`, `FiniteLaw.mean`, `FiniteLaw.prob`, `FiniteLaw.ce`, `FiniteLaw.variance`, `FiniteLaw.cv`, `FiniteLaw.iid`; `Study`, `Study.mk`, `Study.law`, `Study.W`, `Study.X`, `Study.Y`, `Study.Z`, `Study.V`, `Study.monotone`, `Study.noLiarsDesign`, `Study.treatmentIndependent`, `Study.cell`, `Study.nondegenerate`, `Study.delta`, `Study.armCount`, `Study.directArmMean`, `Study.deltaHat`, `Study.directArmVariance`, `Study.deltaVarianceHat`; `bitVal`, `normalCDF`, `normalPValue`, `WeakLimit`, `T22Statement`, `T22WholeStatement`, `WholeOrderAtom`, `wholeOrderLaw`, `wholeOrderStudy`, `WholeOrderEvent` and its three constructors, and `wholeOrderHistory`.

The remaining listed declarations were read using compiled `#print` checks:

- `FiniteLaw.iid._proof_1` proves nonnegativity of each product mass from nonnegative factors. `FiniteLaw.iid._proof_2` proves total mass one by the product-of-sums identity.
- `wholeOrderLaw._proof_1` proves 1/16 and 3/16 are nonnegative. `wholeOrderLaw._proof_2` sums those weights over the Boolean product type to obtain one.
- `T13WholeStatement._proof_1`, `T13WholeStatement._proof_2`, `normalPValue._proof_1`, `wholeCNNAtomMass._proof_1`, `wholeCNNAtomMass._proof_2`, and `wholeCNNAtomMass._proof_3` are proofs of `Nat.AtLeastTwo` for respectively 4,2,2,16,8,3. Their names arise from Lean's sharing of auxiliary numeral-instance proofs; they impose no probabilistic hypotheses.
- `wholeOrderHistory._proof_1` proves `NeZero 3`, used for the finite time-index numerals.

## Junk-value and boundary conventions

- Real division by zero returns zero in Lean. Thus a conditional mean or variance on a probability-zero event would evaluate to zero by these definitions. All population conditional quantities used in the universal assertions have positive denominators under their respective premises. The concrete protocol has every cell probability at least 1/8 and both arm probabilities 1/2.
- Empty-arm means are explicitly completed by arbitrary fixed real constants, not inferred from the value of 0/0. Arm sample variances with fewer than two observations are explicitly zero. The final variance estimate is explicitly cV on samples with either arm count below two. Both latter divisions use positive denominators on their active branches.
- A completed variance cV may be negative. Mathlib's `Real.sqrt` is zero for nonpositive inputs. A zero sample variance can also occur with both arm counts at least two, for example if all answers in each arm agree. In either case the studentized statistic divides by zero and becomes zero, and the normal p-value becomes 2Φ(0)=1. The assertions are asymptotic under positive population arm and response probabilities, so this totalization must be checked for asymptotic irrelevance; it does affect individual finite samples.
- When n=0, `Fin 0` is empty, the sample type has one empty function, the product mass is the empty product 1, and all arm counts are empty sums 0. Thus δ̂=c1−c0 and D=cV. Limits at `atTop` discard this single initial index. An empty underlying Ω cannot carry `FiniteLaw`, because its mass sum would be 0 rather than 1; this does not make the whole universal assertion vacuous on inhabited finite types.
- Counts are natural numbers with exact casts to ℝ. The variance denominator uses real subtraction, not truncated natural subtraction. The count V in the witness uses natural addition. The time indices 0,1,2 are valid elements of `Fin 3`, so finite-numeral wraparound changes none of the scheduled events. The inequalities 0<1 and 1<2 are ordinary natural inequalities.
- `normalCDF` applies `ENNReal.toReal` to a mass bounded by the finite probability mass one, so its value at infinity convention is never used. The limiting Gaussian is a probability measure. Every continuous bounded test function in `WeakLimit` is measurable and integrable against it; its Bochner integral is an ordinary defined integral. Sample expectations are finite sums, so there is no nonintegrability convention on their side.
- There is no logarithm, real power, quantile, infimum/supremum, limsup/liminf, or default selection from a partial function in this closure. The histories use an exhaustive conditional on a three-element type; all their values are specified. Classical decidability affects computation of propositions, not the probabilities or the mathematical meaning.

## Docstring reading

The Challenge and `T22WholeStatement` docstrings describe the null, the studentized normal limit, and asymptotically uniform two-sided p-values. They explicitly limit the statistical result to finite underlying spaces with arbitrary real masses. They explicitly omit the extension to arbitrary measurable spaces, the general randomized causal-effect interpretation, and the positive delayed-treatment implication. They describe the extra protocol as assignment disclosure before the answer with only physical list display delayed, and expressly say it does not refute the printed design assertion. No comparison with the canonical claim or architect's label has been made at this stage.
