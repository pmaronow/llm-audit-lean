import AronowAudit.P022.Wave1.RandomizationVarianceBlueprint

/-!
# Blueprint: P022-T13, unbiasedness, equation (2), and Lemma 1 for every coupling

Record: P022-T13 / `AronowAudit.P022.sharp_bounds_and_variance`; resolution
`repair_and_prove`.

The frozen draft quantifies only over `N`-point pairings `z1, z0` with the given marginal
multisets, while Lemma 1 (p. 853; proof pp. 859–860) ranges over all joint distributions
with the empirical marginals `G_N, F_N`.  The repaired contract (mapper record 9, accepted
by both referees) is the conjunction of *every* conclusion of the frozen
`sharp_bounds_and_variance` with *every* conclusion of the frozen (also drafted)
`hoeffding_all_couplings`; the `example` below checks that `Target` is equivalent to that
conjunction.

Paper proof (map record 9): (1) actual randomization moments (shared
`RandomizationVariance`); (2) finite quantile quadrature on the rank cells
`(j/N, (j+1)/N)`; (3) every coupling with the empirical marginal CDFs is concentrated on the
finite grid, and after subtracting the marginal minima its product moment is a nonnegative
combination of joint upper-tail probabilities (here in the finite "layer" form
`x - a₍₁₎ = Σ_j Δ_j 1{a₍ⱼ₎ ≤ x}`), which lie between the Fréchet bounds
`max(0, p+q-1)` and `min(p, q)`, attained by the sorted and reverse-sorted pair laws;
(4) each finite pairing is such a coupling, and (2) is increasing affine in the covariance.

Nodes: shared `RandomizationVariance.N1`–`N4`, and `N1`–`N12` below.
Writers prove `theorem nk_proof : Nk` in `AronowAudit/P022/Wave1/SharpBounds/Nk.lean`.
Final file: `AronowAudit/P022/Wave1/SharpBounds.lean`, theorem
`AronowAudit.P022.Wave1.sharp_bounds_variance_and_all_couplings`.
-/

set_option autoImplicit false

namespace AronowAudit.P022.Wave1.SharpBounds

open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

/-- The uniform probability law on the `N` unit labels. -/
def unitLaw (N : ℕ) [NeZero N] : ProbabilityMeasure (Fin N) :=
  ⟨(PMF.uniformOfFintype (Fin N)).toMeasure, inferInstance⟩

/-- The empirical joint law `(1/N) Σ_i δ_(z1 i, z0 i)` of two paired arrays. -/
def pairLaw {N : ℕ} [NeZero N] (z1 z0 : Fin N → ℝ) : JointLaw :=
  (unitLaw N).map (fun i => (z1 i, z0 i))

/-- Increments of the sorted values: `a₍ⱼ₎ - a₍ⱼ₋₁₎` for `j ≥ 1` (zero-based), `0` at `j = 0`. -/
def sortedIncrement {N : ℕ} (y : Fin N → ℝ) (j : Fin N) : ℝ :=
  if 0 < j.val then
    sortedValues y j - sortedValues y ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩
  else 0

/-- **Target (P022-T13, repaired).** Every conclusion of `sharp_bounds_and_variance` and of
`hoeffding_all_couplings` (Section 2, p. 851; Lemma 1, p. 853). -/
def Target : Prop :=
  ∀ (d : Design) (y1 y0 : Fin d.N → ℝ),
    designExpectation d (estimatedEffect d y1 y0) = averageEffect d y1 y0 ∧
    trueVariance d y1 y0 = varianceExpression d.N d.m d.k
      (finiteVariance y1) (finiteVariance y0) (finiteCovariance y1 y0) ∧
    (∀ z1 z0 : Fin d.N → ℝ,
      List.Perm (List.ofFn z1) (List.ofFn y1) →
      List.Perm (List.ofFn z0) (List.ofFn y0) →
      sharpCovariance y1 y0 .L ≤ finiteCovariance z1 z0 ∧
      finiteCovariance z1 z0 ≤ sharpCovariance y1 y0 .H ∧
      populationBound d y1 y0 .L ≤ trueVariance d z1 z0 ∧
      trueVariance d z1 z0 ≤ populationBound d y1 y0 .H) ∧
    trueVariance d (sortedValues y1) (sortedValues y0) =
      populationBound d y1 y0 .H ∧
    trueVariance d (sortedValues y1) (fun i => sortedValues y0 i.rev) =
      populationBound d y1 y0 .L ∧
    (∀ J ∈ empiricalCompatibleLaws y1 y0,
      Integrable (fun p : ℝ × ℝ => p.1 * p.2) (J : Measure (ℝ × ℝ)) ∧
      sharpCovariance y1 y0 .L ≤ lawCovariance J ∧
      lawCovariance J ≤ sharpCovariance y1 y0 .H) ∧
    (∀ B, ∃ J ∈ empiricalCompatibleLaws y1 y0,
      lawCovariance J = sharpCovariance y1 y0 B ∧
      ∀ f : BoundedContinuousFunction (ℝ × ℝ) ℝ,
        (∫ p, f p ∂(J : Measure (ℝ × ℝ))) =
          ∫ u in (0 : ℝ)..1,
            f (empiricalQuantile y1 u, empiricalQuantile y0
              (if B = BoundSide.H then u else 1 - u)))

/-- Fidelity check: `Target` is equivalent to the conjunction of the two frozen drafts'
statements (only their *types* are read; their unfinished draft proofs are never used). -/
example : Target ↔ (type_of% @AronowAudit.P022.sharp_bounds_and_variance) ∧
    (type_of% @AronowAudit.P022.hoeffding_all_couplings) := by
  constructor
  · intro hT
    exact ⟨fun d y1 y0 => ⟨(hT d y1 y0).1, (hT d y1 y0).2.1, (hT d y1 y0).2.2.1,
        (hT d y1 y0).2.2.2.1, (hT d y1 y0).2.2.2.2.1⟩,
      fun d y1 y0 => ⟨(hT d y1 y0).2.2.2.2.2.1, (hT d y1 y0).2.2.2.2.2.2⟩⟩
  · rintro ⟨h1, h2⟩ d y1 y0
    obtain ⟨a, b, c, e, f⟩ := h1 d y1 y0
    obtain ⟨g, i⟩ := h2 d y1 y0
    exact ⟨a, b, c, e, f, g, i⟩

/-! ## Nodes -/

/-- **Node N1** (map record 9, step 2/4: "Sorting permutes each marginal multiset,
preserving means and variances"). Averages of any function of an array are invariant under
permutation of its entries. Suggested route: `finiteMean v = (List.ofFn v).sum / N`
(`Finset.expect_eq_sum_div_card`, `List.sum_ofFn`), `List.Perm.map`, `List.Perm.sum_eq`. -/
def N1 : Prop :=
  ∀ {N : ℕ} (z y : Fin N → ℝ), List.Perm (List.ofFn z) (List.ofFn y) →
    ∀ g : ℝ → ℝ, finiteMean (fun i => g (z i)) = finiteMean (fun i => g (y i))

/-- **Node N2** (map record 9, step 2: "Let a_1≤...≤a_N ... be the sorted arrays,
retaining duplicates"). `sortedValues` is a sorted rearrangement, and so is its reversal.
Suggested route: `List.mergeSort_perm`, `List.length_mergeSort`, `List.sortedLE_mergeSort`
(or `List.pairwise_mergeSort`), `List.ofFn_getElem`/`List.getD_eq_getElem`, and
`Fin.revPerm` for the reversed list. -/
def N2 : Prop :=
  ∀ {N : ℕ} (y : Fin N → ℝ),
    List.Perm (List.ofFn (sortedValues y)) (List.ofFn y) ∧
    List.Perm (List.ofFn (fun i => sortedValues y i.rev)) (List.ofFn y) ∧
    Monotone (sortedValues y)

/-- **Node N3** (map record 9, step 2: "Except at the finitely many endpoints j/N,
empiricalQuantile equals a_j on ((j-1)/N,j/N)"). Rank cells, zero-based: on
`(j/N, (j+1)/N)` one has `⌈N u⌉ = j+1` and `⌈N(1-u)⌉ = N-j`, so the quantile is
`sortedValues y j` and the reflected quantile is `sortedValues y j.rev`.
Suggested route: `Nat.ceil_eq_iff`, `orderStatistic`, `List.getD`. -/
def N3 : Prop :=
  ∀ {N : ℕ} (y : Fin N → ℝ) (j : Fin N) (u : ℝ),
    (j : ℝ) / N < u → u < ((j : ℝ) + 1) / N →
      empiricalQuantile y u = sortedValues y j ∧
      empiricalQuantile y (1 - u) = sortedValues y j.rev

/-- **Node N4** (map record 9, step 2: "Endpoints have Lebesgue measure zero, so the
totalized rank conventions do not affect any integral"). Interval integral of a function
that is constant on each open rank cell. `F` is arbitrary off the cells (a finite null set).
Suggested route: `intervalIntegral.sum_integral_adjacent_intervals` on the knots `j/N`, and
on each cell `intervalIntegral.integral_congr_ae` (or `integral_Ioc` with
`MeasureTheory.setIntegral_congr_ae` after removing the right endpoint) plus
`intervalIntegral.integral_const`. -/
def N4 : Prop :=
  ∀ {N : ℕ} [NeZero N] (F : ℝ → ℝ) (c : Fin N → ℝ),
    (∀ (j : Fin N) (u : ℝ), (j : ℝ) / N < u → u < ((j : ℝ) + 1) / N → F u = c j) →
      ∫ u in (0 : ℝ)..1, F u = finiteMean c

/-- **Node N5** (map record 9, step 3: "Explicit endpoint measures are
J_H=(1/N)sum_j delta_(a_j,b_j) ... Borel probability measures"; step 4: "Any arrays z1,z0
... define the probability measure (1/N)sum_i delta_(z1_i,z0_i)"). Integrals, marginal
CDFs, joint upper-tail probabilities and covariance of an empirical pair law.
Suggested route: `ProbabilityMeasure.toMeasure_map`, `integral_map` (every map out of
`Fin N` is measurable: `measurable_of_finite`/`Measurable.of_discrete`), `PMF.integral_eq_sum`,
`PMF.toMeasure_uniformOfFintype_apply`, `Measure.map_apply`, and `N12` for the covariance. -/
def N5 : Prop :=
  ∀ {N : ℕ} [NeZero N] (z1 z0 : Fin N → ℝ),
    (∀ g : ℝ × ℝ → ℝ, Measurable g →
      ∫ p, g p ∂(pairLaw z1 z0 : Measure (ℝ × ℝ)) = finiteMean (fun i => g (z1 i, z0 i))) ∧
    (∀ x, lawCDF (pairLaw z1 z0) true x = empiricalCDF z1 x ∧
      lawCDF (pairLaw z1 z0) false x = empiricalCDF z0 x) ∧
    (∀ c e : ℝ, ((pairLaw z1 z0 : Measure (ℝ × ℝ)) {p | c ≤ p.1 ∧ e ≤ p.2}).toReal =
      finiteMean (fun i => if c ≤ z1 i ∧ e ≤ z0 i then (1 : ℝ) else 0)) ∧
    lawCovariance (pairLaw z1 z0) = finiteCovariance z1 z0

/-- **Node N6** (map record 9, step 3: "Equality of CDFs implies equality of the
one-dimensional Borel marginal measures"). The marginals of a compatible law are the
empirical laws. Suggested route: `MeasureTheory.Measure.ext_of_Iic` (finite measures on
`ℝ`), `Measure.map_apply` with `measurable_fst`/`measurable_snd` and `measurableSet_Iic`,
and `PMF.toMeasure_uniformOfFintype_apply` to evaluate `empiricalCDF`. -/
def N6 : Prop :=
  ∀ {N : ℕ} [NeZero N] (y1 y0 : Fin N → ℝ) (J : JointLaw),
    J ∈ empiricalCompatibleLaws y1 y0 →
      (J : Measure (ℝ × ℝ)).map Prod.fst = ((unitLaw N : Measure (Fin N))).map y1 ∧
      (J : Measure (ℝ × ℝ)).map Prod.snd = ((unitLaw N : Measure (Fin N))).map y0

/-- **Node N7** (map record 9, step 3: "Consequently its first coordinate lies almost
surely in the finite support of y1 and its second in that of y0. Both coordinates and
their product are bounded almost surely; all stated integrals exist and their marginal
means equal the finite means"). Consequences of the marginal identification: a.e. finite
support, integrability of every measurable function (it is bounded on the support), the
marginal means, and the marginal upper-tail probabilities.
Suggested route: `ae_map_iff`/`MeasureTheory.ae_of_ae_map` for the support,
`Integrable.of_bound`-style bounds on the finite grid, `integral_map` for the means. -/
def N7 : Prop :=
  ∀ {N : ℕ} [NeZero N] (y1 y0 : Fin N → ℝ) (J : JointLaw),
    (J : Measure (ℝ × ℝ)).map Prod.fst = ((unitLaw N : Measure (Fin N))).map y1 →
    (J : Measure (ℝ × ℝ)).map Prod.snd = ((unitLaw N : Measure (Fin N))).map y0 →
      (∀ᵐ p ∂(J : Measure (ℝ × ℝ)), p.1 ∈ Set.range y1 ∧ p.2 ∈ Set.range y0) ∧
      (∀ g : ℝ × ℝ → ℝ, Measurable g → Integrable g (J : Measure (ℝ × ℝ))) ∧
      lawMean J true = finiteMean y1 ∧ lawMean J false = finiteMean y0 ∧
      (∀ c : ℝ, ((J : Measure (ℝ × ℝ)) {p | c ≤ p.1}).toReal =
        finiteMean (fun i => if c ≤ y1 i then (1 : ℝ) else 0)) ∧
      (∀ e : ℝ, ((J : Measure (ℝ × ℝ)) {p | e ≤ p.2}).toReal =
        finiteMean (fun i => if e ≤ y0 i then (1 : ℝ) else 0))

/-- **Node N8** (map record 9, step 3: "Subtract the finite marginal minima A,B, giving
X'=X-A≥0 ... E[X'Y']=integral ... P(X'>s,Y'>t)"; finite layer form). For a value `x` of
the array, `x - a₍₀₎ = Σ_j Δ_j 1{a₍ⱼ₎ ≤ x}` with nonnegative increments `Δ_j`
(telescoping over the initial segment `{j | a₍ⱼ₎ ≤ x}`). Stated as a consequence of `N2`. -/
def N8 : Prop :=
  N2 → ∀ {N : ℕ} [NeZero N] (y : Fin N → ℝ),
    (∀ j, 0 ≤ sortedIncrement y j) ∧
    ∀ x ∈ Set.range y, x - sortedValues y 0 =
      ∑ j, sortedIncrement y j * (if sortedValues y j ≤ x then (1 : ℝ) else 0)

/-- **Node N9** (map record 9, step 3: "For aligned quantiles, both upper-tail events are
terminal intervals ... intersection has length min(p_s,q_t). For reversed quantiles, one
is terminal and one initial, giving length max(0,p_s+q_t-1)"). Joint upper-tail
frequencies of monotone (resp. monotone and antitone) arrays. Suggested route: the sets
`{i | c ≤ s i}` are upper sets of `Fin N` (`Finset.filter`, `Fin.rev` is an involution). -/
def N9 : Prop :=
  ∀ {N : ℕ} (s1 s0 : Fin N → ℝ), Monotone s1 → Monotone s0 → ∀ c e : ℝ,
    finiteMean (fun i => if c ≤ s1 i ∧ e ≤ s0 i then (1 : ℝ) else 0) =
      min (finiteMean (fun i => if c ≤ s1 i then (1 : ℝ) else 0))
        (finiteMean (fun i => if e ≤ s0 i then (1 : ℝ) else 0)) ∧
    finiteMean (fun i => if c ≤ s1 i ∧ e ≤ s0 i.rev then (1 : ℝ) else 0) =
      max 0 (finiteMean (fun i => if c ≤ s1 i then (1 : ℝ) else 0) +
        finiteMean (fun i => if e ≤ s0 i then (1 : ℝ) else 0) - 1)

/-- **Node N10** (map record 9, step 3: "By Tonelli applied to the bounded nonnegative
indicators ... Adding back A E Y'+B E X'+AB preserves the bounds"). Layer representation of
the covariance of a law concentrated on the grid, given the two layer identities (supplied
by `N8`) and the marginal means. Integrate the a.e. identity
`(p.1-a)(p.2-b) = Σ_j Σ_l Δ¹_j Δ⁰_l 1{a_j ≤ p.1} 1{b_l ≤ p.2}` (`integral_congr_ae`,
`integral_finset_sum`, `integral_indicator_one`/`integral_indicator_const`), then expand
`(p.1-μ1)(p.2-μ0)`. -/
def N10 : Prop :=
  ∀ {N : ℕ} [NeZero N] (y1 y0 : Fin N → ℝ) (J : JointLaw),
    (∀ x ∈ Set.range y1, x - sortedValues y1 0 =
      ∑ j, sortedIncrement y1 j * (if sortedValues y1 j ≤ x then (1 : ℝ) else 0)) →
    (∀ x ∈ Set.range y0, x - sortedValues y0 0 =
      ∑ j, sortedIncrement y0 j * (if sortedValues y0 j ≤ x then (1 : ℝ) else 0)) →
    (∀ᵐ p ∂(J : Measure (ℝ × ℝ)), p.1 ∈ Set.range y1 ∧ p.2 ∈ Set.range y0) →
    (∀ g : ℝ × ℝ → ℝ, Measurable g → Integrable g (J : Measure (ℝ × ℝ))) →
    lawMean J true = finiteMean y1 → lawMean J false = finiteMean y0 →
      lawCovariance J =
        (∑ j, ∑ l, sortedIncrement y1 j * sortedIncrement y0 l *
          ((J : Measure (ℝ × ℝ)) {p | sortedValues y1 j ≤ p.1 ∧
            sortedValues y0 l ≤ p.2}).toReal) -
        (finiteMean y1 - sortedValues y1 0) * (finiteMean y0 - sortedValues y0 0)

/-- **Node N11** (map record 9, step 3: "elementary inclusion/exclusion gives
max(0,p_s+q_t-1)≤P(X'>s,Y'>t)≤min(p_s,q_t)"). Fréchet bounds for a joint upper-tail
probability. Suggested route: `measure_mono`, `measure_union_le`, `prob_le_one`,
`ENNReal.toReal_mono`. -/
def N11 : Prop :=
  ∀ (J : JointLaw) (c e : ℝ),
    ((J : Measure (ℝ × ℝ)) {p | c ≤ p.1 ∧ e ≤ p.2}).toReal ≤
      min ((J : Measure (ℝ × ℝ)) {p | c ≤ p.1}).toReal
        ((J : Measure (ℝ × ℝ)) {p | e ≤ p.2}).toReal ∧
    ((J : Measure (ℝ × ℝ)) {p | c ≤ p.1}).toReal +
        ((J : Measure (ℝ × ℝ)) {p | e ≤ p.2}).toReal - 1 ≤
      ((J : Measure (ℝ × ℝ)) {p | c ≤ p.1 ∧ e ≤ p.2}).toReal

/-- **Node N12** (finite moment algebra, as `finite_variance_second_moment`). The finite
covariance is the mean product minus the product of means. -/
def N12 : Prop :=
  ∀ {N : ℕ} [NeZero N] (v w : Fin N → ℝ),
    finiteCovariance v w = finiteMean (fun i => v i * w i) - finiteMean v * finiteMean w

/-! ## Glue (proved here from the nodes) -/

theorem mean_perm (h1 : N1) {N : ℕ} {z y : Fin N → ℝ}
    (h : List.Perm (List.ofFn z) (List.ofFn y)) : finiteMean z = finiteMean y :=
  h1 z y h (fun x => x)

theorem variance_perm (h1 : N1) {N : ℕ} {z y : Fin N → ℝ}
    (h : List.Perm (List.ofFn z) (List.ofFn y)) : finiteVariance z = finiteVariance y := by
  unfold finiteVariance
  rw [mean_perm h1 h]
  exact h1 z y h (fun x => (x - finiteMean y) ^ 2)

theorem cdf_perm (h1 : N1) {N : ℕ} {z y : Fin N → ℝ}
    (h : List.Perm (List.ofFn z) (List.ofFn y)) (x : ℝ) :
    empiricalCDF z x = empiricalCDF y x :=
  h1 z y h (fun t => if t ≤ x then 1 else 0)

theorem tail_perm (h1 : N1) {N : ℕ} {z y : Fin N → ℝ}
    (h : List.Perm (List.ofFn z) (List.ofFn y)) (c : ℝ) :
    finiteMean (fun i => if c ≤ z i then (1 : ℝ) else 0) =
      finiteMean (fun i => if c ≤ y i then (1 : ℝ) else 0) :=
  h1 z y h (fun t => if c ≤ t then 1 else 0)

/-- Pair laws of rearrangements are compatible couplings. -/
theorem pair_compatible (h1 : N1) (h5 : N5) {N : ℕ} [NeZero N] {y1 y0 z1 z0 : Fin N → ℝ}
    (hz1 : List.Perm (List.ofFn z1) (List.ofFn y1))
    (hz0 : List.Perm (List.ofFn z0) (List.ofFn y0)) :
    pairLaw z1 z0 ∈ empiricalCompatibleLaws y1 y0 := by
  intro x
  rw [((h5 z1 z0).2.1 x).1, ((h5 z1 z0).2.1 x).2, cdf_perm h1 hz1, cdf_perm h1 hz0]
  exact ⟨rfl, rfl⟩

/-- Quantile quadrature, assembled from the rank cells `N3` and the step integral `N4`. -/
theorem quadrature (h3 : N3) (h4 : N4) {N : ℕ} [NeZero N] (y1 y0 : Fin N → ℝ)
    (B : BoundSide) (g : ℝ × ℝ → ℝ) :
    ∫ u in (0 : ℝ)..1, g (empiricalQuantile y1 u,
        empiricalQuantile y0 (if B = BoundSide.H then u else 1 - u)) =
      finiteMean (fun j => g (sortedValues y1 j,
        sortedValues y0 (if B = BoundSide.H then j else j.rev))) := by
  apply h4
  intro j u hl hu
  obtain ⟨q1, -⟩ := h3 y1 j u hl hu
  obtain ⟨r1, r2⟩ := h3 y0 j u hl hu
  cases B
  · simp only [↓reduceIte]
    rw [q1, r1]
  · simp only [reduceCtorEq, ↓reduceIte]
    rw [q1, r2]

/-- The sorted and reverse-sorted finite covariances are the two sharp covariances. -/
theorem sorted_sharp (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h12 : N12)
    {N : ℕ} [NeZero N] (y1 y0 : Fin N → ℝ) :
    finiteCovariance (sortedValues y1) (sortedValues y0) = sharpCovariance y1 y0 .H ∧
    finiteCovariance (sortedValues y1) (fun i => sortedValues y0 i.rev) =
      sharpCovariance y1 y0 .L := by
  obtain ⟨p1, -, -⟩ := h2 y1
  obtain ⟨p0, p0r, -⟩ := h2 y0
  have qH := quadrature h3 h4 y1 y0 .H (fun p => p.1 * p.2)
  have qL := quadrature h3 h4 y1 y0 .L (fun p => p.1 * p.2)
  simp only [reduceCtorEq, ↓reduceIte] at qH qL
  constructor
  · rw [h12, mean_perm h1 p1, mean_perm h1 p0]
    unfold sharpCovariance
    simp only [↓reduceIte]
    rw [qH]
  · rw [h12, mean_perm h1 p1, mean_perm h1 p0r]
    unfold sharpCovariance
    simp only [reduceCtorEq, ↓reduceIte]
    rw [qL]

/-- Equation (2) is increasing in the covariance argument (coefficient `2/(N-1) > 0`). -/
theorem varianceExpression_mono {N m k : ℕ} (hN : 2 ≤ N) (v1 v0 : ℝ) {c c' : ℝ}
    (hc : c ≤ c') : varianceExpression N m k v1 v0 c ≤ varianceExpression N m k v1 v0 c' := by
  unfold varianceExpression
  have hN1 : 0 < (N : ℝ) - 1 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  apply div_le_div_of_nonneg_right _ hN1.le
  linarith

/-- For every compatible coupling: the layer representation of its covariance and the
Fréchet bounds on its joint upper-tail probabilities at the grid points. -/
theorem compatible_facts (h1 : N1) (h2 : N2) (h6 : N6) (h7 : N7) (h8 : N8) (h10 : N10)
    (h11 : N11) {N : ℕ} [NeZero N] (y1 y0 : Fin N → ℝ) (J : JointLaw)
    (hJ : J ∈ empiricalCompatibleLaws y1 y0) :
    Integrable (fun p : ℝ × ℝ => p.1 * p.2) (J : Measure (ℝ × ℝ)) ∧
    lawCovariance J =
        (∑ j, ∑ l, sortedIncrement y1 j * sortedIncrement y0 l *
          ((J : Measure (ℝ × ℝ)) {p | sortedValues y1 j ≤ p.1 ∧
            sortedValues y0 l ≤ p.2}).toReal) -
        (finiteMean y1 - sortedValues y1 0) * (finiteMean y0 - sortedValues y0 0) ∧
    ∀ c e : ℝ,
      ((J : Measure (ℝ × ℝ)) {p | c ≤ p.1 ∧ e ≤ p.2}).toReal ≤
        min (finiteMean (fun i => if c ≤ sortedValues y1 i then (1 : ℝ) else 0))
          (finiteMean (fun i => if e ≤ sortedValues y0 i then (1 : ℝ) else 0)) ∧
      finiteMean (fun i => if c ≤ sortedValues y1 i then (1 : ℝ) else 0) +
          finiteMean (fun i => if e ≤ sortedValues y0 i then (1 : ℝ) else 0) - 1 ≤
        ((J : Measure (ℝ × ℝ)) {p | c ≤ p.1 ∧ e ≤ p.2}).toReal := by
  obtain ⟨hfst, hsnd⟩ := h6 y1 y0 J hJ
  obtain ⟨hsupp, hint, hm1, hm0, ht1, ht0⟩ := h7 y1 y0 J hfst hsnd
  obtain ⟨p1, -, -⟩ := h2 y1
  obtain ⟨p0, -, -⟩ := h2 y0
  refine ⟨hint _ (measurable_fst.mul measurable_snd),
    h10 y1 y0 J ((h8 h2 y1).2) ((h8 h2 y0).2) hsupp hint hm1 hm0, ?_⟩
  intro c e
  obtain ⟨hu, hl⟩ := h11 J c e
  rw [ht1, ht0, ← tail_perm h1 p1, ← tail_perm h1 p0] at hu hl
  exact ⟨hu, hl⟩

/-! ## Assembly -/

/-- **Assembly.** The nodes suffice for the repaired P022-T13 contract. -/
theorem assemble (r1 : RandomizationVariance.N1) (r2 : RandomizationVariance.N2)
    (r3 : RandomizationVariance.N3) (r4 : RandomizationVariance.N4)
    (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7) (h8 : N8)
    (h9 : N9) (h10 : N10) (h11 : N11) (h12 : N12) : Target := by
  intro d y1 y0
  have : NeZero d.N := ⟨by have := d.population_min; omega⟩
  have hRV := RandomizationVariance.assemble r1 r2 r3 r4
  have hN2 : 2 ≤ d.N := by have := d.population_min; omega
  obtain ⟨p1, -, mono1⟩ := h2 y1
  obtain ⟨p0, p0r, mono0⟩ := h2 y0
  obtain ⟨sH, sL⟩ := sorted_sharp h1 h2 h3 h4 h12 y1 y0
  have cH : pairLaw (sortedValues y1) (sortedValues y0) ∈ empiricalCompatibleLaws y1 y0 :=
    pair_compatible h1 h5 p1 p0
  have cL : pairLaw (sortedValues y1) (fun i => sortedValues y0 i.rev) ∈
      empiricalCompatibleLaws y1 y0 := pair_compatible h1 h5 p1 p0r
  -- the covariance bounds for every compatible coupling
  have hcoup : ∀ J ∈ empiricalCompatibleLaws y1 y0,
      Integrable (fun p : ℝ × ℝ => p.1 * p.2) (J : Measure (ℝ × ℝ)) ∧
      sharpCovariance y1 y0 .L ≤ lawCovariance J ∧
      lawCovariance J ≤ sharpCovariance y1 y0 .H := by
    intro J hJ
    obtain ⟨hint, hrep, hfr⟩ := compatible_facts h1 h2 h6 h7 h8 h10 h11 y1 y0 J hJ
    obtain ⟨-, hrepH, -⟩ := compatible_facts h1 h2 h6 h7 h8 h10 h11 y1 y0 _ cH
    obtain ⟨-, hrepL, -⟩ := compatible_facts h1 h2 h6 h7 h8 h10 h11 y1 y0 _ cL
    have hcovH : lawCovariance (pairLaw (sortedValues y1) (sortedValues y0)) =
        sharpCovariance y1 y0 .H := by rw [(h5 _ _).2.2.2, sH]
    have hcovL : lawCovariance (pairLaw (sortedValues y1) (fun i => sortedValues y0 i.rev)) =
        sharpCovariance y1 y0 .L := by rw [(h5 _ _).2.2.2, sL]
    have hinc1 := (h8 h2 y1).1
    have hinc0 := (h8 h2 y0).1
    refine ⟨hint, ?_, ?_⟩
    · rw [← hcovL, hrep, hrepL]
      apply sub_le_sub_right
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hinc1 j) (hinc0 l))
      rw [(h5 _ _).2.2.1, (h9 _ _ mono1 mono0 _ _).2]
      exact max_le ENNReal.toReal_nonneg ((hfr _ _).2)
    · rw [← hcovH, hrep, hrepH]
      apply sub_le_sub_right
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hinc1 j) (hinc0 l))
      rw [(h5 _ _).2.2.1, (h9 _ _ mono1 mono0 _ _).1]
      exact (hfr _ _).1
  refine ⟨difference_in_means_unbiased d y1 y0, hRV d y1 y0, ?_, ?_, ?_, hcoup, ?_⟩
  · -- finite pairings
    intro z1 z0 hz1 hz0
    have hJ := pair_compatible h1 h5 hz1 hz0
    have hcov : lawCovariance (pairLaw z1 z0) = finiteCovariance z1 z0 := (h5 z1 z0).2.2.2
    obtain ⟨-, hlo, hhi⟩ := hcoup _ hJ
    rw [hcov] at hlo hhi
    refine ⟨hlo, hhi, ?_, ?_⟩
    · rw [hRV, variance_perm h1 hz1, variance_perm h1 hz0]
      exact varianceExpression_mono hN2 _ _ hlo
    · rw [hRV, variance_perm h1 hz1, variance_perm h1 hz0]
      exact varianceExpression_mono hN2 _ _ hhi
  · rw [hRV, variance_perm h1 p1, variance_perm h1 p0, sH]
    rfl
  · rw [hRV, variance_perm h1 p1, variance_perm h1 p0r, sL]
    rfl
  · -- attainment by the sorted / reverse-sorted pair laws
    intro B
    cases B
    · refine ⟨_, cH, by rw [(h5 _ _).2.2.2, sH], fun f => ?_⟩
      rw [(h5 _ _).1 f f.continuous.measurable, quadrature h3 h4 y1 y0 .H f]
      simp only [↓reduceIte]
    · refine ⟨_, cL, by rw [(h5 _ _).2.2.2, sL], fun f => ?_⟩
      rw [(h5 _ _).1 f f.continuous.measurable, quadrature h3 h4 y1 y0 .L f]
      simp only [reduceCtorEq, ↓reduceIte]

end

end AronowAudit.P022.Wave1.SharpBounds
