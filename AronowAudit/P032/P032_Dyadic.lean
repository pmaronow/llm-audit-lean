import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.HasLawExists
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
Carlson, Incerti and Aronow, *Dyadic Clustering in International
Relations*, Political Analysis 32 (2024), 186–198. All finite sums over pairs
are ordered sums. No finite-sample factors or spectral projection are hidden
inside the sandwich definitions. False printed claims are recorded only as
propositions and refuted separately.
-/
namespace AronowAudit.P032
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
open scoped BigOperators
open Matrix MeasureTheory ProbabilityTheory Filter

noncomputable section

/-- A dyad is an unordered set of two distinct members. The paper calls
non-incident dyads "dyads that do not share a common member" (p. 187).
The cardinality field makes the ordinary between-country assumption explicit. -/
structure Dyad (M : Type*) where
  members : Finset M
  two : members.card = 2

variable {R M P : Type*} [Fintype R] [Fintype M] [Fintype P]
  [DecidableEq R] [DecidableEq M] [DecidableEq P]

/-- Table 4 (p. 190): "only observations assumed to be independent are those
for which the dyad does not share any members". Diagonal entries are included. -/
def dyPattern (d : R → Dyad M) (r s : R) : ℝ :=
  if (d r).members ∩ (d s).members |>.Nonempty then 1 else 0

/-- Table 3 (p. 190): errors can correlate when observations "share both
members of the dyad", regardless of period. Dyads here are unordered (p. 192). -/
def repeatPattern (d : R → Dyad M) (r s : R) : ℝ :=
  if (d r).members = (d s).members then 1 else 0

/-- Table 2 (p. 190): "no dependence across observations whatsoever";
the heteroskedasticity-consistent component is diagonal in records. -/
def recordPattern (r s : R) : ℝ := if r = s then 1 else 0

/-- The "dyad-member-i-specific clustered" component (p. 191): incident
records form one cluster, outsiders each form a singleton. The singleton
convention follows the released code (targets T4/T11).
This Lean definition specifies what the published software computes. -/
def memberPattern (d : R → Dyad M) (i : M) (r s : R) : ℝ :=
  (if i ∈ (d r).members ∧ i ∈ (d s).members then 1 else 0) +
  (if r = s ∧ i ∉ (d r).members then 1 else 0)

/-- "substituting residuals for errors" in the sandwich (p. 189): with
bread-premultiplied record scores z, the unadjusted covariance is
Σ_{r,s} P_{rs} z_r z_s^T (T4). -/
def scoreSandwich (pattern : R → R → ℝ) (z : R → P → ℝ) : Matrix P P ℝ :=
  fun i j => ∑ r, ∑ s, pattern r s * z r i * z s j

/-- The scalar quadratic form h^T A h, in the sandwich display on p. 189
and the corrected comparison (T2); finite observation sums, ordered pairs. -/
def quadratic (A : Matrix R R ℝ) (h : R → ℝ) : ℝ :=
  ∑ r, ∑ s, h r * h s * A r s

/-- Ω_D retains entries for incident records and sets only non-incident
entries to zero, the population version of Table 4 (p. 190; T2). -/
def dyRestriction (d : R → Dyad M) (A : Matrix R R ℝ) : Matrix R R ℝ :=
  fun r s => dyPattern d r s * A r s

/-- The correction to pp. 187, 191, 196 (T2): Δ_c is the ordered sum of
h_r h_s Ω_rs over disjoint dyads, not the unweighted covariance sum. -/
def omittedContribution (d : R → Dyad M) (A : Matrix R R ℝ) (h : R → ℝ) : ℝ :=
  ∑ r, ∑ s, if ((d r).members ∩ (d s).members).Nonempty then 0
    else h r * h s * A r s

/-- Auxiliary cardinality fact for T4(ii): two distinct two-member dyads
share at most one member. Equal dyads share two. -/
theorem dyad_intersection_cases (a b : Dyad M) :
    (a.members = b.members ∧ (a.members ∩ b.members).card = 2) ∨
    (a.members ≠ b.members ∧ (a.members ∩ b.members).card ≤ 1) := by
  by_cases h : a.members = b.members
  · left; simp [h, b.two]
  · right; refine ⟨h, ?_⟩
    have hle : (a.members ∩ b.members).card ≤ 2 :=
      a.two ▸ Finset.card_le_card Finset.inter_subset_left
    have hn : (a.members ∩ b.members).card ≠ 2 := by
      intro hc
      have ha : a.members ∩ b.members = a.members :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [a.two, hc])
      have hb : a.members ∩ b.members = b.members :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by rw [b.two, hc])
      exact h (ha.symm.trans hb)
    omega

/-- T4(ii)/T11, p. 191: the four-case coefficient count for each ordered
record pair. Every diagonal appears N times, equal off-diagonal dyads twice,
distinct incident dyads once, disjoint dyads zero times before subtraction. -/
theorem decomposition_coefficient (d : R → Dyad M) (r s : R) :
    (∑ i, memberPattern d i r s) - repeatPattern d r s -
      ((Fintype.card M : ℝ) - 2) * recordPattern r s = dyPattern d r s := by
  by_cases hrs : r = s
  · subst s
    have hmem : ∀ i, memberPattern d i r r = 1 := by
      intro i; by_cases hi : i ∈ (d r).members <;> simp [memberPattern, hi]
    have hne : ((d r).members ∩ (d r).members).Nonempty := by
      simpa using Finset.card_pos.mp (show 0 < (d r).members.card by rw [(d r).two]; omega)
    have hne' : (d r).members.Nonempty := by simpa using hne
    simp [hmem, repeatPattern, recordPattern, dyPattern, hne']
    ring
  · have hsum : (∑ i, memberPattern d i r s) =
        (((d r).members ∩ (d s).members).card : ℝ) := by
      simp only [memberPattern, hrs, false_and, if_false, add_zero]
      have hf : Finset.univ.filter (fun i : M => i ∈ (d r).members ∧ i ∈ (d s).members) =
          (d r).members ∩ (d s).members := by ext i; simp
      simp [hf]
    rw [hsum]
    rcases dyad_intersection_cases (d r) (d s) with heq | hneq
    · have hne : ((d r).members ∩ (d s).members).Nonempty :=
        Finset.card_pos.mp (show 0 < ((d r).members ∩ (d s).members).card by rw [heq.2]; omega)
      have hne' : (d s).members.Nonempty := by simpa [heq.1] using hne
      norm_num [repeatPattern, recordPattern, dyPattern, hrs, heq.1, hne', (d s).two]
    · by_cases hne : ((d r).members ∩ (d s).members).Nonempty
      · have hc : ((d r).members ∩ (d s).members).card = 1 := by
          have := hne.card_pos; omega
        simp [repeatPattern, recordPattern, dyPattern, hrs, hneq.1, hne, hc]
      · have hc : ((d r).members ∩ (d s).members).card = 0 := by
          by_contra hn; exact hne (Finset.card_pos.mp (show 0 < ((d r).members ∩ (d s).members).card by omega))
        simp [repeatPattern, recordPattern, dyPattern, hrs, hneq.1, hne, hc]

/-- T4(i),(v), the corrected record-level implementation of the p. 191
identity: common arbitrary scores, bread and scaling in all components,
no small-sample factors, two distinct members in each unordered dyad. -/
theorem corrected_decomposition (d : R → Dyad M) (z : R → P → ℝ) :
    (∑ i, scoreSandwich (memberPattern d i) z) -
      scoreSandwich (repeatPattern d) z -
      ((Fintype.card M : ℝ) - 2) • scoreSandwich recordPattern z =
    scoreSandwich (dyPattern d) z := by
  ext i j
  simp only [scoreSandwich, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  have hsum :
      (∑ k : M, ∑ r : R, ∑ s : R, memberPattern d k r s * z r i * z s j) =
      ∑ r : R, ∑ s : R, (∑ k : M, memberPattern d k r s) * z r i * z s j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul]
  rw [hsum]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  have hc := decomposition_coefficient d r s
  linear_combination hc * (z r i * z s j)

/-- T4(iv): when the subtracted covariance is α times an id-clustered
matrix instead of the record matrix, the exact unprojected discrepancy is
(N−2)(V0−α Vid). -/
theorem id_substitution_discrepancy (d : R → Dyad M) (z : R → P → ℝ)
    (Vid : Matrix P P ℝ) (α : ℝ) :
    (∑ i, scoreSandwich (memberPattern d i) z) -
      scoreSandwich (repeatPattern d) z - ((Fintype.card M : ℝ) - 2) • (α • Vid) =
    scoreSandwich (dyPattern d) z + ((Fintype.card M : ℝ) - 2) •
      (scoreSandwich recordPattern z - α • Vid) := by
  have he := corrected_decomposition d z
  ext i j
  have hij := congrArg (fun A : Matrix P P ℝ => A i j) he
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul] at *
  linarith

/-- T2(ii), correction to the unconditional lower-bound passages:
full quadratic variance minus its dyadic restriction is exactly the
omitted weighted covariance sum over ordered non-incident pairs. -/
theorem variance_difference (d : R → Dyad M) (A : Matrix R R ℝ) (h : R → ℝ) :
    quadratic A h - quadratic (dyRestriction d A) h = omittedContribution d A h := by
  simp only [quadratic, omittedContribution, dyRestriction]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hi : ((d r).members ∩ (d s).members).Nonempty <;> simp [dyPattern, hi]

/-- T2(iii): weak, strict and reverse population ordering hold exactly
when the omitted weighted sum is respectively ≥0, >0 and <0.
No sign conclusion is asserted for a realized residual-based estimate. -/
theorem variance_sign_conditions (d : R → Dyad M) (A : Matrix R R ℝ) (h : R → ℝ) :
    (quadratic (dyRestriction d A) h ≤ quadratic A h ↔
      0 ≤ omittedContribution d A h) ∧
    (quadratic (dyRestriction d A) h < quadratic A h ↔
      0 < omittedContribution d A h) ∧
    (quadratic A h < quadratic (dyRestriction d A) h ↔
      omittedContribution d A h < 0) := by
  have := variance_difference d A h
  constructor
  · constructor <;> intro hn <;> linarith
  constructor <;> constructor <;> intro hn <;> linarith

/-- Id-clustered covariance groups records with a common subject id;
this is Vid (T3/T4), not the paper's record-level V0. -/
def idPattern {G : Type*} [DecidableEq G] (g : R → G) (r s : R) : ℝ :=
  if g r = g s then 1 else 0

/-- The off-diagonal within-id products removed by the erroneous
subtraction, T4(iii): the ordered sum excludes only identical records. -/
def offIdPattern {G : Type*} [DecidableEq G] (g : R → G) (r s : R) : ℝ :=
  if r ≠ s ∧ g r = g s then 1 else 0

/-- T4(iii): Vid consists of the record-level matrix plus the ordered
within-id cross-record products. -/
theorem id_cross_products {G : Type*} [DecidableEq G] (g : R → G)
    (z : R → P → ℝ) :
    scoreSandwich (idPattern g) z = scoreSandwich recordPattern z +
      scoreSandwich (offIdPattern g) z := by
  ext i j
  simp only [scoreSandwich, Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  by_cases hrs : r = s
  · subst s; simp [idPattern, recordPattern, offIdPattern]
  · by_cases hid : g r = g s <;> simp [idPattern, recordPattern, offIdPattern, hrs, hid]

/-- T4(iii): with an injective (one-record-per-id) id variable,
the id covariance equals the record covariance. -/
theorem singleton_id_covariance {G : Type*} [DecidableEq G] (g : R → G)
    (hg : Function.Injective g) (z : R → P → ℝ) :
    scoreSandwich (idPattern g) z = scoreSandwich recordPattern z := by
  have he : idPattern g = recordPattern := by
    funext r s; simp [idPattern, recordPattern, hg.eq_iff]
  rw [he]

/-- The p. 189 bread is "(X^T X)^{-1}". Over the reals, a nonzero Gram
determinant is precisely the full-column-rank condition; no regularized
or generalized inverse is used. -/
def bread (X : Matrix R P ℝ) : Matrix P P ℝ := (X.transpose * X)⁻¹

/-- The p. 189 model fitted by ordinary least squares: βhat=(X^TX)^−1X^TY. -/
def ols (X : Matrix R P ℝ) (Y : R → ℝ) : P → ℝ :=
  bread X *ᵥ (X.transpose *ᵥ Y)

/-- The p. 189 residuals substituted for errors: Y−Xβhat. -/
def olsResidual (X : Matrix R P ℝ) (Y : R → ℝ) : R → ℝ := Y - X *ᵥ ols X Y

/-- The p. 189 sandwich: "bread, meat, and bread again". A is the
error covariance or a residual-based plug-in covariance. -/
def sandwich (X : Matrix R P ℝ) (A : Matrix R R ℝ) : Matrix P P ℝ :=
  bread X * X.transpose * A * X * bread X

/-- The p. 189 plug-in meat, with residual products retained under the
chosen covariance pattern (Tables 2–4, p. 190). -/
def residualMeat (pattern : R → R → ℝ) (u : R → ℝ) : Matrix R R ℝ :=
  fun r s => pattern r s * u r * u s

/-- The "variance estimator of the following form" on p. 189:
(X^TX)^−1 X^T Ωhat X (X^TX)^−1, with the explicit residual meat. -/
def plugIn (X : Matrix R P ℝ) (u : R → ℝ) (pattern : R → R → ℝ) :=
  sandwich X (residualMeat pattern u)

/-- Auxiliary p. 189 fact: the ordinary least-squares bread is symmetric. -/
theorem bread_symmetric (X : Matrix R P ℝ) : (bread X).transpose = bread X := by
  simp [bread, Matrix.transpose_nonsing_inv, Matrix.transpose_mul]

/-- Auxiliary equivalence of the ordered quadratic sum with h^T A h. -/
theorem quadratic_eq_dot (A : Matrix R R ℝ) (h : R → ℝ) :
    quadratic A h = h ⬝ᵥ (A *ᵥ h) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring


/-- Auxiliary p. 189 sandwich identity: its contrast equals the
error-covariance quadratic form with h=X(X^TX)^−1c. No covariance signs
or invertibility beyond the ordinary symmetric bread are used in this identity. -/
theorem sandwich_quadratic (X : Matrix R P ℝ) (A : Matrix R R ℝ) (c : P → ℝ) :
    quadratic (sandwich X A) c = quadratic A (X *ᵥ (bread X *ᵥ c)) := by
  rw [quadratic_eq_dot,sandwich]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec,← Matrix.mulVec_transpose,bread_symmetric]
  rw [Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
  rw [quadratic_eq_dot]

/-- Auxiliary linearity of the ordered quadratic sum in its covariance
matrix, used by the all-contrasts version of the T2 correction. -/
theorem quadratic_sub (A B : Matrix R R ℝ) (h : R → ℝ) :
    quadratic (A-B) h = quadratic A h-quadratic B h := by
  simp [quadratic,Matrix.sub_apply,mul_sub,Finset.sum_sub_distrib]

/-- The Table 4 pattern and its covariance restriction are symmetric,
so the corrected PSD comparison concerns real symmetric matrices. -/
theorem dyadic_restriction_symmetric (d : R → Dyad M) (A : Matrix R R ℝ)
    (hA : A.transpose = A) : (dyRestriction d A).transpose = dyRestriction d A := by
  ext r s
  have hentry := congrArg (fun B : Matrix R R ℝ => B r s) hA
  simp only [Matrix.transpose_apply] at hentry
  simp only [Matrix.transpose_apply,dyRestriction,dyPattern]
  rw [Finset.inter_comm,hentry]

/-- Symmetric error meat gives a symmetric sandwich, exactly as p. 189.
This is a structural hypothesis check for T2(iv), not a PSD assumption. -/
theorem sandwich_hermitian (X : Matrix R P ℝ) (A : Matrix R R ℝ)
    (hA : A.transpose = A) : (sandwich X A).IsHermitian := by
  rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
  simp only [sandwich,Matrix.transpose_mul,Matrix.transpose_transpose,bread_symmetric,hA]
  simp only [Matrix.mul_assoc]

/-- T2(i), p. 189 fixed-design OLS: for full column rank, the error in a
contrast is h^Tu, with h=X(X^TX)^−1c, for every realization of the errors. -/
theorem ols_contrast_error (X : Matrix R P ℝ)
    (hrank : (X.transpose * X).det ≠ 0) (β c : P → ℝ) (u : R → ℝ) :
    c ⬝ᵥ ols X (X *ᵥ β + u) - c ⬝ᵥ β =
      (X *ᵥ (bread X *ᵥ c)) ⬝ᵥ u := by
  have hinv : bread X * (X.transpose * X) = 1 :=
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hrank)
  have he : ols X (X *ᵥ β + u) = β + bread X *ᵥ (X.transpose *ᵥ u) := by
    simp only [ols, Matrix.mulVec_add]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hinv, Matrix.one_mulVec]
  rw [he, dotProduct_add, add_sub_cancel_left]
  conv_lhs => rw [← bread_symmetric X, Matrix.dotProduct_transpose_mulVec]
  rw [dotProduct_comm, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

/-- T11, the p. 191 display in precisely its p. 189 OLS plug-in form.
N counts the occurring members, dyads are unordered with two distinct
members, and all components use the same residuals, bread and scaling. -/
theorem headline_decomposition (d : R → Dyad M) (X : Matrix R P ℝ)
    (_hrank : (X.transpose * X).det ≠ 0)
    (_all_members : ∀ i : M, ∃ r : R, i ∈ (d r).members) (Y : R → ℝ) :
    plugIn X (olsResidual X Y) (dyPattern d) =
      (∑ i, plugIn X (olsResidual X Y) (memberPattern d i)) -
      plugIn X (olsResidual X Y) (repeatPattern d) -
      ((Fintype.card M : ℝ) - 2) • plugIn X (olsResidual X Y) recordPattern := by
  have hm :
      residualMeat (dyPattern d) (olsResidual X Y) =
      (∑ i, residualMeat (memberPattern d i) (olsResidual X Y)) -
      residualMeat (repeatPattern d) (olsResidual X Y) -
      ((Fintype.card M : ℝ) - 2) • residualMeat recordPattern (olsResidual X Y) := by
    ext r s
    simp only [residualMeat, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, ← Finset.sum_mul]
    have hc := decomposition_coefficient d r s
    linear_combination -hc * (olsResidual X Y r * olsResidual X Y s)
  simp only [plugIn, sandwich]
  rw [hm]
  simp [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Finset.mul_sum, Finset.sum_mul, Matrix.mul_sum, Matrix.sum_mul]

/-- The covariance matrix of errors in the p. 189 model, represented by
ordinary Bochner expectations under an arbitrary probability measure. -/
def errorCovariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (u : R → Ω → ℝ) : Matrix R R ℝ := fun r s => ∫ ω, u r ω * u s ω ∂μ

/-- T2(i): a centered square-integrable error vector has variance
h^T E[uu^T]h in every linear contrast, on any probability space. -/
theorem centered_linear_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : R → Ω → ℝ)
    (hu : ∀ r, MemLp (u r) 2 μ) (hmean : ∀ r, ∫ ω, u r ω ∂μ = 0)
    (h : R → ℝ) :
    variance (fun ω => ∑ r, h r * u r ω) μ = quadratic (errorCovariance μ u) h := by
  have hweighted : ∀ r, MemLp (fun ω => h r * u r ω) 2 μ := fun r => (hu r).const_mul _
  have hsum : MemLp (fun ω => ∑ r, h r * u r ω) 2 μ :=
    memLp_finsetSum _ (fun r _ => hweighted r)
  rw [← covariance_self hsum.aemeasurable, covariance_fun_sum_left hweighted hsum]
  simp_rw [covariance_const_mul_left]
  simp only [quadratic, errorCovariance]
  apply Finset.sum_congr rfl
  intro r _
  rw [covariance_fun_sum_right hweighted (hu r), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [covariance_const_mul_right, covariance_eq_sub (hu r) (hu s)]
  simp [hmean]; ring

/-- T2(i): the OLS contrast's sampling variance equals both the full
error-covariance quadratic form and the p. 189 sandwich contrast. All
moments are actual expectations under a probability measure, and the
fixed design has full column rank. -/
theorem ols_contrast_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Matrix R P ℝ)
    (hrank : (X.transpose * X).det ≠ 0) (β c : P → ℝ) (u : R → Ω → ℝ)
    (hu : ∀ r, MemLp (u r) 2 μ) (hmean : ∀ r, ∫ ω, u r ω ∂μ = 0) :
    variance (fun ω => c ⬝ᵥ ols X (X *ᵥ β + fun r => u r ω)) μ =
      quadratic (errorCovariance μ u) (X *ᵥ (bread X *ᵥ c)) ∧
    quadratic (errorCovariance μ u) (X *ᵥ (bread X *ᵥ c)) =
      quadratic (sandwich X (errorCovariance μ u)) c := by
  let h := X *ᵥ (bread X *ᵥ c)
  have hweighted : ∀ r, MemLp (fun ω => h r*u r ω) 2 μ := fun r => (hu r).const_mul _
  have hsum : MemLp (fun ω => ∑ r, h r*u r ω) 2 μ :=
    memLp_finsetSum _ (fun r _ => hweighted r)
  have he : (fun ω => c ⬝ᵥ ols X (X *ᵥ β + fun r => u r ω)) =
      (fun ω => (∑ r, h r*u r ω) + c ⬝ᵥ β) := by
    funext ω
    have hc := ols_contrast_error X hrank β c (fun r => u r ω)
    change _ = (∑ r, h r*u r ω) at hc
    linarith
  constructor
  · rw [he,variance_add_const hsum.aestronglyMeasurable]
    exact centered_linear_variance μ u hu hmean h
  · exact (sandwich_quadratic X (errorCovariance μ u) c).symm

/-- T2(iv): for all coefficient contrasts the dyadic restriction is a
weak lower bound iff the omitted sandwich is PSD, equivalently iff its
unbreaded X^T(Ω−Ω_D)X meat is PSD. Invertible bread preserves both directions. -/
theorem all_contrasts_lower_bound_iff (d : R → Dyad M)
    (X : Matrix R P ℝ) (hrank : (X.transpose * X).det ≠ 0)
    (A : Matrix R R ℝ) (hsym : A.transpose = A) :
    (∀ c : P → ℝ, quadratic (dyRestriction d A) (X *ᵥ (bread X *ᵥ c)) ≤
      quadratic A (X *ᵥ (bread X *ᵥ c))) ↔
    (sandwich X (A - dyRestriction d A)).PosSemidef := by
  have hsymD : (A-dyRestriction d A).transpose = A-dyRestriction d A := by
    simp only [Matrix.transpose_sub,hsym,dyadic_restriction_symmetric d A hsym]
  have hherm := sandwich_hermitian X (A-dyRestriction d A) hsymD
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro hc
    refine ⟨hherm,?_⟩
    intro c
    have hn := sub_nonneg.mpr (hc c)
    have he := sandwich_quadratic X (A-dyRestriction d A) c
    rw [quadratic_sub] at he
    have hq : 0 ≤ quadratic (sandwich X (A-dyRestriction d A)) c := by
      rw [he]; exact hn
    simpa only [star_trivial,quadratic_eq_dot] using hq
  · rintro ⟨_,hp⟩ c
    have hn := hp c
    have he := sandwich_quadratic X (A-dyRestriction d A) c
    rw [quadratic_sub] at he
    have hn' : 0 ≤ quadratic (sandwich X (A-dyRestriction d A)) c := by
      simpa only [star_trivial,quadratic_eq_dot] using hn
    rw [he] at hn'
    exact sub_nonneg.mp hn'

/-- The equivalent unbreaded condition in T2(iv), without narrowing the
design or assuming the desired PSD condition as a hypothesis. -/
theorem omitted_sandwich_psd_iff (d : R → Dyad M) (X : Matrix R P ℝ)
    (hrank : (X.transpose * X).det ≠ 0) (A : Matrix R R ℝ) :
    (sandwich X (A - dyRestriction d A)).PosSemidef ↔
      (X.transpose * (A - dyRestriction d A) * X).PosSemidef := by
  let G := X.transpose * X
  let C := X.transpose * (A-dyRestriction d A) * X
  have hG : G.transpose = G := by simp [G,Matrix.transpose_mul]
  have hB : bread X * G = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hrank)
  have hB' : G * bread X = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hrank)
  have hS : sandwich X (A-dyRestriction d A) = bread X*C*bread X := by
    simp only [sandwich,C,Matrix.mul_assoc]
  constructor
  · intro hp
    have hc := hp.conjTranspose_mul_mul_same G
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,hG,hS] at hc
    have he : G*(bread X*C*bread X)*G = C := by
      calc
        _ = (G*bread X)*C*(bread X*G) := by noncomm_ring
        _ = C := by rw [hB',hB]; simp
    rw [he] at hc
    exact hc
  · intro hp
    have hc := hp.conjTranspose_mul_mul_same (bread X)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial,bread_symmetric] at hc
    simpa only [hS] using hc

/-- T7: "converts any negative eigenvalue(s) to zero" (p. 191, footnote 3).
This is the exact formula for a specified real orthogonal eigenbasis. -/
def spectralClip (Q : Matrix P P ℝ) (eigs : P → ℝ) : Matrix P P ℝ :=
  Q * Matrix.diagonal (fun j => max (eigs j) 0) * Q.transpose

/-- T7(i): eigenvalue clipping always returns a symmetric PSD matrix,
regardless of diagonal signs. Orthogonality is unnecessary for this direction. -/
theorem spectral_clip_psd (Q : Matrix P P ℝ) (eigs : P → ℝ) :
    (spectralClip Q eigs).PosSemidef := by
  have hd : (Matrix.diagonal (fun j => max (eigs j) 0)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun j => le_max_right _ _)
  simpa [spectralClip, Matrix.conjTranspose_eq_transpose_of_trivial] using hd.mul_mul_conjTranspose_same Q

/-- T7(i): c^T V+ c is the sum of clipped eigenvalues times squared
projections onto eigenvectors, so every contrast has a nonnegative variance. -/
theorem spectral_clip_quadratic (Q : Matrix P P ℝ) (eigs c : P → ℝ) :
    quadratic (spectralClip Q eigs) c =
      ∑ j, max (eigs j) 0 * (∑ i, Q i j * c i)^2 := by
  rw [quadratic_eq_dot, spectralClip]
  simp only [← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct]
  ring

/-- T7(ii): in an orthogonal spectral decomposition, clipping fixes
exactly the matrices that were already positive semidefinite. -/
theorem spectral_clip_fixed_iff (Q : Matrix P P ℝ) (eigs : P → ℝ)
    (horth : Q.transpose * Q = 1) (horth' : Q * Q.transpose = 1) :
    spectralClip Q eigs = Q * Matrix.diagonal eigs * Q.transpose ↔
      (Q * Matrix.diagonal eigs * Q.transpose).PosSemidef := by
  constructor
  · intro he; rw [← he]; exact spectral_clip_psd Q eigs
  · intro hp
    have hd := hp.conjTranspose_mul_mul_same Q
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hd
    have hc : Q.transpose * (Q * Matrix.diagonal eigs * Q.transpose) * Q =
        Matrix.diagonal eigs := by
      calc
        _ = (Q.transpose * Q) * Matrix.diagonal eigs * (Q.transpose * Q) := by noncomm_ring
        _ = _ := by rw [horth]; simp
    rw [hc] at hd
    have hn := Matrix.posSemidef_diagonal_iff.mp hd
    have hmax : (fun j => max (eigs j) 0) = eigs := funext (fun j => max_eq_left (hn j))
    unfold spectralClip
    rw [hmax]

/-- The repaired PSD operation for any real symmetric V. A canonical
orthogonal eigenbasis is supplied by Mathlib's proved real spectral theorem. -/
def positivePart (V : Matrix P P ℝ) (hV : V.IsHermitian) : Matrix P P ℝ :=
  spectralClip (hV.eigenvectorUnitary : Matrix P P ℝ) hV.eigenvalues

/-- T7(i): requesting PSD enforcement always succeeds for a symmetric
matrix of any parameter dimension; it is not gated by diagonal signs. -/
theorem positive_part_psd (V : Matrix P P ℝ) (hV : V.IsHermitian) :
    (positivePart V hV).PosSemidef := spectral_clip_psd _ _

/-- The released software's rule in T6(e): clip only when a diagonal
entry is negative.
This Lean definition specifies what the published software computes. -/
def gatedPart (V : Matrix P P ℝ) (hV : V.IsHermitian) : Matrix P P ℝ :=
  if ∃ i, V i i < 0 then positivePart V hV else V

/-- T7(iii): the diagonal-gated rule succeeds precisely when the gate
activates or the input was already PSD. -/
theorem gated_psd_iff (V : Matrix P P ℝ) (hV : V.IsHermitian) :
    (gatedPart V hV).PosSemidef ↔ (∃ i, V i i < 0) ∨ V.PosSemidef := by
  by_cases hgate : ∃ i, V i i < 0
  · simp [gatedPart, hgate, positive_part_psd]
  · simp [gatedPart, hgate]

/-- T7(iii): for a real symmetric 2×2 matrix with nonnegative diagonal,
PSD is equivalent to ad≥b². A diagonal-sign test alone omits this condition. -/
theorem psd_two_by_two_iff (a b d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) :
    (!![a, b; b, d] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef ↔ b^2 ≤ a*d := by
  constructor
  · intro hp
    have hq : ∀ x y : ℝ, 0 ≤ a*x^2+2*b*x*y+d*y^2 := by
      intro x y
      have h := hp.dotProduct_mulVec_nonneg ![x,y]
      simp only [star_trivial] at h
      rw [← quadratic_eq_dot] at h
      have he : quadratic (!![a,b;b,d] : Matrix (Fin 2) (Fin 2) ℝ) ![x,y] =
          a*x^2+2*b*x*y+d*y^2 := by
        simp [quadratic,Fin.sum_univ_succ]; ring
      rw [he] at h
      exact h
    by_cases hz : a = 0
    · have h := hq (d+1) (-b)
      rw [hz] at h
      nlinarith [sq_nonneg b, mul_nonneg hd (sq_nonneg b)]
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
      have h := hq (-b) a
      have hbad : a*(a*d-b^2) ≥ 0 := by nlinarith [h]
      nlinarith
  · intro hab
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.ext
      intro i j; fin_cases i <;> fin_cases j <;> simp
    · intro v
      simp only [star_trivial]
      rw [← quadratic_eq_dot]
      have he : quadratic (!![a,b;b,d] : Matrix (Fin 2) (Fin 2) ℝ) v =
          a*(v 0)^2+2*b*v 0*v 1+d*(v 1)^2 := by
        simp [quadratic, Fin.sum_univ_succ]; ring
      rw [he]
      by_cases hz : a = 0
      · have hb : b = 0 := by rw [hz] at hab; nlinarith [sq_nonneg b]
        simp [hz,hb, mul_nonneg hd (sq_nonneg (v 1))]
      · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
        have hh := mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg (v 1))
        have hs := sq_nonneg (a*v 0+b*v 1)
        nlinarith

/-- T12, p. 188: "μhat=1/2(Y_US-UK+Y_US-FR)". -/
def tradeMean {Ω : Type*} (Y₁ Y₂ : Ω → ℝ) : Ω → ℝ := fun ω => (1/2 : ℝ)*(Y₁ ω+Y₂ ω)

/-- T12, p. 188: the naive variance is "1/4(V[Y_US-UK]+V[Y_US-FR])",
i.e. the value under zero covariance, not a new sampling distribution. -/
def naiveTradeVariance {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (Y₁ Y₂ : Ω → ℝ) : ℝ := (1/4 : ℝ)*(variance Y₁ μ+variance Y₂ μ)

/-- T12, pp. 188–189: "Y_US,UK=aX_US+bX_UK+U_US,UK" and
"Y_US,FR=cX_US+dX_FR+U_US,FR". Indices 0,1,2 are the country
factors; 3,4 are the idiosyncratic shocks. -/
def tradeOutcomes {Ω : Type*} (Z : Fin 5 → Ω → ℝ) (a b c d : ℝ) :
    (Ω → ℝ) × (Ω → ℝ) :=
  (fun ω => a*Z 0 ω+b*Z 1 ω+Z 3 ω,
   fun ω => c*Z 0 ω+d*Z 2 ω+Z 4 ω)

/-- T12(i), the first p. 189 display, with no independence assumption:
the variance of the average equals the naive value plus half the covariance. -/
theorem toy_variance_identity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y₁ Y₂ : Ω → ℝ)
    (h₁ : MemLp Y₁ 2 μ) (h₂ : MemLp Y₂ 2 μ) :
    variance (tradeMean Y₁ Y₂) μ = naiveTradeVariance μ Y₁ Y₂ +
      (1/2 : ℝ)*covariance Y₁ Y₂ μ := by
  unfold tradeMean
  rw [variance_const_mul, variance_fun_add h₁ h₂]
  unfold naiveTradeVariance
  ring

/-- T12(ii), the last p. 189 equality, using the explicitly allowed
pairwise-uncorrelated hypothesis on all FIVE primitives (including the
shocks). Arbitrary means are allowed; only finite variances are required. -/
theorem toy_shared_country_covariance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Fin 5 → Ω → ℝ)
    (hZ : ∀ i, MemLp (Z i) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (Z i) (Z j) μ = 0)
    (a b c d : ℝ) :
    covariance (tradeOutcomes Z a b c d).1 (tradeOutcomes Z a b c d).2 μ =
      a*c*variance (Z 0) μ := by
  change covariance (((a • Z 0) + (b • Z 1)) + Z 3)
    (((c • Z 0) + (d • Z 2)) + Z 4) μ = _
  rw [covariance_add_left ((hZ 0).const_smul a |>.add ((hZ 1).const_smul b))
    (hZ 3) (((hZ 0).const_smul c |>.add ((hZ 2).const_smul d)).add (hZ 4))]
  rw [covariance_add_left ((hZ 0).const_smul a) ((hZ 1).const_smul b)
    (((hZ 0).const_smul c |>.add ((hZ 2).const_smul d)).add (hZ 4))]
  rw [covariance_add_right ((hZ 0).const_smul a)
    (((hZ 0).const_smul c).add ((hZ 2).const_smul d)) (hZ 4),
    covariance_add_right ((hZ 1).const_smul b)
    (((hZ 0).const_smul c).add ((hZ 2).const_smul d)) (hZ 4),
    covariance_add_right (hZ 3)
    (((hZ 0).const_smul c).add ((hZ 2).const_smul d)) (hZ 4)]
  rw [covariance_add_right ((hZ 0).const_smul a) ((hZ 0).const_smul c) ((hZ 2).const_smul d),
    covariance_add_right ((hZ 1).const_smul b) ((hZ 0).const_smul c) ((hZ 2).const_smul d),
    covariance_add_right (hZ 3) ((hZ 0).const_smul c) ((hZ 2).const_smul d)]
  simp_rw [covariance_smul_left, covariance_smul_right]
  simp [huncorr, covariance_self (hZ 0).aemeasurable]
  ring

/-- T12(ii)–(iii): the complete finite-variance identity and all three
sign cases. The paper's strict same-sign conclusion requires a nonzero
variance of the shared US factor, made explicit in the target. -/
theorem toy_sign_cases {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Fin 5 → Ω → ℝ)
    (hZ : ∀ i, MemLp (Z i) 2 μ)
    (huncorr : ∀ i j, i ≠ j → covariance (Z i) (Z j) μ = 0)
    (a b c d : ℝ) :
    let Y := tradeOutcomes Z a b c d
    let Vn := naiveTradeVariance μ Y.1 Y.2
    let V := variance (tradeMean Y.1 Y.2) μ
    V = Vn + (a*c/2)*variance (Z 0) μ ∧
    (0 < a*c → 0 < variance (Z 0) μ → Vn < V) ∧
    (a*c < 0 → 0 < variance (Z 0) μ → V < Vn) ∧
    (a*c = 0 ∨ variance (Z 0) μ = 0 → V = Vn) := by
  dsimp
  have h₁ : MemLp (tradeOutcomes Z a b c d).1 2 μ :=
    (((hZ 0).const_mul a).add ((hZ 1).const_mul b)).add (hZ 3)
  have h₂ : MemLp (tradeOutcomes Z a b c d).2 2 μ :=
    (((hZ 0).const_mul c).add ((hZ 2).const_mul d)).add (hZ 4)
  have he := toy_variance_identity μ _ _ h₁ h₂
  rw [toy_shared_country_covariance μ Z hZ huncorr a b c d] at he
  have he' : variance (tradeMean (tradeOutcomes Z a b c d).1
      (tradeOutcomes Z a b c d).2) μ =
      naiveTradeVariance μ (tradeOutcomes Z a b c d).1
      (tradeOutcomes Z a b c d).2 + (a*c/2)*variance (Z 0) μ := by
    rw [he]; ring
  refine ⟨he', ?_, ?_, ?_⟩
  · intro hac hv; rw [he']; have := mul_pos hac hv; nlinarith
  · intro hac hv; rw [he']; have := mul_neg_of_neg_of_pos hac hv; nlinarith
  · intro hz; rw [he']; rcases hz with hz | hz <;> simp [hz]

/-- For the bounded counterexamples (T1), a finite probability
law has nonnegative atom weights of total one. It is an actual probability
space, not a formal covariance matrix without a realizing error distribution. -/
structure FiniteLaw (S : Type*) [Fintype S] where
  weight : S → ℝ
  nonneg : ∀ s, 0 ≤ weight s
  total : ∑ s, weight s = 1

/-- Ordinary expectation under a finite law, used only for explicitly
bounded finite-support constructions in T1. -/
def finiteExpectation {S : Type*} [Fintype S] (law : FiniteLaw S) (f : S → ℝ) : ℝ :=
  ∑ s, law.weight s * f s

/-- Finite-law sampling variance E[(f−Ef)²], the same population variance
as p. 189, for the finite-support examples. -/
def finiteVariance {S : Type*} [Fintype S] (law : FiniteLaw S) (f : S → ℝ) : ℝ :=
  finiteExpectation law (fun s => (f s - finiteExpectation law f)^2)

/-- T1(a)–(c): disjoint observations {0,1} and {2,3}. -/
def disjointDyads : Fin 2 → Dyad (Fin 4) := fun r =>
  ⟨![({0,1} : Finset (Fin 4)), {2,3}] r, by fin_cases r <;> decide⟩

/-- T1(a)–(c): four bounded error realizations (−1,−1), (−1,1),
(1,−1), (1,1), so exogeneity is verified by exact expectations. -/
def pairErrors : Fin 4 → Fin 2 → ℝ := ![![-1,-1], ![-1,1], ![1,-1], ![1,1]]

/-- T1(a): negative error covariance, with probabilities 1/8,3/8,3/8,1/8. -/
def negativePairLaw : FiniteLaw (Fin 4) where
  weight := ![1/8,3/8,3/8,1/8]
  nonneg := by intro s; fin_cases s <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- T1(b),(c): positive error covariance, probabilities 3/8,1/8,1/8,3/8. -/
def positivePairLaw : FiniteLaw (Fin 4) where
  weight := ![3/8,1/8,1/8,3/8]
  nonneg := by intro s; fin_cases s <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- T1(a): Ω=(1,−1/2;−1/2,1). T1(b),(c) change the off-diagonals to +1/2. -/
def pairOmega (sign : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1,sign/2; sign/2,1]

/-- T1(a)–(c): the explicit distributions are centered and have exactly
the displayed error covariance matrices; with fixed X this verifies exogeneity. -/
theorem pair_error_moments :
    (∀ r, finiteExpectation negativePairLaw (fun ω => pairErrors ω r) = 0) ∧
    (∀ r s, finiteExpectation negativePairLaw (fun ω => pairErrors ω r * pairErrors ω s) =
      pairOmega (-1) r s) ∧
    (∀ r, finiteExpectation positivePairLaw (fun ω => pairErrors ω r) = 0) ∧
    (∀ r s, finiteExpectation positivePairLaw (fun ω => pairErrors ω r * pairErrors ω s) =
      pairOmega 1 r s) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r; fin_cases r <;> norm_num [finiteExpectation, negativePairLaw, pairErrors, Fin.sum_univ_succ]
  · intro r s; fin_cases r <;> fin_cases s <;>
      norm_num [finiteExpectation, negativePairLaw, pairErrors, pairOmega, Fin.sum_univ_succ]
  · intro r; fin_cases r <;> norm_num [finiteExpectation, positivePairLaw, pairErrors, Fin.sum_univ_succ]
  · intro r s; fin_cases r <;> fin_cases s <;>
      norm_num [finiteExpectation, positivePairLaw, pairErrors, pairOmega, Fin.sum_univ_succ]

/-- T1(a),(b): both error covariance matrices are strictly positive
quadratic forms on every nonzero vector (hence positive definite). -/
theorem pair_omega_positive_definite (sign : ℝ) (hsign : sign = -1 ∨ sign = 1) :
    (pairOmega sign).transpose = pairOmega sign ∧
      ∀ v : Fin 2 → ℝ, v ≠ 0 → 0 < quadratic (pairOmega sign) v := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [pairOmega, Matrix.transpose_apply]
  · intro v hv
    have hn : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply hv
      funext i; fin_cases i <;> simp [hc]
    rcases hsign with hs | hs <;> subst sign
    · have he : quadratic (pairOmega (-1)) v =
          (1/2 : ℝ)*((v 0)^2+(v 1)^2) + (1/2 : ℝ)*(v 0-v 1)^2 := by
        simp [quadratic, pairOmega, Fin.sum_univ_succ]; ring
      rw [he]
      rcases hn with hn | hn <;>
        nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 0-v 1), sq_pos_of_ne_zero hn]
    · have he : quadratic (pairOmega 1) v =
          (1/2 : ℝ)*((v 0)^2+(v 1)^2) + (1/2 : ℝ)*(v 0+v 1)^2 := by
        simp [quadratic, pairOmega, Fin.sum_univ_succ]; ring
      rw [he]
      rcases hn with hn | hn <;>
        nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 0+v 1), sq_pos_of_ne_zero hn]

/-- T1(a),(c): the actual intercept-only design X=(1,1)^T. -/
def pairInterceptDesign : Matrix (Fin 2) (Fin 1) ℝ := fun _ _ => 1

/-- T1(b): the actual one-regressor slope design X=(−1,1)^T. -/
def pairSlopeDesign : Matrix (Fin 2) (Fin 1) ℝ := fun r _ => ![-1,1] r

/-- T1(a), a concrete full-rank intercept design and contrast c=1:
its true variance is 1/4 but the dyadic restriction gives 1/2. The bounded
error law is negativePairLaw, whose moments are proved above. -/
theorem intercept_counterexample :
    let X : Matrix (Fin 2) (Fin 1) ℝ := pairInterceptDesign
    let c : Fin 1 → ℝ := fun _ => 1
    let h := X *ᵥ (bread X *ᵥ c)
    (X.transpose * X).det ≠ 0 ∧ h = ![1/2,1/2] ∧
      quadratic (pairOmega (-1)) h = 1/4 ∧
      quadratic (dyRestriction disjointDyads (pairOmega (-1))) h = 1/2 ∧
      quadratic (pairOmega (-1)) h <
        quadratic (dyRestriction disjointDyads (pairOmega (-1))) h := by
  dsimp only
  have hg : pairInterceptDesign.transpose *
      pairInterceptDesign = !![2] := by
    ext i j; fin_cases i; fin_cases j
    norm_num [pairInterceptDesign,pairSlopeDesign,Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  have hb : bread pairInterceptDesign = !![1/2] := by
    unfold bread; rw [hg]
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i; fin_cases j
    norm_num [pairInterceptDesign,pairSlopeDesign,Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  rw [hb, hg]
  have hh : pairInterceptDesign *ᵥ
      (!![1/2] *ᵥ (fun _ => (1 : ℝ))) = ![1/2,1/2] := by
    ext i; fin_cases i <;> norm_num [pairInterceptDesign,pairSlopeDesign,Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [hh]
  norm_num [quadratic, pairOmega, dyRestriction, dyPattern, disjointDyads,
    Matrix.det_fin_one, Fin.sum_univ_succ]

/-- T1(b),(c): even positive omitted covariance overstates a slope
variance for X=(−1,1); with the same covariance and X=(1,1), the true
variance instead exceeds the dyadic value. There is no universal direction. -/
theorem slope_and_sign_control :
    let X : Matrix (Fin 2) (Fin 1) ℝ := pairSlopeDesign
    let c : Fin 1 → ℝ := fun _ => 1
    let h := X *ᵥ (bread X *ᵥ c)
    (X.transpose * X).det ≠ 0 ∧ h = ![-1/2,1/2] ∧
      quadratic (pairOmega 1) h = 1/4 ∧
      quadratic (dyRestriction disjointDyads (pairOmega 1)) h = 1/2 ∧
      quadratic (pairOmega 1) ![1/2,1/2] = 3/4 ∧
      quadratic (dyRestriction disjointDyads (pairOmega 1)) ![1/2,1/2] = 1/2 := by
  dsimp only
  have hg : pairSlopeDesign.transpose *
      pairSlopeDesign = !![2] := by
    ext i j; fin_cases i; fin_cases j
    norm_num [pairInterceptDesign,pairSlopeDesign,Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ]
  have hb : bread pairSlopeDesign = !![1/2] := by
    unfold bread; rw [hg]
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i; fin_cases j
    norm_num [pairInterceptDesign,pairSlopeDesign,Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  rw [hb, hg]
  have hh : pairSlopeDesign *ᵥ
      (!![1/2] *ᵥ (fun _ => (1 : ℝ))) = ![-1/2,1/2] := by
    ext i; fin_cases i <;> norm_num [pairInterceptDesign,pairSlopeDesign,Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [hh]
  norm_num [quadratic, pairOmega, dyRestriction, dyPattern, disjointDyads,
    Matrix.det_fin_one, Fin.sum_univ_succ]

/-- T5, the formal reading of "will still underestimate"
(p. 187; lower-bound passages pp. 187,196): for every full-rank design,
contrast and PSD error covariance with some nonzero non-incident covariance,
the population dyadic sandwich is a weak lower bound. This is a proposition
as printed, NOT an axiom or a proved theorem. -/
def PrintedPopulationLowerBound : Prop :=
  ∀ (n p k : ℕ) (d : Fin n → Dyad (Fin k))
    (X : Matrix (Fin n) (Fin p) ℝ) (c : Fin p → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ),
    (X.transpose * X).det ≠ 0 → A.PosSemidef →
    (∃ r s, ¬((d r).members ∩ (d s).members).Nonempty ∧ A r s ≠ 0) →
    quadratic (dyRestriction d A) (X *ᵥ (bread X *ᵥ c)) ≤
      quadratic A (X *ᵥ (bread X *ᵥ c))

/-- T5's strict reading; unlike the weak form it also excludes equality.
No restriction on covariance signs is present in the printed passages. -/
def PrintedStrictPopulationLowerBound : Prop :=
  ∀ (n p k : ℕ) (d : Fin n → Dyad (Fin k))
    (X : Matrix (Fin n) (Fin p) ℝ) (c : Fin p → ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ),
    (X.transpose * X).det ≠ 0 → A.PosSemidef →
    (∃ r s, ¬((d r).members ∩ (d s).members).Nonempty ∧ A r s ≠ 0) →
    quadratic (dyRestriction d A) (X *ᵥ (bread X *ᵥ c)) <
      quadratic A (X *ᵥ (bread X *ᵥ c))

/-- T5: the unconditional population lower-bound claim is false,
refuted by T1(a)'s actual centered, bounded, positive-definite model. -/
theorem printed_population_claim_false : ¬PrintedPopulationLowerBound ∧
    ¬PrintedStrictPopulationLowerBound := by
  have hp : (pairOmega (-1)).PosSemidef := by
    rcases pair_omega_positive_definite (-1) (Or.inl rfl) with ⟨hs,hn⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]; exact hs
    · intro v
      simp only [star_trivial,← quadratic_eq_dot]
      by_cases hv : v = 0
      · subst v; simp [quadratic]
      · exact le_of_lt (hn v hv)
  have hd : ∃ r s, ¬((disjointDyads r).members ∩ (disjointDyads s).members).Nonempty ∧
      pairOmega (-1) r s ≠ 0 := by
    refine ⟨0,1,?_⟩
    norm_num [disjointDyads,pairOmega]
  rcases intercept_counterexample with ⟨hr,hh,htrue,hdy,hgt⟩
  constructor
  · intro h
    have hl := h 2 1 4 disjointDyads pairInterceptDesign (fun _ => 1)
      (pairOmega (-1)) hr hp hd
    linarith
  · intro h
    have hl := h 2 1 4 disjointDyads pairInterceptDesign (fun _ => 1)
      (pairOmega (-1)) hr hp hd
    linarith

/-- T1(d): dyads AB,AC,DE,DF on six distinct members (numbered 0…5). -/
def fourDyads : Fin 4 → Dyad (Fin 6) := fun r =>
  ⟨![({0,1} : Finset (Fin 6)), {0,2}, {3,4}, {3,5}] r, by fin_cases r <;> decide⟩

/-- T1(d): the exact 16-point error distribution gives 3/64 to every
sign vector and an additional 1/8 to each of (1,1,−1,−1),(−1,−1,1,1). -/
def fourBlockLaw : FiniteLaw (Fin 16) where
  weight := fun ω => 3/64 + if ω = 3 ∨ ω = 12 then 1/8 else 0
  nonneg := by intro ω; split_ifs <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- T1(d): all sign vectors, ordered lexicographically; bounded errors. -/
def fourBlockErrors : Fin 16 → Fin 4 → ℝ :=
  ![![-1,-1,-1,-1], ![-1,-1,-1,1], ![-1,-1,1,-1], ![-1,-1,1,1],
    ![-1,1,-1,-1], ![-1,1,-1,1], ![-1,1,1,-1], ![-1,1,1,1],
    ![1,-1,-1,-1], ![1,-1,-1,1], ![1,-1,1,-1], ![1,-1,1,1],
    ![1,1,-1,-1], ![1,1,-1,1], ![1,1,1,-1], ![1,1,1,1]]

/-- T1(d): the printed target's covariance has incident entries +1/4,
non-incident entries −1/4 and unit diagonal. -/
def fourOmega : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1/4,-1/4,-1/4; 1/4,1,-1/4,-1/4;
    -1/4,-1/4,1,1/4; -1/4,-1/4,1/4,1]

/-- T1(d): exact mean and second moments of the 16-point law;
this verifies every displayed covariance, unit variances, and exogeneity. -/
theorem four_block_moments :
    (∀ r, finiteExpectation fourBlockLaw (fun ω => fourBlockErrors ω r) = 0) ∧
    (∀ r s, finiteExpectation fourBlockLaw
      (fun ω => fourBlockErrors ω r * fourBlockErrors ω s) = fourOmega r s) := by
  constructor
  · intro r; fin_cases r <;>
      norm_num [finiteExpectation, fourBlockLaw, fourBlockErrors, Fin.sum_univ_succ]
  · intro r s; fin_cases r <;> fin_cases s <;>
      norm_num [finiteExpectation, fourBlockLaw, fourBlockErrors, fourOmega, Fin.sum_univ_succ]

/-- T1(d): a small sum-of-squares certificate of positive definiteness,
rather than enumerating the signs of all possible quadratic-form values. -/
theorem four_omega_square_certificate (h : Fin 4 → ℝ) :
    quadratic fourOmega h = (3/4 : ℝ)*∑ r, (h r)^2 +
      (1/4 : ℝ)*(h 0+h 1-h 2-h 3)^2 := by
  simp [quadratic, fourOmega, Fin.sum_univ_succ]; ring

/-- T1(d): the intercept has true variance 3/16 but population dyadic
variance 5/16, despite positive dependence between incident dyads. -/
theorem four_block_counterexample :
    quadratic fourOmega (fun _ => (1/4 : ℝ)) = 3/16 ∧
    quadratic (dyRestriction fourDyads fourOmega) (fun _ => (1/4 : ℝ)) = 5/16 ∧
    finiteVariance fourBlockLaw
      (fun ω => (1/4 : ℝ)*∑ r, fourBlockErrors ω r) = 3/16 := by
  norm_num [quadratic, fourOmega, dyRestriction, dyPattern, fourDyads,
    finiteVariance, finiteExpectation, fourBlockLaw, fourBlockErrors, Fin.sum_univ_succ]

/-- T1(f): all six unordered distinct-member dyads among four members,
in the exact order 01,02,03,12,13,23. -/
def sixDyads : Fin 6 → Dyad (Fin 4) := fun r =>
  ⟨![({0,1} : Finset (Fin 4)), {0,2}, {0,3}, {1,2}, {1,3}, {2,3}] r,
    by fin_cases r <;> decide⟩

/-- T1(f): unit diagonal, +1/8 for incident distinct edges, −1/2 for
the three complementary pairs 0↔5,1↔4,2↔3. -/
def sixOmega : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,1/8,1/8,1/8,1/8,-1/2;
    1/8,1,1/8,1/8,-1/2,1/8;
    1/8,1/8,1,-1/2,1/8,1/8;
    1/8,1/8,-1/2,1,1/8,1/8;
    1/8,-1/2,1/8,1/8,1,1/8;
    -1/2,1/8,1/8,1/8,1/8,1]

/-- T1(f): all covariance row sums are 1, dyadic row sums 3/2;
the intercept's true, dyadic and naive variances are 1/6,1/4,1/6. -/
theorem six_block_variances :
    (∀ r, ∑ s, sixOmega r s = 1) ∧
    (∀ r, ∑ s, dyRestriction sixDyads sixOmega r s = 3/2) ∧
    (∀ r, ∑ s, dyPattern sixDyads r s = 5) ∧
    quadratic sixOmega (fun _ => (1/6 : ℝ)) = 1/6 ∧
    quadratic (dyRestriction sixDyads sixOmega) (fun _ => (1/6 : ℝ)) = 1/4 ∧
    quadratic (fun r s => recordPattern r s * sixOmega r s) (fun _ => (1/6 : ℝ)) = 1/6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r; fin_cases r <;> norm_num [sixOmega, Fin.sum_univ_succ]
  · intro r; fin_cases r <;> norm_num [sixOmega, sixDyads, dyRestriction, dyPattern, Fin.sum_univ_succ]
  · intro r; fin_cases r <;>
      (simp only [Fin.sum_univ_succ]; norm_num [dyPattern, sixDyads])
  · norm_num [quadratic, sixOmega, Fin.sum_univ_succ]
  · norm_num [quadratic, sixOmega, sixDyads, dyRestriction, dyPattern, Fin.sum_univ_succ]
  · norm_num [quadratic, sixOmega, recordPattern, Fin.sum_univ_succ]

/-- T1(f): exact small square certificate of strict positive definiteness.
The first four squares are the four member shocks, next three complementary
pair shocks; independent own-error shocks contribute 1/4 Σ h². -/
theorem six_omega_square_certificate (h : Fin 6 → ℝ) :
    quadratic sixOmega h =
      (1/8 : ℝ)*((h 0+h 1+h 2)^2+(h 0+h 3+h 4)^2+
        (h 1+h 3+h 5)^2+(h 2+h 4+h 5)^2) +
      (1/2 : ℝ)*((h 0-h 5)^2+(h 1-h 4)^2+(h 2-h 3)^2) +
      (1/4 : ℝ)*∑ r, (h r)^2 := by
  simp [quadratic, sixOmega, Fin.sum_univ_succ]; ring

/-- T3: one counting-process record (start,stop], with status 1 an event,
0 an interval end and 2 a competing event treated as censoring. The model
has Breslow ties, no weights or strata. -/
structure CoxRecord where
  id : Fin 6
  dyad : Dyad (Fin 4)
  start : ℕ
  stop : ℕ
  x : ℝ
  status : ℕ

/-- T3: the ten explicit records for six subjects; country labels have
been shifted from 1…4 to 0…3, preserving all dyads and risk sets. -/
def coxRecords : Fin 10 → CoxRecord :=
  ![⟨0,sixDyads 0,0,1,1,1⟩, ⟨1,sixDyads 5,0,1,-1,1⟩,
    ⟨2,sixDyads 1,0,1,1,0⟩, ⟨2,sixDyads 1,1,2,3,1⟩,
    ⟨3,sixDyads 4,0,1,-1,0⟩, ⟨3,sixDyads 4,1,2,-3,1⟩,
    ⟨4,sixDyads 2,0,1,1,0⟩, ⟨4,sixDyads 2,1,3,1,2⟩,
    ⟨5,sixDyads 3,0,1,-1,0⟩, ⟨5,sixDyads 3,1,3,-1,2⟩]

/-- T3: at risk iff start<t≤stop, exactly the counting-process interval
convention; terminal events remove subjects from later risk sets. -/
abbrev coxRisk (r : Fin 10) (t : ℕ) : Prop :=
  (coxRecords r).start < t ∧ t ≤ (coxRecords r).stop

/-- T3: an event of interest at time t has status 1 and stop=t. -/
abbrev coxEvent (r : Fin 10) (t : ℕ) : Prop :=
  (coxRecords r).status = 1 ∧ (coxRecords r).stop = t

/-- T3: number at risk, number of events and risk-set covariate mean. -/
def coxRiskN (t : ℕ) : ℝ := ∑ r, if coxRisk r t then 1 else 0
/-- T3(a): "two events" at each event time; count records with an event of interest at t. -/
def coxEventN (t : ℕ) : ℝ := ∑ r, if coxEvent r t then 1 else 0
/-- T3(a): "covariate mean 0" in each risk set; define the risk-set sum of x divided by its size. -/
def coxRiskMean (t : ℕ) : ℝ :=
  (∑ r, if coxRisk r t then (coxRecords r).x else 0) / coxRiskN t

/-- T3(a): Breslow partial log-likelihood, directly from the two risk
sets and failures. Constants independent of β have been omitted. -/
def coxLogLikelihood (β : ℝ) : ℝ := ∑ t : Fin 2,
  ((∑ r, if coxEvent r (t.val+1) then β*(coxRecords r).x else 0) -
  coxEventN (t.val+1) * Real.log
    (∑ r, if coxRisk r (t.val+1) then Real.exp (β*(coxRecords r).x) else 0))

/-- T3(a): the target's closed form of the same partial likelihood. -/
def coxClosedLikelihood (β : ℝ) : ℝ :=
  -2*Real.log (6*Real.cosh β) -
    2*Real.log (2*Real.cosh (3*β)+2*Real.cosh β)

/-- T3(b): the efficient score at β=0, computed by summing
[1{failure}−d_t/n_t](x_r−xbar_t) over event times at which the record is at risk. -/
def coxEfficientScore (r : Fin 10) : ℝ := ∑ t : Fin 2,
  if coxRisk r (t.val+1) then
    ((if coxEvent r (t.val+1) then 1 else 0) - coxEventN (t.val+1)/coxRiskN (t.val+1)) *
      ((coxRecords r).x-coxRiskMean (t.val+1)) else 0

/-- T3(b): the exact displayed efficient-score vector. -/
def coxScores : Fin 10 → ℝ := ![2/3,-2/3,-1/3,3/2,1/3,-3/2,-1/3,-1/2,1/3,1/2]

/-- T3(a): observed information at the fitted β=0, computed from the
risk-set variances and Breslow event counts. -/
def coxInformation : ℝ := ∑ t : Fin 2, coxEventN (t.val+1) *
  ((∑ r, if coxRisk r (t.val+1) then ((coxRecords r).x)^2 else 0)/coxRiskN (t.val+1) -
    (coxRiskMean (t.val+1))^2)

/-- T3(a),(b): the two risk sets, event counts and covariate means give
information 12 and exactly the target's efficient scores; their sum is zero. -/
theorem cox_risk_score_certificate :
    coxRiskN 1 = 6 ∧ coxRiskN 2 = 4 ∧ coxEventN 1 = 2 ∧ coxEventN 2 = 2 ∧
    coxRiskMean 1 = 0 ∧ coxRiskMean 2 = 0 ∧ coxInformation = 12 ∧
    (∀ r, coxEfficientScore r = coxScores r) ∧ (∑ r, coxScores r) = 0 := by
  simp only [coxRiskN, coxEventN, coxRiskMean, coxInformation, coxEfficientScore,
    Fin.sum_univ_succ, coxRisk, coxEvent, coxRecords]
  norm_num [coxScores]
  intro r; fin_cases r <;> norm_num

/-- T3(a): the direct Breslow likelihood equals its cosh form, and has
its unique global maximum at βhat=0. This supplies the actual fit hypothesis
for the score-based implementation counterexample, not an assumed optimum. -/
theorem cox_unique_fit :
    (∀ β, coxLogLikelihood β = coxClosedLikelihood β) ∧
    (∀ β, β ≠ 0 → coxLogLikelihood β < coxLogLikelihood 0) := by
  have he : ∀ β, coxLogLikelihood β = coxClosedLikelihood β := by
    intro β
    simp only [coxLogLikelihood,coxEventN,coxRisk,coxEvent,coxRecords,Fin.sum_univ_succ]
    norm_num
    unfold coxClosedLikelihood
    simp only [Real.cosh_eq]
    congr 1 <;> congr 1 <;> ring
  refine ⟨he,?_⟩
  intro β hβ
  have ha : Real.log (6 : ℝ) < Real.log (6*Real.cosh β) :=
    Real.log_lt_log (by norm_num) (by have := Real.one_lt_cosh.mpr hβ; nlinarith)
  have hb : Real.log (4 : ℝ) ≤ Real.log (2*Real.cosh (3*β)+2*Real.cosh β) :=
    Real.log_le_log (by norm_num) (by
      have := Real.one_le_cosh (3*β); have := Real.one_le_cosh β; nlinarith)
  rw [he β,he 0]
  norm_num [coxClosedLikelihood]
  linarith

/-- T3/T8: record-level scalar sandwich ∑z_r², no finite-sample factor. -/
def scalarRecord (z : R → ℝ) : ℝ := ∑ r, (z r)^2

/-- T3/T8: a partition's scalar clustered sandwich, the sum of squared
cluster totals. This is algebraically the ordered pair sum for the partition. -/
def scalarCluster {G : Type*} [Fintype G] [DecidableEq G] (g : R → G) (z : R → ℝ) : ℝ :=
  ∑ k, (∑ r, if g r = k then z r else 0)^2

/-- T3/T8: the member-specific scalar component; all incident records
are clustered together, every outsider contributes its own square. -/
def scalarMember (d : R → Dyad M) (i : M) (z : R → ℝ) : ℝ :=
  (∑ r, if i ∈ (d r).members then z r else 0)^2 +
    ∑ r, if i ∉ (d r).members then (z r)^2 else 0

/-- T3(c)–(f): use the common Cox bread 1/12 on every efficient record
score, without changing the fitted sample or contributions. -/
def coxInfluence (r : Fin 10) : ℝ := coxScores r / 12

/-- T3(c): the record, id/repeated-dyad, and all four member components
computed from the constructed records and common efficient scores. -/
theorem cox_components :
    scalarRecord coxInfluence = 19/432 ∧
    scalarCluster (fun r => (coxRecords r).id) coxInfluence = 5/144 ∧
    (fun i => scalarMember (fun r => (coxRecords r).dyad) i coxInfluence) =
      ![25/864,59/2592,89/2592,185/2592] ∧
    (∑ i : Fin 4, scalarMember (fun r => (coxRecords r).dyad) i coxInfluence) = 17/108 := by
  norm_num [scalarRecord, scalarCluster, scalarMember, coxInfluence, coxScores,
    coxRecords, sixDyads, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

/-- T3(d)–(f): the direct DCR covariance is 5/144. Subtracting the
id-clustered component instead gives 23/432, or 103/2160 with asylike's
27/25 factor, each positive and different from the correct covariance. -/
theorem cox_substitution_counterexample :
    quadratic (fun r s => dyPattern (fun r => (coxRecords r).dyad) r s)
      coxInfluence = 5/144 ∧
    (17/108 : ℝ)-5/144-2*(19/432) = 5/144 ∧
    (17/108 : ℝ)-5/144-2*(5/144) = 23/432 ∧
    (23/432 : ℝ)-(5/144) = 8/432 ∧
    ((10-1 : ℝ)/10)*(6/(6-1)) = 27/25 ∧
    (17/108 : ℝ)-5/144-2*((27/25)*(5/144)) = 103/2160 ∧
    (5/144 : ℝ) ≠ 23/432 ∧ (5/144 : ℝ) ≠ 103/2160 ∧
    (0 : ℝ) < 5/144 ∧ (0 : ℝ) < 23/432 ∧ (0 : ℝ) < 103/2160 := by
  norm_num [quadratic, dyPattern, coxRecords, sixDyads, coxInfluence, coxScores,
    Fin.sum_univ_succ]

/-- T6: all ten edges among five members, in the order defined below. -/
def tenDyads : Fin 10 → Dyad (Fin 5) := fun r =>
  ⟨![({0,1} : Finset (Fin 5)),{0,2},{1,2},{0,3},{1,3},
    {2,3},{0,4},{1,4},{2,4},{3,4}] r, by fin_cases r <;> decide⟩

/-- T6: exact least-squares data x=(3,0,2,1,−1,1,−3,−2,3,−2),
y=(3,−2,−2,1,1,0,0,2,1,0), coefficient order intercept then slope. -/
def tenX : Fin 10 → ℝ := ![3,0,2,1,-1,1,-3,-2,3,-2]
/-- T6(a): "y=(3,−2,−2,1,1,0,0,2,1,0)"; exact response observations in the ten-dyad witness. -/
def tenY : Fin 10 → ℝ := ![3,-2,-2,1,1,0,0,2,1,0]
/-- T6(a): "OLS with intercept and one covariate"; the two columns are 1 and tenX. -/
def tenDesign : Matrix (Fin 10) (Fin 2) ℝ := fun r => ![1,tenX r]

/-- T6(a): explicit ordinary least-squares bread, not an arbitrary matrix. -/
def tenBread : Matrix (Fin 2) (Fin 2) ℝ := (1/208 : ℝ) • !![21,-1;-1,5]

/-- T6(a): exact residuals and record scores of the fitted model. -/
def tenResidual : Fin 10 → ℝ := fun r => ![31,-31,-33,7,9,-6,-2,23,5,-3] r / 13
/-- T6(b): the record score is "x_r uhat_r"; here it is the fitted residual times both design coordinates. -/
def tenScore (r : Fin 10) : Fin 2 → ℝ := fun i => tenResidual r * tenDesign r i

/-- T6(b),(c): direct DCR meat and the final variance matrix. -/
def tenMeat : Matrix (Fin 2) (Fin 2) ℝ := scoreSandwich (dyPattern tenDyads) tenScore
/-- T6(c) and p. 189 sandwich: "bread, meat, and bread"; the actual fitted ten-dyad DCR covariance. -/
def tenVariance : Matrix (Fin 2) (Fin 2) ℝ := tenBread * tenMeat * tenBread

/-- T6(a): full-rank least-squares fit, inverse bread, residuals, and
orthogonality. These certify that the sample really is an OLS counterexample. -/
theorem ten_ols_certificate :
    tenDesign.transpose * tenDesign = !![10,2;2,42] ∧
    tenBread * (tenDesign.transpose * tenDesign) = 1 ∧
    tenBread = bread tenDesign ∧ tenDesign.transpose *ᵥ tenY = ![4,4] ∧
    ols tenDesign tenY = ![5/13,1/13] ∧ olsResidual tenDesign tenY = tenResidual ∧
    tenDesign.transpose *ᵥ tenResidual = 0 := by
  have hg : tenDesign.transpose * tenDesign = (!![10,2;2,42] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tenDesign,tenX,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_succ]
  have hi : tenBread * (tenDesign.transpose * tenDesign) = 1 := by
    rw [hg]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tenBread,Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul,
        Fin.sum_univ_succ,Matrix.one_apply]
  have hb : tenBread = bread tenDesign := (Matrix.inv_eq_left_inv hi).symm
  have hxy : tenDesign.transpose *ᵥ tenY = ![4,4] := by
    ext i; fin_cases i <;>
      norm_num [tenDesign,tenX,tenY,Matrix.mulVec,Matrix.transpose_apply,dotProduct,Fin.sum_univ_succ]
  have hβ : ols tenDesign tenY = ![5/13,1/13] := by
    unfold ols; rw [← hb,hxy]
    ext i; fin_cases i <;>
      norm_num [tenBread,Matrix.mulVec,Matrix.smul_apply,smul_eq_mul,dotProduct,Fin.sum_univ_succ]
  refine ⟨hg,hi,hb,hxy,hβ,?_,?_⟩
  · unfold olsResidual; rw [hβ]
    ext r; fin_cases r <;>
      norm_num [tenDesign,tenX,tenY,tenResidual,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  · ext i; fin_cases i <;>
      norm_num [tenDesign,tenX,tenResidual,Matrix.mulVec,Matrix.transpose_apply,dotProduct,Fin.sum_univ_succ]

/-- T6(b),(c): exact DCR meat and variance, computed from all ordered
incident score pairs in the ten-dyad sample. -/
theorem ten_variance_certificate :
    tenMeat = (1/169 : ℝ) • !![1984,-1108;-1108,50] ∧
    scoreSandwich recordPattern tenScore = (1/169 : ℝ) • !![3744,4052;4052,15584] ∧
    tenVariance = (1/3655808 : ℝ) • !![460765,-79681;-79681,7157] := by
  have hm : tenMeat = (1/169 : ℝ) • (!![1984,-1108;-1108,50] : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tenMeat,scoreSandwich,dyPattern,tenDyads,tenScore,tenResidual,tenDesign,tenX,
        Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ]
  refine ⟨hm,?_,?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [scoreSandwich,recordPattern,tenScore,tenResidual,tenDesign,tenX,
        Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ]
  · unfold tenVariance; rw [hm]
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [tenBread,Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ]

/-- T6(d),(e): positive diagonal does not imply PSD. In the actual
OLS DCR matrix, contrast (1,6) has negative variance. The gated software
rule leaves it unchanged; multiplying by 5/4 also leaves a negative contrast. -/
theorem positive_diagonal_counterexample :
    (∀ i : Fin 2, 0 < tenVariance i i) ∧
    tenVariance.det = -70529/308915776 ∧
    quadratic tenVariance ![1,6] = -237755/3655808 ∧
    ¬tenVariance.PosSemidef ∧
    (∀ hV : tenVariance.IsHermitian, gatedPart tenVariance hV = tenVariance) ∧
    quadratic ((5/4 : ℝ) • tenVariance) ![1,6] = -1188775/14623232 := by
  have hv := ten_variance_certificate.2.2
  have hdiag : ∀ i : Fin 2, 0 < tenVariance i i := by
    intro i; fin_cases i <;> norm_num [hv,Matrix.smul_apply,smul_eq_mul]
  have hq : quadratic tenVariance ![1,6] = -237755/3655808 := by
    norm_num [hv,quadratic,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ]
  refine ⟨hdiag,?_,hq,?_,?_,?_⟩
  · norm_num [hv,Matrix.det_fin_two,Matrix.smul_apply,smul_eq_mul]
  · intro hp
    have hn := hp.dotProduct_mulVec_nonneg ![1,6]
    have hn' : 0 ≤ quadratic tenVariance ![1,6] := by
      simpa only [star_trivial,quadratic_eq_dot] using hn
    rw [hq] at hn'; norm_num at hn'
  · intro hV
    have hgate : ¬∃ i, tenVariance i i < 0 := by
      rintro ⟨i,hi⟩; have := hdiag i; linarith
    simp [gatedPart,hgate]
  · norm_num [hv,quadratic,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ]

/-- T7(iv): exact trace, determinant and the two eigenvalues of the
T6 matrix. These are real roots, not rounded numerical eigenvalues. -/
def tenEigenPlus : ℝ := ((467922/3655808 : ℝ) +
  Real.sqrt ((467922/3655808 : ℝ)^2-4*(-70529/308915776)))/2
/-- T7(iv): "lambda_±=(tau±sqrt(tau²−4delta))/2"; the exact smaller eigenvalue of the ten-dyad covariance. -/
def tenEigenMinus : ℝ := ((467922/3655808 : ℝ) -
  Real.sqrt ((467922/3655808 : ℝ)^2-4*(-70529/308915776)))/2

/-- T8/T9: Rubin's mean of the M coefficient estimates. The target's
M≥2 is an explicit hypothesis on the theorems below. -/
def imputationMean {m : ℕ} (b : Fin m → P → ℝ) : P → ℝ :=
  fun i => (m : ℝ)⁻¹ * ∑ t, b t i

/-- T8/T9: B=(M−1)^−1 Σ(b_m−bbar)(b_m−bbar)^T.
This is the BETWEEN-imputation covariance, not an independent sandwich component. -/
def betweenImputations {m : ℕ} (b : Fin m → P → ℝ) : Matrix P P ℝ :=
  fun i j => ((m : ℝ)-1)⁻¹ *
    ∑ t, (b t i-imputationMean b i)*(b t j-imputationMean b j)

/-- T8/T9: Rubin's full between-imputation contribution Q=(1+1/M)B. -/
def rubinBetween {m : ℕ} (b : Fin m → P → ℝ) : Matrix P P ℝ :=
  (1+(m : ℝ)⁻¹) • betweenImputations b

/-- T9: completed-data component means Ubar_j; no small-sample factor. -/
def componentMean {J : Type*} {m : ℕ} (U : J → Fin m → Matrix P P ℝ)
    (j : J) : Matrix P P ℝ := (m : ℝ)⁻¹ • ∑ t, U j t

/-- T9: component j first pooled as Ubar_j/a_j+Q and then multiplied
by the undo factor a_j. All components share the same coefficient estimates. -/
def pooledFirst {J : Type*} [Fintype J] {m : ℕ}
    (s a : J → ℝ) (U : J → Fin m → Matrix P P ℝ) (b : Fin m → P → ℝ) : Matrix P P ℝ :=
  ∑ j, (s j*a j) • ((a j)⁻¹ • componentMean U j + rubinBetween b)

/-- T9, the repair: form Σ_j s_j U_jm inside each completed data set,
then average and add Rubin's full Q exactly once, before any PSD adjustment. -/
def withinThenPool {J : Type*} [Fintype J] {m : ℕ}
    (s : J → ℝ) (U : J → Fin m → Matrix P P ℝ) (b : Fin m → P → ℝ) : Matrix P P ℝ :=
  (m : ℝ)⁻¹ • (∑ t, ∑ j, s j • U j t) + rubinBetween b

/-- T9(i),(iv): with common fixed nonzero factors, a common sample and
coefficient estimates, and no active nonlinear PSD projection, the exact
pooled-first gap is (c−1)(1+1/M)B. Adding (1−c)Q repairs the gap. -/
theorem rubin_pooling_gap {J : Type*} [Fintype J] {m : ℕ}
    (_hm : 2 ≤ m) (s a : J → ℝ) (ha : ∀ j, a j ≠ 0)
    (U : J → Fin m → Matrix P P ℝ)
    (_hsym : ∀ j t, (U j t).transpose = U j t) (b : Fin m → P → ℝ) :
    pooledFirst s a U b = (∑ j, s j • componentMean U j) + (∑ j, s j*a j) • rubinBetween b ∧
    withinThenPool s U b = (∑ j, s j • componentMean U j) + rubinBetween b ∧
    pooledFirst s a U b - withinThenPool s U b =
      ((∑ j, s j*a j)-1) • rubinBetween b ∧
    pooledFirst s a U b + (1-(∑ j, s j*a j)) • rubinBetween b = withinThenPool s U b := by
  have hfirst : pooledFirst s a U b = (∑ j, s j • componentMean U j) +
      (∑ j, s j*a j) • rubinBetween b := by
    ext i k
    simp only [pooledFirst,Matrix.sum_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    rw [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [ha j] <;> ring
  have hwithin : withinThenPool s U b =
      (∑ j, s j • componentMean U j) + rubinBetween b := by
    ext i k
    simp only [withinThenPool,componentMean,Matrix.sum_apply,Matrix.add_apply,
      Matrix.smul_apply,smul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨hfirst,hwithin,?_,?_⟩
  · rw [hfirst,hwithin]
    ext i k
    simp only [Matrix.sum_apply,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
    ring
  · rw [hfirst,hwithin]
    ext i k
    simp only [Matrix.sum_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
    ring

/-- T9(ii): the DCR weights are +1 for K members, −1 for repeated dyad,
and −(K−2) for records. Fin 2 labels D then 0. -/
def dcrWeight (k : ℕ) : (Fin k ⊕ Fin 2) → ℝ :=
  Sum.elim (fun _ => 1) (fun j => if j = 0 then -1 else -((k : ℝ)-2))

/-- T9(ii): the DCR component weights sum to one, so Rubin pooling
commutes with the unadjusted linear decomposition when all a_j=1. -/
theorem dcr_weights_sum (k : ℕ) : ∑ j, dcrWeight k j = 1 := by
  simp [dcrWeight, Fintype.sum_sum_type, Fin.sum_univ_succ]
  ring

/-- T9(iii): the asylike undo factors depend on the fixed member-cluster,
repeated-dyad and record cluster counts, respectively. -/
def asylikeFactors (k : ℕ) (Gi : Fin k → ℝ) (GD n : ℝ) : (Fin k ⊕ Fin 2) → ℝ :=
  Sum.elim (fun i => 1-1/Gi i) (fun j => if j = 0 then 1-1/GD else 1-1/n)

/-- T9(iii): c−1=−Σ_i1/G_i+1/G_D+(K−2)/n, so the between-imputation
term is not generally preserved by undoing already-pooled covariances. -/
theorem asylike_coefficient_gap (k : ℕ) (Gi : Fin k → ℝ) (GD n : ℝ) :
    (∑ j, dcrWeight k j * asylikeFactors k Gi GD n j)-1 =
      -(∑ i, 1/Gi i) + 1/GD + ((k : ℝ)-2)/n := by
  simp [dcrWeight, asylikeFactors, Fintype.sum_sum_type, Fin.sum_univ_succ,
    Finset.sum_sub_distrib]
  ring

/-- T8: completion A has dyad successes 4,2,2,2,2,0, completion B
4,3,3,3,3,2, each out of four observations. True means the B completion. -/
def miSuccesses (B : Bool) : Fin 6 → ℕ := if B then ![4,3,3,3,3,2] else ![4,2,2,2,2,0]

/-- T8: the 24 binary outcomes, with the successes placed first in each
dyad; repeated dyad label is r.1 and observation within dyad r.2. -/
def miOutcome (B : Bool) (r : Fin 6 × Fin 4) : ℝ :=
  if r.2.val < miSuccesses B r.1 then 1 else 0

/-- T8: intercept-only binary logit fit p=sample mean, b=log(p/(1−p)),
H=np(1−p), efficient record score y_r−p. Neither completion is separated. -/
def miProbability (B : Bool) : ℝ := (1/24 : ℝ)*∑ r, miOutcome B r
/-- T8(a): "b=log(p/(1−p))"; the closed-form intercept-only binary-logit estimate of each completion. -/
def miEstimate (B : Bool) : ℝ := Real.log (miProbability B/(1-miProbability B))
/-- T8(a): "H=24p(1−p)"; observed information at the completed-data logit fit. -/
def miInformation (B : Bool) : ℝ := 24*miProbability B*(1-miProbability B)
/-- T8(a): "s_r=y_r−p"; the efficient record score at that completion’s fitted probability. -/
def miScore (B : Bool) (r : Fin 6 × Fin 4) : ℝ := miOutcome B r - miProbability B

/-- T8(b): unadjusted record, repeated-dyad and member components from
the same logit scores and information. Each member has one incident cluster
of 12 observations and 12 outsider singletons, so G_i=13. -/
def miRecordU (B : Bool) : ℝ := (miInformation B)^(-2 : ℤ)*scalarRecord (miScore B)
/-- T8(b): "U=H^−2 sum_clusters(sum_r s_r)²"; use the repeated-dyad partition of all 24 observations. -/
def miDyadU (B : Bool) : ℝ :=
  (miInformation B)^(-2 : ℤ)*scalarCluster Prod.fst (miScore B)
/-- T8(b): "one cluster of the 12 incident observations and 12 singletons"; the member-specific unadjusted sandwich. -/
def miMemberU (B : Bool) (i : Fin 4) : ℝ :=
  (miInformation B)^(-2 : ℤ)*scalarMember (fun r => sixDyads r.1) i (miScore B)

/-- T8(a)–(c): the exact fitted probabilities, estimates, information,
all unadjusted components and the two completed-data DCR variances. -/
theorem mi_completed_data_certificate :
    miProbability false = 1/2 ∧ miProbability true = 3/4 ∧
    miEstimate false = 0 ∧ miEstimate true = Real.log 3 ∧
    miInformation false = 6 ∧ miInformation true = 9/2 ∧
    miDyadU false = 2/9 ∧ miDyadU true = 8/81 ∧
    miRecordU false = 1/6 ∧ miRecordU true = 2/9 ∧
    (∀ i, miMemberU false i = 7/36) ∧
    (fun i => miMemberU true i) = ![5/27,5/27,11/81,11/81] ∧
    ((∑ i, miMemberU false i)-miDyadU false-2*miRecordU false) = 2/9 ∧
    ((∑ i, miMemberU true i)-miDyadU true-2*miRecordU true) = 8/81 := by
  have hpA : miProbability false = (1/2 : ℝ) := by
    simp only [miProbability,Fintype.sum_prod_type,Fin.sum_univ_succ]
    norm_num [miOutcome,miSuccesses]
  have hpB : miProbability true = (3/4 : ℝ) := by
    simp only [miProbability,Fintype.sum_prod_type,Fin.sum_univ_succ]
    norm_num [miOutcome,miSuccesses]
  have hA : miInformation false = (6 : ℝ) := by norm_num [miInformation,hpA]
  have hB : miInformation true = (9/2 : ℝ) := by norm_num [miInformation,hpB]
  have hDA : miDyadU false = (2/9 : ℝ) := by
    simp only [miDyadU,hA,scalarCluster,Fintype.sum_prod_type,Fin.sum_univ_succ]
    norm_num [miScore,hpA,miOutcome,miSuccesses]
  have hDB : miDyadU true = (8/81 : ℝ) := by
    simp only [miDyadU,hB,scalarCluster,Fintype.sum_prod_type,Fin.sum_univ_succ]
    norm_num [miScore,hpB,miOutcome,miSuccesses]
  have h0A : miRecordU false = (1/6 : ℝ) := by
    simp only [miRecordU,hA,scalarRecord,Fintype.sum_prod_type,Fin.sum_univ_succ]
    norm_num [miScore,hpA,miOutcome,miSuccesses]
  have h0B : miRecordU true = (2/9 : ℝ) := by
    simp only [miRecordU,hB,scalarRecord,Fintype.sum_prod_type,Fin.sum_univ_succ]
    norm_num [miScore,hpB,miOutcome,miSuccesses]
  have hcA : ∀ i : Fin 4, miMemberU false i = (7/36 : ℝ) := by
    intro i; fin_cases i <;>
      simp only [miMemberU,hA,scalarMember,Fintype.sum_prod_type,Fin.sum_univ_succ] <;>
      norm_num [miScore,hpA,miOutcome,miSuccesses,sixDyads]
  have hcB : (fun i => miMemberU true i) = (![5/27,5/27,11/81,11/81] : Fin 4 → ℝ) := by
    ext i; fin_cases i <;>
      simp only [miMemberU,hB,scalarMember,Fintype.sum_prod_type,Fin.sum_univ_succ] <;>
      norm_num [miScore,hpB,miOutcome,miSuccesses,sixDyads]
  refine ⟨hpA,hpB,?_,?_,hA,hB,hDA,hDB,h0A,h0B,hcA,hcB,?_,?_⟩
  · norm_num [miEstimate,hpA]
  · norm_num [miEstimate,hpB]
  · norm_num [hcA,hDA,h0A,Fin.sum_univ_succ]
  · have he : ∀ i, miMemberU true i = (![5/27,5/27,11/81,11/81] : Fin 4 → ℝ) i :=
      fun i => congrFun hcB i
    norm_num [he,hDB,h0B,Fin.sum_univ_succ]

/-- T8(d): five logit estimates, A for imputations 1–3 and B for 4–5. -/
def miFiveEstimates : Fin 5 → Fin 1 → ℝ := fun t _ => ![0,0,0,Real.log 3,Real.log 3] t

/-- T8(d): Rubin's between-imputation variance is 3/10 log²3 and its
full contribution is 9/25 log²3, as derived from the five estimates. -/
theorem mi_between_certificate :
    imputationMean miFiveEstimates 0 = (2/5 : ℝ)*Real.log 3 ∧
    betweenImputations miFiveEstimates 0 0 = (3/10 : ℝ)*(Real.log 3)^2 ∧
    rubinBetween miFiveEstimates 0 0 = (9/25 : ℝ)*(Real.log 3)^2 := by
  simp [imputationMean, betweenImputations, rubinBetween, miFiveEstimates,
    Fin.sum_univ_succ, Matrix.smul_apply, smul_eq_mul]
  refine ⟨?_,?_,?_⟩ <;> ring

/-- T8(e),(f): the component means over the actual five imputations. -/
def miMeanMember (i : Fin 4) : ℝ := (3*miMemberU false i+2*miMemberU true i)/5
/-- T8(f): "Ubar_j" is the component mean across five completions, three A and two B; repeated-dyad component. -/
def miMeanDyad : ℝ := (3*miDyadU false+2*miDyadU true)/5
/-- T8(f): "Ubar_j" is the component mean across five completions, three A and two B; record component. -/
def miMeanRecord : ℝ := (3*miRecordU false+2*miRecordU true)/5

/-- T8: the target covariance pools within-DCR then adds Rubin Q once. -/
def miCorrectTotal : ℝ :=
  (∑ i, miMeanMember i)-miMeanDyad-2*miMeanRecord + rubinBetween miFiveEstimates 0 0

/-- T8: the pooled-first code operation multiplies each entire pooled
component by its undo factor, including its copy of the shared Rubin Q.
This Lean definition specifies what the published software computes. -/
def miCodeTotal : ℝ :=
  (∑ i : Fin 4, (12/13 : ℝ)*(miMeanMember i/(12/13)+rubinBetween miFiveEstimates 0 0)) -
    (5/6 : ℝ)*(miMeanDyad/(5/6)+rubinBetween miFiveEstimates 0 0) -
    2*(23/24 : ℝ)*(miMeanRecord/(23/24)+rubinBetween miFiveEstimates 0 0)

/-- T8(e),(f): in the 24-observation, five-imputation logit example, the
code yields 14/81+(441/1300)log²3 rather than 14/81+(9/25)log²3.
The exact negative gap is −(27/1300)log²3; both variances are positive. -/
theorem mi_pooling_counterexample :
    miCorrectTotal = 14/81+(9/25 : ℝ)*(Real.log 3)^2 ∧
    miCodeTotal = 14/81+(441/1300 : ℝ)*(Real.log 3)^2 ∧
    miCodeTotal-miCorrectTotal = -(27/1300 : ℝ)*(Real.log 3)^2 ∧
    miCodeTotal < miCorrectTotal ∧ 0 < miCodeTotal ∧ 0 < miCorrectTotal ∧
    (4*(12/13 : ℝ)-5/6-2*(23/24)) = 49/52 := by
  rcases mi_completed_data_certificate with ⟨_,_,_,_,_,_,hDA,hDB,h0A,h0B,hcA,hcB,_,_⟩
  have hQ := mi_between_certificate.2.2
  have hcorrect : miCorrectTotal = (14/81 : ℝ)+(9/25 : ℝ)*(Real.log 3)^2 := by
    unfold miCorrectTotal miMeanMember miMeanDyad miMeanRecord
    rw [hQ]
    simp only [Fin.sum_univ_succ,hcA,hDA,hDB,h0A,h0B]
    have he : ∀ i, miMemberU true i = (![5/27,5/27,11/81,11/81] : Fin 4 → ℝ) i :=
      fun i => congrFun hcB i
    simp only [he]; norm_num <;> ring
  have hcode : miCodeTotal = (14/81 : ℝ)+(441/1300 : ℝ)*(Real.log 3)^2 := by
    unfold miCodeTotal miMeanMember miMeanDyad miMeanRecord
    rw [hQ]
    simp only [Fin.sum_univ_succ,hcA,hDA,hDB,h0A,h0B]
    have he : ∀ i, miMemberU true i = (![5/27,5/27,11/81,11/81] : Fin 4 → ℝ) i :=
      fun i => congrFun hcB i
    simp only [he]; norm_num <;> ring
  have hgap : miCodeTotal-miCorrectTotal = -(27/1300 : ℝ)*(Real.log 3)^2 := by
    rw [hcode,hcorrect]; ring
  have hlog : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hs : 0 < (Real.log (3 : ℝ))^2 := sq_pos_of_pos hlog
  refine ⟨hcorrect,hcode,hgap,?_,?_,?_,?_⟩
  · nlinarith
  · rw [hcode]; nlinarith [sq_nonneg (Real.log (3 : ℝ))]
  · rw [hcorrect]; nlinarith [sq_nonneg (Real.log (3 : ℝ))]
  · norm_num

/-- T10: one printed Supplementary Table A.2 row. n counts all KEVs,
loss counts Sig.→Insig. at 5%, and printed decimals are stored exactly as
integer thousandths. The empirical inputs are transcribed, not inferred by Lean. -/
structure StudyRow where
  n : ℕ
  loss : ℕ
  lossMilli : ℕ
  serMilli : ℕ

/-- T10: the 22 rows in printed Table A.2 order (supplement p. A3). -/
def studies : Fin 22 → StudyRow :=
  ![⟨6,1,167,2739⟩, ⟨173,43,249,2187⟩, ⟨29,6,207,2200⟩,
    ⟨8,3,375,1099⟩, ⟨9,8,889,3269⟩, ⟨24,0,0,1526⟩,
    ⟨45,5,111,898⟩, ⟨36,5,139,1511⟩, ⟨4,2,500,4158⟩,
    ⟨1,1,1000,1691⟩, ⟨170,7,41,955⟩, ⟨3,0,0,1895⟩,
    ⟨6,0,0,1301⟩, ⟨41,8,195,1432⟩, ⟨16,0,0,908⟩,
    ⟨18,4,222,1426⟩, ⟨20,1,50,1291⟩, ⟨18,0,0,999⟩,
    ⟨9,0,0,1071⟩, ⟨15,0,0,1212⟩, ⟨28,17,607,3268⟩, ⟨12,2,167,1311⟩]

/-- T10(i): |k/n−r|≤1/2000 after multiplying by 2000n. The integer
form is EXACTLY equivalent when n>0 and r=lossMilli/1000. -/
abbrev roundingConsistent (row : StudyRow) (k : ℕ) : Prop :=
  |2000*(k : ℤ)-2*(row.n : ℤ)*(row.lossMilli : ℤ)| ≤ (row.n : ℤ)

/-- T10(i): every printed rounded loss share has exactly one feasible
integer numerator, namely the loss entry of studies. This does not
certify the original estimates or p-values behind the transcribed table. -/
theorem study_unique_integer_recovery :
    ∀ i : Fin 22, ∀ k : ℕ,
      (k ≤ (studies i).n ∧ roundingConsistent (studies i) k) ↔ k = (studies i).loss := by
  have hc : ∀ i : Fin 22, 0 < (studies i).n ∧ (studies i).n < 1000 ∧
      (studies i).loss ≤ (studies i).n ∧ roundingConsistent (studies i) (studies i).loss := by
    decide
  intro i k
  have hi := hc i
  constructor
  · rintro ⟨hk, hround⟩
    have hr₁ := abs_le.mp hround
    have hr₂ := abs_le.mp hi.2.2.2
    omega
  · intro he; subst k; exact ⟨hi.2.2.1,hi.2.2.2⟩

/-- T10(ii),(iii), correction to p. 196: exactly four studies have
half-or-more loss (Colgan, Efrat–Newman, Fang–Johnson–Leeds, Weisiger),
and exactly three have more-than-half loss (excluding Efrat–Newman). -/
theorem study_threshold_counts :
    (Finset.univ.filter (fun i : Fin 22 => (studies i).n ≤ 2*(studies i).loss)) = ({4,8,9,20} : Finset (Fin 22)) ∧
    (Finset.univ.filter (fun i : Fin 22 => (studies i).n < 2*(studies i).loss)) = ({4,9,20} : Finset (Fin 22)) ∧
    ({i : Fin 22 | (studies i).n ≤ 2*(studies i).loss} : Finset (Fin 22)).card = 4 ∧
    ({i : Fin 22 | (studies i).n < 2*(studies i).loss} : Finset (Fin 22)).card = 3 ∧
    (Finset.univ.filter (fun i : Fin 22 => 500 ≤ (studies i).lossMilli)) = ({4,8,9,20} : Finset (Fin 22)) ∧
    (studies 8).n = 4 ∧ (studies 8).loss = 2 := by decide

/-- T10(iv): the neighboring printed counts are correct: 22 studies,
691 KEVs, seven studies with zero losses, eighteen Avg. SERs above one,
and exact minimum/maximum printed SERs 0.898/4.158. -/
theorem study_neighboring_counts :
    Fintype.card (Fin 22) = 22 ∧ (∑ i, (studies i).n) = 691 ∧
    ({i : Fin 22 | (studies i).loss = 0} : Finset (Fin 22)).card = 7 ∧
    ({i : Fin 22 | 1000 < (studies i).serMilli} : Finset (Fin 22)).card = 18 ∧
    (∀ i, 898 ≤ (studies i).serMilli ∧ (studies i).serMilli ≤ 4158) ∧
    (studies 6).serMilli = 898 ∧ (studies 8).serMilli = 4158 := by decide

/-- T1(e),(f): the intercept-only OLS fit is the sample mean. This uses
the number of RECORDS, not the number of dyad members. -/
def sampleMean (u : R → ℝ) : ℝ := (Fintype.card R : ℝ)⁻¹ * ∑ r, u r

/-- T1(e),(f): residual-based unadjusted intercept DCR estimator,
n^−2 Σ_{r,s incident}(u_r−ubar)(u_s−ubar), exactly the p. 189 plug-in
with intercept bread 1/n and the Table 4 restriction. -/
def interceptDCR (d : R → Dyad M) (u : R → ℝ) : ℝ :=
  (Fintype.card R : ℝ)^(-2 : ℤ) * quadratic (fun r s => dyPattern d r s)
    (fun r => u r-sampleMean u)


/-- Finite lemma for T1(e),(f): any symmetric incidence mask with q
retained entries per row yields the exact centering correction
n² Vhat=u^TWu−qn ubar². For the two examples q=2 and q=5.
This is purely algebraic and uses the actual residual estimator. -/
theorem intercept_dcr_centering (d : R → Dyad M) (q : ℝ)
    (hrow : ∀ r, ∑ s, dyPattern d r s = q)
    (hn : (Fintype.card R : ℝ) ≠ 0) (u : R → ℝ) :
    (Fintype.card R : ℝ)^2 * interceptDCR d u =
      quadratic (fun r s => dyPattern d r s) u -
        q*(Fintype.card R : ℝ)*(sampleMean u)^2 := by
  let W : Matrix R R ℝ := fun r s => dyPattern d r s
  let a := sampleMean u
  have hcol : ∀ s, ∑ r, W r s = q := by
    intro s
    have he : (∑ r, W r s) = ∑ r, W s r := by
      apply Finset.sum_congr rfl
      intro r _
      simp [W,dyPattern,Finset.inter_comm]
    rw [he]; exact hrow s
  have hs : ∑ r, u r = (Fintype.card R : ℝ)*a := by
    dsimp [a,sampleMean]
    simp [hn,mul_assoc]
  have h₁ : (∑ r, ∑ s, a*u r*W r s) = (a*q)*∑ r, u r := by
    calc
      _ = ∑ r, a*u r*q := by
        apply Finset.sum_congr rfl
        intro r _
        rw [← Finset.mul_sum]
        simp only [W,hrow]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _; ring
  have h₂ : (∑ r, ∑ s, a*u s*W r s) = (a*q)*∑ r, u r := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ s, a*u s*q := by
        apply Finset.sum_congr rfl
        intro s _
        rw [← Finset.mul_sum,hcol]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _; ring
  have h₃ : (∑ r, ∑ s, a^2*W r s) = a^2*(Fintype.card R : ℝ)*q := by
    simp [← Finset.mul_sum,W,hrow] <;> ring
  have hpoint : ∀ r s, (u r-a)*(u s-a)*W r s =
      u r*u s*W r s-a*u r*W r s-a*u s*W r s+a^2*W r s := by
    intro r s; ring
  have he : quadratic W (fun r => u r-a) = quadratic W u -
      q*(Fintype.card R : ℝ)*a^2 := by
    simp only [quadratic]
    simp_rw [hpoint,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [h₁,h₂,h₃,hs]
    ring
  unfold interceptDCR
  simp only [_root_.zpow_neg,zpow_ofNat]
  rw [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero 2 hn),one_mul]
  exact he

/-- T1(e), m=1: the actual residual-based estimator already overstates
variance IN EXPECTATION in the bounded 16-point error law, not just under
a population covariance mask. This also contradicts T5's expectation reading. -/
theorem four_residual_expectation_counterexample :
    finiteExpectation fourBlockLaw (fun ω => interceptDCR fourDyads (fourBlockErrors ω)) = 7/32 ∧
    finiteVariance fourBlockLaw (fun ω => sampleMean (fourBlockErrors ω)) = 3/16 ∧
    finiteVariance fourBlockLaw (fun ω => sampleMean (fourBlockErrors ω)) <
      finiteExpectation fourBlockLaw (fun ω => interceptDCR fourDyads (fourBlockErrors ω)) := by
  norm_num [finiteExpectation,finiteVariance,fourBlockLaw,fourBlockErrors,interceptDCR,
    sampleMean,quadratic,dyPattern,fourDyads,Fin.sum_univ_succ]

/-- Disjoint blocks in T1(e),(f) use distinct member labels (b,i).
Lifting a dyad preserves its two distinct members and unordered membership. -/
def liftDyad {k : ℕ} (b : Fin k) (d : Dyad M) : Dyad (Fin k × M) where
  members := d.members.map ⟨fun i => (b,i), by intro i j h; exact (Prod.mk.inj h).2⟩
  two := by simp [d.two]

/-- T1(e): m independent blocks of AB,AC,DE,DF, on 6m members. -/
def replicatedFourDyads (m : ℕ) (r : Fin m × Fin 4) : Dyad (Fin m × Fin 6) :=
  liftDyad r.1 (fourDyads r.2)

/-- T1(f): m independent K4 blocks of six dyads, on 4m members. -/
def replicatedSixDyads (m : ℕ) (r : Fin m × Fin 6) : Dyad (Fin m × Fin 4) :=
  liftDyad r.1 (sixDyads r.2)

/-- T1(e): errors of block b take the 16-point law in (d). A single
probability space carries the infinite sequence; samples use the first m
blocks. The finite target contains m≥1, while m=0 is harmless for limits. -/
def fourSequenceErrors {Ω : Type*} (block : ℕ → Ω → Fin 16)
    (m : ℕ) (ω : Ω) (r : Fin m × Fin 4) : ℝ := fourBlockErrors (block r.1.val ω) r.2

/-- T1(e): the two incident-pair sums within block b. -/
def fourPairSum {Ω : Type*} (block : ℕ → Ω → Fin 16) (b : ℕ) (ω : Ω) (pair : Fin 2) : ℝ :=
  if pair = 0 then fourBlockErrors (block b ω) 0 + fourBlockErrors (block b ω) 1
    else fourBlockErrors (block b ω) 2 + fourBlockErrors (block b ω) 3

/-- T1(e), finite arithmetic consequence of the expectation formula:
the gap is strictly positive for EVERY integer m≥1, not only asymptotically. -/
theorem four_expected_gap_arithmetic (m : ℕ) (hm : 1 ≤ m) :
    (10*(m : ℝ)-3)/(32*(m : ℝ)^2)-3/(16*(m : ℝ)) =
      (4*(m : ℝ)-3)/(32*(m : ℝ)^2) ∧
    0 < (4*(m : ℝ)-3)/(32*(m : ℝ)^2) := by
  have hp : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  constructor
  · field_simp; ring
  · apply div_pos <;> nlinarith [sq_pos_of_pos hp]

/-- T1(f): the 13 independent fair signs consist of four member shocks,
three complementary-pair shocks and six own-edge shocks. -/
def signValue (a : Fin 2) : ℝ := if a = 0 then -1 else 1

/-- T1(f): the exact bounded error loading formula.
Complementary-pair signs are + for edges 0,1,2 and − for 3,4,5.
Node signs occupy indices 0…3, pair signs 4…6, own signs 7…12. -/
def sixErrorsFromSigns (a : Fin 13 → Fin 2) (r : Fin 6) : ℝ :=
  (Real.sqrt 2/4) * (∑ i : Fin 4,
    if i ∈ (sixDyads r).members then signValue (a ⟨i.val, by omega⟩) else 0) +
  (if r.val < 3 then 1 else -1) * (Real.sqrt 2/2) *
    signValue (a ⟨4+(![0,1,2,2,1,0] r : Fin 3).val, by omega⟩) +
  (1/2 : ℝ) * signValue (a ⟨7+r.val, by omega⟩)

/-- T1(f): first m independent sign blocks, with six observations each. -/
def sixSequenceErrors {Ω : Type*} (block : ℕ → Ω → (Fin 13 → Fin 2))
    (m : ℕ) (ω : Ω) (r : Fin m × Fin 6) : ℝ := sixErrorsFromSigns (block r.1.val ω) r.2

/-- T1(f): q_b=u_b^T W_6 u_b, with diagonal included and row sums 5. -/
def sixBlockQ (a : Fin 13 → Fin 2) : ℝ :=
  quadratic (fun r s => dyPattern sixDyads r s) (sixErrorsFromSigns a)

/-- T1(f), finite arithmetic consequence: with n=6m, expected DCR
exceeds 1/n exactly for m≥2. The m=1 residual effect reverses the ordering. -/
theorem six_expected_gap_arithmetic (m : ℕ) (hm : 1 ≤ m) :
    (3/(2*(6*(m : ℝ)))-5/(6*(m : ℝ))^2) - 1/(6*(m : ℝ)) =
      (6*(m : ℝ)-10)/(2*(6*(m : ℝ))^2) ∧
    (0 < (6*(m : ℝ)-10)/(2*(6*(m : ℝ))^2) ↔ 2 ≤ m) ∧
    (3/(2*6 : ℝ)-5/(6 : ℝ)^2) = 1/9 := by
  have hp : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hd : 0 < 2*(6*(m : ℝ))^2 := by positivity
  refine ⟨?_,?_,?_⟩
  · field_simp; ring
  · rw [div_pos_iff_of_pos_right hd]
    constructor
    · intro h
      have hnat : (1 : ℝ) < m := by linarith
      have : 1 < m := by exact_mod_cast hnat
      omega
    · intro h
      have : (2 : ℝ) ≤ m := by exact_mod_cast h
      linarith
  · norm_num

/-- T5's expectation reading, faithfully stated for any square-integrable
centered errors on any probability space, full-rank fixed X and a contrast.
There is no unproved exogeneity or covariance-sign premise hidden in the object. -/
def PrintedExpectationLowerBound : Prop :=
  ∀ (Ω : Type) [meas : MeasurableSpace Ω] (μ : @Measure Ω meas)
    [_prob : @IsProbabilityMeasure Ω meas μ] (n p k : ℕ)
    (d : Fin n → Dyad (Fin k)) (X : Matrix (Fin n) (Fin p) ℝ)
    (β c : Fin p → ℝ) (u : Fin n → Ω → ℝ),
    (X.transpose * X).det ≠ 0 → (∀ r, MemLp (u r) 2 μ) →
    (∀ r, ∫ ω, u r ω ∂μ = 0) →
    (∃ r s, ¬((d r).members ∩ (d s).members).Nonempty ∧ errorCovariance μ u r s ≠ 0) →
    (∫ ω, quadratic (plugIn X (olsResidual X (X *ᵥ β + fun r => u r ω)) (dyPattern d)) c ∂μ) ≤
      variance (fun ω => c ⬝ᵥ ols X (X *ᵥ β + fun r => u r ω)) μ


/-- The explicit finite laws in T1 can also be viewed as ordinary
probability measures: Σ_ω p_ω δ_ω. No atom has negative weight, and no
zero measure is substituted for the sampling law. -/
def finiteLawMeasure {S : Type*} [Fintype S] [MeasurableSpace S]
    (law : FiniteLaw S) : Measure S :=
  ∑ ω, (ENNReal.ofReal (law.weight ω)) • Measure.dirac ω

/-- The finite-law measure has total mass exactly one, by the law's
proved normalization. This bridges explicit bounded examples to T2/T5's
arbitrary-probability-space statements. -/
theorem finite_law_probability {S : Type*} [Fintype S] [MeasurableSpace S]
    (law : FiniteLaw S) : IsProbabilityMeasure (finiteLawMeasure law) := by
  constructor
  simp only [finiteLawMeasure,Measure.finsetSum_apply,MeasurableSet.univ,
    Measure.smul_apply,Measure.dirac_apply_of_mem,Set.mem_univ,smul_eq_mul,mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => law.nonneg ω),law.total]
  norm_num

/-- Expectations under Σ p_ω δ_ω equal the exact weighted finite sums
used in the counterexamples. No unproved distribution-realization axiom. -/
theorem finite_law_integral {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (law : FiniteLaw S) (f : S → ℝ) :
    (∫ ω, f ω ∂finiteLawMeasure law) = finiteExpectation law f := by
  unfold finiteLawMeasure
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure,integral_dirac,smul_eq_mul,
      ENNReal.toReal_ofReal (law.nonneg _),finiteExpectation]
  · intro ω _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

/-- The ordinary sampling variance under the finite-law probability
measure equals E[(f−Ef)²] in the exact finite-sum representation. -/
theorem finite_law_variance {S : Type*} [Fintype S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (law : FiniteLaw S) (f : S → ℝ) :
    variance f (finiteLawMeasure law) = finiteVariance law f := by
  rw [variance_eq_integral (measurable_of_countable f).aemeasurable,
    finite_law_integral law f,finite_law_integral]
  rfl

/-- T1(e),(f): the intercept-only design is the single column of ones,
so its ordinary OLS bread is the inverse RECORD count. -/
def interceptDesign : Matrix R (Fin 1) ℝ := fun _ _ => 1

/-- Finite OLS lemma underlying the replicated examples: for a nonempty
sample, the fit is exactly ubar, the residuals are u−ubar, and the sandwich
contrast equals the explicitly defined residual-based intercept DCR. -/
theorem intercept_fit_certificate (hn : (Fintype.card R : ℝ) ≠ 0)
    (d : R → Dyad M) (u : R → ℝ) :
    (interceptDesign : Matrix R (Fin 1) ℝ).transpose * interceptDesign =
      Matrix.of (fun _ _ => (Fintype.card R : ℝ)) ∧
    bread (interceptDesign : Matrix R (Fin 1) ℝ) =
      Matrix.of (fun _ _ => (Fintype.card R : ℝ)⁻¹) ∧
    (ols interceptDesign u) = (fun _ => sampleMean u) ∧
    olsResidual interceptDesign u = (fun r => u r-sampleMean u) ∧
    quadratic (plugIn interceptDesign (olsResidual interceptDesign u) (dyPattern d))
      (fun _ : Fin 1 => (1 : ℝ)) = interceptDCR d u := by
  let n : ℝ := Fintype.card R
  have hg : (interceptDesign : Matrix R (Fin 1) ℝ).transpose * interceptDesign =
      Matrix.of (fun _ _ => n) := by
    ext i j
    simp [interceptDesign,Matrix.mul_apply,Matrix.transpose_apply,n]
  have hb : bread (interceptDesign : Matrix R (Fin 1) ℝ) =
      Matrix.of (fun _ _ => n⁻¹) := by
    unfold bread; rw [hg]
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i; fin_cases j
    simp [Matrix.mul_apply,Fin.sum_univ_succ,Matrix.one_apply,n,hn]
  have hfit : ols (interceptDesign : Matrix R (Fin 1) ℝ) u = fun _ => sampleMean u := by
    unfold ols; rw [hb]
    ext i; fin_cases i
    simp [interceptDesign,Matrix.mulVec,Matrix.transpose_apply,dotProduct,
      Fin.sum_univ_succ,sampleMean,n]
  have hres : olsResidual (interceptDesign : Matrix R (Fin 1) ℝ) u =
      fun r => u r-sampleMean u := by
    unfold olsResidual; rw [hfit]
    ext r; simp [interceptDesign,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  refine ⟨hg,hb,hfit,hres,?_⟩
  rw [plugIn,sandwich_quadratic,hb,hres]
  have hh : (interceptDesign : Matrix R (Fin 1) ℝ) *ᵥ
      ((Matrix.of (fun _ _ => n⁻¹) : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ (fun _ : Fin 1 => (1 : ℝ))) = fun _ => n⁻¹ := by
    ext r; simp [interceptDesign,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  rw [hh]
  simp only [quadratic,residualMeat,interceptDCR,_root_.zpow_neg,zpow_ofNat,inv_pow,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  dsimp [n]
  ring

/-- T6: the numerical ten-dyad DCR matrix really is symmetric, so its
gated and repaired PSD operations have an inhabited input hypothesis. -/
theorem ten_variance_hermitian : tenVariance.IsHermitian := by
  have hv := ten_variance_certificate.2.2
  apply Matrix.IsHermitian.ext
  intro i j; fin_cases i <;> fin_cases j <;>
    norm_num [hv,Matrix.smul_apply,smul_eq_mul]

/-- T7(ii): Mathlib's canonical spectral positive part fixes exactly
the PSD input matrices, as does any orthogonal eigenbasis realization. -/
theorem positive_part_fixed_iff (V : Matrix P P ℝ) (hV : V.IsHermitian) :
    positivePart V hV = V ↔ V.PosSemidef := by
  let Q : Matrix P P ℝ := hV.eigenvectorUnitary
  have ho : Q.transpose * Q = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hV.eigenvectorUnitary
  have ho' : Q * Q.transpose = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_mul_star_self hV.eigenvectorUnitary
  have hv : V = Q * Matrix.diagonal hV.eigenvalues * Q.transpose := by
    simpa [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial,Q]
      using hV.spectral_theorem
  have he := spectral_clip_fixed_iff Q hV.eigenvalues ho ho'
  simpa only [positivePart,← hv] using he

/-- T5: the residual expectation lower-bound claim is false as well.
T1(e)'s m=1 finite law gives an exact witness, converted to a genuine
probability measure by the proved finite-law bridge. -/
theorem printed_expectation_claim_false : ¬PrintedExpectationLowerBound := by
  let μ := finiteLawMeasure fourBlockLaw
  letI : IsProbabilityMeasure μ := finite_law_probability fourBlockLaw
  let X : Matrix (Fin 4) (Fin 1) ℝ := interceptDesign
  have hfit := fun u : Fin 4 → ℝ => intercept_fit_certificate
    (R := Fin 4) (by norm_num) fourDyads u
  have hr : (X.transpose * X).det ≠ 0 := by
    have hg := (hfit (fun _ => 0)).1
    change ((interceptDesign : Matrix (Fin 4) (Fin 1) ℝ).transpose * interceptDesign).det ≠ 0
    rw [hg]
    norm_num [Matrix.det_fin_one]
  have hmean : ∀ r : Fin 4, (∫ ω, fourBlockErrors ω r ∂μ) = 0 := by
    intro r; rw [finite_law_integral]
    exact four_block_moments.1 r
  have hcov : errorCovariance μ (fun r ω => fourBlockErrors ω r) = fourOmega := by
    ext r t
    rw [errorCovariance,finite_law_integral]
    exact four_block_moments.2 r t
  have hd : ∃ r t, ¬((fourDyads r).members ∩ (fourDyads t).members).Nonempty ∧
      errorCovariance μ (fun r ω => fourBlockErrors ω r) r t ≠ 0 := by
    refine ⟨0,2,?_⟩
    norm_num [hcov,fourDyads,fourOmega]
  intro h
  have he := h (Fin 16) μ 4 1 6 fourDyads X (0 : Fin 1 → ℝ) (fun _ => 1)
    (fun r ω => fourBlockErrors ω r) hr (fun _ => MemLp.of_discrete) hmean hd
  have hθ : (fun ω : Fin 16 => (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
      ols X (X *ᵥ (0 : Fin 1 → ℝ) + fun r => fourBlockErrors ω r)) =
      (fun ω => sampleMean (fourBlockErrors ω)) := by
    funext ω
    simp only [Matrix.mulVec_zero,zero_add]
    rw [(hfit (fourBlockErrors ω)).2.2.1]
    simp [dotProduct,Fin.sum_univ_succ]
  have hV : (fun ω : Fin 16 => quadratic (plugIn X
      (olsResidual X (X *ᵥ (0 : Fin 1 → ℝ) + fun r => fourBlockErrors ω r)) (dyPattern fourDyads))
      (fun _ : Fin 1 => (1 : ℝ))) = (fun ω => interceptDCR fourDyads (fourBlockErrors ω)) := by
    funext ω
    simp only [Matrix.mulVec_zero,zero_add]
    exact (hfit (fourBlockErrors ω)).2.2.2.2
  rw [hθ,hV,finite_law_integral,finite_law_variance] at he
  have hn := four_residual_expectation_counterexample.2.2
  linarith

/-- T1(d),(f): exact covariance eigenbasis certificates. Columns of E4
have eigenvalues 7/4,3/4,3/4,3/4. Columns of E6 have eigenvalues
1/4,1/4,1,3/2,3/2,3/2. Explicit inverses certify completeness/multiplicity. -/
def fourEigenbasis : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1,1,0,1; 1,-1,0,1; -1,0,1,1; -1,0,-1,1]
/-- T1(d): eigenvalues "7/4 and 3/4 (three times)"; explicit inverse of the displayed eigenbasis certifies multiplicities. -/
def fourEigenbasisInv : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1/4,1/4,-1/4,-1/4; 1/2,-1/2,0,0; 0,0,1/2,-1/2; 1/4,1/4,1/4,1/4]
/-- T1(f): eigenvalues "1/4 (twice), 1 (once), 3/2 (three times)"; columns give a complete exact eigenbasis. -/
def sixEigenbasis : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1,1,1,1,0,0; -1,0,1,0,1,0; 0,-1,1,0,0,1;
    0,-1,1,0,0,-1; -1,0,1,0,-1,0; 1,1,1,-1,0,0]
/-- T1(f): eigenvalues "1/4 (twice), 1 (once), 3/2 (three times)"; explicit inverse certifies completeness of sixEigenbasis. -/
def sixEigenbasisInv : Matrix (Fin 6) (Fin 6) ℝ :=
  !![1/6,-2/6,1/6,1/6,-2/6,1/6; 1/6,1/6,-2/6,-2/6,1/6,1/6;
    1/6,1/6,1/6,1/6,1/6,1/6; 1/2,0,0,0,0,-1/2;
    0,1/2,0,0,-1/2,0; 0,0,1/2,-1/2,0,0]

/-- T1(d),(f): full invertible eigenbases prove the exact spectra and
multiplicities without expanding a six-dimensional determinant polynomial. -/
theorem block_eigenbasis_certificates :
    fourEigenbasisInv*fourEigenbasis = 1 ∧
    fourOmega*fourEigenbasis = fourEigenbasis*Matrix.diagonal ![7/4,3/4,3/4,3/4] ∧
    sixEigenbasisInv*sixEigenbasis = 1 ∧
    sixOmega*sixEigenbasis = sixEigenbasis*Matrix.diagonal ![1/4,1/4,1,3/2,3/2,3/2] := by
  refine ⟨?_,?_,?_,?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fourEigenbasisInv,fourEigenbasis,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [fourOmega,fourEigenbasis,Matrix.mul_apply,Matrix.diagonal_apply,Fin.sum_univ_succ]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [sixEigenbasisInv,sixEigenbasis,Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [sixOmega,sixEigenbasis,Matrix.mul_apply,Matrix.diagonal_apply,Fin.sum_univ_succ]

/-- T2(v): exogenous positive-definite models with genuine omitted
covariance have either sign of Δ. Even entrywise positive omitted covariance
can have negative coefficient-specific contribution in a slope contrast. -/
theorem omitted_sign_not_determined :
    omittedContribution disjointDyads (pairOmega (-1)) ![1/2,1/2] = -1/4 ∧
    omittedContribution disjointDyads (pairOmega 1) ![1/2,1/2] = 1/4 ∧
    omittedContribution disjointDyads (pairOmega 1) ![-1/2,1/2] = -1/4 ∧
    pairOmega 1 0 1 > 0 ∧ pairOmega 1 1 0 > 0 := by
  norm_num [omittedContribution,disjointDyads,pairOmega,Fin.sum_univ_succ]

/-- T4(iii): the α=1 erroneous id subtraction equals DCR minus the
ordered within-id cross-record products scaled by N−2. -/
theorem id_substitution_cross_discrepancy {G : Type*} [DecidableEq G]
    (d : R → Dyad M) (z : R → P → ℝ) (g : R → G) :
    (∑ i, scoreSandwich (memberPattern d i) z)-scoreSandwich (repeatPattern d) z-
      ((Fintype.card M : ℝ)-2) • scoreSandwich (idPattern g) z =
    scoreSandwich (dyPattern d) z-
      ((Fintype.card M : ℝ)-2) • scoreSandwich (offIdPattern g) z := by
  have he := id_substitution_discrepancy d z (scoreSandwich (idPattern g) z) 1
  have hc := id_cross_products g z
  simp only [one_smul] at he
  rw [he,hc]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

/-- T9(ii): if all undo factors are one and the linear weights sum to
one, Rubin pooling and decomposition commute, with Q added exactly once. -/
theorem rubin_unadjusted_commutes {J : Type*} [Fintype J] {m : ℕ}
    (hm : 2 ≤ m) (s : J → ℝ) (hs : ∑ j, s j = 1)
    (U : J → Fin m → Matrix P P ℝ) (hU : ∀ j t, (U j t).transpose = U j t)
    (b : Fin m → P → ℝ) :
    pooledFirst s (fun _ => 1) U b = withinThenPool s U b := by
  have he := (rubin_pooling_gap hm s (fun _ => 1) (fun _ => by norm_num) U hU b).2.2.1
  simp only [mul_one,hs,sub_self,zero_smul] at he
  exact sub_eq_zero.mp he

/-- T5's limit reading: along full-rank centered square-integrable
fixed-design sequences with genuine non-incident covariance, any probability
limit L of Vhat/Var(c^T βhat) must satisfy L≤1. The conclusion is recorded
as a proposition, not asserted by an axiom; existence of the ratio limit is
explicit, so no extra convergence claim is attributed to the paper. Finite
record/member types are used without prescribed labels; cardinality growth
is the same n→∞ condition under finite reindexing. -/
def PrintedRatioLimitLowerBound : Prop :=
  ∀ (Ω : Type) [meas : MeasurableSpace Ω] (μ : @Measure Ω meas)
    [_prob : @IsProbabilityMeasure Ω meas μ] (p : ℕ)
    (R M : ℕ → Type) [rows : ∀ m, Fintype (R m)] [rowEq : ∀ m, DecidableEq (R m)]
    [members : ∀ m, Fintype (M m)] [memberEq : ∀ m, DecidableEq (M m)]
    (d : ∀ m, R m → Dyad (M m)) (X : ∀ m, Matrix (R m) (Fin p) ℝ) (β c : Fin p → ℝ)
    (u : ∀ m, R m → Ω → ℝ),
    Tendsto (fun m => Fintype.card (R m)) atTop atTop →
    (∀ m, ((X m).transpose * X m).det ≠ 0) →
    (∀ m r, MemLp (u m r) 2 μ) → (∀ m r, ∫ ω, u m r ω ∂μ = 0) →
    (∀ᶠ m in atTop, ∃ r s, ¬((d m r).members ∩ (d m s).members).Nonempty ∧
      errorCovariance μ (u m) r s ≠ 0) →
    (∀ᶠ m in atTop, 0 < variance (fun ω => c ⬝ᵥ ols (X m)
      (X m *ᵥ β + fun r => u m r ω)) μ) →
    ∀ L : ℝ, TendstoInMeasure μ
      (fun m ω => quadratic (plugIn (X m)
        (olsResidual (X m) (X m *ᵥ β + fun r => u m r ω)) (dyPattern (d m))) c /
          variance (fun ω => c ⬝ᵥ ols (X m) (X m *ᵥ β + fun r => u m r ω)) μ)
      atTop (fun _ => L) → L ≤ 1

/-- A small positivity lemma for the covariance certificates in T1:
any nonzero finite vector has a strictly positive sum of squared coordinates. -/
theorem sum_squares_positive (h : R → ℝ) (hh : h ≠ 0) : 0 < ∑ r, (h r)^2 := by
  have hn : ∃ r, h r ≠ 0 := by
    by_contra he; push Not at he
    exact hh (funext he)
  obtain ⟨r,hr⟩ := hn
  exact Finset.sum_pos' (fun i _ => sq_nonneg (h i))
    ⟨r,Finset.mem_univ r,sq_pos_of_ne_zero hr⟩

/-- T1(d),(f): both nontrivial block covariance matrices are positive
definite. The proof uses explicit sum-of-squares certificates with a strictly
positive own-error contribution, so no PSD hypothesis is assumed. -/
theorem block_covariances_positive_definite : fourOmega.PosDef ∧ sixOmega.PosDef := by
  constructor
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.IsHermitian.ext
      intro i j; fin_cases i <;> fin_cases j <;> norm_num [fourOmega]
    · intro h hh
      simp only [star_trivial,← quadratic_eq_dot,four_omega_square_certificate]
      have hs := sum_squares_positive h hh
      positivity
  · apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · apply Matrix.IsHermitian.ext
      intro i j; fin_cases i <;> fin_cases j <;> norm_num [sixOmega]
    · intro h hh
      simp only [star_trivial,← quadratic_eq_dot,six_omega_square_certificate]
      have hs := sum_squares_positive h hh
      positivity

/-- T3(a): the exact Breslow risk sets from the supplied intervals,
in zero-based record numbering. This checks the counting-process convention. -/
theorem cox_exact_risk_sets :
    (Finset.univ.filter (fun r : Fin 10 => coxRisk r 1)) = {0,1,2,4,6,8} ∧
    (Finset.univ.filter (fun r : Fin 10 => coxRisk r 2)) = {3,5,7,9} := by decide

/-- T3(b): efficient record scores summed within each of the six subjects. -/
theorem cox_subject_score_totals :
    (fun k : Fin 6 => ∑ r, if (coxRecords r).id = k then coxScores r else 0) =
      ![2/3,-2/3,7/6,-7/6,-5/6,5/6] := by
  ext k; fin_cases k <;> norm_num [coxRecords,coxScores,Fin.sum_univ_succ]

/-- T3(c): in this constructed survival sample, subjects and repeated
dyads define the same record partition. It is not asserted for survival
samples in general. -/
theorem cox_id_is_repeated_dyad :
    idPattern (fun r => (coxRecords r).id) = repeatPattern (fun r => (coxRecords r).dyad) := by
  have hp : ∀ r t : Fin 10, (coxRecords r).id = (coxRecords t).id ↔
      ((coxRecords r).dyad).members = ((coxRecords t).dyad).members := by decide
  ext r t
  simp only [idPattern,repeatPattern,hp]

/-- T6(b): for the ten distinct dyads, repeated-dyad clustering equals
the record component; thus the general p. 191 decomposition gives
M=Σ_m C_m−H−(5−2)H, with H exactly the record meat. -/
theorem ten_meat_decomposition :
    (∑ m : Fin 5, scoreSandwich (memberPattern tenDyads m) tenScore)-
      scoreSandwich recordPattern tenScore-
      (3 : ℝ) • scoreSandwich recordPattern tenScore = tenMeat := by
  have hp : repeatPattern tenDyads = recordPattern := by
    have hu : ∀ r t : Fin 10, (tenDyads r).members = (tenDyads t).members ↔ r = t := by decide
    ext r t
    simp only [repeatPattern,recordPattern,hu]
  have he := corrected_decomposition tenDyads tenScore
  rw [hp] at he
  norm_num [tenMeat] at he ⊢
  exact he

/-- T8(b): each member's partition has 12 incident records in its one
common cluster and 12 outsider singletons; there are 24 records total. -/
theorem mi_partition_counts :
    Fintype.card (Fin 6 × Fin 4) = 24 ∧
    (∀ i : Fin 4, (Finset.univ.filter
      (fun r : Fin 6 × Fin 4 => i ∈ (sixDyads r.1).members)).card = 12) := by decide

/-- T10(i): the integer rounding certificate is equivalent to the
literal rational tolerance |k/n−printed_share|≤1/2000. This certifies the
conversion used by the integer recovery proof, with n>0 explicit. -/
theorem rounding_consistent_iff_rational (row : StudyRow) (hn : 0 < row.n) (k : ℕ) :
    roundingConsistent row k ↔
      |(k : ℚ)/(row.n : ℚ)-(row.lossMilli : ℚ)/1000| ≤ (1/2000 : ℚ) := by
  have hp : 0 < (row.n : ℚ) := by exact_mod_cast hn
  have hd : 0 < 2000*(row.n : ℚ) := by positivity
  have he : (k : ℚ)/(row.n : ℚ)-(row.lossMilli : ℚ)/1000 =
      (2000*(k : ℚ)-2*(row.n : ℚ)*(row.lossMilli : ℚ))/(2000*(row.n : ℚ)) := by
    field_simp; ring
  rw [he,abs_div,abs_of_pos hd,div_le_iff₀ hd]
  have hc : (1/2000 : ℚ)*(2000*(row.n : ℚ)) = (row.n : ℚ) := by ring
  rw [hc]
  unfold roundingConsistent
  norm_cast

/-- T10(i), literally on the printed rational shares: every row has
exactly the target's recovered feasible integer numerator within 0.0005. -/
theorem study_unique_rational_recovery :
    ∀ i : Fin 22, ∀ k : ℕ,
      (k ≤ (studies i).n ∧
        |(k : ℚ)/((studies i).n : ℚ)-((studies i).lossMilli : ℚ)/1000| ≤ (1/2000 : ℚ)) ↔
      k = (studies i).loss := by
  have hp : ∀ i : Fin 22, 0 < (studies i).n := by decide
  intro i k
  rw [← rounding_consistent_iff_rational (studies i) (hp i) k]
  exact study_unique_integer_recovery i k

/-- Finite-support version of T2(i), used to certify T1(a)–(c): the
sampling variance of the actual OLS contrast equals its sandwich value
under the explicitly realized centered error covariance. -/
theorem finite_ols_variance {S : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (law : FiniteLaw S) (X : Matrix R P ℝ)
    (hrank : (X.transpose * X).det ≠ 0) (β c : P → ℝ) (u : R → S → ℝ)
    (hmean : ∀ r, finiteExpectation law (u r) = 0) (A : Matrix R R ℝ)
    (hmoment : ∀ r t, finiteExpectation law (fun ω => u r ω*u t ω) = A r t) :
    finiteVariance law (fun ω => c ⬝ᵥ ols X (X *ᵥ β+fun r => u r ω)) =
      quadratic A (X *ᵥ (bread X *ᵥ c)) := by
  let μ := finiteLawMeasure law
  letI : IsProbabilityMeasure μ := finite_law_probability law
  have hm : ∀ r, (∫ ω, u r ω ∂μ) = 0 := by
    intro r; rw [finite_law_integral]; exact hmean r
  have hA : errorCovariance μ u = A := by
    ext r t; rw [errorCovariance,finite_law_integral]; exact hmoment r t
  have he := (ols_contrast_variance μ X hrank β c u (fun _ => MemLp.of_discrete) hm).1
  rw [finite_law_variance,hA] at he
  exact he

/-- T1(a)–(c): explicit bounded centered models, positive-definite
covariance, full-rank designs and the ACTUAL OLS sampling variances 1/4,
1/4,3/4. Combined with the dyadic values 1/2 in the two numerical
certificates, these are complete population counterexamples and sign control. -/
theorem bounded_pair_sampling_models :
    (∀ ω r, |pairErrors ω r| ≤ 1) ∧
    (pairOmega (-1)).PosDef ∧ (pairOmega 1).PosDef ∧
    (pairInterceptDesign.transpose*pairInterceptDesign).det ≠ 0 ∧
    (pairSlopeDesign.transpose*pairSlopeDesign).det ≠ 0 ∧
    finiteVariance negativePairLaw (fun ω => (ols pairInterceptDesign (pairErrors ω)) 0) = 1/4 ∧
    finiteVariance positivePairLaw (fun ω => (ols pairSlopeDesign (pairErrors ω)) 0) = 1/4 ∧
    finiteVariance positivePairLaw (fun ω => (ols pairInterceptDesign (pairErrors ω)) 0) = 3/4 := by
  have hp : ∀ sign, sign = -1 ∨ sign = 1 → (pairOmega sign).PosDef := by
    intro sign hsign
    rcases pair_omega_positive_definite sign hsign with ⟨hs,hn⟩
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]; exact hs
    · intro v hv; simpa only [star_trivial,← quadratic_eq_dot] using hn v hv
  rcases intercept_counterexample with ⟨hrI,hhI,htI,hdI,_⟩
  rcases slope_and_sign_control with ⟨hrS,hhS,htS,hdS,htC,_⟩
  rcases pair_error_moments with ⟨hmI,hAI,hmP,hAP⟩
  refine ⟨?_,hp (-1) (Or.inl rfl),hp 1 (Or.inr rfl),hrI,hrS,?_,?_,?_⟩
  · intro ω r; fin_cases ω <;> fin_cases r <;> norm_num [pairErrors]
  · have he := finite_ols_variance negativePairLaw pairInterceptDesign hrI
      (0 : Fin 1 → ℝ) (fun _ => 1) (fun r ω => pairErrors ω r) hmI (pairOmega (-1)) hAI
    simp only [Matrix.mulVec_zero,zero_add,dotProduct,Fin.sum_univ_one,mul_one,one_mul,add_zero] at he
    rw [htI] at he; exact he
  · have he := finite_ols_variance positivePairLaw pairSlopeDesign hrS
      (0 : Fin 1 → ℝ) (fun _ => 1) (fun r ω => pairErrors ω r) hmP (pairOmega 1) hAP
    simp only [Matrix.mulVec_zero,zero_add,dotProduct,Fin.sum_univ_one,mul_one,one_mul,add_zero] at he
    rw [htS] at he; exact he
  · have he := finite_ols_variance positivePairLaw pairInterceptDesign hrI
      (0 : Fin 1 → ℝ) (fun _ => 1) (fun r ω => pairErrors ω r) hmP (pairOmega 1) hAP
    simp only [Matrix.mulVec_zero,zero_add,dotProduct,Fin.sum_univ_one,mul_one,one_mul,add_zero] at he
    rw [hhI,htC] at he; exact he

/-- Finite lemma for T1(e),(f): lifting member labels to disjoint blocks
retains incidence exactly within the same block. -/
theorem lifted_intersection {m : ℕ} (b c : Fin m) (a d : Dyad M) :
    ((liftDyad b a).members ∩ (liftDyad c d).members).Nonempty ↔
      b = c ∧ (a.members ∩ d.members).Nonempty := by
  constructor
  · rintro ⟨⟨e,i⟩,hi⟩
    rcases Finset.mem_map.mp (Finset.mem_inter.mp hi).1 with ⟨j,hj,hje⟩
    rcases Finset.mem_map.mp (Finset.mem_inter.mp hi).2 with ⟨k,hk,hke⟩
    have hb : b = e := congrArg Prod.fst hje
    have hc : c = e := congrArg Prod.fst hke
    have hji : j = i := congrArg Prod.snd hje
    have hki : k = i := congrArg Prod.snd hke
    refine ⟨hb.trans hc.symm,i,Finset.mem_inter.mpr ⟨?_,?_⟩⟩
    · simpa [← hji] using hj
    · simpa [← hki] using hk
  · rintro ⟨rfl,i,hi⟩
    refine ⟨(b,i),Finset.mem_inter.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_map.mpr ⟨i,(Finset.mem_inter.mp hi).1,rfl⟩
    · exact Finset.mem_map.mpr ⟨i,(Finset.mem_inter.mp hi).2,rfl⟩

/-- Finite lemma for T1(e),(f): the replicated incidence matrix is
block diagonal, with each diagonal block equal to the original mask. -/
theorem replicated_pattern {m : ℕ} (d : R → Dyad M) (r s : Fin m × R) :
    dyPattern (fun t : Fin m × R => liftDyad t.1 (d t.2)) r s =
      if r.1 = s.1 then dyPattern d r.2 s.2 else 0 := by
  simp only [dyPattern,lifted_intersection]
  by_cases h : r.1 = s.1 <;> simp [h]

/-- Finite lemma for T1(e),(f): replication preserves the number q of
retained entries in every incidence row. -/
theorem replicated_row_sum {m : ℕ} (d : R → Dyad M) (q : ℝ)
    (hrow : ∀ r, ∑ s, dyPattern d r s = q) (r : Fin m × R) :
    ∑ s, dyPattern (fun t : Fin m × R => liftDyad t.1 (d t.2)) r s = q := by
  simp only [Fintype.sum_prod_type,replicated_pattern]
  simp [Finset.sum_ite_irrel,hrow]

/-- Finite lemma for T1(e),(f): the uncentered replicated quadratic
form is exactly the sum of the corresponding block quadratic forms. -/
theorem replicated_quadratic {m : ℕ} (d : R → Dyad M) (u : Fin m × R → ℝ) :
    quadratic (fun r s => dyPattern (fun t : Fin m × R => liftDyad t.1 (d t.2)) r s) u =
      ∑ b : Fin m, quadratic (fun r s => dyPattern d r s) (fun r => u (b,r)) := by
  simp only [quadratic,Fintype.sum_prod_type,replicated_pattern,mul_ite,mul_zero]
  simp [Finset.sum_ite_irrel]

/-- T1(e), the exact finite residual identity for every replicated
sample: n² Vhat=Σ pair-sums²−8m ubar². No distributional premise is needed. -/
theorem four_replicated_centering {Ω : Type*} (block : ℕ → Ω → Fin 16)
    (m : ℕ) (hm : 1 ≤ m) (ω : Ω) :
    (4*(m : ℝ))^2 * interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) =
      (∑ b : Fin m, ∑ pair : Fin 2, (fourPairSum block b.val ω pair)^2) -
        8*(m : ℝ)*(sampleMean (fourSequenceErrors block m ω))^2 := by
  have hr : ∀ r : Fin 4, ∑ s, dyPattern fourDyads r s = (2 : ℝ) := by
    intro r; fin_cases r <;> simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] <;> norm_num [dyPattern,fourDyads]
  have hn : (Fintype.card (Fin m × Fin 4) : ℝ) ≠ 0 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    exact mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0)) (by norm_num)
  have he := intercept_dcr_centering (replicatedFourDyads m) 2
    (replicated_row_sum fourDyads 2 hr) hn (fourSequenceErrors block m ω)
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at he
  have hq := replicated_quadratic fourDyads (fourSequenceErrors block m ω)
  have hf : ((m : ℝ)*4)^2 * interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) =
      (∑ b : Fin m, quadratic (fun r s => dyPattern fourDyads r s)
        (fun r => fourSequenceErrors block m ω (b,r))) -
        2*((m : ℝ)*4)*(sampleMean (fourSequenceErrors block m ω))^2 :=
    he.trans (congrArg (fun v : ℝ => v-2*((m : ℝ)*4)*(sampleMean (fourSequenceErrors block m ω))^2) hq)
  have hp : (∑ b : Fin m, quadratic (fun r s => dyPattern fourDyads r s)
      (fun r => fourSequenceErrors block m ω (b,r))) =
      ∑ b : Fin m, ∑ pair : Fin 2, (fourPairSum block b.val ω pair)^2 := by
    apply Finset.sum_congr rfl
    intro b _
    simp [quadratic,dyPattern,fourDyads,fourSequenceErrors,fourPairSum,Fin.sum_univ_succ]
    ring
  rw [hp] at hf
  convert hf using 1 <;> ring

/-- T1(f), the exact finite residual identity for all m blocks:
n Vhat=(Σ_b q_b)/n−5ubar². This is proved without a probability limit. -/
theorem six_replicated_centering {Ω : Type*} (block : ℕ → Ω → (Fin 13 → Fin 2))
    (m : ℕ) (hm : 1 ≤ m) (ω : Ω) :
    (6*(m : ℝ))*interceptDCR (replicatedSixDyads m) (sixSequenceErrors block m ω) =
      (∑ b : Fin m, sixBlockQ (block b.val ω))/(6*(m : ℝ)) -
        5*(sampleMean (sixSequenceErrors block m ω))^2 := by
  have hr : ∀ r : Fin 6, ∑ s, dyPattern sixDyads r s = (5 : ℝ) := by
    intro r; fin_cases r <;> simp only [Fin.sum_univ_succ,Fin.sum_univ_zero] <;> norm_num [dyPattern,sixDyads]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hn : (Fintype.card (Fin m × Fin 6) : ℝ) ≠ 0 := by
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    exact mul_ne_zero hm0 (by norm_num)
  have he := intercept_dcr_centering (replicatedSixDyads m) 5
    (replicated_row_sum sixDyads 5 hr) hn (sixSequenceErrors block m ω)
  simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat] at he
  have hq := replicated_quadratic sixDyads (sixSequenceErrors block m ω)
  have hf := he.trans (congrArg (fun v : ℝ => v-5*((m : ℝ)*6)*(sampleMean (sixSequenceErrors block m ω))^2) hq)
  change ((m : ℝ)*6)^2 * interceptDCR (replicatedSixDyads m) (sixSequenceErrors block m ω) =
    (∑ b : Fin m, sixBlockQ (block b.val ω)) -
      5*((m : ℝ)*6)*(sampleMean (sixSequenceErrors block m ω))^2 at hf
  field_simp [hm0]
  nlinarith [hf]

/-- Finite-law transfer for T1: the explicit atom probabilities
identify the whole distribution of any measurable finite-valued block. -/
theorem finite_law_map {S Ω : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [MeasurableSpace Ω] (law : FiniteLaw S)
    (μ : Measure Ω) (f : Ω → S) (hf : Measurable f)
    (hlaw : ∀ a, μ {ω | f ω = a} = ENNReal.ofReal (law.weight a)) :
    μ.map f = finiteLawMeasure law := by
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply hf (measurableSet_singleton a)]
  change μ {ω | f ω = a} = (finiteLawMeasure law) {a}
  rw [hlaw]
  simp [finiteLawMeasure,Measure.finsetSum_apply,Measure.smul_apply,
    Measure.dirac_apply',smul_eq_mul,Pi.single_apply]

/-- Finite-law transfer for T1: integrating any statistic of a block
with the given atom probabilities equals its certified finite expectation. -/
theorem finite_law_composed_integral {S Ω : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [MeasurableSpace Ω] (law : FiniteLaw S)
    (μ : Measure Ω) (f : Ω → S) (hf : Measurable f)
    (hlaw : ∀ a, μ {ω | f ω = a} = ENNReal.ofReal (law.weight a)) (g : S → ℝ) :
    (∫ ω, g (f ω) ∂μ) = finiteExpectation law g := by
  rw [← integral_map hf.aemeasurable (measurable_of_countable g).aestronglyMeasurable,
    finite_law_map law μ f hf hlaw,finite_law_integral]


/-- T7(iv), finite lemma: an eigenbasis with exactly one positive
coefficient clips to that coefficient times its column outer product. -/
theorem spectral_clip_one_positive (Q : Matrix P P ℝ) (eigs : P → ℝ) (j : P)
    (hp : 0 < eigs j) (hn : ∀ i, i ≠ j → eigs i ≤ 0) :
    spectralClip Q eigs = eigs j • Matrix.vecMulVec (fun r => Q r j) (fun r => Q r j) := by
  ext r s
  change ((Q * Matrix.diagonal (fun i => max (eigs i) 0)) * Q.transpose) r s =
    (eigs j • Matrix.vecMulVec (fun r => Q r j) (fun r => Q r j)) r s
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal,Matrix.transpose_apply,
    Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [max_eq_left hp.le]; ring
  · intro i _ hij
    rw [max_eq_right (hn i hij)]
    ring
  · simp

/-- T7(iv), finite lemma: when exactly one canonical eigenvalue is
positive, the spectral positive part is a PSD rank-one eigenvector product. -/
theorem positive_part_one_positive (V : Matrix P P ℝ) (hV : V.IsHermitian) (j : P)
    (hp : 0 < hV.eigenvalues j) (hn : ∀ i, i ≠ j → hV.eigenvalues i ≤ 0) :
    (∃ q : P → ℝ, q ⬝ᵥ q = 1 ∧ V *ᵥ q = hV.eigenvalues j • q ∧
      positivePart V hV = hV.eigenvalues j • Matrix.vecMulVec q q) ∧
    (positivePart V hV).rank = 1 := by
  let Q : Matrix P P ℝ := hV.eigenvectorUnitary
  let q : P → ℝ := fun r => Q r j
  have ho : Q.transpose * Q = 1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hV.eigenvectorUnitary
  have hqd : Q.det ≠ 0 := Matrix.det_ne_zero_of_left_inverse ho
  have htd : Q.transpose.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hq : q ⬝ᵥ q = 1 := by
    have he := congrArg (fun A : Matrix P P ℝ => A j j) ho
    simpa [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply,dotProduct,q] using he
  have hfit : V *ᵥ q = hV.eigenvalues j • q := by
    simpa only [q,Q,Matrix.IsHermitian.eigenvectorUnitary_apply]
      using hV.mulVec_eigenvectorBasis j
  refine ⟨⟨q,hq,hfit,spectral_clip_one_positive Q hV.eigenvalues j hp hn⟩,?_⟩
  change (Q * Matrix.diagonal (fun i => max (hV.eigenvalues i) 0) * Q.transpose).rank = 1
  rw [Matrix.rank_mul_eq_left_of_det_ne_zero Q.transpose _ htd,
    Matrix.rank_mul_eq_right_of_det_ne_zero Q _ hqd,Matrix.rank_diagonal]
  have he : ∀ i, max (hV.eigenvalues i) 0 ≠ 0 ↔ i = j := by
    intro i
    by_cases hi : i = j
    · subst i
      simp [max_eq_left hp.le,ne_of_gt hp]
    · simp [max_eq_right (hn i hi),hi]
  simp_rw [he]
  exact Fintype.card_subtype_eq j

/-- T7(iv), exact signs: the negative determinant makes the displayed
square-root term strictly larger than the positive trace. -/
theorem ten_eigenvalue_signs : tenEigenMinus < 0 ∧ 0 < tenEigenPlus := by
  have hτ : (0 : ℝ) ≤ 467922/3655808 := by norm_num
  have hs : (467922/3655808 : ℝ) <
      Real.sqrt ((467922/3655808 : ℝ)^2-4*(-70529/308915776)) := by
    apply (Real.lt_sqrt hτ).mpr
    norm_num
  dsimp [tenEigenMinus,tenEigenPlus]
  constructor <;> linarith

/-- T7(iv), exact eigenvalue identification: the two canonical
spectral values are precisely the displayed roots, in either order. -/
theorem ten_eigenvalues_identified (hV : tenVariance.IsHermitian) :
    (hV.eigenvalues 0 = tenEigenPlus ∧ hV.eigenvalues 1 = tenEigenMinus) ∨
    (hV.eigenvalues 1 = tenEigenPlus ∧ hV.eigenvalues 0 = tenEigenMinus) := by
  have hv := ten_variance_certificate.2.2
  have htrace : tenVariance.trace = (467922/3655808 : ℝ) := by
    norm_num [Matrix.trace,Fin.sum_univ_succ,hv,Matrix.smul_apply,smul_eq_mul]
  have ht : hV.eigenvalues 0+hV.eigenvalues 1 = (467922/3655808 : ℝ) := by
    have he := hV.trace_eq_sum_eigenvalues
    rw [htrace] at he
    simpa [Fin.sum_univ_succ] using he.symm
  have hd : hV.eigenvalues 0*hV.eigenvalues 1 = (-70529/308915776 : ℝ) := by
    have he := hV.det_eq_prod_eigenvalues
    rw [positive_diagonal_counterexample.2.1] at he
    simpa [Fin.prod_univ_succ] using he.symm
  have hs : (hV.eigenvalues 0-hV.eigenvalues 1)^2 =
      (467922/3655808 : ℝ)^2-4*(-70529/308915776) := by
    nlinarith [sq_nonneg (hV.eigenvalues 0+hV.eigenvalues 1-467922/3655808)]
  have hm : hV.eigenvalues 0*hV.eigenvalues 1 < 0 := by rw [hd]; norm_num
  rcases mul_neg_iff.mp hm with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · left
    have ha : 0 < hV.eigenvalues 0-hV.eigenvalues 1 := by linarith
    simp only [tenEigenPlus,tenEigenMinus,← hs,Real.sqrt_sq_eq_abs,abs_of_pos ha]
    constructor <;> linarith
  · right
    have ha : hV.eigenvalues 0-hV.eigenvalues 1 < 0 := by linarith
    simp only [tenEigenPlus,tenEigenMinus,← hs,Real.sqrt_sq_eq_abs,abs_of_neg ha]
    constructor <;> linarith

/-- T7(iv): the corrected example has one positive and one negative
eigenvalue; its positive part is a PSD rank-one outer product and differs
from the original V. The unit eigenvector is existential, as in the target. -/
theorem ten_positive_part_rank_one (hV : tenVariance.IsHermitian) :
    tenEigenMinus < 0 ∧ 0 < tenEigenPlus ∧
    (∃ q : Fin 2 → ℝ, q ⬝ᵥ q = 1 ∧ tenVariance *ᵥ q = tenEigenPlus • q ∧
      positivePart tenVariance hV = tenEigenPlus • Matrix.vecMulVec q q) ∧
    (positivePart tenVariance hV).rank = 1 ∧
    (positivePart tenVariance hV).PosSemidef ∧ positivePart tenVariance hV ≠ tenVariance := by
  rcases ten_eigenvalue_signs with ⟨hm,hp⟩
  have hc : (∃ q : Fin 2 → ℝ, q ⬝ᵥ q = 1 ∧ tenVariance *ᵥ q = tenEigenPlus • q ∧
      positivePart tenVariance hV = tenEigenPlus • Matrix.vecMulVec q q) ∧
      (positivePart tenVariance hV).rank = 1 := by
    rcases ten_eigenvalues_identified hV with ⟨h0,h1⟩ | ⟨h1,h0⟩
    · have hpos : 0 < hV.eigenvalues 0 := by rw [h0]; exact hp
      have hneg : ∀ i : Fin 2, i ≠ 0 → hV.eigenvalues i ≤ 0 := by
        intro i hi; fin_cases i
        · exact (hi rfl).elim
        · change hV.eigenvalues 1 ≤ 0
          rw [h1]; exact hm.le
      simpa only [h0] using positive_part_one_positive tenVariance hV 0 hpos hneg
    · have hpos : 0 < hV.eigenvalues 1 := by rw [h1]; exact hp
      have hneg : ∀ i : Fin 2, i ≠ 1 → hV.eigenvalues i ≤ 0 := by
        intro i hi; fin_cases i
        · change hV.eigenvalues 0 ≤ 0
          rw [h0]; exact hm.le
        · exact (hi rfl).elim
      simpa only [h1] using positive_part_one_positive tenVariance hV 1 hpos hneg
  refine ⟨hm,hp,hc.1,hc.2,positive_part_psd tenVariance hV,?_⟩
  intro he
  exact positive_diagonal_counterexample.2.2.2.1 ((positive_part_fixed_iff tenVariance hV).mp he)


/-- T1(a),(b): complete two-dimensional eigenbasis certificates for
both realized pair covariances, showing eigenvalues 1/2 and 3/2 exactly. -/
theorem pair_eigenbasis_certificate :
    pairOmega (-1) * (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.diagonal ![1/2,3/2] ∧
    pairOmega 1 * (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.diagonal ![3/2,1/2] ∧
    (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ) *
      ((1/2 : ℝ) • (!![1,1;1,-1] : Matrix (Fin 2) (Fin 2) ℝ)) = 1 := by
  refine ⟨?_,?_,?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pairOmega,Matrix.mul_apply,Matrix.diagonal,Matrix.smul_apply,
      smul_eq_mul,Matrix.one_apply,Fin.sum_univ_succ]

/-- T1(e), block statistic S: the sum of the four errors of one block. -/
def fourTotal (a : Fin 16) : ℝ := ∑ r, fourBlockErrors a r

/-- T1(e), block statistic P: the sum of squared errors of its two
incident pairs. Its expectation is 5 under the exact 16-point law. -/
def fourPairSquares (a : Fin 16) : ℝ :=
  (fourBlockErrors a 0+fourBlockErrors a 1)^2 +
  (fourBlockErrors a 2+fourBlockErrors a 3)^2

/-- T1(e), exact one-block finite lemmas: E[S]=0, Var(S)=3,
E[S²]=3 and E[P]=5 for the explicit bounded block law. -/
theorem four_block_statistics :
    finiteExpectation fourBlockLaw fourTotal = 0 ∧
    finiteVariance fourBlockLaw fourTotal = 3 ∧
    finiteExpectation fourBlockLaw (fun a => (fourTotal a)^2) = 3 ∧
    finiteExpectation fourBlockLaw fourPairSquares = 5 := by
  norm_num [finiteExpectation,finiteVariance,fourTotal,fourPairSquares,
    fourBlockLaw,fourBlockErrors,Fin.sum_univ_succ]

/-- T1, finite-law transfer: the given block and the identity on its
certified finite probability law are identically distributed. -/
theorem finite_law_identDistrib {S Ω : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [MeasurableSpace Ω] (law : FiniteLaw S)
    (μ : Measure Ω) (f : Ω → S) (hf : Measurable f)
    (hlaw : ∀ a, μ {ω | f ω = a} = ENNReal.ofReal (law.weight a)) :
    IdentDistrib f id μ (finiteLawMeasure law) := by
  exact ⟨hf.aemeasurable,measurable_id.aemeasurable,by
    rw [Measure.map_id,finite_law_map law μ f hf hlaw]⟩

/-- T1, finite-law transfer: every real statistic of the exact finite
block law is square integrable under its realized sampling law. -/
theorem finite_law_composed_memLp {S Ω : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [MeasurableSpace Ω] (law : FiniteLaw S)
    (μ : Measure Ω) (f : Ω → S) (hf : Measurable f)
    (hlaw : ∀ a, μ {ω | f ω = a} = ENNReal.ofReal (law.weight a)) (g : S → ℝ) :
    MemLp (fun ω => g (f ω)) 2 μ := by
  letI : IsProbabilityMeasure (finiteLawMeasure law) := finite_law_probability law
  have he := (finite_law_identDistrib law μ f hf hlaw).comp (measurable_of_countable g)
  exact he.symm.memLp_snd (MemLp.of_discrete : MemLp g 2 (finiteLawMeasure law))

/-- T1(e),(f), iid finite lemma: the actual variance of a sum of m
independent block statistics is m times its exact one-block variance. -/
theorem iid_finite_statistic_variance {S Ω : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [MeasurableSpace Ω] (law : FiniteLaw S)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → S)
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (law.weight a))
    (m : ℕ) (g : S → ℝ) :
    variance (fun ω => ∑ b : Fin m, g (block b.val ω)) μ =
      (m : ℝ)*finiteVariance law g := by
  have hLP : ∀ b : Fin m, MemLp (fun ω => g (block b.val ω)) 2 μ := by
    intro b; exact finite_law_composed_memLp law μ _ (hmeas _) (hlaw _) g
  have hi : Set.Pairwise (Set.univ : Set (Fin m))
      (fun b c => (fun ω => g (block b.val ω)) ⟂ᵢ[μ] (fun ω => g (block c.val ω))) := by
    intro b _ c _ hbc
    exact (hind.indepFun (Fin.val_injective.ne hbc)).comp
      (measurable_of_countable g) (measurable_of_countable g)
  have he := IndepFun.variance_sum (s := Finset.univ)
    (X := fun b : Fin m => fun ω => g (block b.val ω)) (fun b _ => hLP b) (by simpa only [Finset.coe_univ] using hi)
  rw [Finset.sum_fn] at he
  rw [he]
  have hv : ∀ b : Fin m, variance (fun ω => g (block b.val ω)) μ = finiteVariance law g := by
    intro b
    have hd := (finite_law_identDistrib law μ (block b.val) (hmeas b.val) (hlaw b.val)).comp (measurable_of_countable g)
    simpa only [Function.comp_def,id_eq,finite_law_variance] using hd.variance_eq
  simp [hv]

/-- T1(e),(f), iid finite lemma: the expected sum of m block statistics
is m times the exact one-block expectation, with integrability proved. -/
theorem iid_finite_statistic_integral {S Ω : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [MeasurableSpace Ω] (law : FiniteLaw S)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → S)
    (hmeas : ∀ b, Measurable (block b))
    (hlaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (law.weight a))
    (m : ℕ) (g : S → ℝ) :
    (∫ ω, ∑ b : Fin m, g (block b.val ω) ∂μ) = (m : ℝ)*finiteExpectation law g := by
  rw [integral_finsetSum]
  · simp_rw [finite_law_composed_integral law μ _ (hmeas _) (hlaw _)]
    simp
  · intro b _
    exact (finite_law_composed_memLp law μ _ (hmeas _) (hlaw _) g).integrable (by norm_num)

/-- T1(e), exact replication moments: for every m≥1, actual intercept
OLS variance is 3/(16m) and expected residual DCR is (10m−3)/(32m²). -/
theorem four_replicated_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → Fin 16)
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (fourBlockLaw.weight a))
    (m : ℕ) (hm : 1 ≤ m) :
    variance (fun ω => sampleMean (fourSequenceErrors block m ω)) μ = 3/(16*(m : ℝ)) ∧
    (∫ ω, interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) ∂μ) =
      (10*(m : ℝ)-3)/(32*(m : ℝ)^2) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hμ : (fun ω => sampleMean (fourSequenceErrors block m ω)) =
      (fun ω => (4*(m : ℝ))⁻¹ * ∑ b : Fin m, fourTotal (block b.val ω)) := by
    funext ω
    simp [sampleMean,Fintype.card_prod,Fintype.sum_prod_type,fourSequenceErrors,fourTotal,mul_comm]
  have hLPb : ∀ b : Fin m, MemLp (fun ω => fourTotal (block b.val ω)) 2 μ := by
    intro b; exact finite_law_composed_memLp fourBlockLaw μ _ (hmeas _) (hlaw _) fourTotal
  have hLPsum : MemLp (fun ω => ∑ b : Fin m, fourTotal (block b.val ω)) 2 μ :=
    memLp_finsetSum _ (fun b _ => hLPb b)
  have hLPmean : MemLp (fun ω => sampleMean (fourSequenceErrors block m ω)) 2 μ := by
    rw [hμ]; exact hLPsum.const_mul _
  have hmean : (∫ ω, sampleMean (fourSequenceErrors block m ω) ∂μ) = 0 := by
    rw [hμ,integral_const_mul,iid_finite_statistic_integral fourBlockLaw μ block hmeas hlaw,
      four_block_statistics.1]
    ring
  have hv : variance (fun ω => sampleMean (fourSequenceErrors block m ω)) μ =
      3/(16*(m : ℝ)) := by
    rw [hμ,variance_const_mul,iid_finite_statistic_variance fourBlockLaw μ block hmeas hind hlaw,
      four_block_statistics.2.1]
    field_simp; ring
  have hsq : (∫ ω, (sampleMean (fourSequenceErrors block m ω))^2 ∂μ) = 3/(16*(m : ℝ)) := by
    rw [variance_eq_integral hLPmean.aemeasurable,hmean] at hv
    simpa using hv
  have hPs : (fun ω => ∑ b : Fin m, ∑ pair : Fin 2, (fourPairSum block b.val ω pair)^2) =
      (fun ω => ∑ b : Fin m, fourPairSquares (block b.val ω)) := by
    funext ω
    apply Finset.sum_congr rfl
    intro b _
    simp [fourPairSum,fourPairSquares,Fin.sum_univ_succ]
  have hPint : Integrable (fun ω => ∑ b : Fin m, fourPairSquares (block b.val ω)) μ := by
    apply integrable_finsetSum
    intro b _
    exact (finite_law_composed_memLp fourBlockLaw μ _ (hmeas _) (hlaw _) fourPairSquares).integrable (by norm_num)
  have he := congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ)
    (funext (four_replicated_centering block m hm))
  have hPs' := fun ω => congrFun hPs ω
  simp_rw [hPs'] at he
  rw [integral_const_mul,integral_sub hPint (hLPmean.integrable_sq.const_mul _),
    integral_const_mul,iid_finite_statistic_integral fourBlockLaw μ block hmeas hlaw,
    four_block_statistics.2.2.2,hsq] at he
  refine ⟨hv,?_⟩
  apply (mul_left_cancel₀ (show (4*(m : ℝ))^2 ≠ 0 from
    pow_ne_zero 2 (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hm0)))
  rw [he]
  field_simp
  ring


/-- T1(e), all exact finite identities: with independent bounded blocks
of the EXPLICIT law (d), n² Vhat=Σ pair-sums²−8m ubar², Var(βhat)=3/(16m),
E[Vhat]=(10m−3)/(32m²), with exact positive gap (4m−3)/(32m²).
Neither the distribution nor the required expectation is assumed as a conclusion. -/
theorem four_replicated_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → Fin 16)
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (fourBlockLaw.weight a))
    (m : ℕ) (hm : 1 ≤ m) :
    (∀ ω, (4*(m : ℝ))^2 * interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) =
      (∑ b : Fin m, ∑ pair : Fin 2, (fourPairSum block b.val ω pair)^2) -
        8*(m : ℝ)*(sampleMean (fourSequenceErrors block m ω))^2) ∧
    variance (fun ω => sampleMean (fourSequenceErrors block m ω)) μ = 3/(16*(m : ℝ)) ∧
    (∫ ω, interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) ∂μ) =
      (10*(m : ℝ)-3)/(32*(m : ℝ)^2) ∧
    (∫ ω, interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) ∂μ) -
      variance (fun ω => sampleMean (fourSequenceErrors block m ω)) μ =
      (4*(m : ℝ)-3)/(32*(m : ℝ)^2) ∧
    variance (fun ω => sampleMean (fourSequenceErrors block m ω)) μ <
      (∫ ω, interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) ∂μ) := by
  rcases four_replicated_moments μ block hmeas hind hlaw m hm with ⟨hv,he⟩
  have hg := four_expected_gap_arithmetic m hm
  refine ⟨four_replicated_centering block m hm,hv,he,?_,?_⟩
  · rw [he,hv]; exact hg.1
  · rw [he,hv]
    linarith [hg.1,hg.2]


/-- T1(e),(f), limit lemma: independent measurable blocks with the
exact finite law obey the strong law for every real block statistic. -/
theorem iid_finite_statistic_strong_law {S Ω : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [MeasurableSpace Ω] (law : FiniteLaw S)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → S)
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (law.weight a)) (g : S → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun m : ℕ => (∑ b : Fin m, g (block b.val ω))/(m : ℝ))
      atTop (nhds (finiteExpectation law g)) := by
  have hLP := finite_law_composed_memLp law μ _ (hmeas 0) (hlaw 0) g
  have hi : Pairwise (fun b c : ℕ => (fun ω => g (block b ω)) ⟂ᵢ[μ] (fun ω => g (block c ω))) := by
    intro b c hbc
    exact (hind.indepFun hbc).comp (measurable_of_countable g) (measurable_of_countable g)
  have hd : ∀ b, IdentDistrib (fun ω => g (block b ω)) (fun ω => g (block 0 ω)) μ μ := by
    intro b
    have hb := (finite_law_identDistrib law μ _ (hmeas b) (hlaw b)).comp (measurable_of_countable g)
    have h0 := (finite_law_identDistrib law μ _ (hmeas 0) (hlaw 0)).comp (measurable_of_countable g)
    exact hb.trans h0.symm
  have he := strong_law_ae_real (fun b ω => g (block b ω))
    (hLP.integrable (by norm_num)) hi hd
  rw [finite_law_composed_integral law μ _ (hmeas 0) (hlaw 0)] at he
  simpa only [Finset.sum_range] using he

/-- T1(e), exact finite ratio representation: the estimator/sampling
variance ratio is the block average P divided by 3, minus 8ubar²/3. -/
theorem four_replicated_ratio_formula {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → Fin 16)
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (fourBlockLaw.weight a))
    (m : ℕ) (ω : Ω) :
    interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) /
      variance (fun ω => sampleMean (fourSequenceErrors block m ω)) μ =
      ((∑ b : Fin m, fourPairSquares (block b.val ω))/(m : ℝ))/3-
        (8/3 : ℝ)*(sampleMean (fourSequenceErrors block m ω))^2 := by
  by_cases hm : m = 0
  · subst m
    simp [interceptDCR,sampleMean,Fintype.card_prod,quadratic,Fintype.sum_prod_type]
  · have hm' : 1 ≤ m := by omega
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    rw [(four_replicated_moments μ block hmeas hind hlaw m hm').1]
    have hc := four_replicated_centering block m hm' ω
    have hp : ∀ b : Fin m, (∑ pair : Fin 2, (fourPairSum block b.val ω pair)^2) =
        fourPairSquares (block b.val ω) := by
      intro b; simp [fourPairSum,fourPairSquares,Fin.sum_univ_succ]
    simp_rw [hp] at hc
    field_simp [hm0]
    nlinarith [hc]

/-- T1(e), almost-sure finite-law reduction: the actual residual-DCR
ratio converges to 5/3 by the proved strong law applied to P and S. -/
theorem four_replicated_ratio_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → Fin 16)
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (fourBlockLaw.weight a)) :
    ∀ᵐ ω ∂μ, Tendsto (fun m : ℕ =>
      interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) /
        variance (fun ω => sampleMean (fourSequenceErrors block m ω)) μ)
      atTop (nhds (5/3 : ℝ)) := by
  have hT := iid_finite_statistic_strong_law fourBlockLaw μ block hmeas hind hlaw fourTotal
  have hP := iid_finite_statistic_strong_law fourBlockLaw μ block hmeas hind hlaw fourPairSquares
  rw [four_block_statistics.1] at hT
  rw [four_block_statistics.2.2.2] at hP
  filter_upwards [hT,hP] with ω hTω hPω
  have hmean : Tendsto (fun m : ℕ => sampleMean (fourSequenceErrors block m ω)) atTop (nhds (0 : ℝ)) := by
    have he := hTω.div_const (4 : ℝ)
    convert he using 1
    · funext m
      simp [sampleMean,Fintype.card_prod,Fintype.sum_prod_type,fourSequenceErrors,fourTotal,
        div_eq_mul_inv,mul_inv]
      ring
    · norm_num
  have he := (hPω.div_const (3 : ℝ)).sub ((hmean.pow 2).const_mul (8/3 : ℝ))
  convert he using 1
  · funext m
    exact four_replicated_ratio_formula μ block hmeas hind hlaw m ω
  · norm_num


/-- T1(e), asymptotic limit: the actual estimator divided
by the actual sampling variance tends to 5/3 IN PROBABILITY. The errors
remain bounded, exogenous, iid by blocks on disjoint member sets. -/
theorem four_replicated_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → Fin 16)
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (fourBlockLaw.weight a)) :
    TendstoInMeasure μ
      (fun m ω => interceptDCR (replicatedFourDyads m) (fourSequenceErrors block m ω) /
        variance (fun ω => sampleMean (fourSequenceErrors block m ω)) μ)
      atTop (fun _ => (5/3 : ℝ)) := by
  apply tendstoInMeasure_of_tendsto_ae
  · intro m
    have hLPp : MemLp (fun ω => ∑ b : Fin m, fourPairSquares (block b.val ω)) 2 μ :=
      memLp_finsetSum _ (fun b _ => finite_law_composed_memLp fourBlockLaw μ _ (hmeas _) (hlaw _) fourPairSquares)
    have hLPt : MemLp (fun ω => ∑ b : Fin m, fourTotal (block b.val ω)) 2 μ :=
      memLp_finsetSum _ (fun b _ => finite_law_composed_memLp fourBlockLaw μ _ (hmeas _) (hlaw _) fourTotal)
    have hmeanfun : (fun ω => sampleMean (fourSequenceErrors block m ω)) =
        (fun ω => (4*(m : ℝ))⁻¹ * ∑ b : Fin m, fourTotal (block b.val ω)) := by
      funext ω
      simp [sampleMean,Fintype.card_prod,Fintype.sum_prod_type,fourSequenceErrors,fourTotal,mul_comm]
    have hmeanAS : AEStronglyMeasurable (fun ω => sampleMean (fourSequenceErrors block m ω)) μ := by
      rw [hmeanfun]; exact hLPt.aestronglyMeasurable.const_mul _
    have he := funext (four_replicated_ratio_formula μ block hmeas hind hlaw m)
    rw [he]
    have hpa := (hLPp.aestronglyMeasurable.const_mul (m : ℝ)⁻¹).const_mul (3 : ℝ)⁻¹
    have hq := hpa.sub ((hmeanAS.pow 2).const_mul (8/3 : ℝ))
    convert hq using 1
    funext ω
    simp only [Pi.sub_apply,Pi.pow_apply,div_eq_mul_inv]
    ring
  · exact four_replicated_ratio_ae μ block hmeas hind hlaw


/-- T1(f): each primitive is a fair sign, with probabilities 1/2,1/2
on −1,+1. This is the explicit bounded-error construction. -/
def fairSignLaw : FiniteLaw (Fin 2) where
  weight := fun _ => 1/2
  nonneg := by intro a; norm_num
  total := by norm_num [Fin.sum_univ_succ]

/-- T1(f): the 13 fair signs have the uniform joint law, with each
sign vector assigned probability 1/8192. No vector enumeration is used. -/
def sixSignLaw : FiniteLaw (Fin 13 → Fin 2) where
  weight := fun _ => 1/8192
  nonneg := by intro a; norm_num
  total := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_fun,Fintype.card_fin]
    norm_num

/-- T1(f): the same uniform sign law represented as a genuine product
measure of 13 fair-sign probability measures, for independence proofs. -/
def sixSignProduct : Measure (Fin 13 → Fin 2) :=
  Measure.pi (fun _ : Fin 13 => finiteLawMeasure fairSignLaw)

/-- T1, finite-law certificate: every atom has exactly its prescribed
weight in the actual probability-measure realization. -/
theorem finite_law_atom {S : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (law : FiniteLaw S) (a : S) :
    (finiteLawMeasure law) {a} = ENNReal.ofReal (law.weight a) := by
  classical
  simp [finiteLawMeasure,Measure.finsetSum_apply,Measure.smul_apply,
    Measure.dirac_apply',smul_eq_mul,Pi.single_apply]

/-- T1(f): exact equality of the uniform finite law and the product
of 13 fair-sign measures, proved atomwise with only 13 product factors. -/
theorem six_sign_measure_product : finiteLawMeasure sixSignLaw = sixSignProduct := by
  letI : IsProbabilityMeasure (finiteLawMeasure fairSignLaw) := finite_law_probability fairSignLaw
  apply Measure.ext_of_singleton
  intro a
  rw [finite_law_atom]
  change ENNReal.ofReal (sixSignLaw.weight a) =
    (Measure.pi (fun _ : Fin 13 => finiteLawMeasure fairSignLaw)) {a}
  rw [Measure.pi_singleton]
  simp_rw [finite_law_atom]
  norm_num [sixSignLaw,fairSignLaw,Fin.prod_univ_succ]
  rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1/2)]
  norm_num

/-- T1(f): all 13 primitive signs have mean zero and covariance equal
to the identity matrix, derived from the product law rather than assumed. -/
theorem fair_sign_moments :
    (∀ i : Fin 13, (∫ a, signValue (a i) ∂finiteLawMeasure sixSignLaw) = 0) ∧
    (∀ i j : Fin 13, covariance (fun a => signValue (a i)) (fun a => signValue (a j))
      (finiteLawMeasure sixSignLaw) = if i = j then 1 else 0) := by
  letI : IsProbabilityMeasure (finiteLawMeasure fairSignLaw) := finite_law_probability fairSignLaw
  letI : IsProbabilityMeasure sixSignProduct := by
    dsimp only [sixSignProduct]; infer_instance
  rw [six_sign_measure_product]
  have hmean : ∀ i : Fin 13, (∫ a, signValue (a i) ∂sixSignProduct) = 0 := by
    intro i
    change (∫ a, signValue (a i) ∂Measure.pi (fun _ : Fin 13 => finiteLawMeasure fairSignLaw)) = 0
    rw [integral_comp_eval (μ := fun _ : Fin 13 => finiteLawMeasure fairSignLaw) (i := i)
      (measurable_of_countable signValue).aestronglyMeasurable,
      finite_law_integral]
    norm_num [finiteExpectation,fairSignLaw,signValue,Fin.sum_univ_succ]
  have hv : ∀ i : Fin 13, variance (fun a => signValue (a i)) sixSignProduct = 1 := by
    intro i
    have he := variance_map (X := signValue) (Y := fun a : Fin 13 → Fin 2 => a i)
      (μ := sixSignProduct) (measurable_of_countable signValue).aemeasurable
      (measurable_pi_apply i).aemeasurable
    have hm := (measurePreserving_eval (fun _ : Fin 13 => finiteLawMeasure fairSignLaw) i).map_eq
    change sixSignProduct.map (fun a => a i) = finiteLawMeasure fairSignLaw at hm
    rw [hm,finite_law_variance] at he
    norm_num [finiteVariance,finiteExpectation,fairSignLaw,signValue,Fin.sum_univ_succ] at he
    exact he.symm
  refine ⟨hmean,?_⟩
  intro i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl,covariance_self (measurable_of_countable _).aemeasurable,hv]
  · rw [if_neg hij]
    have hind : iIndepFun (fun i : Fin 13 => fun a : Fin 13 → Fin 2 => signValue (a i)) sixSignProduct :=
      iIndepFun_pi (X := fun _ : Fin 13 => signValue) (fun _ => (measurable_of_countable signValue).aemeasurable)
    exact (hind.indepFun hij).covariance_eq_zero MemLp.of_discrete MemLp.of_discrete

/-- T1(f): the 6×13 exact loading matrix of the error
formula, ordered as four node signs, three complementary-pair signs, six own signs. -/
def sixLoading : Matrix (Fin 6) (Fin 13) ℝ :=
  let t := Real.sqrt 2
  ![![t/4,t/4,0,0,t/2,0,0,1/2,0,0,0,0,0],
    ![t/4,0,t/4,0,0,t/2,0,0,1/2,0,0,0,0],
    ![t/4,0,0,t/4,0,0,t/2,0,0,1/2,0,0,0],
    ![0,t/4,t/4,0,0,0,-t/2,0,0,0,1/2,0,0],
    ![0,t/4,0,t/4,0,-t/2,0,0,0,0,0,1/2,0],
    ![0,0,t/4,t/4,-t/2,0,0,0,0,0,0,0,1/2]]

/-- T1(f): the target's membership-based formula is exactly the
linear combination given by the six-loading matrix. -/
theorem six_loading_identity (a : Fin 13 → Fin 2) (r : Fin 6) :
    sixErrorsFromSigns a r = ∑ i : Fin 13, sixLoading r i * signValue (a i) := by
  fin_cases r <;>
    simp only [sixErrorsFromSigns,Fin.sum_univ_succ,Fin.sum_univ_zero] <;>
    norm_num [sixLoading,sixDyads] <;> ring

/-- Finite covariance lemma for T1(f): under zero means and identity
primitive covariance, a pair of loading sums has covariance equal to their
loading inner product. This does not assume any target error moments. -/
theorem linear_covariance_identity {I Ω : Type*} [Fintype I] [DecidableEq I]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : I → Ω → ℝ) (hLP : ∀ i, MemLp (Z i) 2 μ)
    (hc : ∀ i j, covariance (Z i) (Z j) μ = if i = j then 1 else 0)
    (a b : I → ℝ) :
    covariance (fun ω => ∑ i, a i*Z i ω) (fun ω => ∑ i, b i*Z i ω) μ = ∑ i, a i*b i := by
  rw [covariance_fun_sum_fun_sum (fun i => (hLP i).const_mul _) (fun i => (hLP i).const_mul _)]
  simp only [covariance_const_mul_left,covariance_const_mul_right,hc]
  simp [mul_comm]

/-- T1(f): the exact loading Gram matrix is Ω6; the square-root
products reduce via (sqrt 2)²=2, using 36 small row-pair certificates. -/
theorem six_loading_gram_certificate :
    ∀ r s : Fin 6, ∑ i : Fin 13, sixLoading r i*sixLoading s i = sixOmega r s := by
  intro r s
  fin_cases r <;> fin_cases s <;>
    norm_num [sixLoading,sixOmega,Fin.sum_univ_succ] <;>
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- T1(f): the explicit uniform 13-sign law realizes exactly the
centered six-error covariance Ω6, with all moments derived from fair signs. -/
theorem six_sign_error_moments :
    (∀ r : Fin 6, finiteExpectation sixSignLaw (fun a => sixErrorsFromSigns a r) = 0) ∧
    (∀ r s : Fin 6, finiteExpectation sixSignLaw
      (fun a => sixErrorsFromSigns a r*sixErrorsFromSigns a s) = sixOmega r s) := by
  let μ := finiteLawMeasure sixSignLaw
  letI : IsProbabilityMeasure μ := finite_law_probability sixSignLaw
  let Z : Fin 13 → (Fin 13 → Fin 2) → ℝ := fun i a => signValue (a i)
  have hLP : ∀ i, MemLp (Z i) 2 μ := fun _ => MemLp.of_discrete
  have hf : ∀ r : Fin 6, (fun a => sixErrorsFromSigns a r) =
      (fun a => ∑ i : Fin 13, sixLoading r i*Z i a) := by
    intro r; funext a; exact six_loading_identity a r
  have hZm : ∀ i : Fin 13, (∫ a, Z i a ∂μ) = 0 := fun i => fair_sign_moments.1 i
  have hm : ∀ r : Fin 6, (∫ a, sixErrorsFromSigns a r ∂μ) = 0 := by
    intro r
    rw [hf r,integral_finsetSum]
    · simp only [integral_const_mul,hZm,mul_zero,Finset.sum_const_zero]
    · intro i _; exact ((hLP i).const_mul _).integrable (by norm_num)
  refine ⟨?_,?_⟩
  · intro r; rw [← finite_law_integral]; exact hm r
  · intro r s
    have hc := linear_covariance_identity μ Z hLP fair_sign_moments.2 (sixLoading r) (sixLoading s)
    rw [← hf r,← hf s,six_loading_gram_certificate] at hc
    rw [covariance_eq_sub (MemLp.of_discrete : MemLp (fun a => sixErrorsFromSigns a r) 2 μ)
      (MemLp.of_discrete : MemLp (fun a => sixErrorsFromSigns a s) 2 μ),hm r,hm s] at hc
    simp only [mul_zero,sub_zero] at hc
    rw [← finite_law_integral]; exact hc


/-- Finite lemma for T1: expectation commutes with a finite sum of
block statistics; no independence assumption is needed for this identity. -/
theorem finite_expectation_sum {S I : Type*} [Fintype S] [Fintype I]
    (law : FiniteLaw S) (f : I → S → ℝ) :
    finiteExpectation law (fun a => ∑ i, f i a) = ∑ i, finiteExpectation law (f i) := by
  simp only [finiteExpectation,Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Finite lemma for T1: the exact expectation of a quadratic form
is the ordered sum of its coefficients times the realized second moments. -/
theorem finite_expectation_quadratic {S : Type*} [Fintype S]
    (law : FiniteLaw S) (W : Matrix R R ℝ) (u : S → R → ℝ) :
    finiteExpectation law (fun a => quadratic W (u a)) =
      ∑ r, ∑ s, W r s * finiteExpectation law (fun a => u a r*u a s) := by
  simp only [finiteExpectation,quadratic,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- T1(f): S_b is the sum of all six errors in the sign block. -/
def sixTotal (a : Fin 13 → Fin 2) : ℝ := ∑ r : Fin 6, sixErrorsFromSigns a r

/-- T1(f), exact one-block statistic lemmas: E[S_b]=0, Var(S_b)=6
and E[q_b]=9 under the explicit uniform independent-sign law. -/
theorem six_sign_statistics :
    finiteExpectation sixSignLaw sixTotal = 0 ∧
    finiteVariance sixSignLaw sixTotal = 6 ∧
    finiteExpectation sixSignLaw sixBlockQ = 9 := by
  have hm := six_sign_error_moments.1
  have hsecond := six_sign_error_moments.2
  refine ⟨?_,?_,?_⟩
  · change finiteExpectation sixSignLaw (fun a => ∑ r : Fin 6, sixErrorsFromSigns a r) = 0
    rw [finite_expectation_sum]
    simp only [hm,Finset.sum_const_zero]
  · let μ := finiteLawMeasure sixSignLaw
    letI : IsProbabilityMeasure μ := finite_law_probability sixSignLaw
    let u : Fin 6 → (Fin 13 → Fin 2) → ℝ := fun r a => sixErrorsFromSigns a r
    have hmu : ∀ r, (∫ a, u r a ∂μ) = 0 := by
      intro r; rw [finite_law_integral]; exact hm r
    have hA : errorCovariance μ u = sixOmega := by
      ext r s; rw [errorCovariance,finite_law_integral]; exact hsecond r s
    have he := centered_linear_variance μ u (fun _ => MemLp.of_discrete) hmu (fun _ => 1)
    have hq : quadratic sixOmega (fun _ => 1) = 6 := by
      norm_num [quadratic,sixOmega,Fin.sum_univ_succ]
    rw [hA,hq] at he
    rw [← finite_law_variance]
    change variance (fun a => ∑ r : Fin 6, sixErrorsFromSigns a r) (finiteLawMeasure sixSignLaw) = 6
    simpa only [u,one_mul] using he
  · have he : finiteExpectation sixSignLaw sixBlockQ =
        ∑ r : Fin 6, ∑ t : Fin 6, dyPattern sixDyads r t *
          finiteExpectation sixSignLaw (fun a => sixErrorsFromSigns a r*sixErrorsFromSigns a t) :=
      finite_expectation_quadratic sixSignLaw (Matrix.of (fun r t => dyPattern sixDyads r t)) sixErrorsFromSigns
    simp_rw [hsecond] at he
    norm_num [sixOmega,dyPattern,sixDyads,Fin.sum_univ_succ] at he
    exact he

/-- T1(f), finite-law bound: all six explicit errors are bounded by
sqrt(2)+1/2, uniformly over the whole sign space, rather than only a.e. -/
theorem six_errors_bounded :
    ∀ a : Fin 13 → Fin 2, ∀ r : Fin 6, |sixErrorsFromSigns a r| ≤ Real.sqrt 2+1/2 := by
  have hs : ∀ x : Fin 2, |signValue x| = 1 := by
    intro x; fin_cases x <;> norm_num [signValue]
  have hrow : ∀ r : Fin 6, ∑ i : Fin 13, |sixLoading r i| = Real.sqrt 2+1/2 := by
    intro r; fin_cases r <;>
      simp [sixLoading,Fin.sum_univ_succ,abs_div,abs_of_nonneg (Real.sqrt_nonneg 2)] <;> ring
  intro a r
  rw [six_loading_identity]
  calc
    _ ≤ ∑ i : Fin 13, |sixLoading r i*signValue (a i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin 13, |sixLoading r i| := by simp only [abs_mul,hs,mul_one]
    _ = Real.sqrt 2+1/2 := hrow r

/-- T1(e),(f), independent-block covariance lemma: the realized
covariance on replicated errors is block diagonal with the specified
one-block covariance. Means and second moments come from the finite law. -/
theorem iid_block_covariance {S Ω : Type*} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] [MeasurableSpace Ω] (law : FiniteLaw S)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → S)
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (law.weight a))
    (u : S → R → ℝ) (hm : ∀ r, finiteExpectation law (fun a => u a r) = 0)
    (A : Matrix R R ℝ) (hA : ∀ r s, finiteExpectation law (fun a => u a r*u a s) = A r s)
    (m : ℕ) :
    errorCovariance μ (fun r : Fin m × R => fun ω => u (block r.1.val ω) r.2) =
      Matrix.of (fun r s : Fin m × R => if r.1 = s.1 then A r.2 s.2 else 0) := by
  ext ⟨b,r⟩ ⟨c,s⟩
  by_cases hbc : b = c
  · subst c
    simpa [errorCovariance] using
      (finite_law_composed_integral law μ (block b.val) (hmeas b.val) (hlaw b.val)
        (fun a => u a r*u a s)).trans (hA r s)
  · simp only [Matrix.of_apply,ite_eq_right hbc,errorCovariance]
    have hX := finite_law_composed_memLp law μ (block b.val) (hmeas b.val) (hlaw b.val) (fun a => u a r)
    have hY := finite_law_composed_memLp law μ (block c.val) (hmeas c.val) (hlaw c.val) (fun a => u a s)
    have hi := (hind.indepFun (Fin.val_injective.ne hbc)).comp
      (measurable_of_countable (fun a => u a r)) (measurable_of_countable (fun a => u a s))
    have he := hi.integral_mul_eq_mul_integral hX.aestronglyMeasurable hY.aestronglyMeasurable
    change (∫ ω, u (block b.val ω) r*u (block c.val ω) s ∂μ) =
      (∫ ω, u (block b.val ω) r ∂μ)*(∫ ω, u (block c.val ω) s ∂μ) at he
    have hx := (finite_law_composed_integral law μ (block b.val) (hmeas b.val) (hlaw b.val)
      (fun a => u a r)).trans (hm r)
    have hy := (finite_law_composed_integral law μ (block c.val) (hmeas c.val) (hlaw c.val)
      (fun a => u a s)).trans (hm s)
    exact he.trans (by rw [hx,hy]; ring)

/-- T1(e),(f): independent copies have a block-diagonal population
covariance matrix with the same one-block covariance in each block. -/
def blockMatrix (m : ℕ) (A : Matrix R R ℝ) : Matrix (Fin m × R) (Fin m × R) ℝ :=
  Matrix.of (fun r s => if r.1 = s.1 then A r.2 s.2 else 0)

/-- Table 2's diagonal population restriction, used for the naive
comparison in T1(f); every off-record covariance is set to zero. -/
def recordRestriction (A : Matrix R R ℝ) : Matrix R R ℝ :=
  Matrix.of (fun r s => recordPattern r s * A r s)

/-- T1(f), finite algebra: a block covariance quadratic form is the
sum of its block quadratic forms. -/
theorem block_matrix_quadratic (m : ℕ) (A : Matrix R R ℝ) (u : Fin m × R → ℝ) :
    quadratic (blockMatrix m A) u = ∑ b : Fin m, quadratic A (fun r => u (b,r)) := by
  simp only [quadratic,blockMatrix,Matrix.of_apply,Fintype.sum_prod_type,mul_ite,mul_zero]
  simp [Finset.sum_ite_irrel]

/-- T1(f), finite algebra: the population incidence restriction of
independent disjoint blocks restricts each diagonal block separately. -/
theorem block_matrix_restriction (m : ℕ) (d : R → Dyad M) (A : Matrix R R ℝ) :
    dyRestriction (fun r : Fin m × R => liftDyad r.1 (d r.2)) (blockMatrix m A) =
      blockMatrix m (dyRestriction d A) := by
  ext r s
  simp only [dyRestriction,blockMatrix,Matrix.of_apply,replicated_pattern]
  by_cases h : r.1 = s.1 <;> simp [h]

/-- T1(f), finite algebra: the naive diagonal restriction also
commutes with forming the independent block covariance matrix. -/
theorem block_matrix_record_restriction (m : ℕ) (A : Matrix R R ℝ) :
    recordRestriction (blockMatrix m A) = blockMatrix m (recordRestriction A) := by
  ext ⟨b,r⟩ ⟨c,s⟩
  by_cases h : b = c
  · subst c; simp [recordRestriction,blockMatrix,recordPattern]
  · simp [recordRestriction,blockMatrix,recordPattern,Prod.mk.injEq,h]

/-- T1(f), finite algebra: for an intercept influence t in each row,
the covariance quadratic is t² times the total of its covariance entries. -/
theorem constant_quadratic (A : Matrix R R ℝ) (t : ℝ) :
    quadratic A (fun _ => t) = t^2*(∑ r, ∑ s, A r s) := by
  simp only [quadratic,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- T1(f), all replicated population values: with n=6m, full and
naive sandwich values are 1/n, while the dyadic value is 3/(2n). -/
theorem six_replicated_population_values (m : ℕ) (hm : 1 ≤ m) :
    quadratic (blockMatrix m sixOmega) (fun _ => (6*(m : ℝ))⁻¹) = 1/(6*(m : ℝ)) ∧
    quadratic (dyRestriction (replicatedSixDyads m) (blockMatrix m sixOmega))
      (fun _ => (6*(m : ℝ))⁻¹) = 3/(2*(6*(m : ℝ))) ∧
    quadratic (recordRestriction (blockMatrix m sixOmega))
      (fun _ => (6*(m : ℝ))⁻¹) = 1/(6*(m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hfull : (∑ r : Fin 6, ∑ s : Fin 6, sixOmega r s) = (6 : ℝ) := by
    simp [six_block_variances.1]
  have hdy : (∑ r : Fin 6, ∑ s : Fin 6, dyRestriction sixDyads sixOmega r s) = (9 : ℝ) := by
    norm_num [six_block_variances.2.1]
  have hrec : (∑ r : Fin 6, ∑ s : Fin 6, recordRestriction sixOmega r s) = (6 : ℝ) := by
    norm_num [recordRestriction,recordPattern,sixOmega,Fin.sum_univ_succ]
  have hd : dyRestriction (replicatedSixDyads m) (blockMatrix m sixOmega) =
      blockMatrix m (dyRestriction sixDyads sixOmega) := block_matrix_restriction m sixDyads sixOmega
  refine ⟨?_,?_,?_⟩
  · rw [block_matrix_quadratic]
    simp only [constant_quadratic,hfull,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hm0] <;> ring
  · rw [hd,block_matrix_quadratic]
    simp only [constant_quadratic,hdy,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hm0] <;> ring
  · rw [block_matrix_record_restriction,block_matrix_quadratic]
    simp only [constant_quadratic,hrec,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp [hm0] <;> ring

/-- T1(f), exact replicated moments: the actual sampling variance is
1/(6m), and expected residual DCR is 3/(12m)−5/(6m)² for every m≥1. -/
theorem six_replicated_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → (Fin 13 → Fin 2))
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = (1/8192 : ENNReal))
    (m : ℕ) (hm : 1 ≤ m) :
    variance (fun ω => sampleMean (sixSequenceErrors block m ω)) μ = 1/(6*(m : ℝ)) ∧
    (∫ ω, interceptDCR (replicatedSixDyads m) (sixSequenceErrors block m ω) ∂μ) =
      3/(2*(6*(m : ℝ)))-5/(6*(m : ℝ))^2 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hflaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (sixSignLaw.weight a) := by
    intro b a; rw [hlaw]; norm_num [sixSignLaw,ENNReal.ofReal_div_of_pos]
  have hμ : (fun ω => sampleMean (sixSequenceErrors block m ω)) =
      (fun ω => (6*(m : ℝ))⁻¹ * ∑ b : Fin m, sixTotal (block b.val ω)) := by
    funext ω
    simp [sampleMean,Fintype.card_prod,Fintype.sum_prod_type,sixSequenceErrors,sixTotal,mul_comm]
  have hLPb : ∀ b : Fin m, MemLp (fun ω => sixTotal (block b.val ω)) 2 μ := by
    intro b; exact finite_law_composed_memLp sixSignLaw μ _ (hmeas _) (hflaw _) sixTotal
  have hLPsum : MemLp (fun ω => ∑ b : Fin m, sixTotal (block b.val ω)) 2 μ :=
    memLp_finsetSum _ (fun b _ => hLPb b)
  have hLPmean : MemLp (fun ω => sampleMean (sixSequenceErrors block m ω)) 2 μ := by
    rw [hμ]; exact hLPsum.const_mul _
  have hmean : (∫ ω, sampleMean (sixSequenceErrors block m ω) ∂μ) = 0 := by
    rw [hμ,integral_const_mul,iid_finite_statistic_integral sixSignLaw μ block hmeas hflaw,
      six_sign_statistics.1]
    ring
  have hv : variance (fun ω => sampleMean (sixSequenceErrors block m ω)) μ = 1/(6*(m : ℝ)) := by
    rw [hμ,variance_const_mul,iid_finite_statistic_variance sixSignLaw μ block hmeas hind hflaw,
      six_sign_statistics.2.1]
    field_simp [hm0] <;> ring
  have hsq : (∫ ω, (sampleMean (sixSequenceErrors block m ω))^2 ∂μ) = 1/(6*(m : ℝ)) := by
    rw [variance_eq_integral hLPmean.aemeasurable,hmean] at hv
    simpa using hv
  have hPint : Integrable (fun ω => ∑ b : Fin m, sixBlockQ (block b.val ω)) μ := by
    apply integrable_finsetSum
    intro b _
    exact (finite_law_composed_memLp sixSignLaw μ _ (hmeas _) (hflaw _) sixBlockQ).integrable (by norm_num)
  have he := congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ)
    (funext (six_replicated_centering block m hm))
  rw [integral_const_mul,integral_sub (hPint.div_const _) (hLPmean.integrable_sq.const_mul _),
    integral_div,integral_const_mul,iid_finite_statistic_integral sixSignLaw μ block hmeas hflaw,
    six_sign_statistics.2.2,hsq] at he
  refine ⟨hv,?_⟩
  apply (mul_left_cancel₀ (show 6*(m : ℝ) ≠ 0 from mul_ne_zero (by norm_num) hm0))
  rw [he]
  field_simp [hm0]
  ring

/-- T1(f), exact scaled-estimator representation for every sample
size, including the empty initial sample used only for sequence notation. -/
theorem six_scaled_estimator_formula {Ω : Type*}
    (block : ℕ → Ω → (Fin 13 → Fin 2)) (m : ℕ) (ω : Ω) :
    (6*(m : ℝ))*interceptDCR (replicatedSixDyads m) (sixSequenceErrors block m ω) =
      ((∑ b : Fin m, sixBlockQ (block b.val ω))/(m : ℝ))/6-
        5*(sampleMean (sixSequenceErrors block m ω))^2 := by
  by_cases hm : m = 0
  · subst m; simp [sampleMean,Fintype.card_prod]
  · have he := six_replicated_centering block m (by omega) ω
    convert he using 1
    simp only [div_eq_mul_inv,mul_inv]
    ring


/-- T1(f), all finite probabilistic claims: the uniform 2^13 sign law
realizes exactly Ω6, E[q_b]=9, and on n=6m observations Var(βhat)=1/n,
E[Vhat]=3/(2n)−5/n², with n Vhat=(Σ_bq_b)/n−5ubar².
The expectation exceeds truth exactly for m≥2; at m=1 it is 1/9<1/6. -/
theorem six_replicated_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → (Fin 13 → Fin 2))
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = (1/8192 : ENNReal))
    (m : ℕ) (hm : 1 ≤ m) :
    (∀ b r, (∫ ω, sixErrorsFromSigns (block b ω) r ∂μ) = 0) ∧
    (∀ b r s, (∫ ω, sixErrorsFromSigns (block b ω) r * sixErrorsFromSigns (block b ω) s ∂μ) =
      sixOmega r s) ∧
    (∀ b, (∫ ω, sixBlockQ (block b ω) ∂μ) = 9) ∧
    (∀ ω, (6*(m : ℝ))*interceptDCR (replicatedSixDyads m) (sixSequenceErrors block m ω) =
      (∑ b : Fin m, sixBlockQ (block b.val ω))/(6*(m : ℝ)) -
        5*(sampleMean (sixSequenceErrors block m ω))^2) ∧
    variance (fun ω => sampleMean (sixSequenceErrors block m ω)) μ = 1/(6*(m : ℝ)) ∧
    quadratic (dyRestriction (replicatedSixDyads m)
      (errorCovariance μ (fun r ω => sixSequenceErrors block m ω r)))
      (fun _ => (6*(m : ℝ))⁻¹) = 3/(2*(6*(m : ℝ))) ∧
    quadratic (fun r s => recordPattern r s *
      errorCovariance μ (fun r ω => sixSequenceErrors block m ω r) r s)
      (fun _ => (6*(m : ℝ))⁻¹) = 1/(6*(m : ℝ)) ∧
    (∫ ω, interceptDCR (replicatedSixDyads m) (sixSequenceErrors block m ω) ∂μ) =
      3/(2*(6*(m : ℝ)))-5/(6*(m : ℝ))^2 ∧
    ((variance (fun ω => sampleMean (sixSequenceErrors block m ω)) μ <
      (∫ ω, interceptDCR (replicatedSixDyads m) (sixSequenceErrors block m ω) ∂μ)) ↔ 2 ≤ m) := by
  have hflaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (sixSignLaw.weight a) := by
    intro b a; rw [hlaw]; norm_num [sixSignLaw,ENNReal.ofReal_div_of_pos]
  rcases six_replicated_moments μ block hmeas hind hlaw m hm with ⟨hv,he⟩
  have hA : errorCovariance μ (fun r ω => sixSequenceErrors block m ω r) = blockMatrix m sixOmega :=
    iid_block_covariance sixSignLaw μ block hmeas hind hflaw sixErrorsFromSigns
      six_sign_error_moments.1 sixOmega six_sign_error_moments.2 m
  have hp := six_replicated_population_values m hm
  refine ⟨?_,?_,?_,six_replicated_centering block m hm,hv,?_,?_,he,?_⟩
  · intro b r
    exact (finite_law_composed_integral sixSignLaw μ (block b) (hmeas b) (hflaw b)
      (fun a => sixErrorsFromSigns a r)).trans (six_sign_error_moments.1 r)
  · intro b r t
    exact (finite_law_composed_integral sixSignLaw μ (block b) (hmeas b) (hflaw b)
      (fun a => sixErrorsFromSigns a r*sixErrorsFromSigns a t)).trans (six_sign_error_moments.2 r t)
  · intro b
    exact (finite_law_composed_integral sixSignLaw μ (block b) (hmeas b) (hflaw b)
      sixBlockQ).trans six_sign_statistics.2.2
  · rw [hA]; exact hp.2.1
  · change quadratic (recordRestriction (errorCovariance μ (fun r ω => sixSequenceErrors block m ω r)))
      (fun _ => (6*(m : ℝ))⁻¹) = 1/(6*(m : ℝ))
    rw [hA]; exact hp.2.2
  · rw [hv,he,← sub_pos,(six_expected_gap_arithmetic m hm).1]
    exact (six_expected_gap_arithmetic m hm).2.1


/-- T1(f), asymptotic limit: n Vhat converges ALMOST SURELY
to 3/2, with n=6m, on the explicit iid bounded fair-sign blocks. -/
theorem six_replicated_limit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (block : ℕ → Ω → (Fin 13 → Fin 2))
    (hmeas : ∀ b, Measurable (block b)) (hind : iIndepFun block μ)
    (hlaw : ∀ b a, μ {ω | block b ω = a} = (1/8192 : ENNReal)) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun (m : ℕ) => (6*(m : ℝ))*interceptDCR (replicatedSixDyads m) (sixSequenceErrors block m ω))
      atTop (nhds (3/2 : ℝ)) := by
  have hflaw : ∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (sixSignLaw.weight a) := by
    intro b a; rw [hlaw]; norm_num [sixSignLaw,ENNReal.ofReal_div_of_pos]
  have hT := iid_finite_statistic_strong_law sixSignLaw μ block hmeas hind hflaw sixTotal
  have hQ := iid_finite_statistic_strong_law sixSignLaw μ block hmeas hind hflaw sixBlockQ
  rw [six_sign_statistics.1] at hT
  rw [six_sign_statistics.2.2] at hQ
  filter_upwards [hT,hQ] with ω hTω hQω
  have hmean : Tendsto (fun m : ℕ => sampleMean (sixSequenceErrors block m ω)) atTop (nhds (0 : ℝ)) := by
    have he := hTω.div_const (6 : ℝ)
    convert he using 1
    · funext m
      simp [sampleMean,Fintype.card_prod,Fintype.sum_prod_type,sixSequenceErrors,sixTotal,
        div_eq_mul_inv,mul_inv]
      ring
    · norm_num
  have he := (hQω.div_const (6 : ℝ)).sub ((hmean.pow 2).const_mul (5 : ℝ))
  convert he using 1
  · funext m
    exact six_scaled_estimator_formula block m ω
  · norm_num


/-- T5, realization lemma: every certified finite probability law
has a measurable infinite iid block realization with exactly its atom
probabilities. Mathlib constructs the product probability space. -/
theorem finite_law_iid_exists {S : Type} [Fintype S] [MeasurableSpace S]
    [DiscreteMeasurableSpace S] (law : FiniteLaw S) :
    ∃ Ω : Type, ∃ _ : MeasurableSpace Ω, ∃ μ : Measure Ω, ∃ block : ℕ → Ω → S,
      IsProbabilityMeasure μ ∧ (∀ b, Measurable (block b)) ∧ iIndepFun block μ ∧
      (∀ b a, μ {ω | block b ω = a} = ENNReal.ofReal (law.weight a)) := by
  letI : IsProbabilityMeasure (finiteLawMeasure law) := finite_law_probability law
  rcases exists_iid ℕ (finiteLawMeasure law) with ⟨Ω,mΩ,μ,block,hmeas,hLaw,hind,hμ⟩
  letI : MeasurableSpace Ω := mΩ
  refine ⟨Ω,mΩ,μ,block,hμ,hmeas,hind,?_⟩
  intro b a
  calc
    _ = μ.map (block b) {a} := by rw [Measure.map_apply (hmeas b) (measurableSet_singleton a)]; rfl
    _ = (finiteLawMeasure law) {a} := congrArg (fun ν : Measure S => ν {a}) (hLaw b).map_eq
    _ = _ := finite_law_atom law a

/-- T5: the printed limit lower bound is false. The witness is the
actual iid bounded four-observation model, sampled with m+1 blocks to keep
every finite design full rank, and its actual ratio limit is 5/3>1. -/
theorem printed_ratio_limit_claim_false : ¬PrintedRatioLimitLowerBound := by
  rcases finite_law_iid_exists fourBlockLaw with ⟨Ω,mΩ,μ,block,hμ,hmeas,hind,hlaw⟩
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure μ := hμ
  let R : ℕ → Type := fun m => Fin (m+1) × Fin 4
  let M : ℕ → Type := fun m => Fin (m+1) × Fin 6
  letI : ∀ m, Fintype (R m) := fun m => by dsimp [R]; infer_instance
  letI : ∀ m, DecidableEq (R m) := fun m => by dsimp [R]; infer_instance
  letI : ∀ m, Fintype (M m) := fun m => by dsimp [M]; infer_instance
  letI : ∀ m, DecidableEq (M m) := fun m => by dsimp [M]; infer_instance
  let d : ∀ m, R m → Dyad (M m) := fun m => replicatedFourDyads (m+1)
  let X : ∀ m, Matrix (R m) (Fin 1) ℝ := fun _ => interceptDesign
  let u : ∀ m, R m → Ω → ℝ := fun m r ω => fourSequenceErrors block (m+1) ω r
  have hn : ∀ m, (Fintype.card (R m) : ℝ) ≠ 0 := by
    intro m
    simp only [R,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
    positivity
  have hfit := fun m (y : R m → ℝ) => intercept_fit_certificate (R := R m) (hn m) (d m) y
  have hrank : ∀ m, ((X m).transpose * X m).det ≠ 0 := by
    intro m
    have hg := (hfit m (0 : R m → ℝ)).1
    change ((interceptDesign : Matrix (R m) (Fin 1) ℝ).transpose * interceptDesign).det ≠ 0
    rw [hg]
    simpa only [Matrix.det_fin_one,Matrix.of_apply] using hn m
  have hsize : Tendsto (fun m => Fintype.card (R m)) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    refine eventually_atTop.2 ⟨B,fun m hm => ?_⟩
    simp only [R,Fintype.card_prod,Fintype.card_fin]
    omega
  have hLP : ∀ m r, MemLp (u m r) 2 μ := by
    intro m r
    exact finite_law_composed_memLp fourBlockLaw μ (block r.1.val) (hmeas _) (hlaw _)
      (fun a => fourBlockErrors a r.2)
  have hmean : ∀ m r, (∫ ω, u m r ω ∂μ) = 0 := by
    intro m r
    exact (finite_law_composed_integral fourBlockLaw μ (block r.1.val) (hmeas _) (hlaw _)
      (fun a => fourBlockErrors a r.2)).trans (four_block_moments.1 r.2)
  have hCov : ∀ m, errorCovariance μ (u m) = blockMatrix (m+1) fourOmega := by
    intro m
    exact iid_block_covariance fourBlockLaw μ block hmeas hind hlaw fourBlockErrors
      four_block_moments.1 fourOmega four_block_moments.2 (m+1)
  have homit : ∀ᶠ m in atTop, ∃ r s : R m,
      ¬((d m r).members ∩ (d m s).members).Nonempty ∧ errorCovariance μ (u m) r s ≠ 0 := by
    apply Eventually.of_forall
    intro m
    refine ⟨(0,0),(0,2),?_,?_⟩
    · change ¬((liftDyad (0 : Fin (m+1)) (fourDyads 0)).members ∩
        (liftDyad (0 : Fin (m+1)) (fourDyads 2)).members).Nonempty
      rw [lifted_intersection]
      norm_num [fourDyads]
    · rw [hCov]
      norm_num [blockMatrix,fourOmega]
  have hθ : ∀ m, (fun ω => (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ ols (X m)
      (X m *ᵥ (0 : Fin 1 → ℝ)+fun r => u m r ω)) =
      (fun ω => sampleMean (fourSequenceErrors block (m+1) ω)) := by
    intro m; funext ω
    simp only [Matrix.mulVec_zero,zero_add]
    rw [(hfit m (fun r => u m r ω)).2.2.1]
    simp only [dotProduct,Fin.sum_univ_one,one_mul]
    rfl
  have hV : ∀ m, (fun ω => quadratic (plugIn (X m)
      (olsResidual (X m) (X m *ᵥ (0 : Fin 1 → ℝ)+fun r => u m r ω)) (dyPattern (d m)))
      (fun _ : Fin 1 => (1 : ℝ))) =
      (fun ω => interceptDCR (replicatedFourDyads (m+1)) (fourSequenceErrors block (m+1) ω)) := by
    intro m; funext ω
    simp only [Matrix.mulVec_zero,zero_add]
    exact (hfit m (fun r => u m r ω)).2.2.2.2
  have hpos : ∀ᶠ m in atTop, 0 < variance (fun ω => (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
      ols (X m) (X m *ᵥ (0 : Fin 1 → ℝ)+fun r => u m r ω)) μ := by
    apply Eventually.of_forall
    intro m
    rw [hθ m,(four_replicated_moments μ block hmeas hind hlaw (m+1) (by omega)).1]
    positivity
  have hshift : Tendsto (fun m : ℕ => m+1) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    exact eventually_atTop.2 ⟨B,fun m hm => by omega⟩
  have hlimit : TendstoInMeasure μ (fun m ω => quadratic (plugIn (X m)
      (olsResidual (X m) (X m *ᵥ (0 : Fin 1 → ℝ)+fun r => u m r ω)) (dyPattern (d m)))
      (fun _ : Fin 1 => (1 : ℝ)) /
      variance (fun ω => (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
        ols (X m) (X m *ᵥ (0 : Fin 1 → ℝ)+fun r => u m r ω)) μ)
      atTop (fun _ => (5/3 : ℝ)) := by
    have he := (four_replicated_limit μ block hmeas hind hlaw).comp hshift
    have hf : (fun m ω => quadratic (plugIn (X m)
        (olsResidual (X m) (X m *ᵥ (0 : Fin 1 → ℝ)+fun r => u m r ω)) (dyPattern (d m)))
        (fun _ : Fin 1 => (1 : ℝ)) /
        variance (fun ω => (fun _ : Fin 1 => (1 : ℝ)) ⬝ᵥ
          ols (X m) (X m *ᵥ (0 : Fin 1 → ℝ)+fun r => u m r ω)) μ) =
      (fun m ω => interceptDCR (replicatedFourDyads (m+1)) (fourSequenceErrors block (m+1) ω) /
        variance (fun ω => sampleMean (fourSequenceErrors block (m+1) ω)) μ) := by
      funext m ω
      rw [hθ m]
      exact congrArg (fun z : ℝ => z / variance (fun ω => sampleMean (fourSequenceErrors block (m+1) ω)) μ)
        (congrFun (hV m) ω)
    rw [hf]
    exact he
  intro h
  have hc := h Ω μ 1 R M d X (0 : Fin 1 → ℝ) (fun _ => 1) u
    hsize hrank hLP hmean homit hpos (5/3) hlimit
  norm_num at hc


end
end AronowAudit.P032

