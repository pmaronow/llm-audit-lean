import Mathlib

/-!
Formalization of Green, McGrath and Aronow, *Field Experiments and the Study of
Voter Turnout*, printed pp. 27-48 (2013).
The paper has no displayed mathematics. The definitions below express
precision-weighted pooling, shared-control counterexamples, and corrected
covariance formulas, together with finite-population randomization and
one-sided contact effects.
-/

namespace AronowAudit.P042

noncomputable section

set_option autoImplicit false

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- "Weighting each study by the precision with which it estimates the treatment
effect" (p. 31). Here v is the fixed marginal variance and w = 1/v;
the printed article supplies no formula. -/
def precisionWeight {ι : Type*} (v : ι → ℝ) (j : ι) : ℝ := (v j)⁻¹

/-- Total inverse-marginal-variance weight W, representing precision weighting on p. 31. -/
def totalWeight {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ := ∑ j, precisionWeight v j

/-- Normalized fixed precision weights a_j = w_j/W for the pooling on p. 31. -/
def normalizedWeight {ι : Type*} [Fintype ι] (v : ι → ℝ) (j : ι) : ℝ :=
  precisionWeight v j / totalWeight v

/-- "Pools the experiments in a given domain" (p. 31): the pooled effect is
represented as the weighted sum of the random effect estimates. -/
def pooled {ι Ω : Type*} [Fintype ι] (a : ι → ℝ) (D : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => ∑ j, a j * D j ω

/-- Diagonal-only variance corresponding to the printed intervals on pp. 31-33. -/
def diagonalVariance {ι : Type*} [Fintype ι] (v : ι → ℝ) : ℝ :=
  ∑ j, (normalizedWeight v j)^2 * v j

/-- Joint covariance quadratic form correcting the pooling variance on p. 31
by including the missing covariance terms (P042-E001). -/
def covarianceForm {ι : Type*} [Fintype ι] (a : ι → ℝ) (Sigma : ι → ι → ℝ) : ℝ :=
  ∑ j, ∑ k, a j * a k * Sigma j k

/-- Unordered off-diagonal covariance sum, P042-T2 (ii). -/
def offDiagonal {J : ℕ} (a : Fin J → ℝ) (Sigma : Fin J → Fin J → ℝ) : ℝ :=
  ∑ j, ∑ k ∈ Finset.univ.filter (fun k => j < k), a j * a k * Sigma j k

/-- Exact uniform randomization expectation on a finite list of possible
allocations: "assigned at random with known probability" (p. 28). Values here
are rational, so exhaustive witnesses use exact arithmetic. -/
def rationalMean {Ω : Type*} (s : Finset Ω) (X : Ω → ℚ) : ℚ :=
  (∑ ω ∈ s, X ω) / (s.card : ℚ)

/-- Variance over the uniform finite randomization distribution
for the finite-population witness to the intervals on pp. 31-33. -/
def rationalVariance {Ω : Type*} (s : Finset Ω) (X : Ω → ℚ) : ℚ :=
  rationalMean s (fun ω => (X ω - rationalMean s X)^2)

/-- Covariance over the same finite randomization distribution
for P042-E001's shared-control witness. -/
def rationalCovariance {Ω : Type*} (s : Finset Ω) (X Y : Ω → ℚ) : ℚ :=
  rationalMean s (fun ω => (X ω - rationalMean s X) * (Y ω - rationalMean s Y))

/-- "The term 'potential outcomes' refers to the outcomes that a subject would
express depending on whether he or she receives the treatment" (Note 2,
pp. 39-40). Witness A fixes (1,1,1,0,0,0) under all three
conditions, hence zero individual treatment effects. -/
def sixOutcome (i : Fin 6) (_g : Fin 3) : ℚ := if i.val < 3 then 1 else 0

/-- Witness A: every ordered pair of disjoint two-voter treatment sets,
with the two remaining voters as the shared control; uniform over all
such labelled allocations (P042-E001). -/
def sixAllocations : Finset (Finset (Fin 6) × Finset (Fin 6)) :=
  ((Finset.univ.powersetCard 2) ×ˢ (Finset.univ.powersetCard 2)).filter
    (fun a => Disjoint a.1 a.2)

/-- The no-mail shared control in witness A, following the single control
described on p. 36; the numerical population is a constructed example. -/
def sixControl (a : Finset (Fin 6) × Finset (Fin 6)) : Finset (Fin 6) :=
  Finset.univ \ (a.1 ∪ a.2)

/-- Group turnout mean in the six-voter construction; group size is exactly two. -/
def sixGroupMean (s : Finset (Fin 6)) : ℚ := (∑ i ∈ s, sixOutcome i 0) / 2

/-- Treatment-1 minus control turnout contrast (P042-T1 A). -/
def sixD1 (a : Finset (Fin 6) × Finset (Fin 6)) : ℚ :=
  sixGroupMean a.1 - sixGroupMean (sixControl a)

/-- Treatment-2 minus the same control turnout contrast (P042-T1 A). -/
def sixD2 (a : Finset (Fin 6) × Finset (Fin 6)) : ℚ :=
  sixGroupMean a.2 - sixGroupMean (sixControl a)

/-- Every voter has zero effect under either mail treatment: sharp null in
P042-T1 A, not an empirical assertion about the paper's studies. -/
theorem six_sharp_null (i : Fin 6) (g : Fin 3) : sixOutcome i g = sixOutcome i 0 := rfl

/-- P042-T1 A: complete randomization has exactly 90 allocations, with two
subjects in each labelled arm and disjoint treatment sets. -/
theorem six_design : sixAllocations.card = 90 ∧
    ∀ a ∈ sixAllocations, a.1.card = 2 ∧ a.2.card = 2 ∧
      Disjoint a.1 a.2 ∧ (sixControl a).card = 2 := by
  constructor
  · decide +kernel
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨hprod,hdis⟩
    rcases Finset.mem_product.mp hprod with ⟨h1,h2⟩
    have hc1 := (Finset.mem_powersetCard.mp h1).2
    have hc2 := (Finset.mem_powersetCard.mp h2).2
    refine ⟨hc1,hc2,hdis,?_⟩
    rw [sixControl, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_union_of_disjoint hdis, hc1,hc2]
    norm_num

/-- Integer turnout count in an arm of witness A, an exact computational
representation of the fixed zero/one outcomes (P042-E001). -/
def sixTurnoutCount (s : Finset (Fin 6)) : ℤ := (s.filter (fun i => i.val < 3)).card

/-- Twice the first turnout contrast in witness A, as an integer. -/
def sixNumerator1 (a : Finset (Fin 6) × Finset (Fin 6)) : ℤ :=
  sixTurnoutCount a.1 - sixTurnoutCount (sixControl a)

/-- Twice the second turnout contrast in witness A, as an integer. -/
def sixNumerator2 (a : Finset (Fin 6) × Finset (Fin 6)) : ℤ :=
  sixTurnoutCount a.2 - sixTurnoutCount (sixControl a)

/-- Exact integer sufficient statistics of the 90 complete randomizations in
P042-T1 A; this avoids repeated rational centering during kernel evaluation. -/
theorem six_integer_moments :
    (∑ a ∈ sixAllocations, sixNumerator1 a) = 0 ∧
    (∑ a ∈ sixAllocations, sixNumerator2 a) = 0 ∧
    (∑ a ∈ sixAllocations, (sixNumerator1 a)^2) = 108 ∧
    (∑ a ∈ sixAllocations, (sixNumerator2 a)^2) = 108 ∧
    (∑ a ∈ sixAllocations, sixNumerator1 a*sixNumerator2 a) = 54 ∧
    (∑ a ∈ sixAllocations, (sixNumerator1 a+sixNumerator2 a)^2) = 324 := by
  decide +kernel

/-- The integer computation represents the actual turnout contrasts of
P042-T1 A, not an unrelated covariance matrix. -/
theorem six_contrast_numerators (a : Finset (Fin 6) × Finset (Fin 6)) :
    sixD1 a = (sixNumerator1 a:ℚ)/2 ∧ sixD2 a = (sixNumerator2 a:ℚ)/2 := by
  have hg (s : Finset (Fin 6)) : sixGroupMean s = (sixTurnoutCount s:ℚ)/2 := by
    simp [sixGroupMean, sixOutcome, sixTurnoutCount, Finset.sum_boole]
  simp only [sixD1, sixD2, hg, sixNumerator1, sixNumerator2, Int.cast_sub]
  constructor <;> ring

/-- P042-T1 A1-A3 and A5: exhaustive exact randomization means, marginal
variances, shared-control covariance and pooled variance. -/
theorem six_moments :
    rationalMean sixAllocations sixD1 = 0 ∧
    rationalMean sixAllocations sixD2 = 0 ∧
    rationalVariance sixAllocations sixD1 = 3/10 ∧
    rationalVariance sixAllocations sixD2 = 3/10 ∧
    rationalCovariance sixAllocations sixD1 sixD2 = 3/20 ∧
    rationalVariance sixAllocations (fun a => (sixD1 a + sixD2 a)/2) = 9/40 ∧
    rationalMean sixAllocations (fun a => ((sixD1 a + sixD2 a)/2)^2) = 9/40 := by
  rcases six_integer_moments with ⟨hn1,hn2,hs1,hs2,hc,hm⟩
  have hn1q : (∑ a ∈ sixAllocations, (sixNumerator1 a:ℚ)) = 0 := by exact_mod_cast hn1
  have hn2q : (∑ a ∈ sixAllocations, (sixNumerator2 a:ℚ)) = 0 := by exact_mod_cast hn2
  have hs1q : (∑ a ∈ sixAllocations, (sixNumerator1 a:ℚ)^2) = 108 := by exact_mod_cast hs1
  have hs2q : (∑ a ∈ sixAllocations, (sixNumerator2 a:ℚ)^2) = 108 := by exact_mod_cast hs2
  have hcq : (∑ a ∈ sixAllocations, (sixNumerator1 a:ℚ)*(sixNumerator2 a:ℚ)) = 54 :=
    by exact_mod_cast hc
  have hmq : (∑ a ∈ sixAllocations, ((sixNumerator1 a:ℚ)+(sixNumerator2 a:ℚ))^2) = 324 :=
    by exact_mod_cast hm
  have he1 : rationalMean sixAllocations sixD1 = 0 := by
    unfold rationalMean
    simp_rw [(six_contrast_numerators _).1]
    rw [← Finset.sum_div, hn1q]
    norm_num
  have he2 : rationalMean sixAllocations sixD2 = 0 := by
    unfold rationalMean
    simp_rw [(six_contrast_numerators _).2]
    rw [← Finset.sum_div, hn2q]
    norm_num
  have hv1 : rationalVariance sixAllocations sixD1 = 3/10 := by
    unfold rationalVariance
    rw [he1]
    simp only [sub_zero]
    unfold rationalMean
    simp_rw [(six_contrast_numerators _).1, div_pow]
    rw [← Finset.sum_div, hs1q, six_design.1]
    norm_num
  have hv2 : rationalVariance sixAllocations sixD2 = 3/10 := by
    unfold rationalVariance
    rw [he2]
    simp only [sub_zero]
    unfold rationalMean
    simp_rw [(six_contrast_numerators _).2, div_pow]
    rw [← Finset.sum_div, hs2q, six_design.1]
    norm_num
  have hcov : rationalCovariance sixAllocations sixD1 sixD2 = 3/20 := by
    unfold rationalCovariance
    rw [he1,he2]
    simp only [sub_zero]
    unfold rationalMean
    simp_rw [(six_contrast_numerators _).1, (six_contrast_numerators _).2, div_mul_div_comm]
    rw [← Finset.sum_div, hcq, six_design.1]
    norm_num
  have hpool (a) : (sixD1 a+sixD2 a)/2 =
      ((sixNumerator1 a:ℚ)+(sixNumerator2 a:ℚ))/4 := by
    rw [(six_contrast_numerators _).1, (six_contrast_numerators _).2]
    ring
  have hpoolmean : rationalMean sixAllocations (fun a => (sixD1 a+sixD2 a)/2) = 0 := by
    unfold rationalMean
    simp_rw [hpool]
    rw [← Finset.sum_div, Finset.sum_add_distrib, hn1q,hn2q]
    norm_num
  have hpoolsecond : rationalMean sixAllocations (fun a => ((sixD1 a+sixD2 a)/2)^2) = 9/40 := by
    unfold rationalMean
    simp_rw [hpool, div_pow]
    rw [← Finset.sum_div, hmq, six_design.1]
    norm_num
  refine ⟨he1,he2,hv1,hv2,hcov,?_,hpoolsecond⟩
  unfold rationalVariance
  rw [hpoolmean]
  simp only [sub_zero]
  exact hpoolsecond

/-- P042-T1 A4-A5: the exact finite-population witness violates the variance
assigned by inverse-marginal-variance pooling; true variance is 3/2 times 1/W. -/
theorem six_counterexample :
    normalizedWeight (fun _ : Fin 2 => (3:ℝ)/10) 0 = 1/2 ∧
    normalizedWeight (fun _ : Fin 2 => (3:ℝ)/10) 1 = 1/2 ∧
    diagonalVariance (fun _ : Fin 2 => (3:ℝ)/10) = 3/20 ∧
    (totalWeight (fun _ : Fin 2 => (3:ℝ)/10))⁻¹ = 3/20 ∧
    rationalVariance sixAllocations (fun a => (sixD1 a + sixD2 a)/2) =
      (3/2:ℚ)*(3/20) ∧
    (3/20:ℚ) < rationalVariance sixAllocations (fun a => (sixD1 a + sixD2 a)/2) := by
  rcases six_moments with ⟨_, _, _, _, _, h, _⟩
  norm_num [normalizedWeight, precisionWeight, totalWeight, diagonalVariance,
    Fin.sum_univ_succ, h]

/-- P042-T2 (i): every fixed precision weight is positive and normalized
weights sum to one, without any dependence condition. -/
theorem precision_weights {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ) (hv : ∀ j, 0 < v j) :
    0 < totalWeight v ∧ (∀ j, 0 < normalizedWeight v j) ∧
      ∑ j, normalizedWeight v j = 1 := by
  classical
  have hW : 0 < totalWeight v :=
    Finset.sum_pos (fun j _ => inv_pos.mpr (hv j)) Finset.univ_nonempty
  refine ⟨hW, fun j => div_pos (inv_pos.mpr (hv j)) hW, ?_⟩
  simp only [normalizedWeight, ← Finset.sum_div]
  change totalWeight v / totalWeight v = 1
  exact div_self (ne_of_gt hW)

/-- P042-T2 (iii): the diagonal part of precision-weighted variance is 1/W;
this calculation does not assert that off-diagonal covariances vanish. -/
theorem precision_diagonal {ι : Type*} [Fintype ι] [Nonempty ι]
    (v : ι → ℝ) (hv : ∀ j, 0 < v j) : diagonalVariance v = (totalWeight v)⁻¹ := by
  classical
  have hW := (precision_weights v hv).1
  have hterm (j : ι) : normalizedWeight v j ^ 2 * v j =
      precisionWeight v j / (totalWeight v)^2 := by
    dsimp [normalizedWeight, precisionWeight]
    field_simp [ne_of_gt (hv j), ne_of_gt hW]
    <;> ring
  simp_rw [diagonalVariance, hterm, ← Finset.sum_div]
  change totalWeight v / (totalWeight v)^2 = (totalWeight v)⁻¹
  field_simp [ne_of_gt hW]
  <;> ring

section GeneralProbability
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- P042-T2 (i): pooling preserves the fixed weighted mean of the individual
effects; covariances do not enter the expectation. -/
theorem pooled_mean (a : ι → ℝ) (D : ι → Ω → ℝ) (hD : ∀ j, MemLp (D j) 2 μ) :
    (∫ ω, pooled a D ω ∂μ) = ∑ j, a j * (∫ ω, D j ω ∂μ) := by
  classical
  unfold pooled
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro j _
    exact (hD j).integrable (by norm_num) |>.const_mul _

/-- P042-T2 (ii): the variance of any fixed linear combination is the full
covariance quadratic form, for arbitrary real coefficients and finite second
moments. No independence or common-effect assumption is added. -/
theorem pooled_variance (a : ι → ℝ) (D : ι → Ω → ℝ) (hD : ∀ j, MemLp (D j) 2 μ) :
    variance (pooled a D) μ = covarianceForm a (fun j k => covariance (D j) (D k) μ) := by
  classical
  unfold pooled covarianceForm
  rw [variance_fun_sum (fun j => (hD j).const_mul (a j))]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- P042-T2 (iv), first assertion: uncorrelated treatment arms and a shared
uncorrelated control induce covariance exactly equal to the control variance. -/
theorem shared_control_covariance (A B C : Ω → ℝ)
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) (hC : MemLp C 2 μ)
    (hAB : covariance A B μ = 0) (hAC : covariance A C μ = 0)
    (hBC : covariance B C μ = 0) :
    covariance (fun ω => A ω - C ω) (fun ω => B ω - C ω) μ = variance C μ := by
  rw [covariance_fun_sub_fun_sub hA hC hB hC, hAB, hAC,
    covariance_comm C B, hBC, covariance_self hC.aemeasurable]
  ring

/-- P042-T2 (vi), second equality: variance of a difference retains the
between-pool covariance, as required for the comparison on p. 31. -/
theorem difference_variance (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (fun ω => X ω - Y ω) μ =
      variance X μ + variance Y μ - 2 * covariance X Y μ := by
  rw [variance_fun_sub hX hY]
  ring
end GeneralProbability

/-! Exact two-study calculation for Note 5. -/

/-- Note 5 (p. 40) says "a weighted average effect of 1.720 percentage points".
The two deposited input effects are (58247/25000,21649/25000);
these digits are not printed by the paper. -/
def roboEffects : Fin 2 → ℝ := ![58247/25000, 21649/25000]

/-- Standard errors (1741/3125,40891/50000) of "Robo SP1" and "Robo SP2",
P042-E002; exact deposited decimals. -/
def roboSE : Fin 2 → ℝ := ![1741/3125, 40891/50000]

/-- Fixed marginal variances of the Note 5 pair for precision weighting (p. 31). -/
def roboVariances (j : Fin 2) : ℝ := (roboSE j)^2

/-- Declared fixed-effects weighted average of the Note 5 pair (p. 40). -/
def roboFixedMean : ℝ := ∑ j, normalizedWeight roboVariances j * roboEffects j

/-- Diagonal-only variance of the Note 5 fixed-effects average; the corrected
interval treats the two studies as uncorrelated, explicitly a modelling condition. -/
def roboFixedVariance : ℝ := (totalWeight roboVariances)⁻¹

/-- Cochran Q for the two-study alternative method (P042-E002),
not named in the printed article. -/
def roboQ : ℝ := ∑ j, precisionWeight roboVariances j * (roboEffects j - roboFixedMean)^2

/-- DerSimonian-Laird moment denominator, an alternative to the declared
fixed-effects scheme (P042-E002). -/
def roboC : ℝ := totalWeight roboVariances -
  (∑ j, (precisionWeight roboVariances j)^2) / totalWeight roboVariances

/-- DerSimonian-Laird between-study variance estimate for k=2 (P042-E002),
not a method declared by the paper. -/
def roboTauSq : ℝ := max 0 ((roboQ - 1) / roboC)

/-- Alternative random-effects variances v_i + tau^2 of the Note 5 pair. -/
def roboRandomVariances (j : Fin 2) : ℝ := roboVariances j + roboTauSq

/-- Alternative DerSimonian-Laird pooled mean for the two Note 5 rows. -/
def roboRandomMean : ℝ := ∑ j, normalizedWeight roboRandomVariances j * roboEffects j

/-- Alternative DerSimonian-Laird variance for the two Note 5 rows. -/
def roboRandomVariance : ℝ := (totalWeight roboRandomVariances)⁻¹

/-- P042-T3 (i) and T4 (i): exact fixed-effects inputs, total weight, pooled
mean and variance of the two deposited Note 5 rows. -/
theorem robo_fixed_exact :
    roboVariances 0 = 3031081/9765625 ∧
    roboVariances 1 = 1672073881/2500000000 ∧
    totalWeight roboVariances = 23906548994140625/5068191371295361 ∧
    roboFixedMean = 114191974724271/61200765425000 ∧
    roboFixedVariance = 5068191371295361/23906548994140625 := by
  norm_num [roboVariances, roboSE, totalWeight, precisionWeight, normalizedWeight,
    roboFixedMean, roboFixedVariance, roboEffects, Fin.sum_univ_succ]

/-- P042-T3 (i): the fixed-effects mean rounds to 1.866 and lies above the
entire rounding bin for the printed 1.720, so the declared calculation refutes it. -/
theorem robo_fixed_counterexample :
    (18655:ℝ)/10000 < roboFixedMean ∧ roboFixedMean < 18665/10000 ∧
    (17205:ℝ)/10000 < roboFixedMean := by
  rw [robo_fixed_exact.2.2.2.1]
  norm_num

/-- P042-T3 (ii) and T4 (iv): exact DerSimonian-Laird computation, including
positive heterogeneity variance, mean and variance for the two Note 5 inputs. -/
theorem robo_random_exact :
    roboQ = 5357654416/2448030617 ∧ 1 < roboQ ∧
    roboC = 5000000000/2448030617 ∧
    roboTauSq = 2909623799/5000000000 ∧
    precisionWeight roboRandomVariances 0 = 5000000000/4461537271 ∧
    precisionWeight roboRandomVariances 1 = 5000000000/6253771561 ∧
    roboRandomMean = 12592252377/7319600000 ∧
    roboRandomVariance = 27901434903721350031/53576544160000000000 := by
  norm_num [roboQ, roboC, roboTauSq, roboVariances, roboSE, totalWeight, precisionWeight,
    normalizedWeight, roboFixedMean, roboEffects, roboRandomMean, roboRandomVariance,
    roboRandomVariances, Fin.sum_univ_succ, max_eq_right]

/-- P042-T4 (i): corrected fixed-effects point estimate rounds to 1.866. -/
theorem robo_fixed_rounding : (18655:ℝ)/10000 ≤ roboFixedMean ∧
    roboFixedMean < 18665/10000 := by
  exact ⟨le_of_lt robo_fixed_counterexample.1, robo_fixed_counterexample.2.1⟩

/-- P042-T3 (ii): the alternative DerSimonian-Laird point estimate rounds
to the Note 5 value 1.720. Numerical agreement does not establish historical intent. -/
theorem robo_random_rounding : (17195:ℝ)/10000 ≤ roboRandomMean ∧
    roboRandomMean < 17205/10000 := by
  rw [robo_random_exact.2.2.2.2.2.2.1]
  norm_num

/-- Exact square-root enclosure, used to certify the interval endpoints of
Note 5 with rational arithmetic rather than an approximate normal quantile. -/
theorem sqrt_enclosure (v l u : ℝ) (hv : 0 ≤ v) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlv : l^2 < v) (hvu : v < u^2) : l < Real.sqrt v ∧ Real.sqrt v < u := by
  have hs := Real.sq_sqrt hv
  have hn := Real.sqrt_nonneg v
  constructor <;> nlinarith

/-- P042-T4 (ii): for all multipliers in [1.9599,1.96], the corrected
fixed-effects interval rounds to (0.963,2.768). No assertion about the accuracy
of a normal approximation or independence of the historical studies is made. -/
theorem robo_fixed_interval (z : ℝ) (hzlo : 19599/10000 ≤ z) (hzhi : z ≤ 49/25) :
    9625/10000 ≤ roboFixedMean - z * Real.sqrt roboFixedVariance ∧
    roboFixedMean - z * Real.sqrt roboFixedVariance < 9635/10000 ∧
    27675/10000 ≤ roboFixedMean + z * Real.sqrt roboFixedVariance ∧
    roboFixedMean + z * Real.sqrt roboFixedVariance < 27685/10000 := by
  have hs : (4604347:ℝ)/10000000 < Real.sqrt roboFixedVariance ∧
      Real.sqrt roboFixedVariance < 4604348/10000000 := by
    rw [robo_fixed_exact.2.2.2.2]
    apply sqrt_enclosure <;> norm_num
  have hlo := mul_le_mul hzlo hs.1.le (by norm_num : (0:ℝ) ≤ 4604347/10000000)
    (by linarith : 0 ≤ z)
  have hhi := mul_le_mul hzhi hs.2.le (Real.sqrt_nonneg roboFixedVariance)
    (by norm_num : (0:ℝ) ≤ 49/25)
  rw [robo_fixed_exact.2.2.2.1]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- P042-T3 (i): neither endpoint of the fixed-effects interval rounds to the
printed Note 5 endpoints 0.306 and 3.135, for any z in [1.9599,1.96]. -/
theorem robo_fixed_endpoint_counterexample (z : ℝ)
    (hzlo : 19599/10000 ≤ z) (hzhi : z ≤ 49/25) :
    9625/10000 < roboFixedMean - z * Real.sqrt roboFixedVariance ∧
    (3065:ℝ)/10000 < 9625/10000 ∧
    roboFixedMean + z * Real.sqrt roboFixedVariance < 27685/10000 ∧
    (27685:ℝ)/10000 < 31345/10000 := by
  have hs : Real.sqrt roboFixedVariance < (4604348:ℝ)/10000000 := by
    rw [robo_fixed_exact.2.2.2.2]
    exact (sqrt_enclosure _ (4604347/10000000) (4604348/10000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  have hhi := mul_le_mul hzhi hs.le (Real.sqrt_nonneg roboFixedVariance)
    (by norm_num : (0:ℝ) ≤ 49/25)
  refine ⟨?_, by norm_num, (robo_fixed_interval z hzlo hzhi).2.2.2, by norm_num⟩
  rw [robo_fixed_exact.2.2.2.1]
  linarith

/-- P042-T4 (iii): the repaired fixed-effects lower endpoint is positive for
every multiplier between zero and 1.96; Note 5's positive-effect description survives. -/
theorem robo_fixed_positive (z : ℝ) (hzlo : 0 ≤ z) (hzhi : z ≤ 49/25) :
    0 < roboFixedMean - z * Real.sqrt roboFixedVariance := by
  have hs : Real.sqrt roboFixedVariance < (4604348:ℝ)/10000000 := by
    rw [robo_fixed_exact.2.2.2.2]
    exact (sqrt_enclosure _ (4604347/10000000) (4604348/10000000)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2
  have hhi := mul_le_mul hzhi hs.le (Real.sqrt_nonneg roboFixedVariance)
    (by norm_num : (0:ℝ) ≤ 49/25)
  rw [robo_fixed_exact.2.2.2.1]
  linarith

/-- P042-T3 (ii) and T4 (iv): for all multipliers in [1.9599,1.96], the
DerSimonian-Laird interval rounds to the Note 5 endpoints (0.306,3.135). -/
theorem robo_random_interval (z : ℝ) (hzlo : 19599/10000 ≤ z) (hzhi : z ≤ 49/25) :
    3055/10000 ≤ roboRandomMean - z * Real.sqrt roboRandomVariance ∧
    roboRandomMean - z * Real.sqrt roboRandomVariance < 3065/10000 ∧
    31345/10000 ≤ roboRandomMean + z * Real.sqrt roboRandomVariance ∧
    roboRandomMean + z * Real.sqrt roboRandomVariance < 31355/10000 := by
  have hs : (7216488:ℝ)/10000000 < Real.sqrt roboRandomVariance ∧
      Real.sqrt roboRandomVariance < 7216489/10000000 := by
    rw [robo_random_exact.2.2.2.2.2.2.2]
    apply sqrt_enclosure <;> norm_num
  have hlo := mul_le_mul hzlo hs.1.le (by norm_num : (0:ℝ) ≤ 7216488/10000000)
    (by linarith : 0 ≤ z)
  have hhi := mul_le_mul hzhi hs.2.le (Real.sqrt_nonneg roboRandomVariance)
    (by norm_num : (0:ℝ) ≤ 49/25)
  rw [robo_random_exact.2.2.2.2.2.2.1]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-! Further general repair statements; all use actual joint covariance. -/

/-- Splitting a symmetric quadratic form into diagonal and unordered-pair
terms, the finite algebra behind P042-T2 (ii). -/
theorem covariance_form_decomposition {J : ℕ} (a : Fin J → ℝ)
    (Sigma : Fin J → Fin J → ℝ) (hSigma : ∀ j k, Sigma j k = Sigma k j) :
    covarianceForm a Sigma = (∑ j, a j ^ 2 * Sigma j j) + 2 * offDiagonal a Sigma := by
  classical
  have hsplit (j k : Fin J) : a j*a k*Sigma j k =
      (if j = k then a j^2*Sigma j j else 0) +
      (if j < k then a j*a k*Sigma j k else 0) +
      (if k < j then a j*a k*Sigma j k else 0) := by
    rcases lt_trichotomy j k with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst k
      simp [pow_two]
    · simp [h, (ne_of_lt h).symm, not_lt_of_ge h.le]
  have hlower : (∑ j, ∑ k, if k < j then a j*a k*Sigma j k else 0) =
      ∑ j, ∑ k, if j < k then a j*a k*Sigma j k else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> try rfl
    rw [hSigma k j]
    ring
  calc
    covarianceForm a Sigma = ∑ j, ∑ k,
      ((if j = k then a j^2*Sigma j j else 0) +
        (if j < k then a j*a k*Sigma j k else 0) +
        (if k < j then a j*a k*Sigma j k else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      exact hsplit j k
    _ = (∑ j, a j^2*Sigma j j) + 2*offDiagonal a Sigma := by
      simp only [Finset.sum_add_distrib]
      rw [hlower]
      simp [offDiagonal, Finset.sum_filter] <;> ring

section FurtherProbability
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- P042-T2 (ii)-(iii): the corrected precision-weighted variance is 1/W plus
the omitted weighted covariances; equality with 1/W holds exactly when that
off-diagonal sum is zero. -/
theorem corrected_precision_variance {J : ℕ} (hJ : 0 < J) (D : Fin J → Ω → ℝ)
    (hD : ∀ j, MemLp (D j) 2 μ) (hv : ∀ j, 0 < variance (D j) μ) :
    let v := fun j => variance (D j) μ
    let a := normalizedWeight v
    let Sigma := fun j k => covariance (D j) (D k) μ
    variance (pooled a D) μ = (totalWeight v)⁻¹ + 2 * offDiagonal a Sigma ∧
    (variance (pooled a D) μ = (totalWeight v)⁻¹ ↔ offDiagonal a Sigma = 0) := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  dsimp
  have hdiag : (∑ j, normalizedWeight (fun j => variance (D j) μ) j ^ 2 *
      covariance (D j) (D j) μ) = diagonalVariance (fun j => variance (D j) μ) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [covariance_self (hD j).aemeasurable]
  have hid := pooled_variance μ (normalizedWeight (fun j => variance (D j) μ)) D hD
  rw [covariance_form_decomposition _ _ (fun j k => covariance_comm (D j) (D k)),
    hdiag, precision_diagonal _ hv] at hid
  refine ⟨hid, ?_⟩
  rw [hid]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

/-- P042-T2 (iii): pairwise uncorrelated effect estimates are sufficient for
the diagonal-only variance; this is a sufficient hypothesis absent from p. 31. -/
theorem uncorrelated_precision_variance {J : ℕ} (hJ : 0 < J)
    (D : Fin J → Ω → ℝ) (hD : ∀ j, MemLp (D j) 2 μ)
    (hv : ∀ j, 0 < variance (D j) μ)
    (hunc : ∀ j k, j ≠ k → covariance (D j) (D k) μ = 0) :
    variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ =
      (totalWeight (fun j => variance (D j) μ))⁻¹ := by
  classical
  apply (corrected_precision_variance μ hJ D hD hv).2.mpr
  unfold offDiagonal
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro k hk
  dsimp only
  rw [hunc j k (ne_of_lt (Finset.mem_filter.mp hk).2)]
  ring

/-- P042-T2 (iii): nonnegative off-diagonal covariances, one strictly positive,
make the true precision-weighted variance strictly greater than 1/W. -/
theorem positive_covariance_inflation {J : ℕ} (hJ : 0 < J)
    (D : Fin J → Ω → ℝ) (hD : ∀ j, MemLp (D j) 2 μ)
    (hv : ∀ j, 0 < variance (D j) μ)
    (hnn : ∀ j k, j ≠ k → 0 ≤ covariance (D j) (D k) μ)
    (hpos : ∃ j k, j < k ∧ 0 < covariance (D j) (D k) μ) :
    (totalWeight (fun j => variance (D j) μ))⁻¹ <
      variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  let a := normalizedWeight (fun j => variance (D j) μ)
  have ha (j : Fin J) : 0 < a j := (precision_weights _ hv).2.1 j
  have hterm (j k : Fin J) (hjk : j < k) :
      0 ≤ a j*a k*covariance (D j) (D k) μ :=
    mul_nonneg (mul_nonneg (ha j).le (ha k).le) (hnn j k (ne_of_lt hjk))
  rcases hpos with ⟨j,k,hjk,hc⟩
  have hoff : 0 < offDiagonal a (fun j k => covariance (D j) (D k) μ) := by
    apply Finset.sum_pos'
    · intro i _
      apply Finset.sum_nonneg
      intro l hl
      exact hterm i l (Finset.mem_filter.mp hl).2
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      apply Finset.sum_pos'
      · intro l hl
        exact hterm j l (Finset.mem_filter.mp hl).2
      · exact ⟨k, by simp [hjk], mul_pos (mul_pos (ha j) (ha k)) hc⟩
  rw [(corrected_precision_variance μ hJ D hD hv).1]
  change _ < _ + 2*offDiagonal a _
  linarith

/-- P042-T2 (v): the absolute covariance bound for the positive marginal
standard deviations in H1. This is independent of the pooling weights. -/
theorem covariance_abs_bound (X Y : Ω → ℝ) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hvs : variance X μ = s^2) (hvt : variance Y μ = t^2) :
    |covariance X Y μ| ≤ s*t := by
  have hm := variance_nonneg (fun ω => t * X ω - s * Y ω) μ
  have hp := variance_nonneg (fun ω => t * X ω + s * Y ω) μ
  rw [variance_fun_sub (hX.const_mul t) (hY.const_mul s),
    variance_const_mul, variance_const_mul, covariance_const_mul_left,
    covariance_const_mul_right, hvs, hvt] at hm
  rw [variance_fun_add (hX.const_mul t) (hY.const_mul s),
    variance_const_mul, variance_const_mul, covariance_const_mul_left,
    covariance_const_mul_right, hvs, hvt] at hp
  have hst : 0 < s*t := mul_pos hs ht
  have hminus : 0 ≤ (s*t)*(s*t-covariance X Y μ) := by nlinarith [hm]
  have hplus : 0 ≤ (s*t)*(s*t+covariance X Y μ) := by nlinarith [hp]
  have hm' := nonneg_of_mul_nonneg_right hminus hst
  have hp' := nonneg_of_mul_nonneg_right hplus hst
  rw [abs_le]
  constructor <;> linarith

/-- P042-T2 (v): for any nonnegative fixed weights, the variance is bounded
by the square of the weighted sum of marginal standard errors; in particular
this holds for the strictly positive precision weights. -/
theorem pooled_variance_upper_bound {ι : Type*} [Fintype ι]
    (a s : ι → ℝ) (D : ι → Ω → ℝ) (hD : ∀ j, MemLp (D j) 2 μ)
    (ha : ∀ j, 0 ≤ a j) (hs : ∀ j, 0 < s j)
    (hvs : ∀ j, variance (D j) μ = (s j)^2) :
    variance (pooled a D) μ ≤ (∑ j, a j * s j)^2 := by
  classical
  rw [pooled_variance μ a D hD]
  calc
    covarianceForm a (fun j k => covariance (D j) (D k) μ)
        ≤ ∑ j, ∑ k, (a j * s j) * (a k * s k) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      have hc := (abs_le.mp (covariance_abs_bound μ (D j) (D k)
        (hD j) (hD k) (s j) (s k) (hs j) (hs k) (hvs j) (hvs k))).2
      have := mul_le_mul_of_nonneg_left hc (mul_nonneg (ha j) (ha k))
      nlinarith [this]
    _ = (∑ j, a j * s j)^2 := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

/-- P042-T2 (v), equality case: perfectly aligned centered estimates with
standard errors s_j and one zero-mean unit-variance variable attain the bound. -/
theorem pooled_rank_one_equality {ι : Type*} [Fintype ι]
    (a s : ι → ℝ) (D : ι → Ω → ℝ) (Z : Ω → ℝ)
    (hD : ∀ j, MemLp (D j) 2 μ) (hZ : MemLp Z 2 μ)
    (hmean : (∫ ω, Z ω ∂μ) = 0) (hvar : variance Z μ = 1)
    (hcenter : ∀ j, (fun ω => D j ω - (∫ x, D j x ∂μ)) =ᵐ[μ]
      (fun ω => s j * Z ω)) :
    variance (pooled a D) μ = (∑ j, a j*s j)^2 := by
  classical
  have hZsq : (∫ ω, (Z ω)^2 ∂μ) = 1 := by
    rw [variance_eq_sub hZ, hmean] at hvar
    simpa using hvar
  have hc (j k : ι) : covariance (D j) (D k) μ = s j*s k := by
    unfold covariance
    calc
      (∫ ω, (D j ω-(∫ x, D j x ∂μ))*(D k ω-(∫ x, D k x ∂μ)) ∂μ) =
          ∫ ω, (s j*s k)*(Z ω)^2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hcenter j, hcenter k] with ω hj hk
        rw [hj,hk]
        ring
      _ = s j*s k := by rw [integral_const_mul, hZsq, mul_one]
  rw [pooled_variance μ a D hD]
  simp_rw [covarianceForm, hc]
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring


/-- Within-pool precision weights for a subset of estimates; used in the
nonadvocacy/advocacy comparison printed on p. 31. -/
noncomputable def subsetWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ι) (v : ι → ℝ) (j : ι) : ℝ :=
  if j ∈ P then (v j)⁻¹ / (∑ k ∈ P, (v k)⁻¹) else 0

/-- P042-T2 (vi), first equality: the difference of the two disjoint pooled
means has the signed-coefficient covariance quadratic form, including all
between-pool terms. The statement allows arbitrary nonempty disjoint pools. -/
theorem pooled_difference_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N A : Finset ι) (hN : N.Nonempty) (hA : A.Nonempty) (hdis : Disjoint N A)
    (D : ι → Ω → ℝ) (hD : ∀ j, MemLp (D j) 2 μ)
    (hv : ∀ j, 0 < variance (D j) μ) :
    let v := fun j => variance (D j) μ
    let aN := subsetWeight N v
    let aA := subsetWeight A v
    let b := fun j => aN j - aA j
    variance (fun ω => pooled aN D ω - pooled aA D ω) μ =
      covarianceForm b (fun j k => covariance (D j) (D k) μ) := by
  dsimp
  convert pooled_variance μ
    (fun j => subsetWeight N (fun j => variance (D j) μ) j -
      subsetWeight A (fun j => variance (D j) μ) j) D hD using 1
  congr 1
  ext ω
  simp [pooled, sub_mul, Finset.sum_sub_distrib]

end FurtherProbability

/-! Independent-arm and finite-population portions of the covariance repair. -/

/-- Arm sample mean of fixed size n in P042-T2 (iv), for the
sampling model used to explain the single control described on p. 36. -/
def armSampleMean {Ω : Type*} {n : ℕ} (X : Fin n → Ω → ℝ) : Ω → ℝ :=
  fun ω => (∑ i, X i ω)/(n:ℝ)

/-- Correlation is covariance divided by the product of marginal standard
deviations, P042-T2 (iv); this notation is not printed in the paper. -/
noncomputable def effectCorrelation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) : ℝ :=
  covariance X Y μ / (Real.sqrt (variance X μ) * Real.sqrt (variance Y μ))

/-- Sample means of finite-second-moment observations have finite second
moments, a finite lemma for P042-T2 (iv). -/
theorem arm_sample_mean_memLp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    (X : Fin n → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ) :
    MemLp (armSampleMean X) 2 μ := by
  have heq : (∑ i, X i) = (fun ω => ∑ i, X i ω) := by
    funext ω
    simp only [Finset.sum_apply]
  have hs : MemLp (fun ω => ∑ i, X i ω) 2 μ := by
    rw [← heq]
    exact memLp_finsetSum' Finset.univ (fun i _ => hX i)
  unfold armSampleMean
  simp_rw [div_eq_mul_inv]
  exact hs.mul_const ((n:ℝ)⁻¹)

/-- P042-T2 (iv), finite lemma: an arm of n pairwise independent observations
with common variance sigma² has mean variance sigma²/n. -/
theorem arm_sample_mean_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (hn : 0 < n)
    (X : Fin n → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (sigmaSq : ℝ) (hvar : ∀ i, variance (X i) μ = sigmaSq) :
    variance (armSampleMean X) μ = sigmaSq/(n:ℝ) := by
  classical
  have hs : variance (fun ω => ∑ i, X i ω) μ = (n:ℝ)*sigmaSq := by
    rw [variance_fun_sum hX]
    calc
      (∑ i, ∑ j, covariance (X i) (X j) μ) = ∑ _i : Fin n, sigmaSq := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_eq_single i]
        · rw [covariance_self (hX i).aemeasurable, hvar]
        · intro j _ hji
          exact (hind hji.symm).covariance_eq_zero (hX i) (hX j)
        · simp
      _ = (n:ℝ)*sigmaSq := by simp
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  unfold armSampleMean
  simp only [div_eq_mul_inv]
  rw [variance_mul_const, hs]
  field_simp

/-- P042-T2 (iv), finite lemma: means of cross-arm independent observations
are uncorrelated, without imposing independence between the contrasts themselves. -/
theorem arm_sample_means_uncorrelated {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n m : ℕ}
    (X : Fin n → Ω → ℝ) (Y : Fin m → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ) (hY : ∀ j, MemLp (Y j) 2 μ)
    (hind : ∀ i j, IndepFun (X i) (Y j) μ) :
    covariance (armSampleMean X) (armSampleMean Y) μ = 0 := by
  unfold armSampleMean
  rw [covariance_fun_div_left, covariance_fun_div_right,
    covariance_fun_sum_fun_sum hX hY]
  have hzero (i : Fin n) (j : Fin m) : covariance (X i) (Y j) μ = 0 :=
    (hind i j).covariance_eq_zero (hX i) (hY j)
  simp_rw [hzero]
  simp

/-- P042-T2 (iv), algebraic lemma: the equal-observation-variance arm moments
imply the specified shared-control correlation, with positive arm sizes. -/
theorem shared_control_correlation_from_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (D1 D2 : Ω → ℝ) (sigmaSq n0 n1 n2 : ℝ)
    (hs : 0 < sigmaSq) (h0 : 0 < n0) (h1 : 0 < n1) (h2 : 0 < n2)
    (hv1 : variance D1 μ = sigmaSq*(1/n1+1/n0))
    (hv2 : variance D2 μ = sigmaSq*(1/n2+1/n0))
    (hc : covariance D1 D2 μ = sigmaSq/n0) :
    effectCorrelation μ D1 D2 = Real.sqrt (n1*n2/((n1+n0)*(n2+n0))) := by
  have hv1p : 0 < sigmaSq*(1/n1+1/n0) := by positivity
  have hv2p : 0 < sigmaSq*(1/n2+1/n0) := by positivity
  unfold effectCorrelation
  rw [hv1,hv2,hc]
  have hr : 0 ≤ (sigmaSq/n0)/
      (Real.sqrt (sigmaSq*(1/n1+1/n0))*Real.sqrt (sigmaSq*(1/n2+1/n0))) := by positivity
  symm
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) hr).mpr
  rw [div_pow, mul_pow, Real.sq_sqrt hv1p.le, Real.sq_sqrt hv2p.le]
  field_simp [ne_of_gt hs, ne_of_gt h0, ne_of_gt h1, ne_of_gt h2,
    ne_of_gt (add_pos h1 h0), ne_of_gt (add_pos h2 h0), ne_of_gt hv1p, ne_of_gt hv2p]
  <;> ring

/-- P042-T2 (iv), full independent-observation model: all observations in
the three disjoint arms are pairwise independent, have common variance sigma²,
and finite second moments. Contrasts reuse exactly the same control mean. -/
theorem independent_arm_shared_control {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n0 n1 n2 : ℕ}
    (hn0 : 0 < n0) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (X : (Fin n0 ⊕ (Fin n1 ⊕ Fin n2)) → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hind : Pairwise (fun i j => IndepFun (X i) (X j) μ))
    (sigmaSq : ℝ) (hsigma : 0 < sigmaSq) (hvar : ∀ i, variance (X i) μ = sigmaSq) :
    let C := armSampleMean (fun i => X (Sum.inl i))
    let A := armSampleMean (fun i => X (Sum.inr (Sum.inl i)))
    let B := armSampleMean (fun i => X (Sum.inr (Sum.inr i)))
    let D1 := fun ω => A ω - C ω
    let D2 := fun ω => B ω - C ω
    variance D1 μ = sigmaSq * (1/(n1:ℝ) + 1/(n0:ℝ)) ∧
    variance D2 μ = sigmaSq * (1/(n2:ℝ) + 1/(n0:ℝ)) ∧
    covariance D1 D2 μ = sigmaSq/(n0:ℝ) ∧
    effectCorrelation μ D1 D2 = Real.sqrt
      ((n1:ℝ)*(n2:ℝ)/(((n1:ℝ)+(n0:ℝ))*((n2:ℝ)+(n0:ℝ)))) := by
  let C : Ω → ℝ := armSampleMean (fun i : Fin n0 => X (Sum.inl i))
  let A : Ω → ℝ := armSampleMean (fun i : Fin n1 => X (Sum.inr (Sum.inl i)))
  let B : Ω → ℝ := armSampleMean (fun i : Fin n2 => X (Sum.inr (Sum.inr i)))
  let D1 := fun ω => A ω-C ω
  let D2 := fun ω => B ω-C ω
  change variance D1 μ = _ ∧ variance D2 μ = _ ∧ covariance D1 D2 μ = _ ∧
    effectCorrelation μ D1 D2 = _
  have hC := arm_sample_mean_memLp μ (fun i : Fin n0 => X (Sum.inl i))
    (fun i => hX (Sum.inl i))
  have hA := arm_sample_mean_memLp μ (fun i : Fin n1 => X (Sum.inr (Sum.inl i)))
    (fun i => hX (Sum.inr (Sum.inl i)))
  have hB := arm_sample_mean_memLp μ (fun i : Fin n2 => X (Sum.inr (Sum.inr i)))
    (fun i => hX (Sum.inr (Sum.inr i)))
  have hvC : variance C μ = sigmaSq/(n0:ℝ) :=
    arm_sample_mean_variance μ hn0 _ (fun i => hX (Sum.inl i))
      (fun _ _ h => hind (by simpa using h)) sigmaSq (fun i => hvar (Sum.inl i))
  have hvA : variance A μ = sigmaSq/(n1:ℝ) :=
    arm_sample_mean_variance μ hn1 _ (fun i => hX (Sum.inr (Sum.inl i)))
      (fun _ _ h => hind (by simpa using h)) sigmaSq (fun i => hvar (Sum.inr (Sum.inl i)))
  have hvB : variance B μ = sigmaSq/(n2:ℝ) :=
    arm_sample_mean_variance μ hn2 _ (fun i => hX (Sum.inr (Sum.inr i)))
      (fun _ _ h => hind (by simpa using h)) sigmaSq (fun i => hvar (Sum.inr (Sum.inr i)))
  have hAB : covariance A B μ = 0 := arm_sample_means_uncorrelated μ _ _
    (fun i => hX (Sum.inr (Sum.inl i))) (fun i => hX (Sum.inr (Sum.inr i)))
    (fun _ _ => hind (by simp))
  have hAC : covariance A C μ = 0 := arm_sample_means_uncorrelated μ _ _
    (fun i => hX (Sum.inr (Sum.inl i))) (fun i => hX (Sum.inl i))
    (fun _ _ => hind (by simp))
  have hBC : covariance B C μ = 0 := arm_sample_means_uncorrelated μ _ _
    (fun i => hX (Sum.inr (Sum.inr i))) (fun i => hX (Sum.inl i))
    (fun _ _ => hind (by simp))
  have hD1 : variance D1 μ = sigmaSq*(1/(n1:ℝ)+1/(n0:ℝ)) := by
    rw [variance_fun_sub hA hC, hAC, hvA, hvC]
    ring
  have hD2 : variance D2 μ = sigmaSq*(1/(n2:ℝ)+1/(n0:ℝ)) := by
    rw [variance_fun_sub hB hC, hBC, hvB, hvC]
    ring
  have hcov : covariance D1 D2 μ = sigmaSq/(n0:ℝ) := by
    rw [shared_control_covariance μ A B C hA hB hC hAB hAC hBC, hvC]
  refine ⟨hD1,hD2,hcov, ?_⟩
  apply shared_control_correlation_from_moments μ D1 D2 sigmaSq (n0:ℝ) (n1:ℝ) (n2:ℝ)
    hsigma (by exact_mod_cast hn0) (by exact_mod_cast hn1) (by exact_mod_cast hn2) hD1 hD2 hcov

/-- P042-T2 (vii): three equal-weight contrasts form the only nonzero
off-diagonal block; the added variance is 2a²(c12+c13+c23). The free covariance
parameters are not certified historical covariances of the article's estimates. -/
theorem three_contrast_block {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {J : ℕ} (hJ : 0 < J)
    (D : Fin J → Ω → ℝ) (hD : ∀ j, MemLp (D j) 2 μ)
    (hv : ∀ j, 0 < variance (D j) μ) (e : Fin 3 ↪ Fin J)
    (a c12 c13 c23 : ℝ)
    (ha : ∀ g, normalizedWeight (fun j => variance (D j) μ) (e g) = a)
    (hblock : ∀ j k, j ≠ k → covariance (D j) (D k) μ =
      if (j = e 0 ∧ k = e 1) ∨ (j = e 1 ∧ k = e 0) then c12 else
      if (j = e 0 ∧ k = e 2) ∨ (j = e 2 ∧ k = e 0) then c13 else
      if (j = e 1 ∧ k = e 2) ∨ (j = e 2 ∧ k = e 1) then c23 else 0) :
    variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ =
      (totalWeight (fun j => variance (D j) μ))⁻¹ + 2*a^2*(c12+c13+c23) ∧
    (c12 = c13 → c13 = c23 →
      variance (pooled (normalizedWeight (fun j => variance (D j) μ)) D) μ =
        (totalWeight (fun j => variance (D j) μ))⁻¹ + 6*a^2*c12) := by
  classical
  letI : Nonempty (Fin J) := ⟨⟨0,hJ⟩⟩
  let v := fun j => variance (D j) μ
  let w := normalizedWeight v
  have he01 : e 0 ≠ e 1 := e.injective.ne (by decide)
  have he02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have he12 : e 1 ≠ e 2 := e.injective.ne (by decide)
  have hpoint (j k : Fin J) : w j*w k*covariance (D j) (D k) μ =
      (if j = k then w j^2*v j else 0) +
      (if j = e 0 then if k = e 1 then w j*w k*c12 else 0 else 0) +
      (if j = e 1 then if k = e 0 then w j*w k*c12 else 0 else 0) +
      (if j = e 0 then if k = e 2 then w j*w k*c13 else 0 else 0) +
      (if j = e 2 then if k = e 0 then w j*w k*c13 else 0 else 0) +
      (if j = e 1 then if k = e 2 then w j*w k*c23 else 0 else 0) +
      (if j = e 2 then if k = e 1 then w j*w k*c23 else 0 else 0) := by
    by_cases hjk : j = k
    · subst k
      rw [covariance_self (hD j).aemeasurable]
      by_cases h0 : j = e 0 <;> by_cases h1 : j = e 1 <;> by_cases h2 : j = e 2 <;>
        simp_all [v, pow_two]
    · rw [hblock j k hjk]
      by_cases hj0 : j = e 0 <;> by_cases hj1 : j = e 1 <;> by_cases hj2 : j = e 2 <;>
        by_cases hk0 : k = e 0 <;> by_cases hk1 : k = e 1 <;> by_cases hk2 : k = e 2 <;>
        simp_all
  have hcalc : variance (pooled w D) μ = diagonalVariance v + 2*a^2*(c12+c13+c23) := by
    rw [pooled_variance μ w D hD]
    unfold covarianceForm
    simp_rw [hpoint, Finset.sum_add_distrib]
    simp [diagonalVariance, w, v, ha] <;> ring
  rw [precision_diagonal v hv] at hcalc
  refine ⟨hcalc, ?_⟩
  intro h12 h23
  rw [hcalc, h12, h23]
  ring

/-- Real-valued uniform expectation on a finite randomization space:
"assigned at random with known probability" (p. 28). -/
def finiteExpectation {Ω : Type*} (s : Finset Ω) (X : Ω → ℝ) : ℝ :=
  (∑ ω ∈ s, X ω)/(s.card:ℝ)

/-- Real finite randomization covariance for P042-T2 (viii). -/
def finiteCovariance {Ω : Type*} (s : Finset Ω) (X Y : Ω → ℝ) : ℝ :=
  finiteExpectation s (fun ω =>
    (X ω - finiteExpectation s X)*(Y ω - finiteExpectation s Y))

/-- Complete randomization into three disjoint labelled groups of sizes n_g,
possibly leaving other units unassigned. Label 3 means unused; every admissible
allocation is equiprobable, P042-T2 (viii). -/
def completeThreeAllocations (N : ℕ) (n : Fin 3 → ℕ) : Finset (Fin N → Fin 4) :=
  Finset.univ.filter (fun z => ∀ g : Fin 3,
    (Finset.univ.filter (fun i => z i = Fin.castLE (by decide : 3 ≤ 4) g)).card = n g)

/-- Finite-population mean potential outcome under one condition; Note 2,
pp. 39-40 supplies the potential-outcome definition, but does not print this formula. -/
def populationMean {N : ℕ} (Y : Fin N → ℝ) : ℝ := (∑ i, Y i)/(N:ℝ)

/-- S_gh, finite-population covariance with denominator N-1, P042-T2 (viii)
and P042-E001; this notation is not printed in the article. -/
def populationCovariance {N : ℕ} (Y V : Fin N → ℝ) : ℝ :=
  (∑ i, (Y i-populationMean Y)*(V i-populationMean V))/((N-1:ℕ):ℝ)

/-- P042-T2 (viii), finite algebraic lemma: the covariance of the two
individual-effect vectors is S_jk-S_j0-S_0k+S_00. This identity needs no
randomization assumptions; the remaining sampling identity is stated separately. -/
theorem population_effect_covariance {N : ℕ} (Y0 Y1 Y2 : Fin N → ℝ) :
    populationCovariance (fun i => Y1 i-Y0 i) (fun i => Y2 i-Y0 i) =
      populationCovariance Y1 Y2 - populationCovariance Y1 Y0 -
      populationCovariance Y0 Y2 + populationCovariance Y0 Y0 := by
  unfold populationCovariance populationMean
  simp only [Finset.sum_sub_distrib, sub_div]
  conv_rhs => rw [← sub_div, ← sub_div, ← add_div]
  congr 1
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Observed arm mean for complete three-arm randomization in P042-T2 (viii). -/
def randomizedArmMean {N : ℕ} (n : Fin 3 → ℕ) (Y : Fin N → Fin 3 → ℝ)
    (g : Fin 3) (z : Fin N → Fin 4) : ℝ :=
  (∑ i, if z i = Fin.castLE (by decide : 3 ≤ 4) g then Y i g else 0)/(n g:ℝ)


/-! Binomial witness B: exact finite probability masses and coverage counts. -/

/-- Computational binomial coefficient, certified equal to Nat.choose below.
P042-T1 B uses Binomial(100,1/2); descending factorial evaluation avoids the
exponential recursion of Pascal's rule while keeping every proof kernel checked. -/
def exactChoose (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

/-- Computational representation is exactly the usual binomial coefficient
in P042-T1 B's specified mass and coverage sum. -/
theorem exactChoose_eq (n k : ℕ) : exactChoose n k = n.choose k := by
  exact (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- Binomial(n,1/2) probability mass for a turnout count; witness B, P042-E001.
This is a constructed experiment, not the article's observed counts. -/
def binomialMass (n : ℕ) (x : Fin (n+1)) : ℚ := (exactChoose n x.val:ℚ)/2^n

/-- Exact expectation for one 100-voter arm of witness B. -/
def binomialArmExpectation (f : Fin 101 → ℚ) : ℚ := ∑ x, binomialMass 100 x * f x

/-- Independent product of the control and two treatment Binomial(100,1/2)
arms; P042-T1 B. The order of arguments is control, treatment 1, treatment 2. -/
def binomialTripleExpectation (f : Fin 101 → Fin 101 → Fin 101 → ℚ) : ℚ :=
  ∑ x0, binomialMass 100 x0 *
    ∑ x1, binomialMass 100 x1 * ∑ x2, binomialMass 100 x2 * f x0 x1 x2

/-- Variance on the independent binomial product distribution of witness B. -/
def binomialTripleVariance (f : Fin 101 → Fin 101 → Fin 101 → ℚ) : ℚ :=
  binomialTripleExpectation (fun x0 x1 x2 =>
    (f x0 x1 x2 - binomialTripleExpectation f)^2)

/-- Centered covariance on the independent binomial product distribution,
the actual shared-control covariance asserted in P042-T1 B1. -/
def binomialTripleCovariance (f g : Fin 101 → Fin 101 → Fin 101 → ℚ) : ℚ :=
  binomialTripleExpectation (fun x0 x1 x2 =>
    (f x0 x1 x2-binomialTripleExpectation f)*(g x0 x1 x2-binomialTripleExpectation g))

/-- Shared-control treatment contrasts in turnout proportions, P042-T1 B. -/
def binomialD1 (x0 x1 _x2 : Fin 101) : ℚ := ((x1.val:ℚ)-(x0.val:ℚ))/100

/-- Second treatment contrast uses exactly the same control count, P042-T1 B. -/
def binomialD2 (x0 _x1 x2 : Fin 101) : ℚ := ((x2.val:ℚ)-(x0.val:ℚ))/100

/-- Equal precision-weighted mean M in the binomial witness, P042-T1 B2. -/
def binomialPooled (x0 x1 x2 : Fin 101) : ℚ := (binomialD1 x0 x1 x2 + binomialD2 x0 x1 x2)/2

/-- P042-T1 B: each arm is a normalized nonnegative finite Binomial mass,
with mean 50 and second moment 2525 (variance 25), computed exactly. -/
theorem binomial_arm_moments :
    (∀ x, 0 ≤ binomialMass 100 x) ∧
    binomialArmExpectation (fun _ => 1) = 1 ∧
    binomialArmExpectation (fun x => (x.val:ℚ)) = 50 ∧
    binomialArmExpectation (fun x => (x.val:ℚ)^2) = 2525 := by
  constructor
  · intro x
    exact div_nonneg (Nat.cast_nonneg _) (by positivity)
  · decide +kernel

/-- Linearity of the explicit independent-arm expectation, finite lemma for
P042-T1 B1-B3. -/
theorem binomial_expectation_add (f g : Fin 101 → Fin 101 → Fin 101 → ℚ) :
    binomialTripleExpectation (fun x y z => f x y z + g x y z) =
      binomialTripleExpectation f + binomialTripleExpectation g := by
  simp [binomialTripleExpectation, mul_add, Finset.sum_add_distrib]

/-- Subtraction commutes with the independent-arm expectation (P042-T1 B). -/
theorem binomial_expectation_sub (f g : Fin 101 → Fin 101 → Fin 101 → ℚ) :
    binomialTripleExpectation (fun x y z => f x y z - g x y z) =
      binomialTripleExpectation f - binomialTripleExpectation g := by
  simp [binomialTripleExpectation, mul_sub, Finset.sum_sub_distrib]

/-- Fixed scaling commutes with binomial-arm expectation (P042-T1 B). -/
theorem binomial_expectation_mul (b : ℚ) (f : Fin 101 → Fin 101 → Fin 101 → ℚ) :
    binomialTripleExpectation (fun x y z => b*f x y z) = b*binomialTripleExpectation f := by
  simp [binomialTripleExpectation, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

/-- Fixed division commutes with binomial-arm expectation (P042-T1 B). -/
theorem binomial_expectation_div (f : Fin 101 → Fin 101 → Fin 101 → ℚ) (b : ℚ) :
    binomialTripleExpectation (fun x y z => f x y z/b) = binomialTripleExpectation f/b := by
  have hp : (fun x y z => f x y z/b) = (fun x y z => b⁻¹*f x y z) := by
    funext x y z
    rw [div_eq_mul_inv, mul_comm]
  rw [hp, binomial_expectation_mul]
  ring

/-- Products of functions on the three independent arms factor into their
three expectations. This proves independence in the explicit finite model. -/
theorem binomial_expectation_tensor (f g h : Fin 101 → ℚ) :
    binomialTripleExpectation (fun x y z => f x*g y*h z) =
      binomialArmExpectation f * binomialArmExpectation g * binomialArmExpectation h := by
  simp [binomialTripleExpectation, binomialArmExpectation, Finset.mul_sum,
    Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_comm, mul_left_comm]

/-- The first coordinate has its declared binomial marginal, finite lemma
for the exact shared-control construction. -/
theorem binomial_marginal_zero (f : Fin 101 → ℚ) :
    binomialTripleExpectation (fun x _ _ => f x) = binomialArmExpectation f := by
  have hn := binomial_arm_moments.2.1
  simpa [hn] using binomial_expectation_tensor f (fun _ => 1) (fun _ => 1)

/-- The first treatment coordinate has its declared binomial marginal. -/
theorem binomial_marginal_one (f : Fin 101 → ℚ) :
    binomialTripleExpectation (fun _ y _ => f y) = binomialArmExpectation f := by
  have hn := binomial_arm_moments.2.1
  simpa [hn] using binomial_expectation_tensor (fun _ => 1) f (fun _ => 1)

/-- The second treatment coordinate has its declared binomial marginal. -/
theorem binomial_marginal_two (f : Fin 101 → ℚ) :
    binomialTripleExpectation (fun _ _ z => f z) = binomialArmExpectation f := by
  have hn := binomial_arm_moments.2.1
  simpa [hn] using binomial_expectation_tensor (fun _ => 1) (fun _ => 1) f

/-- P042-T1 B1-B3: exact moments of the independent binomial-arm contrasts,
including nonzero covariance and the true pooled variance 3/800. -/
theorem binomial_shared_control_moments :
    binomialTripleExpectation binomialD1 = 0 ∧
    binomialTripleExpectation binomialD2 = 0 ∧
    binomialTripleVariance binomialD1 = 1/200 ∧
    binomialTripleVariance binomialD2 = 1/200 ∧
    binomialTripleCovariance binomialD1 binomialD2 = 1/400 ∧
    binomialTripleVariance (fun x0 _ _ => (x0.val:ℚ)/100) = 1/400 ∧
    (∀ x0 x1 x2, binomialPooled x0 x1 x2 =
      ((x1.val:ℚ)+(x2.val:ℚ)-2*(x0.val:ℚ))/200) ∧
    binomialTripleExpectation binomialPooled = 0 ∧
    binomialTripleVariance binomialPooled = 3/800 ∧
    (1/400:ℚ) < binomialTripleVariance binomialPooled := by
  have hn := binomial_arm_moments.2.1
  have hm := binomial_arm_moments.2.2.1
  have hs := binomial_arm_moments.2.2.2
  have he0 := binomial_marginal_zero (fun x => (x.val:ℚ))
  have he1 := binomial_marginal_one (fun x => (x.val:ℚ))
  have he2 := binomial_marginal_two (fun x => (x.val:ℚ))
  rw [hm] at he0 he1 he2
  have hs0 := binomial_marginal_zero (fun x => (x.val:ℚ)^2)
  have hs1 := binomial_marginal_one (fun x => (x.val:ℚ)^2)
  have hs2 := binomial_marginal_two (fun x => (x.val:ℚ)^2)
  rw [hs] at hs0 hs1 hs2
  have he01 : binomialTripleExpectation (fun x y _ => (x.val:ℚ)*(y.val:ℚ)) = 2500 := by
    have h := binomial_expectation_tensor
      (fun x => (x.val:ℚ)) (fun x => (x.val:ℚ)) (fun _ => 1)
    norm_num [hn, hm] at h
    exact h
  have he02 : binomialTripleExpectation (fun x _ z => (x.val:ℚ)*(z.val:ℚ)) = 2500 := by
    have h := binomial_expectation_tensor
      (fun x => (x.val:ℚ)) (fun _ => 1) (fun x => (x.val:ℚ))
    norm_num [hn, hm] at h
    exact h
  have he12 : binomialTripleExpectation (fun _ y z => (y.val:ℚ)*(z.val:ℚ)) = 2500 := by
    have h := binomial_expectation_tensor
      (fun _ => 1) (fun x => (x.val:ℚ)) (fun x => (x.val:ℚ))
    norm_num [hn, hm] at h
    exact h
  have hd1 : binomialTripleExpectation binomialD1 = 0 := by
    unfold binomialD1
    rw [binomial_expectation_div, binomial_expectation_sub, he1, he0]
    norm_num
  have hd2 : binomialTripleExpectation binomialD2 = 0 := by
    unfold binomialD2
    rw [binomial_expectation_div, binomial_expectation_sub, he2, he0]
    norm_num
  have hv1 : binomialTripleVariance binomialD1 = 1/200 := by
    unfold binomialTripleVariance
    rw [hd1]
    simp only [sub_zero]
    have hp : (fun x y z => (binomialD1 x y z)^2) =
        fun x y z => ((y.val:ℚ)^2+(x.val:ℚ)^2-2*((x.val:ℚ)*(y.val:ℚ)))/10000 := by
      funext x y z
      unfold binomialD1
      ring
    rw [hp, binomial_expectation_div, binomial_expectation_sub,
      binomial_expectation_add, binomial_expectation_mul, hs1, hs0, he01]
    norm_num
  have hv2 : binomialTripleVariance binomialD2 = 1/200 := by
    unfold binomialTripleVariance
    rw [hd2]
    simp only [sub_zero]
    have hp : (fun x y z => (binomialD2 x y z)^2) =
        fun x y z => ((z.val:ℚ)^2+(x.val:ℚ)^2-2*((x.val:ℚ)*(z.val:ℚ)))/10000 := by
      funext x y z
      unfold binomialD2
      ring
    rw [hp, binomial_expectation_div, binomial_expectation_sub,
      binomial_expectation_add, binomial_expectation_mul, hs2, hs0, he02]
    norm_num
  have hcov : binomialTripleExpectation
      (fun x y z => binomialD1 x y z*binomialD2 x y z) = 1/400 := by
    have hp : (fun x y z => binomialD1 x y z*binomialD2 x y z) =
        fun x y z => ((y.val:ℚ)*(z.val:ℚ)-(x.val:ℚ)*(y.val:ℚ)-
          (x.val:ℚ)*(z.val:ℚ)+(x.val:ℚ)^2)/10000 := by
      funext x y z
      unfold binomialD1 binomialD2
      ring
    rw [hp, binomial_expectation_div, binomial_expectation_add,
      binomial_expectation_sub, binomial_expectation_sub, he12, he01, he02, hs0]
    norm_num
  have hpool : ∀ x y z, binomialPooled x y z =
      ((y.val:ℚ)+(z.val:ℚ)-2*(x.val:ℚ))/200 := by
    intro x y z
    unfold binomialPooled binomialD1 binomialD2
    ring
  have hpoolmean : binomialTripleExpectation binomialPooled = 0 := by
    unfold binomialPooled
    rw [binomial_expectation_div, binomial_expectation_add, hd1, hd2]
    norm_num
  have hpoolvar : binomialTripleVariance binomialPooled = 3/800 := by
    unfold binomialTripleVariance
    rw [hpoolmean]
    simp only [sub_zero]
    have hp : (fun x y z => (binomialPooled x y z)^2) =
        fun x y z => ((y.val:ℚ)^2+(z.val:ℚ)^2+4*((x.val:ℚ)^2)+
          2*((y.val:ℚ)*(z.val:ℚ))-4*((x.val:ℚ)*(y.val:ℚ))-
          4*((x.val:ℚ)*(z.val:ℚ)))/40000 := by
      funext x y z
      rw [hpool]
      ring
    rw [hp, binomial_expectation_div]
    simp only [binomial_expectation_sub, binomial_expectation_add,
      binomial_expectation_mul, hs0, hs1, hs2, he01, he02, he12]
    norm_num
  have hcenterCov : binomialTripleCovariance binomialD1 binomialD2 = 1/400 := by
    unfold binomialTripleCovariance
    rw [hd1,hd2]
    simp only [sub_zero]
    exact hcov
  have hcontrolMean : binomialTripleExpectation (fun x0 _ _ => (x0.val:ℚ)/100) =
      1/2 := by
    rw [binomial_expectation_div, he0]
    norm_num
  have hone : binomialTripleExpectation (fun _ _ _ => 1) = 1 := by
    simpa [hn] using binomial_marginal_zero (fun _ => 1)
  have hcontrolVar : binomialTripleVariance (fun x0 _ _ => (x0.val:ℚ)/100) =
      1/400 := by
    unfold binomialTripleVariance
    rw [hcontrolMean]
    have hp : (fun x y z : Fin 101 => ((x.val:ℚ)/100 - 1/2)^2) =
        fun x y z => ((x.val:ℚ)^2-100*(x.val:ℚ)+2500*1)/10000 := by
      funext x y z
      ring
    rw [hp, binomial_expectation_div, binomial_expectation_add,
      binomial_expectation_sub, binomial_expectation_mul, binomial_expectation_mul,
      hs0, he0, hone]
    norm_num
  refine ⟨hd1, hd2, hv1, hv2, hcenterCov, hcontrolVar, hpool, hpoolmean, hpoolvar, ?_⟩
  rw [hpoolvar]
  norm_num

/-- P042-T1 B2-B3: known equal marginal variances give normalized weights
1/2 and reported diagonal variance 1/400; the numerical inflation factor is 3/2. -/
theorem binomial_diagonal :
    normalizedWeight (fun _ : Fin 2 => (1:ℝ)/200) 0 = 1/2 ∧
    normalizedWeight (fun _ : Fin 2 => (1:ℝ)/200) 1 = 1/2 ∧
    diagonalVariance (fun _ : Fin 2 => (1:ℝ)/200) = 1/400 ∧
    (totalWeight (fun _ : Fin 2 => (1:ℝ)/200))⁻¹ = 1/400 ∧
    (3/800:ℚ) = (3/2)*(1/400) := by
  norm_num [normalizedWeight, precisionWeight, totalWeight, diagonalVariance, Fin.sum_univ_succ]

/-- The nominal interval contains the true zero effect if and only if the
absolute pooled contrast is at most z times its standard error (P042-T1 B4-B6). -/
def coversZero (estimate radius : ℝ) : Prop := estimate-radius ≤ 0 ∧ 0 ≤ estimate+radius

/-- Interval containment of zero is an absolute-error inequality, finite
lemma behind P042-T1 B4-B6. -/
theorem covers_zero_iff_abs (estimate radius : ℝ) : coversZero estimate radius ↔
    |estimate| ≤ radius := by
  unfold coversZero
  rw [abs_le]
  constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith

/-- P042-T1 B4: the nominal variance 1/400 yields exactly the radius 49/500. -/
theorem binomial_diagonal_radius : (49/25:ℝ)*Real.sqrt (1/400) = 49/500 := by
  have h : Real.sqrt (1/400:ℝ) = 1/20 := by
    rw [show (1/400:ℝ) = (1/20)^2 by norm_num, Real.sqrt_sq_eq_abs]
    norm_num
  rw [h]
  norm_num

/-- P042-T1 B4 and B6: exact integer coverage thresholds for the nominal
diagonal variance and the repaired true variance, using the multiplier 49/25. -/
theorem binomial_interval_thresholds (x0 x1 x2 : Fin 101) :
    let q : ℤ := (x1.val:ℤ)+(x2.val:ℤ)-2*(x0.val:ℤ)
    (coversZero ((q:ℝ)/200) (49/500) ↔ |q| ≤ 19) ∧
    (coversZero ((q:ℝ)/200) ((49/25)*Real.sqrt (3/800)) ↔ |q| ≤ 24) ∧
    ((24:ℝ)^2 < 200^2*(49/25)^2*(3/800) ∧
      200^2*(49/25)^2*(3/800) < 25^2) := by
  dsimp
  let q : ℤ := (x1.val:ℤ)+(x2.val:ℤ)-2*(x0.val:ℤ)
  have hs : (6123:ℝ)/100000 < Real.sqrt (3/800:ℝ) ∧
      Real.sqrt (3/800:ℝ) < 6124/100000 := by
    apply sqrt_enclosure <;> norm_num
  have hrlo : (24:ℝ)/200 < (49/25)*Real.sqrt (3/800:ℝ) := by linarith [hs.1]
  have hrhi : (49/25:ℝ)*Real.sqrt (3/800:ℝ) < 25/200 := by linarith [hs.2]
  have habs : |(q:ℝ)/200| = (|q|:ℝ)/200 := by
    rw [abs_div, ← Int.cast_abs]
    norm_num
  change (coversZero ((q:ℝ)/200) _ ↔ |q| ≤ 19) ∧
    (coversZero ((q:ℝ)/200) _ ↔ |q| ≤ 24) ∧ _
  refine ⟨?_, ?_, by norm_num⟩
  · rw [covers_zero_iff_abs, habs]
    constructor
    · intro h
      have hlt : (|q|:ℝ) < 20 := by linarith
      have hi : |q| < 20 := by exact_mod_cast hlt
      omega
    · intro h
      have hi : (|q|:ℝ) ≤ 19 := by exact_mod_cast h
      linarith
  · rw [covers_zero_iff_abs, habs]
    constructor
    · intro h
      have hlt : (|q|:ℝ) < 25 := by linarith
      have hi : |q| < 25 := by exact_mod_cast hlt
      omega
    · intro h
      have hi : (|q|:ℝ) ≤ 24 := by exact_mod_cast h
      linarith

/-- Number of binary outcome sequences covered at integer threshold r;
P042-T1 B5-B6. Natural subtraction implements max(0,2x-r); upper endpoint
is min(200,2x+r). The coefficient exactChoose is certified Nat.choose. -/
def coverageCount (r : ℕ) : ℕ :=
  ∑ x ∈ Finset.range 101, exactChoose 100 x *
    ∑ t ∈ Finset.Icc (2*x-r) (min 200 (2*x+r)), exactChoose 200 t

/-- Exact coverage probability K/2^300 on the reduced count distribution
(control Binomial(100,1/2), combined treatment count Binomial(200,1/2)). -/
def binomialCoverage (r : ℕ) : ℚ := (coverageCount r:ℚ)/2^300

/-- P042-T1 B5, finite convolution lemma: the sum of two independent
Binomial(100,1/2) counts has the Binomial(200,1/2) mass, by Vandermonde's
identity. Terms outside the possible count range vanish as binomial coefficients. -/
theorem binomial_convolution (t : ℕ) :
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal t,
      ((exactChoose 100 ij.1:ℚ)/2^100)*((exactChoose 100 ij.2:ℚ)/2^100)) =
      (exactChoose 200 t:ℚ)/2^200 := by
  simp_rw [exactChoose_eq, div_mul_div_comm]
  rw [← Finset.sum_div]
  have hc : (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal t,
      ((100:ℕ).choose ij.1:ℚ)*((100:ℕ).choose ij.2:ℚ)) = ((200:ℕ).choose t:ℚ) := by
    exact_mod_cast (Nat.add_choose_eq 100 100 t).symm
  rw [hc]
  norm_num

/-- P042-T1 B5-B6: the proposed coverage sum has the exact displayed fraction
for threshold 19, lies between 0.888 and 0.889, and exceeds 0.95 for threshold 24.
Its equality with the three-arm probability is a separately stated identity. -/
theorem binomial_coverage_exact :
    binomialCoverage 19 =
      (56571224212801903286613058436266763680981055287737934836552182663205237639665445537726383:ℚ)/2^295 ∧
    (888:ℚ)/1000 < binomialCoverage 19 ∧
    binomialCoverage 19 < 889/1000 ∧ (889:ℚ)/1000 < 95/100 ∧
    (95:ℚ)/100 < binomialCoverage 24 := by
  decide +kernel

/-- P042-T1 B5: the displayed coverage numerator and denominator 2^295
are coprime, so the stated exact fraction is in lowest terms. -/
theorem binomial_coverage_fraction_reduced :
    Nat.Coprime
      56571224212801903286613058436266763680981055287737934836552182663205237639665445537726383
      (2^295) := by
  decide +kernel


/-! Complete randomization and the one-sided contact/CACE reading (P042-T6). -/

/-- Every subset of m subjects is equally likely: complete randomization,
a precise design interpretation of "assigned at random" (p. 28) and the
same-in-expectation assertion (p. 30). -/
def completeAssignments (N m : ℕ) : Finset (Finset (Fin N)) := Finset.univ.powersetCard m

/-- Turnout rate among subjects assigned to treatment (p. 32), with denominator
the fixed number m assigned; used for both potential and observed outcomes. -/
def assignedTreatmentMean {N : ℕ} (m : ℕ) (S : Finset (Fin N)) (U : Fin N → ℝ) : ℝ :=
  (∑ i, if i ∈ S then U i else 0)/(m:ℝ)

/-- Turnout rate among the N-m subjects assigned to control (p. 32). -/
def assignedControlMean {N : ℕ} (m : ℕ) (S : Finset (Fin N)) (U : Fin N → ℝ) : ℝ :=
  (∑ i, if i ∉ S then U i else 0)/((N-m:ℕ):ℝ)

/-- Note 2 (pp. 39-40): "Untreated subjects express their untreated potential
outcome, while treated subjects express their treated potential outcome";
Boolean false/true indexes no treatment/treatment. -/
def assignedOutcome {N : ℕ} (S : Finset (Fin N)) (Y : Fin N → Bool → ℝ) (i : Fin N) : ℝ :=
  if i ∈ S then Y i true else Y i false

/-- Finite-sum linearity used for p. 30's randomization expectation. -/
theorem finite_expectation_sub {Ω : Type*} (s : Finset Ω) (X Y : Ω → ℝ) :
    finiteExpectation s (fun ω => X ω-Y ω) = finiteExpectation s X-finiteExpectation s Y := by
  simp [finiteExpectation, Finset.sum_sub_distrib, sub_div]

/-- Finite-sum linearity used for the turnout and contact rates on p. 32. -/
theorem finite_expectation_sum {Ω ι : Type*} [Fintype ι]
    (s : Finset Ω) (X : ι → Ω → ℝ) :
    finiteExpectation s (fun ω => ∑ i, X i ω) = ∑ i, finiteExpectation s (X i) := by
  unfold finiteExpectation
  rw [Finset.sum_comm, Finset.sum_div]

/-- Multiplication by a fixed coefficient commutes with randomization
expectation, the finite lemma used by the p. 30 and p. 32 readings. -/
theorem finite_expectation_mul {Ω : Type*} (s : Finset Ω) (b : ℝ) (X : Ω → ℝ) :
    finiteExpectation s (fun ω => b*X ω) = b*finiteExpectation s X := by
  simp only [finiteExpectation, ← Finset.mul_sum]
  ring

/-- Division by a fixed arm size commutes with randomization expectation. -/
theorem finite_expectation_div {Ω : Type*} (s : Finset Ω) (b : ℝ) (X : Ω → ℝ) :
    finiteExpectation s (fun ω => X ω/b) = finiteExpectation s X/b := by
  simp only [finiteExpectation, ← Finset.sum_div]
  ring

/-- Constants have their own expectation on a nonempty uniform finite design. -/
theorem finite_expectation_const {Ω : Type*} (s : Finset Ω) (hs : s.Nonempty) (b : ℝ) :
    finiteExpectation s (fun _ => b) = b := by
  have hcard : (s.card:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs.card_pos)
  simp [finiteExpectation, hcard]

/-- Complete randomization assigns each subject to treatment with probability
m/N. This counting lemma supplies the precise design fact behind p. 30. -/
theorem complete_inclusion_probability {N m : ℕ} (hN : 0 < N)
    (hm : 1 ≤ m) (hmN : m ≤ N) (i : Fin N) :
    finiteExpectation (completeAssignments N m) (fun S => if i ∈ S then 1 else 0) =
      (m:ℝ)/(N:ℝ) := by
  have hcard : (completeAssignments N m).card = N.choose m := by
    simp [completeAssignments]
  have hfilter : ((completeAssignments N m).filter (fun S => i ∈ S)).card =
      (N-1).choose (m-1) := by
    simpa [completeAssignments] using
      (Finset.card_filter_powersetCard_subset ({i} : Finset (Fin N)) Finset.univ m
        (by simp) (by simpa using hm))
  have hbin := Nat.add_one_mul_choose_eq (N-1) (m-1)
  have hn' : N-1+1 = N := by omega
  have hm' : m-1+1 = m := by omega
  rw [hn', hm'] at hbin
  have hbinR : (N:ℝ)*((N-1).choose (m-1):ℝ) = (N.choose m:ℝ)*(m:ℝ) := by
    exact_mod_cast hbin
  have hNc : (N:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hchoose : (N.choose m:ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.choose_pos hmN))
  unfold finiteExpectation
  rw [Finset.sum_boole, hfilter, hcard]
  apply (div_eq_div_iff hchoose hNc).mpr
  nlinarith [hbinR]

/-- Exact expectation of either assigned-group mean for an arbitrary fixed
real outcome vector; finite core of the p. 30 potential-outcome assertion. -/
theorem complete_group_mean {N m : ℕ} (hN : 2 ≤ N)
    (hm : 1 ≤ m) (hmN : m ≤ N-1) (U : Fin N → ℝ) :
    finiteExpectation (completeAssignments N m) (fun S => assignedTreatmentMean m S U) =
      populationMean U ∧
    finiteExpectation (completeAssignments N m) (fun S => assignedControlMean m S U) =
      populationMean U := by
  have hNc : (N:ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmc : (m:ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hcm : ((N-m:ℕ):ℝ) ≠ 0 := by exact_mod_cast (by omega : N-m ≠ 0)
  have hNsub : ((N-m:ℕ):ℝ) = (N:ℝ)-(m:ℝ) := by
    exact_mod_cast (Nat.cast_sub (by omega : m ≤ N) :
      ((N-m:ℕ):ℝ) = (N:ℝ)-(m:ℝ))
  have hnonempty : (completeAssignments N m).Nonempty := by
    exact Finset.powersetCard_nonempty.mpr (by simpa using (by omega : m ≤ N))
  have hi (i : Fin N) := complete_inclusion_probability (by omega : 0 < N) hm
    (by omega : m ≤ N) i
  have hci (i : Fin N) :
      finiteExpectation (completeAssignments N m) (fun S => if i ∉ S then 1 else 0) =
        ((N-m:ℕ):ℝ)/(N:ℝ) := by
    have hfun : (fun S : Finset (Fin N) => if i ∉ S then (1:ℝ) else 0) =
        fun S => 1-(if i ∈ S then 1 else 0) := by
      funext S
      by_cases h : i ∈ S <;> simp [h]
    rw [hfun, finite_expectation_sub, finite_expectation_const _ hnonempty, hi, hNsub]
    field_simp
  have htfun (S : Finset (Fin N)) (i : Fin N) :
      (if i ∈ S then U i else 0) = U i*(if i ∈ S then 1 else 0) := by
    by_cases h : i ∈ S <;> simp [h]
  have hcfun (S : Finset (Fin N)) (i : Fin N) :
      (if i ∉ S then U i else 0) = U i*(if i ∉ S then 1 else 0) := by
    by_cases h : i ∈ S <;> simp [h]
  constructor
  · unfold assignedTreatmentMean
    rw [finite_expectation_div, finite_expectation_sum]
    simp_rw [htfun, finite_expectation_mul, hi]
    simp only [populationMean, ← Finset.sum_mul]
    field_simp
  · unfold assignedControlMean
    rw [finite_expectation_div, finite_expectation_sum]
    simp_rw [hcfun, finite_expectation_mul, hci]
    simp only [populationMean, ← Finset.sum_mul]
    field_simp

/-- P042-T6 (a): treatment and control averages of either fixed potential
outcome have expectation equal to its population average under complete
randomization. This also proves unbiasedness of the observed difference. -/
theorem complete_randomization_balance {N m : ℕ} (hN : 2 ≤ N)
    (hm : 1 ≤ m) (hmN : m ≤ N-1) (Y : Fin N → Bool → ℝ) :
    (∀ t : Bool,
      finiteExpectation (completeAssignments N m)
        (fun S => assignedTreatmentMean m S (fun i => Y i t)) = populationMean (fun i => Y i t) ∧
      finiteExpectation (completeAssignments N m)
        (fun S => assignedControlMean m S (fun i => Y i t)) = populationMean (fun i => Y i t)) ∧
    finiteExpectation (completeAssignments N m)
      (fun S => assignedTreatmentMean m S (assignedOutcome S Y) -
        assignedControlMean m S (assignedOutcome S Y)) =
      populationMean (fun i => Y i true - Y i false) := by
  constructor
  · intro t
    exact complete_group_mean hN hm hmN (fun i => Y i t)
  · have ht (S : Finset (Fin N)) :
        assignedTreatmentMean m S (assignedOutcome S Y) =
          assignedTreatmentMean m S (fun i => Y i true) := by
      unfold assignedTreatmentMean
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i ∈ S <;> simp [assignedOutcome, h]
    have hctrl (S : Finset (Fin N)) :
        assignedControlMean m S (assignedOutcome S Y) =
          assignedControlMean m S (fun i => Y i false) := by
      unfold assignedControlMean
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : i ∈ S <;> simp [assignedOutcome, h]
    simp_rw [ht, hctrl]
    rw [finite_expectation_sub, (complete_group_mean hN hm hmN _).1,
      (complete_group_mean hN hm hmN _).2]
    simp [populationMean, Finset.sum_sub_distrib, sub_div]

/-- P. 32 calls Compliers those "who would be contacted if visited or called".
A Boolean c_i identifies this fixed subgroup; its complement is Never-takers. -/
def complierCount {N : ℕ} (c : Fin N → Bool) : ℕ :=
  (Finset.univ.filter (fun i => c i = true)).card

/-- Finite-population share of Compliers, used for the contact-rate identity
of p. 32; a positive count is required in all identification statements. -/
def complierShare {N : ℕ} (c : Fin N → Bool) : ℝ := (complierCount c:ℝ)/(N:ℝ)

/-- Complier average causal effect: "average treatment effect among
'Compliers'" (p. 32), represented as the mean contact effect over c_i=true. -/
def complierEffect {N : ℕ} (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) : ℝ :=
  (∑ i, if c i = true then Y i true - Y i false else 0)/(complierCount c:ℝ)

/-- Assignment effect ITT in the paper's one-sided contact framework (p. 32).
Assignment can affect each subject only by their own contact; potential outcomes
with/without contact are fixed, so this also encodes exclusion and no interference. -/
def assignmentEffect {N : ℕ} (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) : ℝ :=
  populationMean (fun i => Y i (c i) - Y i false)

/-- One-sided noncompliance: a subject receives contact iff assigned to treatment
and a Complier (p. 32). Control subjects are never contacted; outcomes depend on
contact only. These conditions make the framework's implicit assumptions explicit. -/
def contactedOutcome {N : ℕ} (S : Finset (Fin N))
    (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) (i : Fin N) : ℝ :=
  Y i (if i ∈ S then c i else false)

/-- The fraction of the assigned treatment group actually contacted (p. 32). -/
def assignedContactRate {N : ℕ} (m : ℕ) (S : Finset (Fin N)) (c : Fin N → Bool) : ℝ :=
  assignedTreatmentMean m S (fun i => if c i = true then 1 else 0)


/-- P042-T6 (b1): ITT equals the Complier share times CACE in the stated
one-sided, exclusion/no-interference finite-population contact model. -/
theorem itt_complier_identity {N : ℕ} (hN : 0 < N)
    (Y : Fin N → Bool → ℝ) (c : Fin N → Bool) (hc : 0 < complierCount c) :
    assignmentEffect Y c = complierShare c * complierEffect Y c := by
  have hcnt : (complierCount c:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  have hp : ∀ i, Y i (c i)-Y i false =
      if c i = true then Y i true-Y i false else 0 := by
    intro i
    cases h : c i <;> simp [h]
  unfold assignmentEffect populationMean complierShare complierEffect
  simp_rw [hp]
  field_simp
  <;> ring

/-- P042-T6 (b2)-(b3): under complete randomization, the turnout difference
estimates ITT, contact rate estimates the Complier share, and their expectation
ratio equals CACE. This is a ratio of expectations, not an unbiased random ratio. -/
theorem cace_randomization_identity {N m : ℕ} (hN : 2 ≤ N)
    (hm : 1 ≤ m) (hmN : m ≤ N-1) (Y : Fin N → Bool → ℝ)
    (c : Fin N → Bool) (hc : 0 < complierCount c) :
    let S := completeAssignments N m
    let diff := fun s => assignedTreatmentMean m s (contactedOutcome s Y c) -
      assignedControlMean m s (contactedOutcome s Y c)
    finiteExpectation S diff = assignmentEffect Y c ∧
    finiteExpectation S (fun s => assignedContactRate m s c) = complierShare c ∧
    complierEffect Y c = finiteExpectation S diff /
      finiteExpectation S (fun s => assignedContactRate m s c) := by
  dsimp
  let Yassign : Fin N → Bool → ℝ := fun i t => if t then Y i (c i) else Y i false
  have hob (S : Finset (Fin N)) : assignedOutcome S Yassign = contactedOutcome S Y c := by
    ext i
    by_cases h : i ∈ S <;> simp [assignedOutcome, contactedOutcome, Yassign, h]
  have hdiff := (complete_randomization_balance hN hm hmN Yassign).2
  simp_rw [hob] at hdiff
  change finiteExpectation (completeAssignments N m) _ = assignmentEffect Y c at hdiff
  have hcontact : finiteExpectation (completeAssignments N m)
      (fun S => assignedContactRate m S c) = complierShare c := by
    have h := (complete_group_mean hN hm hmN (fun i => if c i = true then 1 else 0)).1
    simpa [assignedContactRate, populationMean, complierShare, complierCount,
      Finset.sum_boole] using h
  refine ⟨hdiff, hcontact, ?_⟩
  rw [hdiff, hcontact, itt_complier_identity (by omega : 0 < N) Y c hc]
  have hcnt : (complierCount c:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  have hNc : (N:ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hshare : complierShare c ≠ 0 := div_ne_zero hcnt hNc
  field_simp

/-- P042-T6 (b4): the p. 32 Michelson illustration, (9.4-7.0)/0.50=4.8,
in percentage-point units; the printed decimals are taken as exact numbers. -/
theorem michelson_cace_example : ((94:ℝ)/10 - 70/10)/(1/2) = 48/10 := by norm_num

end
end AronowAudit.P042
