import SAP.P004b.Defs.WholeW1
import SAP.P004b.Bridge
import AronowAudit.P004.Wave1.DesignLimits.NF
import AronowAudit.P004.Wave1.FiniteConditioning.FC4
import AronowAudit.P004.Wave1.FiniteConditioning.FC8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W1

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section
set_option maxHeartbeats 1000000

/-- The exact three-node validator, including the population projections and all five terms.
Enumerate the eight assignments with Fin.sum_univ_succ and Fintype.sum_bool. First show
all arm marginal means vanish, hence both projection right-hand sides and fits vanish.
The 1-by-1 information matrix is [1/4]. Then enumerate the finite expectations and pairs.
No inverse computation is needed for beta once its right-hand side is zero. -/
def T22_L1 : Prop := threeNodeVarianceWitness

/-- Uniform L2-NED of size -4 survives the corrected own-coin affine transformation.
Use FiniteConditioning.fc8_proof with coefficient
alpha(a)=bit(a)/(N*p)-(1-bit(a))/(N*(1-p)) and the own-coin offset in the expanded
summand. For i : Fin N, N>=1; bound |alpha| by C/N with
C=max(1/p,1/(1-p))>0. Retain psi and use g'_(N,i)=C*g_(N,i)/N, bounded by C*G.
This preserves the same decay exponent and monotonicity of psi. All finite variables
are square integrable. The zero-node row has no i, so imposes no positivity obligation. -/
def T25_L1 : Prop :=
  ∀ (p μ1 μ0 : ℝ) (D : ∀ N, Fin N → Fin N → ℝ) (R : ∀ N, CircleTable N),
    (0 < p ∧ p < 1) → (∀ N i, D N i i = 0) → TableNED p D R →
    TableNED p D (fun N i => expandedCenteredSummand p (R N) μ1 μ0 i)

/-- Deterministic exterior-tail kernel limit for eventually bounded centered arrays.
Adapt Wave1.T26_centered_kernel_split, intersecting the eventual events at the current N.
Take r_N=b_N^(1/6); then r_N/b_N and r_N^3/b_N tend to zero. The split bounds the
absolute form by A^2*C*Cb*(r_N/b_N+r_N^3/b_N)+(L+1)*exteriorEnvelope. Use le_csSup
for each finite tail row, then squeeze_zero'. No probability or overlap assumption
is needed, and no regularity at an irrelevant finite prefix is needed.
Expected size: 100–180 lines, using the existing finite split rather than reproving it. -/
def T26_L1 : Prop :=
  ∀ (D : ∀ N, Fin N → Fin N → ℝ) (a : ∀ N, Fin N → ℝ)
    (K φ : ℝ → ℝ) (b : ℕ → ℝ),
    (∀ᶠ N in atTop, ∀ i j, 0 ≤ D N i j) →
    (∀ᶠ N in atTop, ∑ i, a N i = 0) →
    (∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ N in atTop, ∀ i, |a N i| ≤ A) →
    (∃ Cb : ℝ, 0 < Cb ∧ ∀ᶠ N in atTop, ∀ i s, 0 ≤ s →
      ((ball (D N) i s).card : ℝ) ≤ Cb*(1+s^2)) →
    KernelConditions K → Tendsto b atTop atTop →
    (∀ s, 0 ≤ s → 0 ≤ φ s) →
    (∀ᶠ N in atTop, ∀ i j, |a N i| * |a N j| ≤ φ (D N i j)) →
    (∀ r : ℕ → ℝ, Tendsto r atTop atTop →
      Tendsto (exteriorEnvelope D φ r) atTop (nhds 0)) →
    Tendsto (arrayKernel D a K b) atTop (nhds 0)

/-- Finite inside-ball bounds, the mathematical content of the printed-hypothesis remark.
The diagonal belongs to its ball. Nonnegativity and Finset.single_le_sum give
phi(0)<=the maximum row sum and a_i^2<=that maximum. For the kernel bound, its
support removes pairs outside the ball; apply the triangle inequality, the envelope,
and the bound |K|<=L, then average the row bounds. The real finite supremum exists
because N>0 and its range is finite. No centering, spacing or independence is needed.
Expected size: 80–150 lines of finite sum inequalities and le_csSup/csSup_le. -/
def T26_L2 : Prop :=
  ∀ {N : ℕ} (D : Fin N → Fin N → ℝ) (a : Fin N → ℝ) (K φ : ℝ → ℝ) (b L : ℝ),
    0 < N → (∀ i j, 0 ≤ D i j) → (∀ i, D i i = 0) → 0 < b →
    (∀ s, 0 ≤ s → 0 ≤ φ s) → (∀ i j, |a i| * |a j| ≤ φ (D i j)) →
    (∀ t, 1 < t → K t = 0) → (∀ t, 0 ≤ t → |K t| ≤ L) →
    let S := rowMaximum (fun i => ∑ j ∈ ball D i b, φ (D i j))
    φ 0 ≤ S ∧ rowMaximum (fun i => (a i)^2) ≤ S ∧
    |(∑ i, ∑ j, K (D i j/b)*a i*a j)/(N : ℝ)| ≤ L*S

private theorem projection_linear_eq {N k : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (O : Fin N → Fin k → ℝ) :
    projectionLinearIPW p R O = augmented p R (projectionFits p R O) := by
  funext z
  unfold projectionLinearIPW augmented residualContrast
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem second_moment_terms {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) :
    secondMomentBound p R B g =
      armSecondMoment p R g true + armSecondMoment p R g false + signedPairSecondMoment p R B g := by
  simp only [secondMomentBound, armSecondMoment, signedPairSecondMoment, coin,
    ite_true, Bool.false_eq_true, ite_false, Finset.sum_add_distrib, add_div]

private theorem effect_mean_terms {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ) (hself : ∀ i, i ∈ B i) :
    diagonalEffectSquare p R g + signedPairMeanProduct p R B g = homophilyQ p R B g/N := by
  have hpair (i j : Fin N) :
      (∑ a : Bool, ∑ b : Bool, armSign a*armSign b*(marginal p R i a-g i a)*
        (marginal p R j b-g j b)) = residualEffect p R g i*residualEffect p R g j := by
    simp only [Fintype.sum_bool, armSign, Bool.false_eq_true, ite_false, ite_true,
      residualEffect, nodeEffect]
    ring
  unfold diagonalEffectSquare signedPairMeanProduct homophilyQ
  simp_rw [hpair]
  rw [← add_div, div_div]
  congr 1
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_erase_add _ _ (hself i)]
    ring
  · ring

private theorem expand_variance {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (B : Fin N → Finset (Fin N)) (g : Fin N → Bool → ℝ)
    (hN : 0 < N) (hp : ∀ i, 0 < p i ∧ p i < 1) (hself : ∀ i, i ∈ B i)
    (hout : ∀ i j, j ∉ B i → ¬ sharesSource R i j) : varianceExpansion p R B g := by
  have hv : variance p (augmented p R g) = secondMomentBound p R B g-homophilyQ p R B g/N :=
    AronowAudit.P004.augmented_variance p R B g hN hp hself hout
  have hs := second_moment_terms p R B g
  have hm := effect_mean_terms p R B g hself
  refine ⟨?_, ?_, ?_⟩
  · unfold fiveTermVariance
    linarith
  · rw [show -(∑ i, ∑ j ∈ B i, residualEffect p R g i*residualEffect p R g j)/(N : ℝ)^2 =
      -(homophilyQ p R B g/N) by unfold homophilyQ; rw [div_div]; ring]
    linarith
  · intro hh
    rw [← hs]
    exact AronowAudit.P004.augmented_homophily_bound p R B g hN hp hself hout hh

theorem T22_assembly (h1 : T22_L1) : T22WholeStatement := by
  refine ⟨?_, ?_, h1⟩
  · exact fun p R B g hN hp hself hout => expand_variance p R B g hN hp hself hout
  · intro N k p R B O hN hp _ hself hout
    exact ⟨projection_linear_eq p R O, expand_variance p R B _ hN hp hself hout⟩

private theorem treatment_quadratic_entry (A : Matrix (Fin 2) (Fin 2) ℝ) :
    treatmentQuadratic A = A 1 1 := by
  simp [treatmentQuadratic, treatmentSelector, dotProduct, Matrix.mulVec, Fin.sum_univ_two]

private theorem kernel_neighborhood_sum {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (B : Fin N → Finset (Fin N)) : kernelVariance z e (neighborhoodMatrix B) =
      ∑ i, ∑ j ∈ B i, lambda z i*lambda z j*e i*e j := by
  unfold kernelVariance neighborhoodMatrix
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter,
    Finset.filter_mem_eq_inter, Finset.univ_inter]

private theorem gaussian_quantiles (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    FiniteQuantile (α/2) ∧ FiniteQuantile (1-α/2) ∧
    normalQuantile (α/2) = -normalQuantile (1-α/2) ∧
    normalQuantile (α/2) < 0 ∧ 0 < normalQuantile (1-α/2) := by
  obtain ⟨_, hm, hz, hn, hq, _, _⟩ := AronowAudit.P004.Wave1.DesignLimits.nf_proof
  change StrictMono normalCDF at hm
  change normalCDF 0 = 1/2 at hz
  change ∀ x, normalCDF (-x) = 1-normalCDF x at hn
  change ∀ a, 0 < a → a < 1 → normalCDF (normalQuantile a) = a at hq
  have hlo := hq (α/2) (by linarith) (by linarith)
  have hhi := hq (1-α/2) (by linarith) (by linarith)
  have hs : normalQuantile (α/2) = -normalQuantile (1-α/2) := by
    apply hm.injective
    rw [hlo, hn, hhi]
    ring
  have hpos : 0 < normalQuantile (1-α/2) := hm.lt_iff_lt.mp (by rw [hz, hhi]; linarith)
  have hf (a : ℝ) (ha : normalCDF (normalQuantile a) = a) : FiniteQuantile a := by
    have he : {x : ℝ | a ≤ normalCDF x} = Set.Ici (normalQuantile a) := by
      ext x
      change a ≤ normalCDF x ↔ normalQuantile a ≤ x
      conv_lhs => rw [← ha]
      exact hm.le_iff_le
    rw [FiniteQuantile, he]
    exact ⟨Set.nonempty_Ici, bddBelow_Ici⟩
  exact ⟨hf _ hlo, hf _ hhi, hs, by rw [hs]; linarith, hpos⟩

theorem T23_assembly : T23WholeStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro N phat R B g z hN ha hp
    obtain ⟨he, hs⟩ := AronowAudit.P004.observational_sandwich_identity phat R B g z hN ha.1 ha.2 hp
    refine ⟨AronowAudit.P004.MatrixCompletion.treatment_row z ha.1 ha.2, he,
      treatment_quadratic_entry _, ?_, hs⟩
    change sandwich z _ (neighborhoodMatrix B) 1 1 = _
    rw [show sandwich z _ (neighborhoodMatrix B) 1 1 = kernelVariance z _ (neighborhoodMatrix B) from
      AronowAudit.P004.MatrixCompletion.sandwich_treatment z ha.1 ha.2 _ _]
    exact kernel_neighborhood_sum z _ B
  · intro N k p R B O θ β z _ _
    refine ⟨?_, ?_, fun _ => rfl, rfl⟩
    · intro i
      have he := Real.exp_pos (∑ j, O i j*θ j)
      unfold logisticPropensity
      exact ⟨div_pos he (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩
    · unfold homophilyQ residualEffect
      simp only [Finset.mul_sum]
  · intro α hα hα1
    obtain ⟨hfl, hfu, hs, hlo, hhi⟩ := gaussian_quantiles α hα hα1
    have hev (t : ℝ) :
        ((normalQuantile (α/2) ≤ |t| ∧ |t| ≤ normalQuantile (1-α/2)) ↔
          |t| ≤ normalQuantile (1-α/2)) ∧
        ((|t| ≤ normalQuantile (1-α/2)) ↔
          (normalQuantile (α/2) ≤ t ∧ t ≤ normalQuantile (1-α/2))) := by
      rw [hs]
      exact ⟨AronowAudit.P004.symmetric_critical_event _ t hhi.le, abs_le⟩
    refine ⟨hfl, hfu, hs, hlo, hhi, hev, ?_⟩
    intro N p phat R z Vsah Vhac _ _ _ _ _
    exact ⟨hev _, hev _⟩

theorem T24_assembly : T24WholeStatement := by
  refine ⟨?_, fun N => ⟨eq_comm, Iff.rfl⟩⟩
  intro N z ha
  have hc : armCount z true+armCount z false = N := AronowAudit.P004.MatrixCompletion.counts_total z
  have hn : (0 : ℝ) < N := by linarith [ha.1, ha.2]
  refine ⟨?_, ?_⟩
  · intro e Q
    obtain ⟨hs, hi, hx, hr, hg, hl, hv⟩ := AronowAudit.P004.regression_matrix_identities z ha.1 ha.2 e Q
    change (((designMatrix z).transpose * designMatrix z)⁻¹) 1 1 =
      N/(armCount z true*armCount z false) at hg
    refine ⟨hs, hi, hx, hr, ?_, hl, ?_, ?_, ?_⟩
    · rw [treatment_quadratic_entry]
      exact hg
    · rw [treatment_quadratic_entry, hg]
      field_simp
    · rw [treatment_quadratic_entry]
      exact hv
    · intro _
      unfold effectiveDegreesOfFreedom traceMu traceNu
      ring
  · intro e D h hD hh
    dsimp only
    have hQ : distanceKernel D uniformKernel h = neighborhoodMatrix (fun i => ball D i h) := by
      ext i j
      simp only [distanceKernel, uniformKernel, neighborhoodMatrix, ball, Finset.mem_filter,
        Finset.mem_univ, true_and, div_nonneg (hD i j) hh.le, true_and,
        div_le_one hh]
    refine ⟨hQ, ?_⟩
    rw [hQ, treatment_quadratic_entry,
      show sandwich z e (neighborhoodMatrix (fun i => ball D i h)) 1 1 =
        kernelVariance z e (neighborhoodMatrix (fun i => ball D i h)) from
        AronowAudit.P004.MatrixCompletion.sandwich_treatment z ha.1 ha.2 e _]
    simp only [kernelVariance, leverageKernel, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

private theorem expanded_centered_eq {N : ℕ} (p : ℝ) (R : CircleTable N) (μ1 μ0 : ℝ) (i : Fin N) :
    expandedCenteredSummand p R μ1 μ0 i = centeredSummand (fun _ => p) R μ1 μ0 i := by
  funext z
  unfold expandedCenteredSummand centeredSummand residualContrast
  simp only [ite_true, Bool.false_eq_true, ite_false, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem expanded_printed_eq {N : ℕ} (p : ℝ) (R : CircleTable N) (μ1 μ0 : ℝ) (i : Fin N) :
    expandedPrintedSummand p R μ1 μ0 i = fun z =>
      centeredSummand (fun _ => p) R μ1 μ0 i z + (1/(N : ℝ)-1)*nodeEffect (fun _ => p) R i := by
  funext z
  rw [← expanded_centered_eq]
  unfold expandedPrintedSummand expandedCenteredSummand
  ring

private theorem expanded_conditional {N : ℕ} (p : ℝ) (R : CircleTable N) (μ1 μ0 : ℝ)
    (hp : 0 < p ∧ p < 1) (D : Fin N → Fin N → ℝ) (hD : ∀ i, D i i = 0)
    (i : Fin N) (s : ℝ) (hs : 0 ≤ s) (z : Assignment N) :
    conditionOn (fun _ => p) (ball D i s) (expandedCenteredSummand p R μ1 μ0 i) z =
      (bit (z i)/(N*p)-(1-bit (z i))/(N*(1-p))) *
        conditionOn (fun _ => p) (ball D i s) (R i) z + (μ1-μ0)/N -
        (bit (z i)*μ1/(N*p)-(1-bit (z i))*μ0/(N*(1-p))) - nodeEffect (fun _ => p) R i/N := by
  let α := fun a : Bool => bit a/(N*p)-(1-bit a)/(N*(1-p))
  let β := fun a : Bool => (μ1-μ0)/N -
    (bit a*μ1/(N*p)-(1-bit a)*μ0/(N*(1-p))) - nodeEffect (fun _ => p) R i/N
  have hi : i ∈ ball D i s := by simp [ball, hD, hs]
  have hdep (f : Bool → ℝ) : ∀ x y : Assignment N,
      (∀ j ∈ ball D i s, x j = y j) → f (x i) = f (y i) :=
    fun _ _ h => congrArg f (h i hi)
  have hβ : conditionOn (fun _ => p) (ball D i s) (fun z => β (z i)) z = β (z i) :=
    congrFun (AronowAudit.P004.Wave1.FiniteConditioning.conditionOn_of_depends
      (fun _ => p) (fun _ => hp) (ball D i s) (fun z => β (z i)) (hdep β)) z
  have hF : expandedCenteredSummand p R μ1 μ0 i = fun z => α (z i)*R i z+β (z i) := by
    funext z
    dsimp [expandedCenteredSummand, α, β]
    ring
  rw [hF]
  have hadd : conditionOn (fun _ => p) (ball D i s) (fun z => α (z i)*R i z+β (z i)) z =
      conditionOn (fun _ => p) (ball D i s) (fun z => α (z i)*R i z) z +
        conditionOn (fun _ => p) (ball D i s) (fun z => β (z i)) z :=
    (AronowAudit.P004.Wave1.FiniteConditioning.fc2_proof (fun _ => p) (fun _ => hp) _).2.1 _ _ z
  have hpull : conditionOn (fun _ => p) (ball D i s) (fun z => α (z i)*R i z) z =
      α (z i)*conditionOn (fun _ => p) (ball D i s) (R i) z :=
    (AronowAudit.P004.Wave1.FiniteConditioning.fc2_proof (fun _ => p) (fun _ => hp) _).2.2.2
      (fun z => α (z i)) (R i) (hdep α) z
  rw [hadd, hpull, hβ]
  dsimp [α, β]
  ring

private theorem centered_facts {N : ℕ} (p : ℝ) (R : CircleTable N) (μ1 μ0 : ℝ)
    (hN : 0 < N) (hp : 0 < p ∧ p < 1) :
    (∀ i, expect (fun _ => p) (expandedCenteredSummand p R μ1 μ0 i) = 0) ∧
    (∀ z, (∑ i, expandedCenteredSummand p R μ1 μ0 i z) =
      augmented (fun _ => p) R (fun _ a => if a then μ1 else μ0) z-ame (fun _ => p) R) ∧
    (∀ i, expect (fun _ => p) (expandedPrintedSummand p R μ1 μ0 i) =
      (1/(N : ℝ)-1)*nodeEffect (fun _ => p) R i) := by
  simp only [expanded_centered_eq, expanded_printed_eq]
  exact AronowAudit.P004.centered_summand_identity (fun _ => p) R μ1 μ0 hN (fun _ => hp)

theorem T25_assembly (h1 : T25_L1) : T25WholeStatement := by
  refine ⟨?_, ?_, h1⟩
  · intro N p R μ1 μ0 hN hp
    obtain ⟨hm, hsum, hprinted⟩ := centered_facts p R μ1 μ0 hN hp
    refine ⟨fun i => expanded_centered_eq p R μ1 μ0 i, hm, hsum, ?_, hprinted, ?_⟩
    · intro z
      have hz := (centered_facts p R 0 0 hN hp).2.1 z
      simpa only [augmented, ht, sub_zero, zero_add, ite_self] using hz
    · exact fun D hD i s hs z => expanded_conditional p R μ1 μ0 hp D hD i s hs z
  · dsimp only
    intro i
    have hmarg (a : Bool) : marginal (fun _ => (1/2 : ℝ)) (fun j (z : Assignment 8) => bit (z j)) i a = bit a := by
      have hm : marginal (fun _ => (1/2 : ℝ)) (fun j (z : Assignment 8) => bit (z j)) i a =
          expect (fun _ => 1/2) (fun z => bit ((Function.update z i a) i)) :=
        AronowAudit.P004.marginal_is_marginalization (fun _ : Fin 8 => (1/2 : ℝ))
          (fun j (z : Assignment 8) => bit (z j)) i a (fun _ => by norm_num)
      rw [hm]
      simp only [Function.update_self]
      exact AronowAudit.P004.expect_const (fun _ : Fin 8 => (1/2 : ℝ)) (bit a)
    have htau : nodeEffect (fun _ => 1/2) (fun i (z : Assignment 8) => bit (z i)) i = 1 := by
      unfold nodeEffect
      rw [hmarg true, hmarg false]
      norm_num [bit]
    obtain ⟨hm, _, hp⟩ := centered_facts (1/2) (fun i (z : Assignment 8) => bit (z i)) 0 0 (by decide) (by norm_num)
    exact ⟨htau, by rw [hp i, htau]; norm_num, hm i⟩

private theorem auxiliary_radius (b : ℕ → ℝ) (hb : Tendsto b atTop atTop) :
    Tendsto (fun N => (b N)^(1/6 : ℝ)) atTop atTop ∧
    Tendsto (fun N => ((b N)^(1/6 : ℝ))^3/b N) atTop (nhds 0) := by
  refine ⟨(tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/6)).comp hb, ?_⟩
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp hb
  apply ht.congr'
  filter_upwards [hb.eventually (eventually_gt_atTop 0)] with N hN
  rw [← Real.rpow_mul_natCast hN.le, ← Real.rpow_sub_one hN.ne']
  norm_num

private theorem kernel_consequences (D : ∀ N, Fin N → Fin N → ℝ) (a : ∀ N, Fin N → ℝ)
    (K : ℝ → ℝ) (b : ℕ → ℝ) (h : Tendsto (arrayKernel D a K b) atTop (nhds 0)) :
    kernelLimitConclusion D a K b := by
  refine ⟨h, h.liminf_eq, ?_⟩
  intro ε hε
  filter_upwards [h.eventually (eventually_gt_nhds (by linarith : -ε < (0 : ℝ)))] with N hN
  simpa only [zero_sub] using hN.le

private theorem forced_centered_bounds {N : ℕ} (p : Fin N → ℝ) (R : CircleTable N)
    (hN : 0 < N) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (M : ℝ) (hR : ∀ i z, |R i z| ≤ M) :
    (∑ i, forcedCentered p R i) = 0 ∧ ∀ i, |forcedCentered p R i| ≤ 4*M := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hw (z : Assignment N) : 0 ≤ designWeight p z := by
    apply Finset.prod_nonneg
    intro i _
    cases z i <;> simp only [coin, Bool.false_eq_true, ite_false, ite_true]
    · linarith [(hp i).2]
    · exact (hp i).1
  have hnorm : (∑ z : Assignment N, designWeight p z) = 1 := AronowAudit.P004.design_normalized p
  have hm (i : Fin N) (a : Bool) : |forcedMarginal p R i a| ≤ M := by
    unfold forcedMarginal expect
    calc
      |∑ z, designWeight p z*R i (Function.update z i a)| ≤
          ∑ z, |designWeight p z*R i (Function.update z i a)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ z, designWeight p z*|R i (Function.update z i a)| := by
        simp only [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ z, designWeight p z*M := Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hR i _) (hw z))
      _ = M := by rw [← Finset.sum_mul, hnorm, one_mul]
  have htau (i : Fin N) : |forcedEffect p R i| ≤ 2*M :=
    (abs_sub _ _).trans (by linarith [hm i true, hm i false])
  have hame : |forcedAME p R| ≤ 2*M := by
    rw [forcedAME, abs_div, abs_of_pos hn]
    apply (div_le_iff₀ hn).mpr
    calc
      |∑ i, forcedEffect p R i| ≤ ∑ i, |forcedEffect p R i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, 2*M := Finset.sum_le_sum (fun i _ => htau i)
      _ = _ := by simp [mul_comm]
  constructor
  · simp only [forcedCentered, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, forcedAME]
    field_simp [hn.ne']
    ring
  · intro i
    exact (abs_sub _ _).trans (by linarith [htau i])

private theorem row_maximum_zero {N : ℕ} : rowMaximum (fun _ : Fin N => (0 : ℝ)) = 0 := by
  by_cases hN : 0 < N
  · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    simp [rowMaximum, hN]
  · simp [rowMaximum, hN]

private theorem printed_consequences (h2 : T26_L2)
    (D : ∀ N, Fin N → Fin N → ℝ) (a : ∀ N, Fin N → ℝ) (K φ : ℝ → ℝ) (b : ℕ → ℝ)
    (hD : ∀ N i j, 0 ≤ D N i j) (hself : ∀ N i, D N i i = 0)
    (hK : KernelConditions K) (hb : Tendsto b atTop atTop)
    (hφ : ∀ s, 0 ≤ s → 0 ≤ φ s)
    (henv : ∀ᶠ N in atTop, ∀ i j, |a N i| * |a N j| ≤ φ (D N i j))
    (hinside : Tendsto (interiorEnvelope D φ b) atTop (nhds 0)) :
    printedInteriorConclusion D a K φ b := by
  obtain ⟨L, hL⟩ := hK.2.2.1
  have hfinite : ∀ᶠ N in atTop, φ 0 ≤ interiorEnvelope D φ b N ∧
      arraySquareMaximum a N ≤ interiorEnvelope D φ b N ∧
      |arrayKernel D a K b N| ≤ L*interiorEnvelope D φ b N := by
    filter_upwards [eventually_gt_atTop 0, hb.eventually (eventually_gt_atTop 0), henv] with N hN hbN heN
    exact h2 (D N) (a N) K φ (b N) L hN (hD N) (hself N) hbN hφ heN hK.2.1 (fun t ht => (hL t ht).le)
  have hzero : φ 0 = 0 := le_antisymm (ge_of_tendsto hinside (hfinite.mono (fun _ h => h.1))) (hφ 0 le_rfl)
  have ha0 : ∀ᶠ N in atTop, ∀ i, a N i = 0 := by
    filter_upwards [henv] with N hN i
    have he := hN i i
    rw [hself N i, hzero] at he
    have : |a N i| = 0 := by nlinarith [abs_nonneg (a N i)]
    exact abs_eq_zero.mp this
  have hmax0 : ∀ᶠ N in atTop, arraySquareMaximum a N = 0 := by
    filter_upwards [ha0] with N hN
    simp only [arraySquareMaximum, hN, zero_pow (by decide : 2 ≠ 0), row_maximum_zero]
  have hform0 : ∀ᶠ N in atTop, arrayKernel D a K b N = 0 := by
    filter_upwards [ha0] with N hN
    simp [arrayKernel, hN]
  have hlim : Tendsto (arrayKernel D a K b) atTop (nhds 0) :=
    tendsto_const_nhds.congr' (hform0.mono (fun _ h => h.symm))
  refine ⟨hzero, ha0, hfinite.mono (fun _ h => h.2.1),
    tendsto_const_nhds.congr' (hmax0.mono (fun _ h => h.symm)), ?_, kernel_consequences D a K b hlim⟩
  intro L' hL'
  filter_upwards [eventually_gt_atTop 0, hb.eventually (eventually_gt_atTop 0), henv] with N hN hbN heN
  exact (h2 (D N) (a N) K φ (b N) L' hN (hD N) (hself N) hbN hφ heN hK.2.1
    (fun t ht => (hL' t ht).le)).2.2

theorem T26_assembly (h1 : T26_L1) (h2 : T26_L2) : T26WholeStatement := by
  refine ⟨auxiliary_radius, ?_, ?_⟩
  · intro Space _ _ P p d K φ b hp _ hbounded hWD hmetric hspacing hK hdiv hφ
    dsimp only
    intro henv
    let D := fun N => nodeSeparation (P N)
    let a := fun N => forcedCentered (fun _ => p) (circleAverage (P N) d)
    obtain ⟨M, hM, hbound⟩ := hbounded
    have hca : ∀ᶠ N in atTop, (∑ i, a N i) = 0 ∧ ∀ i, |a N i| ≤ 4*M := by
      filter_upwards [eventually_gt_atTop 0, hWD, hbound] with N hN hWN hBN
      exact forced_centered_bounds (fun _ => p) (circleAverage (P N) d) hN (fun _ => hp) M
        (AronowAudit.P004.CLTCompletion.circleAverage_abs_le (Bridge.population (P N)) d M hWN
          (fun x z => (hBN x z).le))
    constructor
    · intro htail
      apply kernel_consequences
      exact h1 D a K φ b (Eventually.of_forall (fun N => (hmetric N).1))
        (hca.mono (fun _ h => h.1)) ⟨4*M, by positivity, hca.mono (fun _ h => h.2)⟩
        hspacing hK hdiv hφ henv htail
    · exact printed_consequences h2 D a K φ b (fun N => (hmetric N).1)
        (fun N i => ((hmetric N).2.1 i i).2 rfl) hK hdiv hφ henv
  · intro N p R hp
    have hm : ∀ i a, forcedMarginal p R i a = marginal p R i a := by
      intro i a
      exact (AronowAudit.P004.marginal_is_marginalization p R i a hp).symm
    have ha : forcedAME p R = ame p R := by
      simp only [forcedAME, forcedEffect, hm, ame, nodeEffect]
    exact ⟨hm, ha, fun i => by simp only [forcedCentered, forcedEffect, hm, ha, nodeEffect]⟩

end
end SAP.P004b.WH.W1
