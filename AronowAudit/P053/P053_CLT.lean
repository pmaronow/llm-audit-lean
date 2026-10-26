import AronowAudit.P053.P053_NormalQuantiles
import AronowAudit.P053.P053_MomentConsistency
import AronowAudit.P061.P061_Foundations
import AronowAudit.External.StatLean.HypothesisTesting.ForMathlib.CombinatorialCLT
import Mathlib.GroupTheory.GroupAction.SubMulAction.Combination

/-!
The sharp-null Wald limit under bounded-fourth-moment regularity. The
finite-population Hájek CLT is imported from Apache-2.0 licensed StatLean. Fourth-moment regularity discharges its
Lindeberg condition. Finite transitive orbit averaging identifies permutation
and complete-randomization laws without factorial enumeration; the proved
moment LLN and varying-space Slutsky theorem supply studentization.
-/

namespace AronowAudit.P053
open scoped BigOperators Topology BoundedContinuousFunction
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

namespace CLTCompletion

/-- The uniform average on a transitive finite orbit is the uniform average
on its carrier. This avoids expanding any factorial fiber count. -/
theorem average_transitive {G S : Type*} [Group G] [Fintype G]
    [Fintype S] [MulAction G S] [MulAction.IsPretransitive G S]
    (x : S) (f : S → ℝ) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, f (g • x) =
      (Fintype.card S : ℝ)⁻¹ * ∑ y : S, f y := by
  classical
  letI : Nonempty S := ⟨x⟩
  have hc (y : S) : (∑ g : G, f (g • y)) = ∑ g : G, f (g • x) := by
    obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G x y
    apply Fintype.sum_equiv (Equiv.mulRight a)
    intro g
    change f (g • (a • x)) = f ((g*a) • x)
    rw [mul_smul]
  have hr (g : G) : (∑ y : S, f (g • y)) = ∑ y : S, f y := by
    apply Fintype.sum_equiv (MulAction.toPerm g)
    intro y
    rfl
  have he : (Fintype.card S : ℝ) * (∑ g : G, f (g • x)) =
      (Fintype.card G : ℝ) * (∑ y : S, f y) := by
    calc
      _ = ∑ y : S, ∑ g : G, f (g • y) := by simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ g : G, ∑ y : S, f (g • y) := Finset.sum_comm
      _ = _ := by simp only [hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hS : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  nlinarith only [he]


theorem sum_combinations {U : Type*} [Fintype U] [DecidableEq U]
    (m : ℕ) (f : Finset U → ℝ) :
    (∑ z : Set.powersetCard U m, f z) = ∑ z ∈ support m, f z := by
  classical
  rw [← Finset.sum_attach (support m) f]
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight (fun z => by
    simp [support, Set.powersetCard])) _ _ (fun _ => rfl)

theorem card_combinations {U : Type*} [Fintype U] [DecidableEq U] (m : ℕ) :
    Fintype.card (Set.powersetCard U m) = (support (ι := U) m).card := by
  have hh := sum_combinations (U := U) m (fun _ => (1 : ℝ))
  have hh' : (Fintype.card (Set.powersetCard U m) : ℝ) = (support (ι := U) m).card := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hh
  exact_mod_cast hh' 

def blockEmbedding (P : Population) : Fin P.n1 ↪ Fin P.size :=
  ⟨fun i => ⟨i.val, by have := i.isLt; dsimp [Population.size]; omega⟩,
    fun i j h => Fin.ext (congrArg (fun x : Fin P.size => x.val) h)⟩

def initialBlock (P : Population) : Set.powersetCard (Fin P.size) P.n1 :=
  ⟨Finset.univ.map (blockEmbedding P), by simp [Set.powersetCard]⟩

def assignment (P : Population) (σ : Equiv.Perm (Fin P.size)) : Finset (Fin P.size) :=
  (σ • initialBlock P : Set.powersetCard (Fin P.size) P.n1)

theorem assignment_card (P : Population) (σ : Equiv.Perm (Fin P.size)) :
    (assignment P σ).card = P.n1 := Set.powersetCard.card_eq _

theorem permutation_average (P : Population) (f : Finset (Fin P.size) → ℝ) :
    (Fintype.card (Equiv.Perm (Fin P.size)) : ℝ)⁻¹ *
      ∑ σ : Equiv.Perm (Fin P.size), f (assignment P σ) = randomizationMean P f := by
  letI := Set.powersetCard.isPretransitive (α := Fin P.size) (n := P.n1)
  have hh := average_transitive (G := Equiv.Perm (Fin P.size)) (initialBlock P)
    (fun z => f z)
  rw [sum_combinations, card_combinations] at hh
  simpa only [assignment, randomizationMean, div_eq_inv_mul] using hh

theorem permutation_probability (P : Population) (A : Finset (Fin P.size) → Prop) :
    AronowAudit.P061.probability (AronowAudit.P061.uniformDesign (Equiv.Perm (Fin P.size)))
      (fun σ => A (assignment P σ)) = randomizationProbability P A := by
  classical
  simp only [AronowAudit.P061.probability, AronowAudit.P061.uniformDesign, tsum_fintype]
  have hh := permutation_average P (fun z => if A z then (1 : ℝ) else 0)
  rw [show randomizationMean P (fun z => if A z then (1 : ℝ) else 0) =
    randomizationProbability P A by simp [randomizationMean, randomizationProbability,
      Finset.sum_boole]] at hh
  rw [← hh, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs <;> simp

theorem centered_sum (P : Population) (y : Fin P.size → ℝ) (hN : 0 < P.size) :
    ∑ i, (y i-populationMean P y) = 0 := by
  have hN0 : (P.size : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, populationMean, sampleMean]
  field_simp
  ring

theorem centered_square_sum (P : Population) (y : Fin P.size → ℝ) (hN : 1 < P.size) :
    ∑ i, (y i-populationMean P y)^2 = ((P.size : ℝ)-1)*populationVariance P y := by
  have hN0 : (P.size : ℝ)-1 ≠ 0 := by exact_mod_cast (show (P.size : ℤ)-1 ≠ 0 by omega)
  simp only [populationVariance, sampleVariance, centeredSS, populationMean,
    Finset.card_univ, Fintype.card_fin]
  field_simp

open Causalean.Experimentation.FinitePopulationMoments

def normalizedOutcome (P : Population) (v : ℝ) (i : Fin P.size) : ℝ :=
  (P.Y0 i-populationMean P P.Y0)/Real.sqrt v

/-- Bounded fourth moments imply that no individual can reach a fixed
Hájek cutoff eventually, for either arm size. -/
theorem hajek_lindeberg (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ)
    (hsize : ∀ k, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0) (hv : 0 < v0) :
    ∀ ε > (0 : ℝ), Tendsto (fun k => ((E k).size : ℝ)⁻¹ *
      ∑ i, if ε*Real.sqrt (min ((E k).n1 : ℝ) (((E k).size : ℝ)-(E k).n1)) ≤
        |normalizedOutcome (E k) v0 i| then (normalizedOutcome (E k) v0 i)^2 else 0)
      atTop (𝓝 0) := by
  letI : ∀ k, Nonempty (Fin (E k).size) := fun k =>
    ⟨⟨0, by have hh := hsize k; dsimp [Population.size]; omega⟩⟩
  obtain ⟨B,hB,hfourth⟩ := h.fourth_moments
  have hNpos (k : ℕ) : (0:ℝ) < (E k).size := by
    exact_mod_cast (by have hh := hsize k; dsimp [Population.size]; omega : 0 < (E k).size)
  have htotal (k : ℕ) :
      (∑ i : Fin (E k).size, (((E k).Y1 i)^4+((E k).Y0 i)^4)) ≤ B*(E k).size :=
    (div_le_iff₀ (hNpos k)).mp (hfourth k)
  have hfourth0 (k : ℕ) : (∑ i, ((E k).Y0 i)^4) ≤ B*(Fintype.card (Fin (E k).size) : ℝ) := by
    simp only [Fintype.card_fin]
    exact (Finset.sum_le_sum (fun i _ => le_add_of_nonneg_left (by positivity))).trans (htotal k)
  have hNinv : Tendsto (fun k => 1/(Fintype.card (Fin (E k).size) : ℝ)) atTop (𝓝 0) := by
    simpa only [Fintype.card_fin] using regularity_inverse_size E p v1 v0 vt τ h
  have hmax1 := MomentCompletion.maximal_square_rate (fun k => (E k).Y0) (fun k => (E k).n1)
    (fun k => by have hh := hsize k; omega) (fun k => by simp [Population.size])
    B p hB (ne_of_gt h.p_positive) hfourth0 hNinv
    (by simpa only [Fintype.card_fin] using h.allocation)
  have hmax0 := MomentCompletion.maximal_square_rate (fun k => (E k).Y0) (fun k => (E k).n0)
    (fun k => by have hh := hsize k; omega) (fun k => by simp [Population.size])
    B (1-p) hB (by linarith [h.p_less_one]) hfourth0 hNinv
    (by simpa only [Fintype.card_fin] using regularity_allocation_control E p v1 v0 vt τ h)
  intro ε hε
  apply tendsto_const_nhds.congr'
  filter_upwards [hmax1.eventually_lt_const (by positivity : (0:ℝ) < ε^2*v0),
    hmax0.eventually_lt_const (by positivity : (0:ℝ) < ε^2*v0)] with k h1 h0
  symm
  have hn1 : (0:ℝ) < (E k).n1 := by exact_mod_cast (by have hh := hsize k; omega : 0 < (E k).n1)
  have hn0 : (0:ℝ) < (E k).n0 := by exact_mod_cast (by have hh := hsize k; omega : 0 < (E k).n0)
  have hmin : (0:ℝ) ≤ min ((E k).n1 : ℝ) (((E k).size : ℝ)-(E k).n1) := by
    simp only [Population.size, Nat.cast_add, add_sub_cancel_left]; positivity
  have hroot := Real.sq_sqrt hmin
  have hrootv := Real.sq_sqrt hv.le
  have hh (i : Fin (E k).size) :
      ¬ ε*Real.sqrt (min ((E k).n1 : ℝ) (((E k).size : ℝ)-(E k).n1)) ≤
        |normalizedOutcome (E k) v0 i| := by
    intro hi
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ ε*Real.sqrt _) (abs_nonneg _)).mpr hi
    have hbound : ((E k).Y0 i-populationMean (E k) (E k).Y0)^2 ≤ popMaxSqDev (E k).Y0 := by
      simpa only [popMaxSqDev, CausalBridge.populationMean_eq] using
        (Finset.le_sup' (fun i => ((E k).Y0 i-popMean (E k).Y0)^2) (Finset.mem_univ i))
    rw [div_lt_iff₀ hn1] at h1
    rw [div_lt_iff₀ hn0] at h0
    simp only [normalizedOutcome, sq_abs, div_pow, hrootv, mul_pow, hroot] at hs
    rw [le_div_iff₀ hv] at hs
    have hminle : ε^2*min ((E k).n1 : ℝ) (((E k).size : ℝ)-(E k).n1)*v0 <
        ε^2*min ((E k).n1 : ℝ) (((E k).size : ℝ)-(E k).n1)*v0 := by
      rcases le_total ((E k).n1 : ℝ) ((E k).n0 : ℝ) with hc | hc
      · rw [show ((E k).size : ℝ)-(E k).n1 = (E k).n0 by simp [Population.size], min_eq_left hc] at hs ⊢
        nlinarith only [hs, hbound, h1]
      · rw [show ((E k).size : ℝ)-(E k).n1 = (E k).n0 by simp [Population.size], min_eq_right hc] at hs ⊢
        nlinarith only [hs, hbound, h0]
    exact (lt_irrefl _ hminle)
  simp only [if_neg (hh _), Finset.sum_const_zero, mul_zero]


theorem normalized_centered (P : Population) (v : ℝ) (hN : 0 < P.size) :
    ∑ i, normalizedOutcome P v i = 0 := by
  simp only [normalizedOutcome, ← Finset.sum_div, centered_sum P P.Y0 hN, zero_div]

theorem normalized_second_moment (P : Population) (v : ℝ)
    (hN : 1 < P.size) (hv : 0 < v) :
    (P.size : ℝ)⁻¹ * ∑ i, (normalizedOutcome P v i)^2 =
      (1-1/(P.size : ℝ))*populationVariance P P.Y0/v := by
  have hN0 : (P.size : ℝ) ≠ 0 := by exact_mod_cast (by omega : P.size ≠ 0)
  simp only [normalizedOutcome, div_pow, Real.sq_sqrt hv.le, ← Finset.sum_div,
    centered_square_sum P P.Y0 hN]
  field_simp

theorem normalized_second_moment_limit (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ)
    (hsize : ∀ k, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0) (hv : 0 < v0) :
    Tendsto (fun k => ((E k).size : ℝ)⁻¹ * ∑ i, (normalizedOutcome (E k) v0 i)^2)
      atTop (𝓝 1) := by
  have hh := ((tendsto_const_nhds (x := (1:ℝ))).sub
    (regularity_inverse_size E p v1 v0 vt τ h)).mul h.variance0
  have hh := hh.div_const v0
  simp only [sub_zero, one_mul, div_self hv.ne'] at hh
  apply hh.congr
  intro k
  symm
  apply normalized_second_moment _ _ _ hv
  have hk := hsize k
  dsimp [Population.size]
  omega

open MeasureTheory ProbabilityTheory

/-- The StatLean Hájek theorem converted to the bounded-test-function notion
of weak convergence. -/
theorem permutation_weakCLT {N m : ℕ → ℕ}
    (a : ∀ k, Fin (m k) → Fin (N k)) (ha : ∀ k, Function.Injective (a k))
    (d : ∀ k, Fin (N k) → ℝ) (hcent : ∀ k, ∑ l, d k l = 0)
    (hm : Tendsto (fun k => (m k : ℝ)) atTop atTop)
    (hNm : Tendsto (fun k => (N k : ℝ)-m k) atTop atTop)
    (hvar : Tendsto (fun k => (N k : ℝ)⁻¹*∑ l, d k l^2) atTop (𝓝 1))
    (hlind : ∀ ε > (0 : ℝ), Tendsto (fun k => (N k : ℝ)⁻¹*
      ∑ l, if ε*Real.sqrt (min (m k : ℝ) ((N k : ℝ)-m k)) ≤ |d k l|
        then d k l^2 else 0) atTop (𝓝 0)) :
    AronowAudit.P061.WeakConverges
      (fun k => AronowAudit.P061.uniformDesign (Equiv.Perm (Fin (N k))))
      (fun k σ => (StatLean.HypothesisTesting.blockSumScale (N k) (m k))⁻¹*
        ∑ i, d k (σ (a k i))) (gaussianReal 0 1) := by
  rw [AronowAudit.P061.weakConverges_iff_designLaw_tendsto,
    tendsto_iff_forall_lipschitz_integral_tendsto]
  rintro F ⟨C,hC⟩ ⟨L,hL⟩
  let Fb : ℝ →ᵇ ℝ := ⟨⟨F,hL.continuous⟩, C,hC⟩
  have hbdd (x : ℝ) : |F x| ≤ C+|F 0| := by
    have hh := hC x 0
    rw [Real.dist_eq] at hh
    calc
      |F x| = |(F x-F 0)+F 0| := by ring_nf
      _ ≤ |F x-F 0|+|F 0| := abs_add_le _ _
      _ ≤ _ := by linarith only [hh]
  have hlip (x y : ℝ) : |F x-F y| ≤ (L : ℝ)*|x-y| := by
    simpa only [Real.dist_eq] using hL.dist_le_mul x y
  have ht := StatLean.HypothesisTesting.tendsto_perm_avg_lipschitz
    a ha d hcent hm hNm hvar hlind F hlip hbdd
  change Tendsto (fun k => ∫ x, Fb x ∂AronowAudit.P061.designLaw
    (AronowAudit.P061.uniformDesign (Equiv.Perm (Fin (N k))))
    (fun σ => (StatLean.HypothesisTesting.blockSumScale (N k) (m k))⁻¹*
      ∑ i, d k (σ (a k i)))) atTop (𝓝 (∫ x, Fb x ∂gaussianReal 0 1))
  simp_rw [AronowAudit.P061.designLaw_integral]
  simpa only [AronowAudit.P061.expectation, AronowAudit.P061.uniformDesign,
    tsum_fintype, ← Finset.mul_sum, StatLean.HypothesisTesting.stdGaussianExpect, Fb,
    BoundedContinuousFunction.coe_mk, ContinuousMap.coe_mk] using ht


theorem assignment_sum (P : Population) (σ : Equiv.Perm (Fin P.size))
    (y : Fin P.size → ℝ) :
    ∑ i ∈ assignment P σ, y i = ∑ i, y (σ (blockEmbedding P i)) := by
  simp only [assignment, Set.powersetCard.coe_smul, initialBlock,
    Finset.smul_finset_def, Equiv.Perm.smul_def]
  rw [Finset.sum_image (fun x _ y _ h => σ.injective h), Finset.sum_map]

theorem observed_sharp (P : Population) (hs : SharpNull P) (z : Finset (Fin P.size)) :
    observed P z = P.Y0 := by
  funext i
  simp [observed, hs i]

theorem estimate_centered (P : Population) (hs : SharpNull P)
    (h1 : 0 < P.n1) (h0 : 0 < P.n0) (z : Finset (Fin P.size)) (hz : z ∈ support P.n1) :
    estimate P z = (P.size : ℝ)/((P.n1 : ℝ)*P.n0)*
      ∑ i ∈ z, (P.Y0 i-populationMean P P.Y0) := by
  have h1r : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
  have h0r : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
  have hNr : (P.size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [Population.size]; omega : P.size ≠ 0)
  have hc := (arm_cards P z hz).1
  rw [estimate, observed_sharp P hs z, difference_sample_sum P z hz]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hc,
    populationMean, sampleMean, Finset.card_univ, Fintype.card_fin]
  field_simp
  simp only [Population.size, Nat.cast_add]
  ring

/-- Deterministic standard deviation with the asymptotic population variance
in place of its finite-population counterpart. -/
def inferentialScale (P : Population) (v : ℝ) : ℝ :=
  Real.sqrt v*StatLean.HypothesisTesting.blockSumScale P.size P.n1*(P.size : ℝ)/
    ((P.n1 : ℝ)*P.n0)

theorem blockScale_pos (P : Population) (h1 : 0 < P.n1) (h0 : 0 < P.n0) :
    0 < StatLean.HypothesisTesting.blockSumScale P.size P.n1 := by
  rw [StatLean.HypothesisTesting.blockSumScale, Real.sqrt_pos]
  simp only [Population.size, Nat.cast_add, add_sub_cancel_left]
  positivity

theorem inferentialScale_pos (P : Population) (v : ℝ) (hv : 0 < v)
    (h1 : 0 < P.n1) (h0 : 0 < P.n0) : 0 < inferentialScale P v := by
  have hb := blockScale_pos P h1 h0
  have hs := Real.sqrt_pos.mpr hv
  have hN : (0:ℝ) < P.size := by exact_mod_cast (by dsimp [Population.size]; omega : 0 < P.size)
  unfold inferentialScale
  positivity

theorem normalized_estimate (P : Population) (hs : SharpNull P) (v : ℝ)
    (hv : 0 < v) (h1 : 0 < P.n1) (h0 : 0 < P.n0)
    (σ : Equiv.Perm (Fin P.size)) :
    estimate P (assignment P σ)/inferentialScale P v =
      (StatLean.HypothesisTesting.blockSumScale P.size P.n1)⁻¹*
        ∑ i, normalizedOutcome P v (σ (blockEmbedding P i)) := by
  have hz : assignment P σ ∈ support P.n1 := by
    simp only [support, Finset.mem_powersetCard, Finset.subset_univ, true_and, assignment_card]
  rw [estimate_centered P hs h1 h0 _ hz, assignment_sum]
  simp only [normalizedOutcome, ← Finset.sum_div, inferentialScale]
  have h1r : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
  have h0r : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
  have hNr : (P.size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [Population.size]; omega : P.size ≠ 0)
  have hvr := (Real.sqrt_pos.mpr hv).ne'
  have hbr := (blockScale_pos P h1 h0).ne'
  field_simp

/-- Scaling identity used to compare the deterministic CLT standard deviation
with the proved OLS variance consistency theorem. -/
theorem inferentialScale_square (P : Population) (v : ℝ) (hv : 0 < v)
    (h1 : 0 < P.n1) (h0 : 0 < P.n0) :
    (P.size : ℝ)*(inferentialScale P v)^2 =
      v/(((P.n1 : ℝ)/P.size)*((P.n0 : ℝ)/P.size)) := by
  have h1r : (P.n1 : ℝ) ≠ 0 := by exact_mod_cast h1.ne'
  have h0r : (P.n0 : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
  have hNr : (P.size : ℝ) ≠ 0 := by
    exact_mod_cast (by dsimp [Population.size]; omega : P.size ≠ 0)
  have harg : (0:ℝ) ≤ (P.n1 : ℝ)*((P.size : ℝ)-P.n1)/P.size := by
    simp only [Population.size, Nat.cast_add, add_sub_cancel_left]
    positivity
  simp only [inferentialScale, mul_pow, div_pow,
    StatLean.HypothesisTesting.blockSumScale, Real.sq_sqrt hv.le, Real.sq_sqrt harg]
  field_simp
  simp only [Population.size, Nat.cast_add]
  ring


theorem oracle_weakCLT_all_sizes (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) (hs : ∀ k, SharpNull (E k))
    (hsize : ∀ k, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0) (hv : 0 < v0) :
    AronowAudit.P061.WeakConverges
      (fun k => AronowAudit.P061.uniformDesign (Equiv.Perm (Fin (E k).size)))
      (fun k σ => estimate (E k) (assignment (E k) σ)/inferentialScale (E k) v0)
      (gaussianReal 0 1) := by
  have hclt := permutation_weakCLT
    (fun k => blockEmbedding (E k)) (fun k => (blockEmbedding (E k)).injective)
    (fun k => normalizedOutcome (E k) v0)
    (fun k => normalized_centered (E k) v0 (by have hk := hsize k; dsimp [Population.size]; omega))
    (tendsto_natCast_atTop_iff.mpr (MomentCompletion.sample_size_diverges
      (fun k => (E k).size) (fun k => (E k).n1) p h.p_positive h.size_diverges h.allocation))
    (show Tendsto (fun k => ((E k).size : ℝ)-(E k).n1) atTop atTop from by
      simpa only [Population.size, Nat.cast_add, add_sub_cancel_left] using
        (tendsto_natCast_atTop_iff.mpr (MomentCompletion.sample_size_diverges
          (fun k => (E k).size) (fun k => (E k).n0) (1-p) (by linarith [h.p_less_one])
          h.size_diverges (regularity_allocation_control E p v1 v0 vt τ h))))
    (normalized_second_moment_limit E p v1 v0 vt τ h hsize hv)
    (hajek_lindeberg E p v1 v0 vt τ h hsize hv)
  intro f
  apply (hclt f).congr
  intro k
  apply congrArg (AronowAudit.P061.expectation _)
  funext σ
  dsimp only
  rw [normalized_estimate (E k) (hs k) v0 hv (by have hk := hsize k; omega)
    (by have hk := hsize k; omega)]

theorem sharp_variance_limits (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) (hs : ∀ k, SharpNull (E k)) : v1 = v0 := by
  have hh : (fun k => populationVariance (E k) (E k).Y1) =
      (fun k => populationVariance (E k) (E k).Y0) := by
    funext k
    congr 1
    funext i
    exact hs k i
  exact tendsto_nhds_unique (by simpa only [hh] using h.variance1) h.variance0

theorem scale_square_limit (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ)
    (hsize : ∀ k, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0) (hv : 0 < v0) :
    Tendsto (fun k => ((E k).size : ℝ)*(inferentialScale (E k) v0)^2)
      atTop (𝓝 (olsLimit p v0 v0)) := by
  have hc : 1-p ≠ 0 := by linarith [h.p_less_one]
  have hh := (tendsto_const_nhds (x := v0)).div
    (h.allocation.mul (regularity_allocation_control E p v1 v0 vt τ h))
    (mul_ne_zero h.p_positive.ne' hc)
  have he : v0/(p*(1-p)) = olsLimit p v0 v0 := by
    unfold olsLimit
    field_simp [h.p_positive.ne', hc]
    ring
  rw [← he]
  apply hh.congr
  intro k
  symm
  exact inferentialScale_square (E k) v0 hv
    (by have hk := hsize k; omega) (by have hk := hsize k; omega)

/-- The OLS standard error divided by the deterministic CLT scale tends to
one, including assignments on which the fitted variance is zero. -/
theorem relative_scale_consistency (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) (hs : ∀ k, SharpNull (E k))
    (hsize : ∀ k, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0) (hv : 0 < v0) :
    InProbability E (fun k z => Real.sqrt (olsVariance (E k) z)/inferentialScale (E k) v0) 1 := by
  let c := olsLimit p v0 v0
  have hc : 0 < c := by
    dsimp [c, olsLimit]
    exact add_pos (div_pos hv (by linarith [h.p_less_one])) (div_pos hv h.p_positive)
  have hv1 := sharp_variance_limits E p v1 v0 vt τ h hs
  have hols : InProbability E (fun k z => ((E k).size : ℝ)*olsVariance (E k) z) c := by
    simpa only [hv1] using ols_variance_limit_of_momentLLN finitePopulationMomentLLN E p v1 v0 vt τ h
  have hdet : InProbability E (fun k _ => ((E k).size : ℝ)*(inferentialScale (E k) v0)^2) c :=
    inProbability_deterministic E _ c (scale_square_limit E p v1 v0 vt τ h hsize hv)
  have hh := inProbability_continuous_pair E _ _ c c hols hdet
    (fun t => Real.sqrt (t.1/t.2)) (by fun_prop (disch := exact hc.ne'))
  have hc1 : Real.sqrt (c/c) = 1 := by rw [div_self hc.ne']; norm_num
  rw [hc1] at hh
  apply inProbability_congr_eventually E _ _ 1 _ hh
  filter_upwards [] with k
  intro z hz
  have hsp := inferentialScale_pos (E k) v0 hv
    (by have hk := hsize k; omega) (by have hk := hsize k; omega)
  have hN : ((E k).size : ℝ) ≠ 0 := by
    exact_mod_cast (by have hk := hsize k; dsimp [Population.size]; omega : (E k).size ≠ 0)
  have he : (((E k).size : ℝ)*olsVariance (E k) z)/
      (((E k).size : ℝ)*(inferentialScale (E k) v0)^2) =
      olsVariance (E k) z/(inferentialScale (E k) v0)^2 := by field_simp
  rw [he, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq hsp.le]

theorem studentized_weakCLT_all_sizes (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) (hs : ∀ k, SharpNull (E k))
    (hsize : ∀ k, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0) (hv : 0 < v0) :
    AronowAudit.P061.WeakConverges
      (fun k => AronowAudit.P061.uniformDesign (Equiv.Perm (Fin (E k).size)))
      (fun k σ => estimate (E k) (assignment (E k) σ)/
        Real.sqrt (olsVariance (E k) (assignment (E k) σ)))
      (gaussianReal 0 1) := by
  have horacle := oracle_weakCLT_all_sizes E p v1 v0 vt τ h hs hsize hv
  have hscale := relative_scale_consistency E p v1 v0 vt τ h hs hsize hv
  have hscale' : AronowAudit.P061.ConvergesInProbability
      (fun k => AronowAudit.P061.uniformDesign (Equiv.Perm (Fin (E k).size)))
      (fun k σ => Real.sqrt (olsVariance (E k) (assignment (E k) σ))/inferentialScale (E k) v0) 1 := by
    intro ε hε
    apply (hscale ε hε).congr
    intro k
    exact (permutation_probability (E k) _).symm
  have hh := AronowAudit.P061.weakConverges_div_consistent _ _ _ _ horacle hscale'
  intro f
  apply (hh f).congr
  intro k
  apply congrArg (AronowAudit.P061.expectation _)
  funext σ
  congr 1
  have hsp := inferentialScale_pos (E k) v0 hv
    (by have hk := hsize k; omega) (by have hk := hsize k; omega)
  field_simp


local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

theorem wald_validity_all_sizes (E : ℕ → Population) (p v1 v0 vt τ : ℝ)
    (h : Regularity E p v1 v0 vt τ) (hs : ∀ k, SharpNull (E k))
    (hsize : ∀ k, 2 ≤ (E k).n1 ∧ 2 ≤ (E k).n0) (hv : 0 < v0) :
    (∀ t : ℝ, Tendsto (fun k => randomizationProbability (E k)
      (fun z => estimate (E k) z/Real.sqrt (olsVariance (E k) z) ≤ t))
        atTop (nhds (standardNormalCDF t))) ∧
    (∀ α : ℝ, 0 < α → α < 1 → Tendsto
      (fun k => randomizationProbability (E k)
        (fun z => normalCritical α < |estimate (E k) z|/Real.sqrt (olsVariance (E k) z)))
      atTop (nhds α)) := by
  have hw := studentized_weakCLT_all_sizes E p v1 v0 vt τ h hs hsize hv
  constructor
  · intro t
    have hf : (gaussianReal 0 1) (frontier (Set.Iic t)) = 0 := by
      rw [frontier_Iic]
      exact measure_singleton t
    have hh := AronowAudit.P061.weakConverges_continuitySet _ _ _ hw
      (Set.Iic t) measurableSet_Iic hf
    change Tendsto (fun k => AronowAudit.P061.probability
      (AronowAudit.P061.uniformDesign (Equiv.Perm (Fin (E k).size)))
      (fun σ => estimate (E k) (assignment (E k) σ)/Real.sqrt
        (olsVariance (E k) (assignment (E k) σ)) ≤ t)) atTop
      (𝓝 (standardNormalCDF t)) at hh
    apply hh.congr
    intro k
    exact permutation_probability (E k)
      (fun z => estimate (E k) z/Real.sqrt (olsVariance (E k) z) ≤ t)
  · intro α hα hα1
    let q := normalCritical α
    have hq : 0 < q := NormalCompletion.normalCritical_pos α hα hα1
    have hh := AronowAudit.P061.weakConverges_abs_le _ _ _ hw q hq
      (measure_singleton q) (measure_singleton (-q))
    rw [NormalCompletion.normalCritical_interval_mass α hα hα1] at hh
    have ht := (tendsto_const_nhds (x := (1:ℝ))).sub hh
    have hlim : (1:ℝ)-(1-α) = α := by ring
    rw [hlim] at ht
    apply ht.congr
    intro k
    rw [← AronowAudit.P061.probability_complement]
    have he (σ : Equiv.Perm (Fin (E k).size)) :
        ¬ |estimate (E k) (assignment (E k) σ)/
          Real.sqrt (olsVariance (E k) (assignment (E k) σ))| ≤ q ↔
        normalCritical α < |estimate (E k) (assignment (E k) σ)|/
          Real.sqrt (olsVariance (E k) (assignment (E k) σ)) := by
      rw [not_le, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    simp_rw [he]
    exact permutation_probability (E k)
      (fun z => normalCritical α < |estimate (E k) z|/Real.sqrt (olsVariance (E k) z))

end CLTCompletion

/-- T6(c), proved by the finite-population Hájek CLT, the actual
moment LLN, and the varying-space Slutsky theorem. -/
theorem sharp_null_wald_validity (E : ℕ → Population) (p v1 v0 vt tauInf : ℝ)
    (h : Regularity E p v1 v0 vt tauInf) (hs : ∀ k, SharpNull (E k)) (hv : 0 < v0) :
    (∀ t : ℝ, Tendsto (fun k => randomizationProbability (E k)
      (fun z => estimate (E k) z/Real.sqrt (olsVariance (E k) z) ≤ t))
        atTop (nhds (standardNormalCDF t))) ∧
    (∀ α : ℝ, 0 < α → α < 1 → Tendsto
      (fun k => randomizationProbability (E k)
        (fun z => normalCritical α < |estimate (E k) z|/Real.sqrt (olsVariance (E k) z)))
      atTop (nhds α)) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp h.arm_sizes
  have hh := CLTCompletion.wald_validity_all_sizes (fun k => E (k+K)) p v1 v0 vt tauInf
    (MomentCompletion.regularity_shift E p v1 v0 vt tauInf h K)
    (fun k => hs (k+K)) (fun k => hK (k+K) (by omega)) hv
  constructor
  · intro t
    exact (tendsto_add_atTop_iff_nat K).mp (hh.1 t)
  · intro α hα hα1
    exact (tendsto_add_atTop_iff_nat K).mp (hh.2 α hα hα1)

end
end AronowAudit.P053
