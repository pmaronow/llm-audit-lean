import SAP.P004a.WH.W1.Leaves
import AronowAudit.P004.P004_DependencyCompletion
import AronowAudit.P004.P004_SpatialCLTCompletion
import AronowAudit.P004.Wave1.DesignLimits.DL5
import AronowAudit.P004.Wave1.DesignLimits.DL9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T1_L5

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology
noncomputable section

def leadingSummand (N : ℕ) (i : Fin N) (z : Assignment N) : ℝ :=
  w1ThreeA (i.val % 3) * (AronowAudit.P004.bit (z i) - w1ThreeP N i)

def leadingSum (N : ℕ) (z : Assignment N) : ℝ :=
  ∑ i, leadingSummand N i z

def leadingMeasure (N : ℕ) : Measure (Assignment N) :=
  AronowAudit.P004.CLTCompletion.designMeasure (w1ThreeP N) (fun i => by
    have hp : w1ThreeP N = fun i => AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) :=
      AronowAudit.P004.Wave1.DecideP004T1_propensities N
    rw [hp]
    exact AronowAudit.P004.Wave1.DecideP004T1_prob (i.val % 3))

theorem threeAdmissible (N : ℕ) (i : Fin N) :
    0 < w1ThreeP N i ∧ w1ThreeP N i < 1 := by
  have hp : w1ThreeP N = fun i => AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) :=
    AronowAudit.P004.Wave1.DecideP004T1_propensities N
  rw [hp]
  exact AronowAudit.P004.Wave1.DecideP004T1_prob (i.val % 3)

theorem leading_mean (N : ℕ) (i : Fin N) :
    AronowAudit.P004.expect (w1ThreeP N) (leadingSummand N i) = 0 := by
  let f : Bool → ℝ := fun a => w1ThreeA (i.val % 3) *
    (AronowAudit.P004.bit a - w1ThreeP N i)
  have he := AronowAudit.P004.Wave1.ObservationalCoverage.own_expect
    (w1ThreeP N) i f
  change AronowAudit.P004.expect (w1ThreeP N) (fun z => f (z i)) = 0
  rw [he]
  simp [f, AronowAudit.P004.bit]
  ring

theorem leading_sum_mean (N : ℕ) :
    AronowAudit.P004.expect (w1ThreeP N) (leadingSum N) = 0 := by
  change AronowAudit.P004.expect (w1ThreeP N) (fun z => ∑ i, leadingSummand N i z) = 0
  rw [AronowAudit.P004.expect_sum]
  simp only [leading_mean, Finset.sum_const_zero]

theorem leading_integral_second (N : ℕ) :
    (∫ z, (leadingSum N z)^2 ∂leadingMeasure N) =
      ∑ i : Fin N, w1ThreeP N i * (1-w1ThreeP N i) * (w1ThreeA (i.val % 3))^2 := by
  change (∫ z, (leadingSum N z)^2 ∂
    AronowAudit.P004.CLTCompletion.designMeasure (w1ThreeP N) (fun i => threeAdmissible N i)) = _
  rw [AronowAudit.P004.CLTCompletion.designMeasure_integral]
  have hvar : AronowAudit.P004.variance (w1ThreeP N) (leadingSum N) =
      ∑ i : Fin N, w1ThreeP N i * (1-w1ThreeP N i) * (w1ThreeA (i.val % 3))^2 := by
    have h := AronowAudit.P004.Wave1.DecideP004T1_sum_variance
      (w1ThreeP N) (fun i => threeAdmissible N i) (fun i => w1ThreeA (i.val % 3)) 1
    have hsum : leadingSum N = fun z =>
        ∑ i, w1ThreeA (i.val % 3) *
          (AronowAudit.P004.bit (z i) - w1ThreeP N i) := by
      funext z
      rfl
    rw [hsum]
    simpa using h
  have hm := leading_sum_mean N
  rw [AronowAudit.P004.variance, AronowAudit.P004.cov, hm, zero_mul, sub_zero] at hvar
  simpa only [pow_two] using hvar

theorem leading_variance_floor (N : ℕ) :
    (N : ℝ) / 1000 ≤
      (∫ z, (leadingSum N z)^2 ∂leadingMeasure N) := by
  rw [leading_integral_second]
  have hterm (i : Fin N) : (1/1000 : ℝ) ≤
      w1ThreeP N i * (1-w1ThreeP N i) * (w1ThreeA (i.val % 3))^2 := by
    have hp : w1ThreeP N = fun i => AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) :=
      AronowAudit.P004.Wave1.DecideP004T1_propensities N
    rw [hp]
    have ht : i.val % 3 < 3 := Nat.mod_lt _ (by omega)
    interval_cases h : i.val % 3 <;>
      norm_num [AronowAudit.P004.Wave1.DecideP004T1_p, w1ThreeA, h]
  calc
    (N : ℝ) / 1000 = ∑ i : Fin N, (1/1000 : ℝ) := by simp [div_eq_mul_inv]
    _ ≤ ∑ i : Fin N,
        w1ThreeP N i * (1-w1ThreeP N i) * (w1ThreeA (i.val % 3))^2 :=
      Finset.sum_le_sum (fun i _ => hterm i)

theorem leading_bound (N : ℕ) (i : Fin N) (z : Assignment N) :
    |leadingSummand N i z| ≤ 1 := by
  change |w1ThreeA (i.val % 3) *
    (AronowAudit.P004.bit (z i) - w1ThreeP N i)| ≤ 1
  have hc : |w1ThreeA (i.val % 3)| ≤ 1 := by
    unfold w1ThreeA
    split_ifs <;> norm_num
  have hp := threeAdmissible N i
  have hb : |AronowAudit.P004.bit (z i) - w1ThreeP N i| ≤ 1 := by
    cases hz : z i
    · simpa [AronowAudit.P004.bit, hz, abs_of_pos hp.1] using hp.2.le
    · have hpos : 0 < 1 - w1ThreeP N i := sub_pos.mpr hp.2
      simpa [AronowAudit.P004.bit, hz, abs_of_pos hpos] using
        (by linarith [hp.1] : 1-w1ThreeP N i ≤ 1)
  rw [abs_mul]
  calc
    |w1ThreeA (i.val % 3)| *
        |AronowAudit.P004.bit (z i) - w1ThreeP N i| ≤
        1 * |AronowAudit.P004.bit (z i) - w1ThreeP N i| :=
      mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = 1 := by norm_num

theorem leading_dependency (N : ℕ) :
    AronowAudit.P004.DependencyGraph (leadingMeasure N) (leadingSummand N) (fun i => {i}) := by
  exact AronowAudit.P004.CLTCompletion.finiteGraph_to_measureGraph
    (w1ThreeP N) (fun i => threeAdmissible N i)
    (leadingSummand N) (fun i => {i})
    (AronowAudit.P004.Wave1.ObservationalCoverage.own_finiteDependencyGraph (w1ThreeP N)
      (fun i a => w1ThreeA (i.val % 3) * (AronowAudit.P004.bit a - w1ThreeP N i)))

theorem leading_all_sizes_clt :
    ∀ x : ℝ, Tendsto (fun N : ℕ =>
      ((leadingMeasure N) {z | leadingSum N z /
        Real.sqrt (∫ z', (leadingSum N z')^2 ∂leadingMeasure N) ≤ x}).toReal) atTop
      (nhds (normalCDF x)) := by
  intro x
  let V : ∀ N, Fin N → Assignment N → ℝ := fun N i z => leadingSummand N i z
  let B : ∀ N, Fin N → Finset (Fin N) := fun _ i => {i}
  let μ : ∀ N, Measure (Assignment N) := leadingMeasure
  have hμ (N : ℕ) : IsProbabilityMeasure (μ N) := by
    exact AronowAudit.P004.CLTCompletion.designMeasure_probability
      (w1ThreeP N) (fun i => threeAdmissible N i)
  have hmeas (N : ℕ) (i : Fin N) : Measurable (V N i) := measurable_of_finite _
  have hmean (N : ℕ) (i : Fin N) : ∫ z, V N i z ∂μ N = 0 := by
    change (∫ z, V N i z ∂
      AronowAudit.P004.CLTCompletion.designMeasure (w1ThreeP N)
        (fun i => threeAdmissible N i)) = 0
    rw [AronowAudit.P004.CLTCompletion.designMeasure_integral]
    exact leading_mean N i
  have hbound : ∃ M : ℝ, ∀ N i, ∀ᵐ z ∂μ N, |V N i z| ≤ M := by
    refine ⟨1, ?_⟩
    intro N i
    exact Filter.Eventually.of_forall (leading_bound N i)
  have hdep (N : ℕ) : AronowAudit.P004.DependencyGraph (μ N) (V N) (B N) := by
    exact leading_dependency N
  have hdegree : ∃ D : ℕ, ∀ N i, (B N i).card ≤ D := by
    refine ⟨1, ?_⟩
    intro N i
    simp [B]
  have hvar : ∃ v : ℝ, 0 < v ∧ ∀ᶠ N : ℕ in atTop,
      v*N ≤ ∫ z, (∑ i, V N i z)^2 ∂μ N := by
    refine ⟨1/1000, by norm_num, Filter.Eventually.of_forall (fun N => ?_)⟩
    have hf := leading_variance_floor N
    change (1/1000 : ℝ) * (N : ℝ) ≤
      ∫ z, (leadingSum N z)^2 ∂leadingMeasure N
    nlinarith [hf]
  have hclt := AronowAudit.P004.corrected_dependency_clt μ hμ V B hmeas hmean hbound hdep hdegree hvar
  simpa [V, μ, leadingSum, AronowAudit.P004.normalCDF, SAP.P004a.normalCDF] using hclt x

theorem leading_second_three (K : ℕ) (hK : 0 < K) :
    (∫ z, (leadingSum (3*K) z)^2 ∂leadingMeasure (3*K)) =
      ((3*K : ℕ) : ℝ) * (3/625 : ℝ) := by
  rw [leading_integral_second]
  have hp : w1ThreeP (3*K) = fun i =>
      AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) :=
    AronowAudit.P004.Wave1.DecideP004T1_propensities (3*K)
  rw [hp]
  have hcycle := AronowAudit.P004.Wave1.DecideP004T1_cycle_average K hK
    (fun t => AronowAudit.P004.Wave1.DecideP004T1_p t *
      (1-AronowAudit.P004.Wave1.DecideP004T1_p t) * (w1ThreeA t)^2)
  have havg :
      (AronowAudit.P004.Wave1.DecideP004T1_p 0 *
        (1-AronowAudit.P004.Wave1.DecideP004T1_p 0) * (w1ThreeA 0)^2 +
       AronowAudit.P004.Wave1.DecideP004T1_p 1 *
        (1-AronowAudit.P004.Wave1.DecideP004T1_p 1) * (w1ThreeA 1)^2 +
       AronowAudit.P004.Wave1.DecideP004T1_p 2 *
        (1-AronowAudit.P004.Wave1.DecideP004T1_p 2) * (w1ThreeA 2)^2) / 3 =
        (3/625 : ℝ) := by
    norm_num [AronowAudit.P004.Wave1.DecideP004T1_p, w1ThreeA]
  have hmean :
      (∑ i : Fin (3*K), AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) *
        (1-AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3)) *
          (w1ThreeA (i.val % 3))^2) / ((3*K : ℕ) : ℝ) = 3/625 := by
    exact hcycle.trans havg
  have hn : (3*K : ℝ) ≠ 0 := by exact_mod_cast (by omega : 3*K ≠ 0)
  calc
    _ = ((3*K : ℕ) : ℝ) *
        ((∑ i : Fin (3*K), AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) *
          (1-AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3)) *
            (w1ThreeA (i.val % 3))^2) / ((3*K : ℕ) : ℝ)) := by
      field_simp [hn]
    _ = ((3*K : ℕ) : ℝ) * (3/625 : ℝ) := by rw [hmean]

theorem leading_restricted_clt :
    W1NormalLimit (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => Real.sqrt (3*K : ℕ) * w1ThreeLinear w1ThreeA (3*K) z /
        Real.sqrt (3/625 : ℝ)) := by
  intro x
  have hbase := (leading_all_sizes_clt x).comp
    (SAP.P004a.WH.W1.multiples_tendsto 3 (by omega))
  apply hbase.congr'
  filter_upwards [eventually_gt_atTop 0] with K hK
  have hKpos : 0 < K := by omega
  let N : ℕ := 3*K
  have hN : (N : ℝ) ≠ 0 := by
    dsimp [N]
    exact_mod_cast (by omega : 3*K ≠ 0)
  have hNpos : 0 < N := by dsimp [N]; omega
  have hsecond := leading_second_three K hKpos
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
  have hsC : 0 < Real.sqrt (3/625 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsqr : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
  have hsum (z : Assignment N) :
      leadingSum N z = (N : ℝ) * w1ThreeLinear w1ThreeA N z := by
    have hbit (a : Bool) : AronowAudit.P004.bit a = SAP.P004a.bit a := rfl
    simp only [leadingSum, leadingSummand, w1ThreeLinear]
    simp_rw [hbit]
    field_simp [hN]
  have hden :
      Real.sqrt (∫ z', (leadingSum N z')^2 ∂leadingMeasure N) =
        Real.sqrt (N : ℝ) * Real.sqrt (3/625 : ℝ) := by
    rw [hsecond, Real.sqrt_mul (Nat.cast_nonneg N)]
  have hratio (z : Assignment N) :
      leadingSum N z / Real.sqrt (∫ z', (leadingSum N z')^2 ∂leadingMeasure N) =
        Real.sqrt (N : ℝ) * w1ThreeLinear w1ThreeA N z / Real.sqrt (3/625 : ℝ) := by
    rw [hsum, hden]
    have hnum : (N : ℝ) * w1ThreeLinear w1ThreeA N z =
        (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ)) *
          w1ThreeLinear w1ThreeA N z := by rw [hsqr]
    calc
      (N : ℝ) * w1ThreeLinear w1ThreeA N z /
          (Real.sqrt (N : ℝ) * Real.sqrt (3/625 : ℝ)) =
        (Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) *
          w1ThreeLinear w1ThreeA N z) /
          (Real.sqrt (N : ℝ) * Real.sqrt (3/625 : ℝ)) := by
            rw [← hnum]
      _ = Real.sqrt (N : ℝ) * w1ThreeLinear w1ThreeA N z /
          Real.sqrt (3/625 : ℝ) := by
        field_simp [ne_of_gt hsN, ne_of_gt hsC]
  have hevent (z : Assignment N) :
      (leadingSum N z / Real.sqrt
        (∫ z', (leadingSum N z')^2 ∂leadingMeasure N) ≤ x) ↔
      (Real.sqrt (N : ℝ) * w1ThreeLinear w1ThreeA N z /
        Real.sqrt (3/625 : ℝ) ≤ x) := by
    rw [hratio z]
  have hprob : (leadingMeasure N
      {z | leadingSum N z / Real.sqrt
        (∫ z', (leadingSum N z')^2 ∂leadingMeasure N) ≤ x}).toReal =
      prob (w1ThreeP N) (fun z => Real.sqrt (N : ℝ) *
        w1ThreeLinear w1ThreeA N z / Real.sqrt (3/625 : ℝ) ≤ x) := by
    change (AronowAudit.P004.CLTCompletion.designMeasure (w1ThreeP N)
      (fun i => threeAdmissible N i)
      {z | leadingSum N z / Real.sqrt
        (∫ z', (leadingSum N z')^2 ∂leadingMeasure N) ≤ x}).toReal = _
    rw [AronowAudit.P004.CLTCompletion.designMeasure_apply]
    change AronowAudit.P004.prob (w1ThreeP N) _ =
      AronowAudit.P004.prob (w1ThreeP N) _
    exact AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_congr
      (w1ThreeP N) _ _ hevent
  simpa [N] using hprob

theorem prob_eq_donor {N : ℕ} (p : Fin N → ℝ) (A : Assignment N → Prop) :
    SAP.P004a.prob p A = AronowAudit.P004.prob p A := rfl

theorem local_prob_congr {N : ℕ} (p : Fin N → ℝ)
    (A B : Assignment N → Prop) (h : ∀ z, A z ↔ B z) :
    SAP.P004a.prob p A = SAP.P004a.prob p B := by
  calc
    SAP.P004a.prob p A = AronowAudit.P004.prob p A := prob_eq_donor p A
    _ = AronowAudit.P004.prob p B :=
      AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_congr p A B h
    _ = SAP.P004a.prob p B := (prob_eq_donor p B).symm

theorem reindexed_additive_slutsky
    (p : ∀ K, Fin (3*K) → ℝ)
    (hp : ∀ K i, 0 < p K i ∧ p K i < 1)
    (T U : ∀ K, Assignment (3*K) → ℝ)
    (hT : W1NormalLimit (fun K => 3*K) p T)
    (hU : W1InProb (fun K => 3*K) p U) :
    W1NormalLimit (fun K => 3*K) p (fun K z => T K z + U K z) := by
  have hCDF : SAP.P004a.normalCDF = AronowAudit.P004.normalCDF := rfl
  have hclose (x η : ℝ) (hη : 0 < η) : ∃ δ : ℝ,
      0 < δ ∧
      |SAP.P004a.normalCDF (x-δ) - SAP.P004a.normalCDF x| < η ∧
      |SAP.P004a.normalCDF (x+δ) - SAP.P004a.normalCDF x| < η := by
    have hcont : ContinuousAt SAP.P004a.normalCDF x := by
      rw [hCDF]
      exact AronowAudit.P004.Wave1.DesignLimits.nf_proof.1.continuousAt
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hcont η hη
    have hminus : dist (x-r/2) x < r := by
      rw [Real.dist_eq]
      have heq : x-r/2-x = -(r/2) := by ring
      rw [heq, abs_neg, abs_of_pos (half_pos hr)]
      linarith
    have hplus : dist (x+r/2) x < r := by
      rw [Real.dist_eq]
      have heq : x+r/2-x = r/2 := by ring
      rw [heq, abs_of_pos (half_pos hr)]
      linarith
    refine ⟨r/2, half_pos hr, ?_, ?_⟩
    · simpa only [Real.dist_eq] using hball hminus
    · simpa only [Real.dist_eq] using hball hplus
  have hsandwich (x δ : ℝ) (hδ : 0 < δ) (K : ℕ) :
      prob (p K) (fun z => T K z ≤ x-δ) -
          prob (p K) (fun z => δ < |U K z|) ≤
        prob (p K) (fun z => T K z + U K z ≤ x) ∧
      prob (p K) (fun z => T K z + U K z ≤ x) ≤
        prob (p K) (fun z => T K z ≤ x+δ) +
          prob (p K) (fun z => δ < |U K z|) := by
    have hlo := AronowAudit.P004.Wave1.DesignLimits.prob_le_add_of_imp_finite
      (p K) (hp K) (fun z => T K z ≤ x-δ)
      (fun z => T K z + U K z ≤ x) (fun z => δ < |U K z|) (by
        intro z hz
        by_cases hb : δ < |U K z|
        · exact Or.inr hb
        · left
          have hUle : U K z ≤ δ := le_trans (le_abs_self _) (le_of_not_gt hb)
          linarith)
    have hup := AronowAudit.P004.Wave1.DesignLimits.prob_le_add_of_imp_finite
      (p K) (hp K) (fun z => T K z + U K z ≤ x)
      (fun z => T K z ≤ x+δ) (fun z => δ < |U K z|) (by
        intro z hz
        by_cases hb : δ < |U K z|
        · exact Or.inr hb
        · left
          have hUlo : -U K z ≤ δ := le_trans (neg_le_abs _) (le_of_not_gt hb)
          linarith)
    have hlo' : prob (p K) (fun z => T K z ≤ x-δ) ≤
        prob (p K) (fun z => T K z + U K z ≤ x) +
          prob (p K) (fun z => δ < |U K z|) := by
      simpa only [← prob_eq_donor] using hlo
    have hup' : prob (p K) (fun z => T K z + U K z ≤ x) ≤
        prob (p K) (fun z => T K z ≤ x+δ) +
          prob (p K) (fun z => δ < |U K z|) := by
      simpa only [← prob_eq_donor] using hup
    exact ⟨by linarith, by linarith⟩
  intro x
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨δ,hδ,hminus,_⟩ := hclose x ((SAP.P004a.normalCDF x-a)/2) (by linarith)
    have hgap : a < SAP.P004a.normalCDF (x-δ) := by
      have := (abs_lt.mp hminus).1
      linarith
    have hlim : Tendsto
        (fun K => prob (p K) (fun z => T K z ≤ x-δ) -
          prob (p K) (fun z => δ < |U K z|)) atTop
        (nhds (SAP.P004a.normalCDF (x-δ))) := by
      simpa using (hT (x-δ)).sub (hU δ hδ)
    filter_upwards [(tendsto_order.mp hlim).1 a hgap] with K hK
    exact lt_of_lt_of_le hK (hsandwich x δ hδ K).1
  · intro b hb
    obtain ⟨δ,hδ,_,hplus⟩ := hclose x ((b-SAP.P004a.normalCDF x)/2) (by linarith)
    have hgap : SAP.P004a.normalCDF (x+δ) < b := by
      have := (abs_lt.mp hplus).2
      linarith
    have hlim : Tendsto
        (fun K => prob (p K) (fun z => T K z ≤ x+δ) +
          prob (p K) (fun z => δ < |U K z|)) atTop
        (nhds (SAP.P004a.normalCDF (x+δ))) := by
      simpa using (hT (x+δ)).add (hU δ hδ)
    filter_upwards [(tendsto_order.mp hlim).2 b hgap] with K hK
    exact lt_of_le_of_lt (hsandwich x δ hδ K).2 hK

theorem expansion_root_remainder {θhat : ∀ N, Assignment N → Fin 2 → ℝ}
    (hExpansion : T1ExpansionStatement θhat) :
    W1InProb (fun K => 3*K) (fun K => w1ThreeP (3*K))
      (fun K z => Real.sqrt (3*K : ℕ) *
        (w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z)) := by
  intro ε hε
  have hsqrtN : Tendsto (fun K : ℕ => Real.sqrt (3*K : ℕ)) atTop atTop := by
    exact Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop.comp (SAP.P004a.WH.W1.multiples_tendsto 3 (by omega)))
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [] with K
    exact lt_of_lt_of_le ha
      (AronowAudit.P004.Wave1.DesignLimits.prob_nonneg_finite (w1ThreeP (3*K))
        (fun i => threeAdmissible (3*K) i) _)
  · intro b hb
    let δ : ℝ := b/2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨C,hC,hE⟩ := hExpansion δ hδ
    have hlarge : ∀ᶠ K : ℕ in atTop, C < ε * Real.sqrt (3*K : ℕ) := by
      have := hsqrtN.eventually (eventually_gt_atTop (C / ε))
      filter_upwards [this] with K hK
      simpa only [mul_comm] using (div_lt_iff₀ hε).1 hK
    have hNpos : ∀ᶠ K : ℕ in atTop, 0 < (3*K : ℕ) := by
      filter_upwards [eventually_gt_atTop 0] with K hK
      omega
    have hbound : ∀ᶠ K : ℕ in atTop,
        prob (w1ThreeP (3*K)) (fun z => ε < |Real.sqrt (3*K : ℕ) *
          (w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z)|) < b := by
      filter_upwards [hE, hlarge, hNpos] with K hE hlarge hK
      have hN : (0 : ℝ) < (3*K : ℕ) := by exact_mod_cast hK
      have hs : 0 < Real.sqrt (3*K : ℕ) := Real.sqrt_pos.2 hN
      have hsquare : (Real.sqrt (3*K : ℕ))^2 = (3*K : ℕ) :=
        Real.sq_sqrt (Nat.cast_nonneg (3*K))
      have hratio : C * |((3*K : ℕ) : ℝ)⁻¹| ≤ ε / Real.sqrt (3*K : ℕ) := by
        calc
          C * |((3*K : ℕ) : ℝ)⁻¹| = C / (3*K : ℕ) := by
            rw [abs_of_pos (inv_pos.mpr hN)]
            rfl
          _ ≤ ε / Real.sqrt (3*K : ℕ) :=
            (div_le_div_iff₀ hN hs).2 (by nlinarith [hlarge, hsquare])
      have hsub : ∀ z, ε < |Real.sqrt (3*K : ℕ) *
          (w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z)| →
          C * |((3*K : ℕ) : ℝ)⁻¹| <
            |w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z| := by
        intro z hz
        rw [abs_mul, abs_of_pos hs] at hz
        exact lt_of_le_of_lt hratio ((div_lt_iff₀ hs).2 (by nlinarith [hz]))
      have hm := AronowAudit.P004.Wave1.DesignLimits.DLbSupport.prob_mono
        (w1ThreeP (3*K)) (fun i => threeAdmissible (3*K) i) _ _ hsub
      have hEK : prob (w1ThreeP (3*K))
          (fun z => C * |((3*K : ℕ) : ℝ)⁻¹| <
            |w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z|) < δ := by
        simpa [T1ExpansionStatement, W1BigOp, δ] using hE
      have hEK' : AronowAudit.P004.prob (w1ThreeP (3*K))
          (fun z => C * |((3*K : ℕ) : ℝ)⁻¹| <
            |w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z|) < δ := by
        change prob (w1ThreeP (3*K)) _ < δ
        exact hEK
      exact lt_of_le_of_lt hm (lt_of_lt_of_le hEK' (by dsimp [δ]; linarith))
    exact hbound

end
end SAP.P004a.WH.W1.P.T1_L5

namespace SAP.P004a.WH.W1

open SAP.P004a.WH.W1.P.T1_L5
open Filter
noncomputable section

theorem T1_L5_proof : SAP.P004a.WH.W1.T1_L5 := by
  intro θhat _hlog hExpansion
  let p : ∀ K, Fin (3*K) → ℝ := fun K => w1ThreeP (3*K)
  let T : ∀ K, Assignment (3*K) → ℝ := fun K z =>
    Real.sqrt (3*K : ℕ) * w1ThreeLinear w1ThreeA (3*K) z /
      Real.sqrt (3/625 : ℝ)
  let U : ∀ K, Assignment (3*K) → ℝ := fun K z =>
    Real.sqrt (3*K : ℕ) *
      (w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z) /
        Real.sqrt (3/625 : ℝ)
  have hp (K : ℕ) (i : Fin (3*K)) : 0 < p K i ∧ p K i < 1 :=
    threeAdmissible (3*K) i
  have hLeading : W1NormalLimit (fun K => 3*K) p T := by
    simpa [p, T] using leading_restricted_clt
  have hRemainder := expansion_root_remainder hExpansion
  have hsC : 0 < Real.sqrt (3/625 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hU : W1InProb (fun K => 3*K) p U := by
    intro ε hε
    have hErr := hRemainder (ε * Real.sqrt (3/625 : ℝ)) (mul_pos hε hsC)
    have heq : (fun K => prob (p K) (fun z => ε < |U K z|)) =
        (fun K => prob (p K) (fun z => ε * Real.sqrt (3/625 : ℝ) <
          |Real.sqrt (3*K : ℕ) *
            (w1ThreeIPW θhat (3*K) z - w1ThreeLinear w1ThreeA (3*K) z)|)) := by
      funext K
      apply local_prob_congr
      intro z
      dsimp [U]
      rw [abs_div, abs_of_pos hsC, lt_div_iff₀ hsC]
    rw [heq]
    exact hErr
  have hSumLimit := reindexed_additive_slutsky p hp T U hLeading hU
  have hFirst : W1NormalLimit (fun K => 3*K) p
      (fun K z => Real.sqrt (3*K : ℕ) * w1ThreeIPW θhat (3*K) z /
        Real.sqrt (3/625 : ℝ)) := by
    intro x
    refine (hSumLimit x).congr (fun K => ?_)
    apply local_prob_congr
    intro z
    dsimp [T, U]
    ring_nf
  have hSecond : W1NormalLimit (fun K => 3*K) p
      (fun K z => w1ThreeIPW θhat (3*K) z /
        Real.sqrt (variance (w1ThreeP (3*K)) (w1ThreePrinted (3*K))) /
          Real.sqrt (3600/1753 : ℝ)) := by
    intro x
    have hlim := hFirst x
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop 0] with K hK
    have hKpos : 0 < K := by omega
    let N : ℕ := 3*K
    have hNpos : 0 < N := by dsimp [N]; omega
    have hN : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
    rcases SAP.P004a.WH.W1.three_linear K hKpos with ⟨_,_,_,hprint,_⟩
    have hprint' : (N : ℝ) * variance (w1ThreeP N) (w1ThreePrinted N) =
        1753/750000 := by simpa [N] using hprint
    have hvar : variance (w1ThreeP N) (w1ThreePrinted N) =
        (1753/750000 : ℝ) / (N : ℝ) := by
      apply (eq_div_iff hN).2
      nlinarith [hprint']
    have hvarpos : 0 < variance (w1ThreeP N) (w1ThreePrinted N) := by
      rw [hvar]
      exact div_pos (by norm_num) (by exact_mod_cast hNpos)
    have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hNpos)
    have hsV : 0 < Real.sqrt (variance (w1ThreeP N) (w1ThreePrinted N)) :=
      Real.sqrt_pos.mpr hvarpos
    have hsQ : 0 < Real.sqrt (3600/1753 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hdenSq :
        (Real.sqrt (variance (w1ThreeP N) (w1ThreePrinted N)) *
          Real.sqrt (3600/1753 : ℝ))^2 =
        (Real.sqrt (3/625 : ℝ) / Real.sqrt (N : ℝ))^2 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hvarpos),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3600/1753),
        div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3/625),
        Real.sq_sqrt (Nat.cast_nonneg N), hvar]
      field_simp [hN]
      norm_num
    have hden :
        Real.sqrt (variance (w1ThreeP N) (w1ThreePrinted N)) *
          Real.sqrt (3600/1753 : ℝ) =
        Real.sqrt (3/625 : ℝ) / Real.sqrt (N : ℝ) := by
      have hleftpos := mul_pos hsV hsQ
      have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
      have hrightpos := div_pos hsC (Real.sqrt_pos.mpr hNr)
      have hfactor :
          (Real.sqrt (variance (w1ThreeP N) (w1ThreePrinted N)) *
            Real.sqrt (3600/1753 : ℝ) - Real.sqrt (3/625 : ℝ) / Real.sqrt (N : ℝ)) *
          (Real.sqrt (variance (w1ThreeP N) (w1ThreePrinted N)) *
            Real.sqrt (3600/1753 : ℝ) + Real.sqrt (3/625 : ℝ) / Real.sqrt (N : ℝ)) = 0 := by
        nlinarith [hdenSq]
      rcases mul_eq_zero.mp hfactor with hEq | hSum
      · linarith
      · linarith
    have hstat (z : Assignment N) :
        w1ThreeIPW θhat N z /
            Real.sqrt (variance (w1ThreeP N) (w1ThreePrinted N)) /
              Real.sqrt (3600/1753 : ℝ) =
          Real.sqrt (N : ℝ) * w1ThreeIPW θhat N z /
            Real.sqrt (3/625 : ℝ) := by
      rw [div_div, hden]
      field_simp [ne_of_gt hsN, ne_of_gt hsC]
    have hEqProb : prob (p K)
        (fun z => w1ThreeIPW θhat N z /
          Real.sqrt (variance (w1ThreeP N) (w1ThreePrinted N)) /
            Real.sqrt (3600/1753 : ℝ) ≤ x) =
        prob (p K) (fun z => Real.sqrt (N : ℝ) * w1ThreeIPW θhat N z /
          Real.sqrt (3/625 : ℝ) ≤ x) := by
      apply local_prob_congr
      intro z
      rw [hstat z]
    simpa [p, N] using hEqProb.symm
  exact ⟨by simpa [p] using hFirst, by simpa [p] using hSecond⟩

end
end SAP.P004a.WH.W1
