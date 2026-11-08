import SAP.P029b.WH.W2.Leaves
import AronowAudit.P015.P015_ConvergenceCompletion
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W2.P.T27_L4

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable section

def cellObs (x z : Bool) (a : CancelAtomW2) : ℝ :=
  if a.1.1 = x ∧ a.2 = z then 1 else 0

def successObs (x z : Bool) (a : CancelAtomW2) : ℝ :=
  if a.1.1 = x ∧ a.2 = z then bit ((cancelUnitW2 a).receipt a.2) else 0

def empiricalAvg (f : CancelAtomW2 → ℝ) (n : ℕ) (ω : CancelSpaceW2) : ℝ :=
  (∑ i : Fin (n+1), f (ω i.val)) / (n+1)

lemma empiricalAvg_measurable (f : CancelAtomW2 → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (fun ω => empiricalAvg f n ω) := by
  unfold empiricalAvg
  apply Measurable.div
  · apply Finset.measurable_sum
    intro i hi
    exact hf.comp (measurable_pi_apply i.val)
  · exact measurable_const

lemma empiricalAvg_tendstoInMeasure (f : CancelAtomW2 → ℝ) (hf : Measurable f)
    (hbound : ∀ a, ‖f a‖ ≤ 1) :
    TendstoInMeasure cancelSampleLawW2 (fun n ω => empiricalAvg f n ω) atTop
      (fun _ => ∫ a, f a ∂cancelLawW2) := by
  let μ : Measure CancelSpaceW2 := cancelSampleLawW2
  let P : Measure CancelAtomW2 := cancelLawW2
  let Y : ℕ → CancelSpaceW2 → ℝ := fun i ω => f (ω i)
  have hP : IsProbabilityMeasure P := by
    dsimp [P, cancelLawW2]
    infer_instance
  letI : IsProbabilityMeasure P := hP
  have hμ : IsProbabilityMeasure μ := by
    dsimp [μ, cancelSampleLawW2]
    infer_instance
  letI : IsProbabilityMeasure μ := hμ
  have hbound_ae : ∀ᵐ a ∂P, ‖f a‖ ≤ 1 := Filter.Eventually.of_forall hbound
  have hint : Integrable f P := Integrable.of_bound hf.aestronglyMeasurable 1 hbound_ae
  have hMP : ∀ i : ℕ, MeasurePreserving (fun ω : CancelSpaceW2 => ω i) μ P := by
    intro i
    exact measurePreserving_eval_infinitePi (μ := fun _ : ℕ => P) i
  have hYmeas : ∀ i, Measurable (Y i) := fun i => hf.comp (measurable_pi_apply i)
  have hY0 : Integrable (Y 0) μ := by
    have hc := (hMP 0).integrable_comp hf.aestronglyMeasurable
    simpa [Y, Function.eval] using! hc.mpr hint
  have hind : iIndepFun Y μ := by
    simpa [CancelSpaceW2, cancelSampleLawW2, Y, μ, P] using
      (iIndepFun_infinitePi (Ω := fun _ : ℕ => CancelAtomW2)
        (P := fun _ : ℕ => P) (X := fun _ : ℕ => f) (fun _ => hf))
  have hmap : ∀ i : ℕ, Measure.map (Y i) μ = Measure.map f P := by
    intro i
    have hcomp : Y i = f ∘ (fun ω : CancelSpaceW2 => ω i) := by
      funext ω
      rfl
    rw [hcomp, ← Measure.map_map hf (measurable_pi_apply i), (hMP i).map_eq]
  have hident : ∀ i : ℕ, IdentDistrib (Y i) (Y 0) μ μ := by
    intro i
    exact
      { aemeasurable_fst := (hYmeas i).aemeasurable
        aemeasurable_snd := (hYmeas 0).aemeasurable
        map_eq := by rw [hmap i, hmap 0] }
  have hsl : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, Y i ω) / n) atTop (𝓝 (∫ a, f a ∂P)) := by
    have hs := strong_law_ae_real Y hY0 (fun i j hij => hind.indepFun hij) hident
    filter_upwards [hs] with ω hω
    have hmean : ∫ a, Y 0 a ∂μ = ∫ a, f a ∂P := by
      have hi : ∫ a, f a ∂P = ∫ ω, f (ω 0) ∂μ := by
        rw [← (hMP 0).map_eq]
        exact integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable
      simpa [Y] using hi.symm
    simpa [hmean] using hω
  have hsl' : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n+1), Y i ω) / (n+1)) atTop
        (𝓝 (∫ a, f a ∂P)) := by
    filter_upwards [hsl] with ω hω
    convert hω.comp (tendsto_add_atTop_nat 1) using 1 <;>
      ext n <;> simp [Function.comp_def, Nat.cast_add, Nat.cast_one]
  have hae : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => empiricalAvg f n ω) atTop (𝓝 (∫ a, f a ∂P)) := by
    filter_upwards [hsl'] with ω hω
    apply hω.congr'
    filter_upwards [] with n
    unfold empiricalAvg Y
    rw [← Fin.sum_univ_eq_sum_range (fun i => f (ω i))]
  have hconv : TendstoInMeasure μ (fun n ω => empiricalAvg f n ω) atTop
      (fun _ => ∫ a, f a ∂P) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (empiricalAvg_measurable f hf n).aestronglyMeasurable) hae
  simpa [μ, P] using hconv

lemma cellObs_integral (x z : Bool) :
    ∫ a, cellObs x z a ∂cancelLawW2 = (1/4 : ℝ) := by
  cases x <;> cases z <;>
    norm_num [cellObs, cancelLawW2, PMF.integral_eq_sum, PMF.uniformOfFintype_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ]

lemma successObs_integral (x z : Bool) :
    ∫ a, successObs x z a ∂cancelLawW2 = if z then (1/6 : ℝ) else (1/12 : ℝ) := by
  cases x <;> cases z <;>
    norm_num [successObs, cancelLawW2, cancelUnitW2, cancelSignW2, PotentialUnit.receipt, bit,
      PMF.integral_eq_sum, PMF.uniformOfFintype_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ]

lemma cellObs_measurable (x z : Bool) : Measurable (cellObs x z) := by
  exact Measurable.of_discrete

lemma successObs_measurable (x z : Bool) : Measurable (successObs x z) := by
  exact Measurable.of_discrete

lemma cellObs_bound (x z : Bool) (a : CancelAtomW2) : ‖cellObs x z a‖ ≤ 1 := by
  unfold cellObs
  split_ifs <;> norm_num

lemma successObs_bound (x z : Bool) (a : CancelAtomW2) : ‖successObs x z a‖ ≤ 1 := by
  unfold successObs
  split_ifs with h
  · cases hr : (cancelUnitW2 a).receipt a.2 <;> simp [bit]
  · norm_num

lemma cellAvg_eq (n : ℕ) (ω : CancelSpaceW2) (x z : Bool) :
    empiricalAvg (cellObs x z) n ω = cancelCellFractionW2 n ω x z := by
  simp [empiricalAvg, cancelCellFractionW2, cellObs]

lemma rate_eq_avg_div (n : ℕ) (ω : CancelSpaceW2) (x z : Bool) :
    cancelRateW2 n ω x z =
      empiricalAvg (successObs x z) n ω / empiricalAvg (cellObs x z) n ω := by
  change
    (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then
      bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0) /
      (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then (1 : ℝ) else 0) =
    ((∑ i : Fin (n+1), successObs x z (ω i.val)) / (n+1)) /
      ((∑ i : Fin (n+1), cellObs x z (ω i.val)) / (n+1))
  have hnum :
      (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then
        bit ((cancelDrawW2 i.val ω).receipt (cancelZW2 i.val ω)) else 0) =
      ∑ i : Fin (n+1), successObs x z (ω i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  have hden :
      (∑ i : Fin (n+1), if (ω i.val).1.1 = x ∧ (ω i.val).2 = z then (1 : ℝ) else 0) =
      ∑ i : Fin (n+1), cellObs x z (ω i.val) := by
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  rw [hnum, hden]
  have hN : (n+1 : ℝ) ≠ 0 := by positivity
  exact (div_div_div_cancel_right₀ hN _ _).symm

lemma success_limit (x z : Bool) :
    TendstoInMeasure cancelSampleLawW2
      (fun n ω => empiricalAvg (successObs x z) n ω) atTop
      (fun _ => if z then (1/6 : ℝ) else (1/12 : ℝ)) := by
  simpa [successObs_integral] using
    empiricalAvg_tendstoInMeasure (successObs x z) (successObs_measurable x z)
      (successObs_bound x z)

lemma cell_limit (x z : Bool) :
    TendstoInMeasure cancelSampleLawW2
      (fun n ω => empiricalAvg (cellObs x z) n ω) atTop (fun _ => (1/4 : ℝ)) := by
  simpa [cellObs_integral] using
    empiricalAvg_tendstoInMeasure (cellObs x z) (cellObs_measurable x z)
      (cellObs_bound x z)

lemma rate_limit (x z : Bool) :
    TendstoInMeasure cancelSampleLawW2 (fun n ω => cancelRateW2 n ω x z) atTop
      (fun _ => if z then (2/3 : ℝ) else (1/3 : ℝ)) := by
  rw [show (fun n ω => cancelRateW2 n ω x z) =
    (fun n ω => empiricalAvg (successObs x z) n ω / empiricalAvg (cellObs x z) n ω) by
      funext n ω
      exact rate_eq_avg_div n ω x z]
  have hdiv := AronowAudit.P015.ConvergenceCompletion.div_limit cancelSampleLawW2
    (success_limit x z) (cell_limit x z) (by norm_num : (1/4 : ℝ) ≠ 0)
  have hlim : (fun _ : CancelSpaceW2 => if z then (2/3 : ℝ) else 1/3) =
      (fun _ => (if z then (1/6 : ℝ) else 1/12) / (1/4 : ℝ)) := by
    funext ω
    cases z <;> norm_num
  rw [hlim]
  exact hdiv

end
end SAP.P029b.WH.W2.P.T27_L4

theorem SAP.P029b.WH.W2.T27_L4_proof : SAP.P029b.WH.W2.T27_L4 := by
  intro x z
  constructor
  · simpa [SAP.P029b.WH.W2.P.T27_L4.cellAvg_eq] using
      SAP.P029b.WH.W2.P.T27_L4.cell_limit x z
  · exact SAP.P029b.WH.W2.P.T27_L4.rate_limit x z
