import SAP.P011c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
open AronowAudit.P011.ProbabilityCompletion
open AronowAudit.P011.CoverageCompletion
open Causalean.Mathlib.Probability.SteinMethod

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

theorem SAP.P011c.WH.W1.T38_L1_proof : SAP.P011c.WH.W1.T38_L1 := by
  intro F c1 c2 c3 c4 h
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let (k : ℕ) : IsProbabilityMeasure (Bridge.toModel (F.model k)).law :=
    (F.model k).probability
  rcases h with ⟨hc1, hc2, hc3, hc4, hDep, hBound, hDeg, hVar, hTheta⟩
  have hL2 (k : ℕ) (i : Fin (F.size k)) :=
    weighted_memLp (Bridge.toModel (F.model k)) c1 (hBound k) i
  let X : ∀ k, Fin (F.size k) → (Fin (F.size k) → ℝ) → ℝ := fun k i y =>
    weighted (F.model k) y i - expectation (F.model k)
      (fun z => weighted (F.model k) z i)
  let D := fun k => modelDep (Bridge.toModel (F.model k)) (hDep k)
  have hdeg (k : ℕ) (i : Fin (F.size k)) : ((D k).nbhd i).card ≤ ⌈c2⌉₊ + 1 := by
    dsimp [D]
    rw [modelDep_degree]
    change degree (F.model k).G i + 1 ≤ ⌈c2⌉₊ + 1
    have hh : degree (F.model k).G i ≤ ⌈c2⌉₊ := by
      exact_mod_cast (hDeg k i).trans (Nat.le_ceil c2)
    omega
  have hb (k : ℕ) (i : Fin (F.size k)) :
      ∀ᵐ y ∂(F.model k).law, |X k i y| ≤ 2 * c1 :=
    (own_centred_bound (Bridge.toModel (F.model k)) c1 (hL2 k) (hBound k)).mono
      (fun y hy => hy i)
  have hm (k : ℕ) (i : Fin (F.size k)) : ∫ y, X k i y ∂(F.model k).law = 0 := by
    change (∫ y, (AronowAudit.P011.weighted (Bridge.toModel (F.model k)) y i -
      AronowAudit.P011.expectation (Bridge.toModel (F.model k))
        (fun z => AronowAudit.P011.weighted (Bridge.toModel (F.model k)) z i))
      ∂(Bridge.toModel (F.model k)).law) = 0
    rw [integral_sub ((hL2 k i).integrable (by norm_num)) (integrable_const _)]
    simp [AronowAudit.P011.expectation]
  let v := fun k => (F.size k : ℝ)^2 * var (F.model k) (betaHat (F.model k))
  have hv (k : ℕ) : ∫ y, (depSum (X k) y)^2 ∂(F.model k).law = v k :=
    sum_variance (F.positive k) (Bridge.toModel (F.model k)) (hL2 k)
  have hvc : ∀ᶠ k in atTop,
      (c3 / 2) * (Fintype.card (Fin (F.size k)) : ℝ) ≤ v k := by
    have hev : ∀ᶠ k in atTop,
        c3 / 2 < (F.size k : ℝ) * var (F.model k) (betaHat (F.model k)) :=
      hVar.eventually (Ioi_mem_nhds (show c3 / 2 < c3 by linarith))
    filter_upwards [hev] with k hk
    dsimp [v]
    simp only [Fintype.card_fin]
    have hn : 0 < (F.size k : ℝ) := by exact_mod_cast F.positive k
    nlinarith
  intro t
  have hh := bounded_degree_dependency_clt_ae (fun k => (F.model k).law) X D
    (⌈c2⌉₊ + 1) hdeg (2 * c1) hb hm v hv (c3 / 2) (by linarith) hvc
    (by simpa only [Fintype.card_fin] using F.grows) t
  have hid (k : ℕ) :
      (fun y => depSum (X k) y / Real.sqrt (v k)) = standardized (F.model k) :=
    funext (depSum_standardized (F.positive k) (Bridge.toModel (F.model k)) (hL2 k))
  simp only [hid] at hh
  have hPhi : (gaussianReal 0 1).real (Set.Iic t) = Phi t :=
    (ProbabilityTheory.cdf_eq_real (gaussianReal 0 1) t).symm
  rw [hPhi] at hh
  convert hh using 1
  funext k
  have hstd : Measurable (standardized (F.model k)) :=
    ((betaHat_measurable (Bridge.toModel (F.model k))).sub measurable_const).div_const _
  symm
  simpa [probability, Set.preimage, Set.Iic] using
    map_measureReal_apply hstd measurableSet_Iic

