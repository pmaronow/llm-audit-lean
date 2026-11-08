import SAP.P029a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology

universe u v

theorem SAP.P029a.WH.W1.T4_L4_proof : SAP.P029a.WH.W1.T4_L4 := by
  intro Ω X _ _ μ _ a s A p ha hs hp hdom
  let I := Sum (WholeCellIndex X) X
  let q : I → ℝ := fun i => Sum.elim A p i
  let f : ℕ → Ω → I → ℝ := fun n ω i => Sum.elim (a n ω) (s n ω) i
  let B : (I → ℝ) → Bool → Fin 3 → ℝ := fun w z k =>
    ∑ x : X, (1 / w (Sum.inr x)) * w (Sum.inl (x, z, k))
  let F : (I → ℝ) → ℝ := fun w =>
    (B w true 1 / B w true 0 - B w false 1 / B w false 0) /
      (B w true 2 / B w true 0 - B w false 2 / B w false 0)
  have hcoords : ∀ i, TendstoInMeasure μ (fun n ω => f n ω i) atTop
      (fun _ => q i) := by
    intro i
    cases i with
    | inl c => simpa [f, q] using ha c
    | inr x => simpa [f, q] using hs x
  have hB : ∀ z k, ContinuousAt (fun w => B w z k) q := by
    intro z k
    change Tendsto (fun w => ∑ x : X,
      (1 / w (Sum.inr x)) * w (Sum.inl (x, z, k))) (𝓝 q)
      (𝓝 (∑ x : X, (1 / q (Sum.inr x)) * q (Sum.inl (x, z, k))))
    apply tendsto_finsetSum Finset.univ
    intro x hx
    have hrec : ContinuousAt (fun w => 1 / w (Sum.inr x)) q := by
      apply continuousAt_const.div (continuous_apply _).continuousAt
      simpa [q] using hp x
    have hval : ContinuousAt (fun w => w (Sum.inl (x, z, k))) q :=
      (continuous_apply _).continuousAt
    exact (hrec.mul hval).tendsto
  have hBt0 : B q true 0 ≠ 0 := by
    simpa [B, q, wholeCellArm] using hdom.1
  have hBf0 : B q false 0 ≠ 0 := by
    simpa [B, q, wholeCellArm] using hdom.2.1
  have hBd : B q true 2 / B q true 0 - B q false 2 / B q false 0 ≠ 0 := by
    simpa [B, q, wholeCellArm] using hdom.2.2
  have hyT : ContinuousAt (fun w => B w true 1 / B w true 0) q :=
    (hB true 1).div (hB true 0) hBt0
  have hyF : ContinuousAt (fun w => B w false 1 / B w false 0) q :=
    (hB false 1).div (hB false 0) hBf0
  have hdT : ContinuousAt (fun w => B w true 2 / B w true 0) q :=
    (hB true 2).div (hB true 0) hBt0
  have hdF : ContinuousAt (fun w => B w false 2 / B w false 0) q :=
    (hB false 2).div (hB false 0) hBf0
  have hnum : ContinuousAt
      (fun w => B w true 1 / B w true 0 - B w false 1 / B w false 0) q :=
    hyT.sub hyF
  have hden : ContinuousAt
      (fun w => B w true 2 / B w true 0 - B w false 2 / B w false 0) q :=
    hdT.sub hdF
  have hF : ContinuousAt F q := by
    dsimp [F]
    exact hnum.div hden hBd
  have hlim := AronowAudit.P015.ConvergenceCompletion.finite_cmt μ f q F hcoords hF
  simpa [F, B, f, q, wholeCellWald, wholeCellArm] using hlim
