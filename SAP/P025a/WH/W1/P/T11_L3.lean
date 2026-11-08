import SAP.P025a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open AronowAudit.P025
open SAP.P025a
open scoped BigOperators

theorem SAP.P025a.WH.W1.T11_L3_proof : SAP.P025a.WH.W1.T11_L3 := by
  intro J hJ y m hm c hc
  dsimp only
  let mass : Fin J → ℝ := fun j => c * (m j : ℝ)
  let μ : ℝ := (∑ j, (m j : ℝ) * y j) / (∑ j, (m j : ℝ))
  have hmass : ∀ j, mass j ≠ 0 := by
    intro j
    dsimp [mass]
    exact ne_of_gt (mul_pos hc (Nat.cast_pos.mpr (hm j)))
  have hidentity : ∀ j, (m j : ℝ) / mass j = 1 / c := by
    intro j
    dsimp [mass]
    have hmne : (m j : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (hm j))
    field_simp [hmne, hc.ne']
  have hratio : ratio y mass (fun j => (m j : ℝ) / mass j) = μ := by
    simpa [SAP.P025a.ratio, AronowAudit.P025.ratio, μ, classMean] using
      (class_mean_ratio y mass m hmass)
  have htrue : (fun j => (m j : ℝ) / mass j) = (fun _ => 1 / c) := by
    funext j
    exact hidentity j
  have hconstant : ratio y mass (fun _ => 1 / c) = μ := by
    rw [← htrue]
    exact hratio
  have hbox (w : Fin J → ℝ) : weightBox c c w ↔ w = (fun _ => 1 / c) := by
    constructor
    · intro hw
      funext j
      exact le_antisymm (hw j).2 (hw j).1
    · intro hw
      subst w
      intro j
      exact ⟨le_rfl, le_rfl⟩
  have hsingleton : attainable y mass c c = {μ} := by
    ext v
    constructor
    · rintro ⟨w, hw, hval⟩
      have hw' : w = (fun _ => 1 / c) := (hbox w).1 hw
      rw [hw'] at hval
      rw [hconstant] at hval
      exact hval.symm
    · intro hv
      have hv' : v = μ := by simpa using hv
      subst v
      exact ⟨(fun _ => 1 / c), (hbox _).2 rfl, hconstant⟩
  refine ⟨hidentity, hratio, hbox, hsingleton, ?_, ?_, ?_, ?_⟩
  · rw [hsingleton]
    exact isLeast_singleton
  · rw [hsingleton]
    exact isGreatest_singleton
  · change sInf (attainable y mass c c) = μ
    rw [hsingleton, csInf_singleton]
  · change sSup (attainable y mass c c) = μ
    rw [hsingleton, csSup_singleton]

