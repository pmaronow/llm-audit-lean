import SAP.P001c.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped BigOperators Classical

noncomputable section

theorem SAP.P001c.WH.W1.T49_L1_proof : SAP.P001c.WH.W1.T49_L1 := by
  intro Ω mΩ μ pμ K X Y hX hY hfin
  have hpred (b : Fin (K + 1) → ℝ) :
      Measurable (fun ω => SAP.P001c.affinePredictor b (X ω)) := by
    unfold SAP.P001c.affinePredictor
    fun_prop
  have hres_meas (b : Fin (K + 1) → ℝ) :
      Measurable (SAP.P001c.affineResidual X Y b) := by
    unfold SAP.P001c.affineResidual
    exact hY.sub (hpred b)
  have hres (b : Fin (K + 1) → ℝ) :
      MemLp (SAP.P001c.affineResidual X Y b) 2 μ := by
    apply (memLp_two_iff_integrable_sq (hres_meas b).aestronglyMeasurable).2
    exact hfin b
  have hY2 : MemLp Y 2 μ := by
    let b0 : Fin (K + 1) → ℝ := fun _ => 0
    have hz := hres b0
    have heq : SAP.P001c.affineResidual X Y b0 = Y := by
      funext ω
      simp [SAP.P001c.affineResidual, SAP.P001c.affinePredictor, b0]
    rw [heq] at hz
    exact hz
  refine ⟨?_, hres⟩
  intro k
  let bk : Fin (K + 1) → ℝ := fun j => if j = k.succ then 1 else 0
  have hYminusX : MemLp (fun ω => Y ω - X ω k) 2 μ := by
    have hk := hres bk
    have heq : SAP.P001c.affineResidual X Y bk = (fun ω => Y ω - X ω k) := by
      funext ω
      simp [SAP.P001c.affineResidual, SAP.P001c.affinePredictor, bk,
        Fin.succ_inj, Ne.symm (Fin.succ_ne_zero k), Finset.sum_ite_eq']
    rw [heq] at hk
    exact hk
  have hXk : MemLp (fun ω => X ω k) 2 μ := by
    have h := hY2.sub hYminusX
    have heq : Y - (fun ω => Y ω - X ω k) = (fun ω => X ω k) := by
      funext ω
      change Y ω - (Y ω - X ω k) = X ω k
      ring
    rw [heq] at h
    exact h
  exact hXk
