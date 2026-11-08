import SAP.P009b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b.WH.W1.P.T27_L3

noncomputable section
attribute [local instance] Classical.propDecidable

lemma prob_singleton {Ω : Type*} [Fintype Ω] (P : SAP.P009b.Law Ω) (x : Ω) :
    SAP.P009b.prob P (fun z => z = x) = P.mass x := by
  classical
  simp [SAP.P009b.prob, SAP.P009b.mean, Finset.sum_ite_eq']

lemma prob_mono {Ω : Type*} [Fintype Ω] (P : SAP.P009b.Law Ω)
    (A B : Ω → Prop) (hAB : ∀ z, A z → B z) :
    SAP.P009b.prob P A ≤ SAP.P009b.prob P B := by
  simpa [SAP.P009b.prob, SAP.P009b.mean, SAP.P009b.Bridge.toLaw,
    AronowAudit.P009.prob, AronowAudit.P009.mean] using
      AronowAudit.P009.finite_probability_mono (SAP.P009b.Bridge.toLaw P) A B hAB

lemma prob_complement_singleton {Ω : Type*} [Fintype Ω]
    (P : SAP.P009b.Law Ω) (x : Ω) :
    SAP.P009b.prob P (fun z => z ≠ x) = 1 - P.mass x := by
  calc
    SAP.P009b.prob P (fun z => z ≠ x) =
        AronowAudit.P009.prob (SAP.P009b.Bridge.toLaw P) (fun z => ¬ z = x) := rfl
    _ = 1 - AronowAudit.P009.prob (SAP.P009b.Bridge.toLaw P) (fun z => z = x) :=
      AronowAudit.P009.probability_complement (SAP.P009b.Bridge.toLaw P)
        (fun z => z = x)
    _ = 1 - SAP.P009b.prob P (fun z => z = x) := rfl
    _ = 1 - P.mass x := by rw [prob_singleton]

lemma prob_le_outside_singleton {Ω : Type*} [Fintype Ω]
    (P : SAP.P009b.Law Ω) (x : Ω) (A : Ω → Prop)
    (hA : ∀ z, A z → z ≠ x) :
    SAP.P009b.prob P A ≤ 1 - P.mass x := by
  calc
    SAP.P009b.prob P A ≤ SAP.P009b.prob P (fun z => z ≠ x) :=
      prob_mono P A (fun z => z ≠ x) hA
    _ = 1 - P.mass x := prob_complement_singleton P x

end

end SAP.P009b.WH.W1.P.T27_L3

open SAP.P009b.WH.W1.P.T27_L3

theorem SAP.P009b.WH.W1.T27_L3_proof : SAP.P009b.WH.W1.T27_L3 := by
  classical
  intro P hmass c hc f hlimits
  rcases hlimits with ⟨hplus, hminus⟩
  let x : (b : ℕ) → SAP.P009b.Assignment b := fun _ _ => false
  have houtside : Tendsto (fun b => 1 - (P b).mass (x b)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
    simpa [x] using hconst.sub hmass
  have hplus_ev : ∀ᶠ b : ℕ in atTop,
      c/2 < SAP.P009b.prob (P b) (fun z => f b z = 1) :=
    hplus.eventually (Ioi_mem_nhds (by linarith))
  have hminus_ev : ∀ᶠ b : ℕ in atTop,
      c/2 < SAP.P009b.prob (P b) (fun z => f b z = -1) :=
    hminus.eventually (Ioi_mem_nhds (by linarith))
  have hout_ev : ∀ᶠ b : ℕ in atTop, 1 - (P b).mass (x b) < c/2 :=
    houtside.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨b, ⟨hbplus, hbminus⟩, hbout⟩ :=
    (hplus_ev.and hminus_ev |>.and hout_ev).exists
  by_cases hx : f b (x b) = 1
  · have hnot : ∀ z, f b z = -1 → z ≠ x b := by
      intro z hz hzx
      subst z
      linarith
    have hbound := prob_le_outside_singleton (P b) (x b)
      (fun z => f b z = -1) hnot
    linarith
  · have hnot : ∀ z, f b z = 1 → z ≠ x b := by
      intro z hz hzx
      subst z
      exact hx hz
    have hbound := prob_le_outside_singleton (P b) (x b)
      (fun z => f b z = 1) hnot
    linarith
