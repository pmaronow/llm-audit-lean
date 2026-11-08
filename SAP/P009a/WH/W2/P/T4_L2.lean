import SAP.P009a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009a.WH.W2.P.T4_L2

open scoped BigOperators Classical

lemma expectation_eq_of_support_eq {Ω : Type} [Fintype Ω]
    (P : SAP.P009a.FiniteDistribution Ω) (u v : Ω → ℝ)
    (h : ∀ ω, 0 < P.mass ω → u ω = v ω) :
    SAP.P009a.expectation P u = SAP.P009a.expectation P v := by
  unfold SAP.P009a.expectation
  apply Finset.sum_congr rfl
  intro ω hω
  by_cases hp : 0 < P.mass ω
  · rw [h ω hp]
  · have hz : P.mass ω = 0 := le_antisymm (not_lt.mp hp) (P.nonneg ω)
    simp [hz]

lemma covariance_eq_of_support_eq {Ω : Type} [Fintype Ω]
    (P : SAP.P009a.FiniteDistribution Ω) (u u' v v' : Ω → ℝ)
    (hu : ∀ ω, 0 < P.mass ω → u ω = u' ω)
    (hv : ∀ ω, 0 < P.mass ω → v ω = v' ω) :
    SAP.P009a.covariance P u v = SAP.P009a.covariance P u' v' := by
  have hmu := expectation_eq_of_support_eq P u u' hu
  have hmv := expectation_eq_of_support_eq P v v' hv
  unfold SAP.P009a.covariance
  rw [hmu, hmv]
  apply expectation_eq_of_support_eq
  intro ω hp
  rw [hu ω hp, hv ω hp]

end SAP.P009a.WH.W2.P.T4_L2

theorem SAP.P009a.WH.W2.T4_L2_proof : SAP.P009a.WH.W2.T4_L2 := by
  intro Ω A B _ _ _ P X Y f g M N hM hN hf hg
  let fT : A → ℝ := fun a => AronowAudit.P009.Wave1.t4_trunc M (f a)
  let gT : B → ℝ := fun b => AronowAudit.P009.Wave1.t4_trunc N (g b)
  have hf_support (ω : Ω) (hω : 0 < P.mass ω) :
      f (X ω) = fT (X ω) := by
    simp only [fT, AronowAudit.P009.Wave1.t4_trunc]
    rw [if_pos (hf ω hω)]
  have hg_support (ω : Ω) (hω : 0 < P.mass ω) :
      g (Y ω) = gT (Y ω) := by
    simp only [gT, AronowAudit.P009.Wave1.t4_trunc]
    rw [if_pos (hg ω hω)]
  have hcov := SAP.P009a.WH.W2.P.T4_L2.covariance_eq_of_support_eq P
    (fun ω => f (X ω)) (fun ω => fT (X ω))
    (fun ω => g (Y ω)) (fun ω => gT (Y ω)) hf_support hg_support
  have hb := AronowAudit.P009.Wave1.t4_bounded_covariance
    (SAP.P009a.Bridge.toProjectDistribution P) X Y fT gT M N hM hN
    (fun a => AronowAudit.P009.Wave1.t4_trunc_abs M (f a) hM)
    (fun b => AronowAudit.P009.Wave1.t4_trunc_abs N (g b) hN)
  rw [← SAP.P009a.Bridge.covariance_correspondence,
    ← SAP.P009a.Bridge.mixing_correspondence] at hb
  rw [hcov]
  exact hb
