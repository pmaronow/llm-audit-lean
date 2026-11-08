import SAP.P018a.WH.W2.Leaves
import Mathlib.Probability.Independence.Integration

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W2.P.T3_L1

open Finset MeasureTheory ProbabilityTheory

private lemma sign_mul_self {N : ℕ} (i : Fin N) (ω : Fin N → Bool) :
    AronowAudit.P018.signValue (ω i) * AronowAudit.P018.signValue (ω i) = 1 := by
  simpa [pow_two] using AronowAudit.P018.Wave1.printed_sign_square (ω i)

end SAP.P018a.WH.W2.P.T3_L1

open SAP.P018a.WH.W2.P.T3_L1
open AronowAudit.P018.Wave1
open MeasureTheory ProbabilityTheory

theorem SAP.P018a.WH.W2.T3_L1_proof : SAP.P018a.WH.W2.T3_L1 := by
  classical
  intro N i j k l
  let P := AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N
  let X : Fin N → (Fin N → Bool) → ℝ := fun a ω => AronowAudit.P018.signValue (ω a)
  letI : IsProbabilityMeasure AronowAudit.P018.fairLaw := printed_fair_probability
  letI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  have hind : iIndepFun X P := by
    dsimp [X, P, AronowAudit.P018.unitSampleLaw, AronowAudit.P018.signKernel]
    exact iIndepFun_pi (μ := fun _ : Fin N => AronowAudit.P018.fairLaw)
      (X := fun _ => AronowAudit.P018.signValue)
      (fun _ => (measurable_of_countable AronowAudit.P018.signValue).aemeasurable)
  have hpair (a b : Fin N) : (∫ ω, X a ω * X b ω ∂ P) = if a = b then 1 else 0 := by
    change (∫ ω, AronowAudit.P018.signValue (ω a) * AronowAudit.P018.signValue (ω b)
      ∂ AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N) = _
    exact appendixB_coord_product a b
  have hsmul (a : Fin N) (ω : Fin N → Bool) : X a ω * X a ω = 1 :=
    sign_mul_self a ω
  change (∫ ω, X i ω * X j ω * X k ω * X l ω ∂ P) =
    (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0) - (if i = j ∧ j = k ∧ k = l then 2 else 0)
  by_cases hij : i = j
  · subst j
    have hpoint : (fun ω : Fin N → Bool => X i ω * X i ω * X k ω * X l ω) =
        (fun ω => X k ω * X l ω) := by
      funext ω
      calc
        X i ω * X i ω * X k ω * X l ω = (X i ω * X i ω) * (X k ω * X l ω) := by ring
        _ = X k ω * X l ω := by rw [hsmul]; ring
    rw [hpoint, hpair]
    by_cases hkl : k = l
    · subst l
      by_cases hik : i = k
      · subst k
        norm_num
      · simp [hik]
    · have hbad₁ : ¬ (i = k ∧ i = l) := by
        rintro ⟨hik, hil⟩
        exact hkl (hik.symm.trans hil)
      have hbad₂ : ¬ (i = l ∧ i = k) := by
        rintro ⟨hil, hik⟩
        exact hkl (hik.symm.trans hil)
      simp [hkl, hbad₁, hbad₂]
  · by_cases hkl : k = l
    · subst l
      have hpoint : (fun ω : Fin N → Bool => X i ω * X j ω * X k ω * X k ω) =
          (fun ω => X i ω * X j ω) := by
        funext ω
        calc
          X i ω * X j ω * X k ω * X k ω = (X k ω * X k ω) * (X i ω * X j ω) := by ring
          _ = X i ω * X j ω := by rw [hsmul]; ring
      rw [hpoint, hpair]
      have hbad : ¬ (i = k ∧ j = k) := by
        rintro ⟨hik, hjk⟩
        exact hij (hik.trans hjk.symm)
      simp [hij, hbad]
    · by_cases hik : i = k
      · subst k
        by_cases hjl : j = l
        · subst l
          have hpoint : (fun ω : Fin N → Bool => X i ω * X j ω * X i ω * X j ω) =
              (fun _ => 1) := by
            funext ω
            calc
              X i ω * X j ω * X i ω * X j ω = (X i ω * X i ω) * (X j ω * X j ω) := by ring
              _ = 1 := by rw [hsmul, hsmul]; norm_num
          rw [hpoint]
          simp [hij]
        · have hpoint : (fun ω : Fin N → Bool => X i ω * X j ω * X i ω * X l ω) =
              (fun ω => X j ω * X l ω) := by
            funext ω
            calc
              X i ω * X j ω * X i ω * X l ω = (X i ω * X i ω) * (X j ω * X l ω) := by ring
              _ = X j ω * X l ω := by rw [hsmul]; ring
          rw [hpoint, hpair]
          have hbad : ¬ (i = l ∧ j = i) := by
            rintro ⟨hil, hji⟩
            exact hij hji.symm
          simp [hij, hjl, hbad]
      · by_cases hil : i = l
        · subst l
          by_cases hjk : j = k
          · subst k
            have hpoint : (fun ω : Fin N → Bool => X i ω * X j ω * X j ω * X i ω) =
                (fun _ => 1) := by
              funext ω
              calc
                X i ω * X j ω * X j ω * X i ω = (X i ω * X i ω) * (X j ω * X j ω) := by ring
                _ = 1 := by rw [hsmul, hsmul]; norm_num
            rw [hpoint]
            simp [hij]
          · have hpoint : (fun ω : Fin N → Bool => X i ω * X j ω * X k ω * X i ω) =
                (fun ω => X j ω * X k ω) := by
              funext ω
              calc
                X i ω * X j ω * X k ω * X i ω = (X i ω * X i ω) * (X j ω * X k ω) := by ring
                _ = X j ω * X k ω := by rw [hsmul]; ring
            rw [hpoint, hpair]
            simp [hij, hik, hjk]
        · by_cases hjk : j = k
          · subst k
            have hpoint : (fun ω : Fin N → Bool => X i ω * X j ω * X j ω * X l ω) =
                (fun ω => X i ω * X l ω) := by
              funext ω
              calc
                X i ω * X j ω * X j ω * X l ω = (X j ω * X j ω) * (X i ω * X l ω) := by ring
                _ = X i ω * X l ω := by rw [hsmul]; ring
            rw [hpoint, hpair]
            simp [hij, hil]
          · by_cases hjl : j = l
            · subst l
              have hpoint : (fun ω : Fin N → Bool => X i ω * X j ω * X k ω * X j ω) =
                  (fun ω => X i ω * X k ω) := by
                funext ω
                calc
                  X i ω * X j ω * X k ω * X j ω = (X j ω * X j ω) * (X i ω * X k ω) := by ring
                  _ = X i ω * X k ω := by rw [hsmul]; ring
              rw [hpoint, hpair]
              simp [hij, hik, hjk]
            · have hdist (a b : Fin N) (h : a ≠ b) :
                (∫ ω, X a ω * X b ω ∂ P) = 0 := by
                  rw [hpair]
                  simp [h]
              have hfour : (fun ω : Fin N → Bool => X i ω * X j ω * X k ω * X l ω) =
                  (fun ω => (X i ω * X j ω) * (X k ω * X l ω)) := by
                funext ω
                ring
              rw [hfour]
              change (∫ ω, (X i * X j) ω * (X k * X l) ω ∂ P) = _
              have hindpair := hind.indepFun_mul_mul
                (fun a => (measurable_of_countable AronowAudit.P018.signValue).comp
                  (measurable_pi_apply a))
                i j k l hik hil hjk hjl
              rw [hindpair.integral_fun_mul_eq_mul_integral (by fun_prop) (by fun_prop)]
              have hdi : (∫ ω, (X i * X j) ω ∂ P) = 0 := by
                change (∫ ω, X i ω * X j ω ∂ P) = 0
                exact hdist i j hij
              have hdk : (∫ ω, (X k * X l) ω ∂ P) = 0 := by
                change (∫ ω, X k ω * X l ω ∂ P) = 0
                exact hdist k l hkl
              rw [hdi, hdk]
              simp [hij, hkl, hik, hil, hjk, hjl]
