import SAP.P013b.Bridge.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b.Bridge
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]

theorem school_B_marginal (a : School) :
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∈ z a.1) = 1/2 := by
  exact AronowAudit.P013.school_B_marginal a

theorem school_C_marginal (a : School) :
    uniformSchoolProbability schoolCSupport (fun z => a ∈ z) = 1/2 := by
  exact AronowAudit.P013.school_C_marginal a

theorem school_B_joint (a b : School) (hab : a ≠ b) :
    uniformSchoolProbability schoolBSupport
      (fun z => a.2 ∈ z a.1 ∧ b.2 ∈ z b.1) =
      if a.1 = b.1 then 1/6 else 1/4 := by
  exact AronowAudit.P013.school_B_joint a b hab

theorem school_C_joint (a b : School) (hab : a ≠ b) :
    uniformSchoolProbability schoolCSupport (fun z => a ∈ z ∧ b ∈ z) = 27/110 := by
  exact AronowAudit.P013.school_C_joint a b hab

theorem school_joint_differences  :
    (27/110 : ℝ) - 1/6 = 13/165 ∧ (27/110 : ℝ) - 1/4 = -(1/220) := by
  exact AronowAudit.P013.school_joint_differences

theorem school_B_pair_distribution (a b : School) (hab : a ≠ b) :
    let p : ℝ := if a.1 = b.1 then 1/6 else 1/4
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∉ z a.1 ∧ b.2 ∉ z b.1) = p ∧
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∉ z a.1 ∧ b.2 ∈ z b.1) = 1/2-p ∧
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∈ z a.1 ∧ b.2 ∉ z b.1) = 1/2-p ∧
    uniformSchoolProbability schoolBSupport (fun z => a.2 ∈ z a.1 ∧ b.2 ∈ z b.1) = p := by
  exact AronowAudit.P013.school_B_pair_distribution a b hab

theorem school_C_pair_distribution (a b : School) (hab : a ≠ b) :
    uniformSchoolProbability schoolCSupport (fun z => a ∉ z ∧ b ∉ z) = 27/110 ∧
    uniformSchoolProbability schoolCSupport (fun z => a ∉ z ∧ b ∈ z) = 14/55 ∧
    uniformSchoolProbability schoolCSupport (fun z => a ∈ z ∧ b ∉ z) = 14/55 ∧
    uniformSchoolProbability schoolCSupport (fun z => a ∈ z ∧ b ∈ z) = 27/110 := by
  exact AronowAudit.P013.school_C_pair_distribution a b hab

theorem school_exposure_probabilities_unchanged {Ξ : Type*} [Fintype Ξ] {N : ℕ}
    (_hN : 0 < N) (Q : Ξ → ℝ) (_hQ : ∀ x, 0 ≤ Q x) (_htotal : ∑ x, Q x = 1)
    (school : Fin N → School) (studentCode : Ξ → Fin N → Fin 4) :
    (∀ i d, schoolStudentMarginal schoolBSupport schoolBHosts Q school studentCode i d =
      schoolStudentMarginal schoolCSupport schoolCHosts Q school studentCode i d) ∧
    (∀ i j d e, school i = school j →
      schoolStudentJoint schoolBSupport schoolBHosts Q school studentCode i j d e =
        schoolStudentJoint schoolCSupport schoolCHosts Q school studentCode i j d e) := by
  exact AronowAudit.P013.school_exposure_probabilities_unchanged _hN Q _hQ _htotal school studentCode

theorem school_hosted_no_exposure (host : Bool) (studentCode : Fin 4) :
    schoolHostedExposure host studentCode = 0 ↔ host = false := by
  exact AronowAudit.P013.school_hosted_no_exposure host studentCode

theorem school_no_exposure_probabilities {Ξ : Type*} [Fintype Ξ] {N : ℕ}
    (Q : Ξ → ℝ) (_hQ : ∀ x, 0 ≤ Q x) (htotal : ∑ x, Q x = 1)
    (school : Fin N → School) (studentCode : Ξ → Fin N → Fin 4) :
    (∀ i, schoolStudentMarginal schoolBSupport schoolBHosts Q school studentCode i 0 = 1/2 ∧
      schoolStudentMarginal schoolCSupport schoolCHosts Q school studentCode i 0 = 1/2) ∧
    (∀ i j, school i ≠ school j →
      schoolStudentJoint schoolBSupport schoolBHosts Q school studentCode i j 0 0 =
        (if (school i).1 = (school j).1 then 1/6 else 1/4) ∧
      schoolStudentJoint schoolCSupport schoolCHosts Q school studentCode i j 0 0 = 27/110) := by
  exact AronowAudit.P013.school_no_exposure_probabilities Q _hQ htotal school studentCode

theorem section10_wearing_unbiased {N M : ℕ} (P : Design Ω) (hN : 0 < N)
    (analysed : Fin N → Fin M) (_hinjective : Function.Injective analysed)
    (school : Fin M → Fin 56) (hosts : Ω → Fin 56 → Bool)
    (assigned : Ω → Fin M → Bool) (neighbors : Fin M → Finset (Fin M))
    (y : Fin N → Fin 5 → ℝ) (_hbinary : ∀ i d, y i d = 0 ∨ y i d = 1)
    (_hdiag : ∀ i, i ∉ neighbors i)
    (_hsym : ∀ i j, j ∈ neighbors i ↔ i ∈ neighbors j)
    (_hschool : ∀ i j, j ∈ neighbors i → school i = school j)
    (hpos : ∀ i d, 0 < pi (section10Population P analysed school hosts assigned neighbors y) i d) :
    let F := section10Population P analysed school hosts assigned neighbors y
    (∀ z i, observed F z i = ∑ d, indicator F.exposure i d z * y i d) ∧
    (∀ d : Fin 5, d ≠ 0 →
      causalEffect F d 0 = (∑ i, y i d) / (N : ℝ) - (∑ i, y i 0) / (N : ℝ) ∧
      expectation P (htEffect F d 0) = causalEffect F d 0) := by
  exact AronowAudit.P013.section10_wearing_unbiased (toDesign P) hN analysed _hinjective school hosts assigned neighbors y _hbinary _hdiag _hsym _hschool hpos

end
end SAP.P013b.Bridge
