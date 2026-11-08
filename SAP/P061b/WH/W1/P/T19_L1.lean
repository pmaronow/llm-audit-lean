import SAP.P061b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061b.WH.W1.P.T19_L1

open SAP.P061b
open SAP.P061b.Bridge
open AronowAudit.P061
open scoped BigOperators Classical

end SAP.P061b.WH.W1.P.T19_L1

open SAP.P061b
open SAP.P061b.Bridge
open AronowAudit.P061
open scoped BigOperators Classical

set_option maxHeartbeats 800000 in
theorem SAP.P061b.WH.W1.T19_L1_proof : SAP.P061b.WH.W1.T19_L1 := by
  intro Ω N D g y d hp hn
  let D₀ := SAP.P061b.Bridge.toAudit D
  have hp₀ : ∀ i, 0 < AronowAudit.P061.pi D₀ g i d := by
    intro i
    simpa [D₀, AronowAudit.P061.pi, AronowAudit.P061.probability,
      SAP.P061b.exposureProbability, SAP.P061b.eventProbability,
      SAP.P061b.Bridge.toAudit] using hp i
  have hn₀ : AronowAudit.P061.NURVA D₀ g y := by
    intro i z w hz hw he
    exact hn i z w hz hw he
  have hpair (i j : Fin N) :
      AronowAudit.P061.Integrable D₀
        (fun z =>
          ((AronowAudit.P061.jointPi D₀ g i j d d -
              AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d) /
            (AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d)) *
            y i z * y j z *
            (if g i z = d ∧ g j z = d then 1 else 0) /
            AronowAudit.P061.jointPi D₀ g i j d d) := by
    classical
    let P := fun (i j : Fin N) (z : Ω) =>
      ((AronowAudit.P061.jointPi D₀ g i j d d -
          AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d) /
        (AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d)) *
        y i z * y j z * (if g i z = d ∧ g j z = d then 1 else 0) /
        AronowAudit.P061.jointPi D₀ g i j d d
    let C := fun (i j : Fin N) =>
      ((AronowAudit.P061.jointPi D₀ g i j d d -
          AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d) /
        (AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d)) *
        AronowAudit.P061.epo D₀ g y i d * AronowAudit.P061.epo D₀ g y j d
    let J := fun z : Ω => g i z = d ∧ g j z = d
    have he : ∀ z, AronowAudit.P061.Support D₀ z →
        P i j z = AronowAudit.P061.eventResponse J
          (C i j / AronowAudit.P061.jointPi D₀ g i j d d) z := by
      intro z hz
      by_cases hi : g i z = d <;> by_cases hj : g j z = d
      · have hi' := (AronowAudit.P061.nurva_epo D₀ g y hn₀ i d (hp₀ i) z hz hi).symm
        have hj' := (AronowAudit.P061.nurva_epo D₀ g y hn₀ j d (hp₀ j) z hz hj).symm
        simp only [P, C, AronowAudit.P061.eventResponse, J, hi, hj,
          and_self, ite_true, hi', hj', mul_one]
      · simp [P, C, AronowAudit.P061.eventResponse, J, hi, hj]
      · simp [P, C, AronowAudit.P061.eventResponse, J, hi, hj]
      · simp [P, C, AronowAudit.P061.eventResponse, J, hi, hj]
    change AronowAudit.P061.Integrable D₀ (P i j)
    exact (AronowAudit.P061.integrable_support_congr D₀ _ _ he).2
      (AronowAudit.P061.integrable_event D₀ J _)
  have hsingle (i : Fin N) :
      AronowAudit.P061.Integrable D₀
        (fun z => (if g i z = d then y i z ^ 2 / 2 else 0) /
          AronowAudit.P061.pi D₀ g i d) := by
    classical
    let S := fun (i : Fin N) (z : Ω) =>
      (if g i z = d then y i z ^ 2 / 2 else 0) /
        AronowAudit.P061.pi D₀ g i d
    have he : ∀ z, AronowAudit.P061.Support D₀ z →
        S i z = AronowAudit.P061.eventResponse (fun z => g i z = d)
          (AronowAudit.P061.epo D₀ g y i d ^ 2 / 2 /
            AronowAudit.P061.pi D₀ g i d) z := by
      intro z hz
      by_cases hi : g i z = d
      · have hi' := (AronowAudit.P061.nurva_epo D₀ g y hn₀ i d (hp₀ i) z hz hi).symm
        simp [S, AronowAudit.P061.eventResponse, hi, hi']
      · simp [S, AronowAudit.P061.eventResponse, hi]
    change AronowAudit.P061.Integrable D₀ (S i)
    exact (AronowAudit.P061.integrable_support_congr D₀ _ _ he).2
      (AronowAudit.P061.integrable_event D₀ _ _)
  have hconservativePair (i j : Fin N) :
      AronowAudit.P061.Integrable D₀
        (fun z => if 0 < AronowAudit.P061.jointPi D₀ g i j d d then
          ((AronowAudit.P061.jointPi D₀ g i j d d -
              AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d) /
            (AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d)) *
            y i z * y j z *
            (if g i z = d ∧ g j z = d then 1 else 0) /
            AronowAudit.P061.jointPi D₀ g i j d d
          else if AronowAudit.P061.jointPi D₀ g i j d d = 0 then
            (if g i z = d then y i z ^ 2 / 2 else 0) /
                AronowAudit.P061.pi D₀ g i d +
              (if g j z = d then y j z ^ 2 / 2 else 0) /
                AronowAudit.P061.pi D₀ g j d
          else 0) := by
    classical
    let R := fun (i j : Fin N) (z : Ω) =>
      if 0 < AronowAudit.P061.jointPi D₀ g i j d d then
        ((AronowAudit.P061.jointPi D₀ g i j d d -
            AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d) /
          (AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d)) *
          y i z * y j z *
          (if g i z = d ∧ g j z = d then 1 else 0) /
          AronowAudit.P061.jointPi D₀ g i j d d
      else if AronowAudit.P061.jointPi D₀ g i j d d = 0 then
        (if g i z = d then y i z ^ 2 / 2 else 0) /
            AronowAudit.P061.pi D₀ g i d +
          (if g j z = d then y j z ^ 2 / 2 else 0) /
            AronowAudit.P061.pi D₀ g j d
      else 0
    change AronowAudit.P061.Integrable D₀ (R i j)
    by_cases hr : 0 < AronowAudit.P061.jointPi D₀ g i j d d
    · simpa only [R, if_pos hr] using hpair i j
    · have hr0 : AronowAudit.P061.jointPi D₀ g i j d d = 0 :=
        le_antisymm (le_of_not_gt hr)
          (AronowAudit.P061.probability_nonneg D₀ _)
      simp only [R, if_neg hr, if_pos hr0]
      exact AronowAudit.P061.integrable_add D₀ (hsingle i) (hsingle j)
  have hht : HasFirstMoment D (htVarianceEstimate D g y d) := by
    change AronowAudit.P061.Integrable D₀
      (AronowAudit.P061.htVarianceEstimator D₀ g y d)
    unfold AronowAudit.P061.htVarianceEstimator
    have hsum : AronowAudit.P061.Integrable D₀
        (fun z => ∑ i, ∑ j,
          ((AronowAudit.P061.jointPi D₀ g i j d d -
              AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d) /
            (AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d)) *
            y i z * y j z *
            (if g i z = d ∧ g j z = d then 1 else 0) /
            AronowAudit.P061.jointPi D₀ g i j d d) := by
      exact AronowAudit.P061.integrable_sum D₀ _ (fun i =>
        AronowAudit.P061.integrable_sum D₀ _ (fun j => hpair i j))
    exact AronowAudit.P061.integrable_mul D₀ hsum ((N : ℝ)⁻¹ ^ 2)
  have hcons : HasFirstMoment D (conservativeVarianceEstimate D g y d) := by
    change AronowAudit.P061.Integrable D₀
      (AronowAudit.P061.conservativeVarianceEstimator D₀ g y d)
    unfold AronowAudit.P061.conservativeVarianceEstimator
    have hsum : AronowAudit.P061.Integrable D₀
        (fun z => ∑ i, ∑ j,
          (if 0 < AronowAudit.P061.jointPi D₀ g i j d d then
            ((AronowAudit.P061.jointPi D₀ g i j d d -
                AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d) /
              (AronowAudit.P061.pi D₀ g i d * AronowAudit.P061.pi D₀ g j d)) *
              y i z * y j z *
              (if g i z = d ∧ g j z = d then 1 else 0) /
              AronowAudit.P061.jointPi D₀ g i j d d
            else if AronowAudit.P061.jointPi D₀ g i j d d = 0 then
              (if g i z = d then y i z ^ 2 / 2 else 0) /
                  AronowAudit.P061.pi D₀ g i d +
                (if g j z = d then y j z ^ 2 / 2 else 0) /
                  AronowAudit.P061.pi D₀ g j d
            else 0)) := by
      exact AronowAudit.P061.integrable_sum D₀ _ (fun i =>
        AronowAudit.P061.integrable_sum D₀ _ (fun j => hconservativePair i j))
    exact AronowAudit.P061.integrable_mul D₀ hsum ((N : ℝ)⁻¹ ^ 2)
  exact ⟨fun hj => hht, hcons⟩

