import SAP.P037a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal NNReal Classical Topology

theorem SAP.P037a.WH.W2.T5_L3_proof : SAP.P037a.WH.W2.T5_L3 := by
  intro hInv m e he
  let T : ℝ := ∑ i, e i
  have hT : 0 < T := by
    dsimp [T]
    exact SAP.P037a.WH.W2.positive_totalW2 m e he
  have hTne : T ≠ 0 := hT.ne'
  have hsum : DifferentiableAt ℝ (fun x : Fin (m+1) → ℝ => ∑ i, x i) e := by
    fun_prop
  have hrecip : DifferentiableAt ℝ (fun x : Fin (m+1) → ℝ => (∑ i, x i)⁻¹) e :=
    hsum.inv (by simpa [T] using hTne)
  have hnorm : DifferentiableAt ℝ (fun x : Fin (m+1) → ℝ =>
      SAP.P037a.normalizedWeights x) e := by
    rw [differentiableAt_pi]
    intro i
    have hi : DifferentiableAt ℝ (fun x : Fin (m+1) → ℝ => x i) e := by fun_prop
    have hmul := hi.mul hrecip
    convert hmul using 1 <;> ext x <;>
      simp [SAP.P037a.normalizedWeights, div_eq_mul_inv]
  have hF : DifferentiableAt ℝ (SAP.P037a.forwardNormalizationW2 m) e := by
    rw [differentiableAt_pi]
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [SAP.P037a.forwardNormalizationW2, Fin.snoc_last] using hsum
    · have hj : DifferentiableAt ℝ
        (fun x : Fin (m+1) → ℝ => SAP.P037a.normalizedWeights x j.castSucc) e :=
        differentiableAt_pi.mp hnorm j.castSucc
      simpa [SAP.P037a.forwardNormalizationW2, Fin.snoc_castSucc,
        SAP.P037a.headCoordinatesW2] using hj
  have hy : SAP.P037a.forwardNormalizationW2 m e ∈ SAP.P037a.normalizationDomainW2 m :=
    (SAP.P037a.WH.W2.geometry_proofW2 m).1 e he |>.1
  have hH : DifferentiableAt ℝ (SAP.P037a.inverseNormalizationW2 m)
      (SAP.P037a.forwardNormalizationW2 m e) := (hInv m _ hy).1
  have hposEv : ∀ᶠ x : Fin (m+1) → ℝ in 𝓝 e,
      x ∈ SAP.P037a.positiveOrthantW2 (m+1) := by
    have hn : Set.pi (Set.univ : Set (Fin (m+1))) (fun _ : Fin (m+1) => Ioi (0 : ℝ))
        ∈ 𝓝 e := by
      exact set_pi_mem_nhds Set.finite_univ (fun i _ => Ioi_mem_nhds (he i))
    filter_upwards [hn] with x hx
    exact fun i => hx i (by simp)
  have hEq : (fun x : Fin (m+1) → ℝ => x) =ᶠ[𝓝 e]
      (SAP.P037a.inverseNormalizationW2 m ∘ SAP.P037a.forwardNormalizationW2 m) := by
    filter_upwards [hposEv] with x hx
    exact ((SAP.P037a.WH.W2.geometry_proofW2 m).1 x hx).2.symm
  have hcomp := hH.hasFDerivAt.comp e hF.hasFDerivAt
  have hcomp' := hcomp.congr_of_eventuallyEq hEq
  have hid : HasFDerivAt (fun x : Fin (m+1) → ℝ => x) (ContinuousLinearMap.id ℝ _) e :=
    hasFDerivAt_id e
  have hlin := hcomp'.unique hid
  have hdetLin : LinearMap.det
      ((fderiv ℝ (SAP.P037a.inverseNormalizationW2 m)
          (SAP.P037a.forwardNormalizationW2 m e)).toLinearMap.comp
        (fderiv ℝ (SAP.P037a.forwardNormalizationW2 m) e).toLinearMap) = 1 := by
    have h := congrArg ContinuousLinearMap.toLinearMap hlin
    rw [ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.coe_id] at h
    have hdet' := congrArg
      (fun L : (Fin (m+1) → ℝ) →ₗ[ℝ] (Fin (m+1) → ℝ) => LinearMap.det L) h
    rw [LinearMap.det_comp, LinearMap.det_id] at hdet'
    simpa only [LinearMap.det_comp] using hdet'
  rw [LinearMap.det_comp] at hdetLin
  have hdet :
      |(fderiv ℝ (SAP.P037a.inverseNormalizationW2 m)
          (SAP.P037a.forwardNormalizationW2 m e)).det| *
        |(fderiv ℝ (SAP.P037a.forwardNormalizationW2 m) e).det| = 1 := by
    rw [← abs_mul, hdetLin, abs_one]
  have hInvDet :
      |(fderiv ℝ (SAP.P037a.inverseNormalizationW2 m)
          (SAP.P037a.forwardNormalizationW2 m e)).det| = T^m := by
    simpa [T, SAP.P037a.WH.W2.last_forwardW2] using (hInv m _ hy).2
  have hdetHne :
      |(fderiv ℝ (SAP.P037a.inverseNormalizationW2 m)
          (SAP.P037a.forwardNormalizationW2 m e)).det| ≠ 0 := by
    rw [hInvDet]
    exact pow_ne_zero _ hTne
  have hgoal :
      |(fderiv ℝ (SAP.P037a.forwardNormalizationW2 m) e).det| = (T^m)⁻¹ := by
    calc
      _ = (|(fderiv ℝ (SAP.P037a.inverseNormalizationW2 m)
            (SAP.P037a.forwardNormalizationW2 m e)).det| *
          |(fderiv ℝ (SAP.P037a.forwardNormalizationW2 m) e).det|) /
          |(fderiv ℝ (SAP.P037a.inverseNormalizationW2 m)
            (SAP.P037a.forwardNormalizationW2 m e)).det| := by
          field_simp
      _ = (T^m)⁻¹ := by rw [hdet, hInvDet]; simp
  constructor
  · exact hF
  · simpa [T] using hgoal

