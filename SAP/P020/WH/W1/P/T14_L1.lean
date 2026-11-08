import SAP.P020.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter

namespace SAP.P020.WH.W1.P.T14_L1

open SAP.P020.WH.W1

theorem linear_hasDerivAt (A B x : ℝ) :
    HasDerivAt (fun y : ℝ => A * y + B) A x := by
  simpa using (hasDerivAt_const_mul A).add_const B

theorem linear_right_hasDerivAt (A B x : ℝ) :
    HasDerivAt (fun y : ℝ => y * A + B) A x := by
  simpa using (hasDerivAt_mul_const A).add_const B

theorem quadratic_hasDerivAt (A B C x : ℝ) :
    HasDerivAt (fun y : ℝ => A * y ^ 2 + B * y + C) (2 * A * x + B) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hA : HasDerivAt (fun y : ℝ => A * y ^ 2) (A * (2 * x)) x :=
    hpow.const_mul A
  have hB : HasDerivAt (fun y : ℝ => B * y) B x := hasDerivAt_const_mul B
  have hC : HasDerivAt (fun _ : ℝ => C) 0 x := hasDerivAt_const x C
  have h := (hA.add hB).add hC
  convert h using 1 <;> ring

end SAP.P020.WH.W1.P.T14_L1

open SAP.P020.WH.W1

theorem SAP.P020.WH.W1.T14_L1_proof : SAP.P020.WH.W1.T14_L1 := by
  intro P
  refine ⟨?_, ?_⟩
  · intro a k
    let s : ℝ := W1SizeVariance P
    let q : ℝ := W1SizeCovariance P a
    let C : ℝ := clusterVariance (if a then P.y1 else P.y0)
    have hexp (x : ℝ) : W1ArmVariance P a x =
        C + x ^ 2 * s - 2 * x * q := (arm_expansion P a x).2.2
    have hfun : W1ArmVariance P a = fun x : ℝ => s * x ^ 2 + (-2 * q) * x + C := by
      funext x
      rw [hexp]
      ring
    have hfirst (x : ℝ) : HasDerivAt (W1ArmVariance P a)
        (2 * x * s - 2 * q) x := by
      have hnear : W1ArmVariance P a =ᶠ[nhds x]
          (fun y : ℝ => s * y ^ 2 + (-2 * q) * y + C) :=
        Filter.Eventually.of_forall fun y => congrFun hfun y
      have h := (SAP.P020.WH.W1.P.T14_L1.quadratic_hasDerivAt s (-2 * q) C x).congr_of_eventuallyEq hnear
      exact h.congr_deriv (by ring)
    have hderiv : deriv (W1ArmVariance P a) = fun x : ℝ => 2 * x * s - 2 * q :=
      funext fun x => (hfirst x).deriv
    have hsecond : HasDerivAt (deriv (W1ArmVariance P a)) (2 * s) k := by
      rw [hderiv]
      have heq : (fun x : ℝ => 2 * x * s - 2 * q) =
          (fun x : ℝ => x * (2 * s) + (-2 * q)) := by
        funext x
        ring
      exact (SAP.P020.WH.W1.P.T14_L1.linear_right_hasDerivAt (2 * s) (-2 * q) k).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun x => congrFun heq x)
    exact ⟨hfirst k, hsecond⟩
  · intro k
    let s : ℝ := W1SizeVariance P
    let q0 : ℝ := W1SizeCovariance P false
    let q1 : ℝ := W1SizeCovariance P true
    let c : ℝ := W1c P
    let t : ℝ := W1t P
    let A : ℝ := (c + t + 2) * s
    let B : ℝ := -2 * ((c + 1) * q0 + (t + 1) * q1)
    let C : ℝ := c * clusterVariance P.y0 + t * clusterVariance P.y1 +
      2 * clusterCovariance P.y0 P.y1
    have hexp (x : ℝ) : rajMomentObjective P x =
        c * (clusterVariance P.y0 + x ^ 2 * s - 2 * x * q0) +
        t * (clusterVariance P.y1 + x ^ 2 * s - 2 * x * q1) +
        2 * (clusterCovariance P.y0 P.y1 - x * q0 - x * q1 + x ^ 2 * s) :=
      (objective_expansion P x).2
    have hfun : rajMomentObjective P = fun x : ℝ => A * x ^ 2 + B * x + C := by
      funext x
      rw [hexp]
      dsimp [A, B, C]
      ring
    have hfirst (x : ℝ) : HasDerivAt (rajMomentObjective P) (2 * A * x + B) x := by
      have hnear : rajMomentObjective P =ᶠ[nhds x]
          (fun y : ℝ => A * y ^ 2 + B * y + C) :=
        Filter.Eventually.of_forall fun y => congrFun hfun y
      exact (SAP.P020.WH.W1.P.T14_L1.quadratic_hasDerivAt A B C x).congr_of_eventuallyEq hnear
    have hfirst_target (x : ℝ) : HasDerivAt (rajMomentObjective P)
        (W1c P * (2 * x * W1SizeVariance P - 2 * W1SizeCovariance P false) +
         W1t P * (2 * x * W1SizeVariance P - 2 * W1SizeCovariance P true) +
         2 * (-W1SizeCovariance P false - W1SizeCovariance P true +
           2 * x * W1SizeVariance P)) x := by
      have h := hfirst x
      apply h.congr_deriv
      dsimp [A, B, c, t, s, q0, q1]
      ring
    have hderiv : deriv (rajMomentObjective P) = fun x : ℝ => 2 * A * x + B :=
      funext fun x => (hfirst x).deriv
    have hderiv_target (x : ℝ) : deriv (rajMomentObjective P) x =
        2 * (W1c P + W1t P + 2) * x * W1SizeVariance P -
          2 * ((W1c P + 1) * W1SizeCovariance P false +
            (W1t P + 1) * W1SizeCovariance P true) := by
      rw [hderiv]
      dsimp [A, B]
      ring
    have hsecond : HasDerivAt (deriv (rajMomentObjective P))
        (2 * (W1c P + W1t P + 2) * W1SizeVariance P) k := by
      rw [hderiv]
      have hlin := SAP.P020.WH.W1.P.T14_L1.linear_hasDerivAt (2 * A) B k
      have hslope : 2 * A = 2 * (W1c P + W1t P + 2) * W1SizeVariance P := by
        dsimp [A, c, t, s]
        ring
      exact hlin.congr_deriv hslope
    exact ⟨hfirst_target k, hderiv_target k, hsecond⟩

