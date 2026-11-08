import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
attribute [local instance 0] Classical.propDecidable

theorem SAP.P003a.WH.W2.T14_L1_proof : SAP.P003a.WH.W2.T14_L1 := by
  intro k hk f hf
  let e : ℤ ≃ SAP.P003a.W2Lattice k :=
    Equiv.ofBijective (SAP.P003a.w2Point k)
      (SAP.P003a.WH.W2.point_bijective k hk)
  have hnonneg : ∀ j : ℤ, 0 ≤ SAP.P003a.w2Rescale f j := by
    intro j
    exact hf.1 (SAP.P003a.w2Point k j)
  have hsum : Summable (SAP.P003a.w2Rescale f) := by
    apply (Equiv.summable_iff e).2
    simpa only [Function.comp_apply, SAP.P003a.w2Rescale, e] using hf.2.1
  have htotal : (∑' j : ℤ, SAP.P003a.w2Rescale f j) = 1 := by
    calc
      (∑' j : ℤ, SAP.P003a.w2Rescale f j) =
          ∑' j : ℤ, f (e j) := by rfl
      _ = ∑' x : SAP.P003a.W2Lattice k, f x := Equiv.tsum_eq e f
      _ = 1 := hf.2.2
  refine ⟨⟨hnonneg, hsum, htotal⟩, ?_⟩
  intro j
  have hfiber : (fun x : SAP.P003a.W2Lattice k =>
      if (k : ℝ) * x.val = (j : ℝ) then f x else 0) =
      fun x => if x = SAP.P003a.w2Point k j then f x else 0 := by
    funext x
    have hcoord := SAP.P003a.WH.W2.point_coordinate k hk x j
    exact if_congr hcoord rfl rfl
  rw [SAP.P003a.w2ImageMass, hfiber, tsum_ite_eq]
  rfl

