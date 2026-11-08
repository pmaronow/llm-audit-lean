import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open SAP.P003a.Bridge

attribute [local instance 0] Classical.propDecidable

theorem SAP.P003a.WH.W2.T14_L2_proof : SAP.P003a.WH.W2.T14_L2 := by
  intro k hk f
  let q : W2Lattice k ≃ ℤ :=
    (Equiv.ofBijective (w2Point k) (point_bijective k hk)).symm
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hcoord (x : W2Lattice k) :
      x.val * f x = ((q x : ℤ) : ℝ) * w2Rescale f (q x) / (k : ℝ) := by
    have hqx : w2Point k (q x) = x := q.symm_apply_apply x
    have hxv : x.val = ((q x : ℤ) : ℝ) / (k : ℝ) := by
      have hv := congrArg Subtype.val hqx
      simpa [w2Point] using hv.symm
    have hmass : w2Rescale f (q x) = f x := by
      change f (w2Point k (q x)) = f x
      rw [hqx]
    rw [hxv, hmass]
    field_simp [hkR]
  have hfun :
      (fun x : W2Lattice k => x.val * f x) =
        (fun x : W2Lattice k => (q x : ℝ) * w2Rescale f (q x) / (k : ℝ)) :=
    funext hcoord
  have hsum_reindex :
      Summable (fun x : W2Lattice k => x.val * f x) ↔
        Summable (fun j : ℤ => (j : ℝ) * w2Rescale f j / (k : ℝ)) := by
    rw [hfun]
    exact q.summable_iff (f := fun j : ℤ => (j : ℝ) * w2Rescale f j / (k : ℝ))
  have htsum_reindex :
      (∑' x : W2Lattice k, x.val * f x) =
        ∑' j : ℤ, (j : ℝ) * w2Rescale f j / (k : ℝ) := by
    calc
      (∑' x : W2Lattice k, x.val * f x) =
          ∑' x : W2Lattice k, (q x : ℝ) * w2Rescale f (q x) / (k : ℝ) := by
        apply tsum_congr
        exact hcoord
      _ = ∑' j : ℤ, (j : ℝ) * w2Rescale f j / (k : ℝ) :=
        q.tsum_eq (fun j : ℤ => (j : ℝ) * w2Rescale f j / (k : ℝ))
  refine ⟨?_, ?_⟩
  · change Summable (fun x : W2Lattice k => x.val * f x) ↔
      Summable (fun j : ℤ => (j : ℝ) * w2Rescale f j)
    exact hsum_reindex.trans (summable_div_const_iff hkR)
  · intro hm
    have hmean : w2SourceMean f =
        (∑' j : ℤ, (j : ℝ) * w2Rescale f j) / (k : ℝ) := by
      change (∑' x : W2Lattice k, x.val * f x) = _
      rw [htsum_reindex, tsum_div_const]
    refine ⟨hmean, ?_⟩
    intro c₂
    rw [hmean]
    constructor
    · intro h
      field_simp [hkR] at h ⊢
      linarith
    · intro h
      field_simp [hkR] at h ⊢
      linarith
