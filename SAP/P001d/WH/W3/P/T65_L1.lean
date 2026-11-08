import SAP.P001d.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Topology

namespace SAP.P001d.WH.W3.P.T65_L1

theorem coordinate_normal_equation {n K : ℕ}
    (X : Matrix (Fin n) (Fin (K + 1)) ℝ) (Y : Fin n → ℝ)
    (b : Fin (K + 1) → ℝ)
    (hmin : ∀ c, SAP.P001d.olsRSS X Y b ≤ SAP.P001d.olsRSS X Y c)
    (k : Fin (K + 1)) :
    ∑ i, X i k * (Y i - (X.mulVec b) i) = 0 := by
  classical
  let f : ℝ → ℝ := fun t => SAP.P001d.olsRSS X Y (b + t • Pi.single k 1)
  have hlocal : IsLocalMin f 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), f 0 ≤ f t
    filter_upwards [] with t
    simpa [f] using hmin (b + t • Pi.single k 1)
  have hpath (i : Fin n) :
      HasDerivAt
        (fun t : ℝ => Y i - (X.mulVec (b + t • Pi.single k 1)) i)
        (-(X i k)) 0 := by
    have hfun :
        (fun t : ℝ => Y i - (X.mulVec (b + t • Pi.single k 1)) i) =
          fun t => (Y i - (X.mulVec b) i) - t * X i k := by
      funext t
      simp [Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.col_apply, Pi.smul_apply]
      ring
    have hbase : HasDerivAt
        (fun t : ℝ => (Y i - (X.mulVec b) i) - t * X i k)
        (-(X i k)) 0 := by
      have hbase0 := (hasDerivAt_const 0 (Y i - (X.mulVec b) i)).sub
        ((hasDerivAt_id 0).mul_const (X i k))
      have hbasefun :
          ((fun t : ℝ => Y i - (X.mulVec b) i) - fun t => id t * X i k) =
            (fun t => (Y i - (X.mulVec b) i) - t * X i k) := by
        funext t
        simp
      rw [hbasefun] at hbase0
      simpa using hbase0
    rw [hfun]
    exact hbase
  have hsq (i : Fin n) :
      HasDerivAt
        (fun t : ℝ => (Y i - (X.mulVec (b + t • Pi.single k 1)) i) ^ 2)
        (2 * (Y i - (X.mulVec b) i) * (-(X i k))) 0 := by
    simpa using! (hpath i).pow 2
  have hderiv : HasDerivAt f
      (∑ i, 2 * (Y i - (X.mulVec b) i) * (-X i k)) 0 := by
    simpa [f, SAP.P001d.olsRSS] using
      (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hsq i))
  have hz := hlocal.hasDerivAt_eq_zero hderiv
  have hfactor :
      (∑ i, 2 * (Y i - (X.mulVec b) i) * (-X i k)) =
        -(2 * (∑ i, X i k * (Y i - (X.mulVec b) i))) := by
    calc
      (∑ i, 2 * (Y i - (X.mulVec b) i) * (-X i k)) =
          ∑ i, -(2 * (X i k * (Y i - (X.mulVec b) i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = -(∑ i, 2 * (X i k * (Y i - (X.mulVec b) i))) := by
            simpa using (Finset.sum_neg_distrib (s := Finset.univ)
              (f := fun i : Fin n => 2 * (X i k * (Y i - (X.mulVec b) i)))
              )
      _ = -(2 * (∑ i, X i k * (Y i - (X.mulVec b) i))) := by
            congr 1
            simpa using (Finset.mul_sum (Finset.univ : Finset (Fin n))
              (fun i => X i k * (Y i - (X.mulVec b) i)) 2).symm
  rw [hfactor] at hz
  have htwice : 2 * (∑ i, X i k * (Y i - (X.mulVec b) i)) = 0 := by
    linarith
  linarith

end SAP.P001d.WH.W3.P.T65_L1

theorem SAP.P001d.WH.W3.T65_L1_proof : SAP.P001d.WH.W3.T65_L1 := by
  classical
  intro n K X Y b hmin
  ext k
  simpa [Matrix.mulVec, dotProduct] using
    SAP.P001d.WH.W3.P.T65_L1.coordinate_normal_equation X Y b hmin k
