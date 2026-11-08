import SAP.P009b.Defs.WholeW3
import SAP.P009b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P009b.WH.W3
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Real-order finite Jensen interpolation, including m = 0 and m = q.
Apply `Real.concaveOn_rpow` with theta = m/q in [0,1] and
`ConcaveOn.le_map_sum` to the probability weights and the nonnegative values
|X|^q. Rewrite (|X|^q)^(m/q) = |X|^m with `Real.rpow_mul` and q > 0.
This generalizes the donor's positive natural order to all real orders in
[0,q], without excluding zero outcomes at either endpoint. -/
def T29_L1 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] (P : Law Ω) (X : Ω → ℝ) (m q : ℝ),
    0 ≤ m → 0 < q → m ≤ q →
    mean P (fun ω => Real.rpow |X ω| m) ≤
      Real.rpow (mean P (fun ω => Real.rpow |X ω| q)) (m/q)

/-- The ordinary-power convention gives the square identity in every branch.
Only nonnegative bases are passed to the real-power multiplication rule. -/
theorem ordinaryPower_square (x a u : ℝ) (h : OrdinaryPowerW3 x a u) :
    u^2 = Real.rpow |x| (2*a) := by
  have habs : (Real.rpow |x| a)^2 = Real.rpow |x| (2*a) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast (|x| ^ a) 2,
      ← Real.rpow_mul (abs_nonneg x)]
    congr 1
    norm_num
    ring
  rcases h with ⟨ha, hu⟩ | ⟨_ha, hx, hu⟩ | ⟨_ha, _hx, p, d, _hd, _hodd, _hcop, _hat, hu⟩
  · simp [ha, hu]
  · rw [hu]
    simpa only [abs_of_nonneg hx] using habs
  · rw [hu, mul_pow]
    have hs : ((-1 : ℝ)^p)^2 = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [hs, one_mul, habs]

/-- Masking an ordinary power by an arm indicator can only decrease its second
moment. The support guard is sufficient: terms of mass zero disappear. -/
theorem arm_variance_le {n : ℕ} (E : Experiment n) (a : ℝ)
    (i : Fin n) (b : Bool) (u : Assignment n → ℝ)
    (hu : ∀ z, 0 < E.design.mass z → OrdinaryPowerW3 (E.outcome i z) a (u z)) :
    var E.design (powerArmW3 u i b) ≤ outcomeMomentW3 E i (2*a) := by
  have hvar : var E.design (powerArmW3 u i b) =
      mean E.design (fun z => (powerArmW3 u i b z)^2) -
        (mean E.design (powerArmW3 u i b))^2 :=
    AronowAudit.P009.variance_second_moment (Bridge.toLaw E.design) _
  calc
    _ ≤ mean E.design (fun z => (powerArmW3 u i b z)^2) := by
      rw [hvar]
      exact sub_le_self _ (sq_nonneg _)
    _ ≤ outcomeMomentW3 E i (2*a) := by
      unfold outcomeMomentW3 mean
      apply Finset.sum_le_sum
      intro z _
      by_cases hp : 0 < E.design.mass z
      · apply mul_le_mul_of_nonneg_left _ (E.design.nonneg z)
        by_cases hb : z i = b
        · simp only [powerArmW3, hb, ite_true]
          exact (ordinaryPower_square _ _ _ (hu z hp)).le
        · simp only [powerArmW3, hb, ite_false, zero_pow (by decide : (2 : ℕ) ≠ 0)]
          exact Real.rpow_nonneg (abs_nonneg _) _
      · have hz : E.design.mass z = 0 :=
          le_antisymm (le_of_not_gt hp) (E.design.nonneg z)
        simp only [hz, zero_mul, le_refl]

/-- Assembly of the corrected claim. Existing finite covariance and variance
facts supply Cauchy--Schwarz and nonnegative variances. The only new analytic
leaf is real-order Jensen interpolation. The power square identity, masking,
nonnegative multiplication, monotonicity and endpoint algebra are proved here. -/
theorem T29_assembly (h1 : T29_L1) : T29WholeStatement_W3 := by
  constructor
  · intro n _hn E u i j b
    exact (le_abs_self _).trans (AronowAudit.P009.covariance_cauchy_schwarz
      (Bridge.toLaw E.design) (powerArmW3 u i b) (powerArmW3 u j b))
  · intro n _hn E k q a hk hq ha hqa hMoment i j b u v hu hv
    have hqpos : 0 < q := by linarith
    have htheta : 0 ≤ 2*a/q := div_nonneg (by positivity) hqpos.le
    let X := powerArmW3 u i b
    let Y := powerArmW3 v j b
    let M := fun r => outcomeMomentW3 E r (2*a)
    let Q := fun r => Real.rpow (outcomeMomentW3 E r q) (2*a/q)
    let K := Real.rpow (Real.rpow k q) (2*a/q)
    have hMomNonneg (r : Fin n) (t : ℝ) : 0 ≤ outcomeMomentW3 E r t :=
      Finset.sum_nonneg (fun z _ =>
        mul_nonneg (E.design.nonneg z) (Real.rpow_nonneg (abs_nonneg _) t))
    have hM (r : Fin n) : 0 ≤ M r := hMomNonneg r _
    have hQ (r : Fin n) : 0 ≤ Q r := Real.rpow_nonneg (hMomNonneg r q) _
    have hK : 0 ≤ K := Real.rpow_nonneg (Real.rpow_nonneg hk.le _) _
    have hMQ (r : Fin n) : M r ≤ Q r :=
      h1 E.design (E.outcome r) (2*a) q (by positivity) hqpos hqa
    have hQK (r : Fin n) : Q r ≤ K :=
      Real.rpow_le_rpow (hMomNonneg r q) (hMoment r) htheta
    have hvX : var E.design X ≤ M i := arm_variance_le E a i b u hu
    have hvY : var E.design Y ≤ M j := arm_variance_le E a j b v hv
    have hvY0 : 0 ≤ var E.design Y :=
      AronowAudit.P009.variance_nonnegative (Bridge.toLaw E.design) Y
    have hCS : |cov E.design X Y| ≤ Real.sqrt (var E.design X * var E.design Y) :=
      AronowAudit.P009.covariance_cauchy_schwarz (Bridge.toLaw E.design) X Y
    have hAB := Real.sqrt_le_sqrt (mul_le_mul hvX hvY hvY0 (hM i))
    have hBC := Real.sqrt_le_sqrt (mul_le_mul (hMQ i) (hMQ j) (hM j) (hQ i))
    have hCD := Real.sqrt_le_sqrt (mul_le_mul (hQK i) (hQK j) (hQ j) hK)
    have hKpow : K = Real.rpow k (2*a) := by
      dsimp only [K]
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul hk.le]
      congr 1
      field_simp
    have hD : Real.sqrt (K*K) = Real.sqrt (Real.rpow k (4*a)) := by
      rw [hKpow]
      congr 1
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hk]
      congr 1
      ring
    have hsqrt : Real.sqrt (Real.rpow k (4*a)) = Real.rpow k (2*a) := by
      have he : Real.rpow k (4*a) = (Real.rpow k (2*a))^2 := by
        simp only [Real.rpow_eq_pow]
        rw [pow_two, ← Real.rpow_add hk]
        congr 1
        ring
      rw [he]
      exact Real.sqrt_sq (Real.rpow_nonneg hk.le _)
    have hEnd : |cov E.design X Y| ≤ Real.rpow k (2*a) :=
      hCS.trans (hAB.trans (hBC.trans (hCD.trans (hD.trans hsqrt).le)))
    exact ⟨(le_abs_self _).trans hCS, hCS, hAB, hBC, hCD, hD, hsqrt,
      (le_abs_self _).trans hEnd, hEnd⟩

end
end SAP.P009b.WH.W3
