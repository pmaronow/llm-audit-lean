import AronowAudit.P001.Wave1.Lib.TailA.CDFTangent

/-! Finite evaluation operators converging on the CDF tangent space. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace AronowAudit.P001.Wave1.TailA

set_option maxHeartbeats 800000

/-- Total boundedness of the CDF range supplies finite threshold nets. -/
theorem ta18_finite_cdf_net (F : ℝ → ℝ) (hF : TotallyBounded (range F))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (r : ℕ) (x : Fin r → ℝ) (q : ℝ → Fin r),
      ∀ z, |F (x (q z)) - F z| < ε := by
  classical
  obtain ⟨s, hs, hfin, hcover⟩ := Metric.finite_approx_of_totallyBounded hF ε hε
  let instFintypeNet : Fintype s := hfin.fintype
  have hex (z : ℝ) : ∃ y : s, dist (y : ℝ) (F z) < ε := by
    obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (hcover (mem_range_self z))
    exact ⟨⟨y, hy⟩, by simpa only [Metric.mem_ball, dist_comm] using hzy⟩
  choose p hp using hex
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let x : Fin (Fintype.card s) → ℝ := fun j => (hs (e.symm j).property).choose
  refine ⟨Fintype.card s, x, fun z => e (p z), ?_⟩
  intro z
  have hx : F (x (e (p z))) = (p z : ℝ) := by
    dsimp only [x]
    simpa only [Equiv.symm_apply_apply] using (hs (e.symm (e (p z))).property).choose_spec
  rw [hx]
  exact hp z

/-- Replace each coordinate by its selected net coordinate. This operator has
norm at most one and is defined on the entire bounded-path space. -/
def ta18_coordinate_approx (r : ℕ) (x : Fin r → ℝ) (q : ℝ → Fin r) :
    KolmogorovSpace →L[ℝ] KolmogorovSpace := by
  let S : KolmogorovSpace →ₗ[ℝ] KolmogorovSpace :=
    { toFun := fun h => ⟨fun z => h (x (q z)), memℓp_infty ⟨‖h‖, by
        rintro y ⟨z, rfl⟩
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero h (x (q z))⟩⟩
      map_add' := by intro h g; apply lp.ext; funext z; rfl
      map_smul' := by intro a h; apply lp.ext; funext z; rfl }
  exact S.mkContinuous 1 fun h => by
    simp only [one_mul]
    apply lp.norm_le_of_forall_le (norm_nonneg h)
    intro z
    exact lp.norm_apply_le_norm ENNReal.top_ne_zero h (x (q z))

/-- A bounded indicator path for one cell of a finite coordinate selector. -/
def ta18_selector_cell {r : ℕ} (q : ℝ → Fin r) (j : Fin r) : KolmogorovSpace :=
  ⟨fun z => if q z = j then 1 else 0, memℓp_infty ⟨1, by
    rintro y ⟨z, rfl⟩
    change ‖(if q z = j then 1 else 0 : ℝ)‖ ≤ 1
    split_ifs <;> norm_num⟩⟩

/-- The approximating operator is explicitly finite rank. -/
theorem ta18_coordinate_approx_sum (r : ℕ) (x : Fin r → ℝ) (q : ℝ → Fin r)
    (h : KolmogorovSpace) :
    ta18_coordinate_approx r x q h = ∑ j, h (x j) • ta18_selector_cell q j := by
  classical
  apply lp.ext
  funext z
  rw [lp.coeFn_sum]
  change h (x (q z)) = (∑ j, h (x j) • (fun z => if q z = j then (1 : ℝ) else 0)) z
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp

/-- Finite nets give continuous linear scalar approximations, expressed as
finite linear combinations of evaluations, converging on every tangent path. -/
theorem ta18_cdf_linear_approx (F : ℝ → ℝ) (hF : TotallyBounded (range F))
    (L : KolmogorovSpace →L[ℝ] ℝ) :
    ∃ Y : ℕ → KolmogorovSpace →L[ℝ] ℝ,
      (∀ n, ∃ (r : ℕ) (x a : Fin r → ℝ), ∀ h, Y n h = ∑ j, a j * h (x j)) ∧
      ∀ h ∈ CDFTangent F, Tendsto (fun n => Y n h) atTop (𝓝 (L h)) := by
  classical
  let ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  choose r x q hq using fun n => ta18_finite_cdf_net F hF (ε n) (hε n)
  let S : ℕ → KolmogorovSpace →L[ℝ] KolmogorovSpace :=
    fun n => ta18_coordinate_approx (r n) (x n) (q n)
  refine ⟨fun n => L.comp (S n), ?_, ?_⟩
  · intro n
    refine ⟨r n, x n, fun j => L (ta18_selector_cell (q n) j), fun h => ?_⟩
    change L (ta18_coordinate_approx (r n) (x n) (q n) h) = _
    rw [ta18_coordinate_approx_sum, map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro h hh
    apply L.continuous.tendsto h |>.comp
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨δ, hδ, hd⟩ := hh.1 (η / 2) (by positivity)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hε0.eventually_lt_const hδ)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    apply lt_of_le_of_lt (lp.norm_le_of_forall_le (by positivity : 0 ≤ η / 2) ?_)
      (by linarith : η / 2 < η)
    intro z
    change |h (x n (q n z)) - h z| ≤ η / 2
    exact (hd _ _ ((hq n z).trans (hN n hn))).le

end AronowAudit.P001.Wave1.TailA
