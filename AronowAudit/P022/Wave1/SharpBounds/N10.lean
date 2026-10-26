import AronowAudit.P022.Wave1.SharpBoundsBlueprint

set_option autoImplicit false
namespace AronowAudit.P022.Wave1.SharpBounds
open AronowAudit.P022 MeasureTheory Filter Finset
open scoped BigOperators Topology
noncomputable section

private theorem shifted_product (J : JointLaw)
    (hg : ∀ g : ℝ × ℝ → ℝ, Measurable g → Integrable g (J : Measure (ℝ × ℝ)))
    (a b : ℝ) :
    (∫ p, (p.1 - a) * (p.2 - b) ∂(J : Measure (ℝ × ℝ))) =
      (∫ p, p.1 * p.2 ∂(J : Measure (ℝ × ℝ))) -
        b * lawMean J true - a * lawMean J false + a * b := by
  have heq : (fun p : ℝ × ℝ => (p.1 - a) * (p.2 - b)) =
      (fun p => p.1 * p.2 - b * p.1 - a * p.2 + a * b) := by funext p; ring
  rw [heq, integral_add (hg _ (by fun_prop)) (hg _ measurable_const),
    integral_sub (hg _ (by fun_prop)) (hg _ (by fun_prop)),
    integral_sub (hg _ (by fun_prop)) (hg _ (by fun_prop)),
    integral_const_mul, integral_const_mul]
  simp [lawMean]

theorem n10_proof : N10 := by
  intro N _ y1 y0 J h1 h0 hs hg hm1 hm0
  classical
  let A := sortedValues y1 0
  let B := sortedValues y0 0
  let T : Fin N → Fin N → ℝ × ℝ → ℝ := fun j l p =>
    sortedIncrement y1 j * sortedIncrement y0 l *
      (if sortedValues y1 j ≤ p.1 ∧ sortedValues y0 l ≤ p.2 then 1 else 0)
  have hset (j l : Fin N) : MeasurableSet {p : ℝ × ℝ |
      sortedValues y1 j ≤ p.1 ∧ sortedValues y0 l ≤ p.2} :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)
  have hTm (j l : Fin N) : Measurable (T j l) :=
    measurable_const.mul (Measurable.ite (hset j l) measurable_const measurable_const)
  have hTi (j l : Fin N) : Integrable (T j l) (J : Measure (ℝ × ℝ)) := hg _ (hTm j l)
  have hlayer : (fun p : ℝ × ℝ => (p.1 - A) * (p.2 - B)) =ᵐ[(J : Measure (ℝ × ℝ))]
      (fun p => ∑ j, ∑ l, T j l p) := by
    filter_upwards [hs] with p hp
    rw [h1 p.1 hp.1, h0 p.2 hp.2, Finset.sum_mul_sum]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro l _
    dsimp [T]
    split_ifs <;> simp_all <;> ring
  have hint : (∫ p, (p.1 - A) * (p.2 - B) ∂(J : Measure (ℝ × ℝ))) =
      ∑ j, ∑ l, sortedIncrement y1 j * sortedIncrement y0 l *
        ((J : Measure (ℝ × ℝ)) {p | sortedValues y1 j ≤ p.1 ∧ sortedValues y0 l ≤ p.2}).toReal := by
    rw [integral_congr_ae hlayer, integral_finsetSum]
    · apply sum_congr rfl
      intro j _
      rw [integral_finsetSum univ (fun l _ => hTi j l)]
      apply sum_congr rfl
      intro l _
      dsimp [T]
      rw [integral_const_mul]
      congr 1
      simpa only [Set.indicator_apply, Pi.one_apply, Set.mem_setOf_eq, Measure.real] using
        (integral_indicator_one (μ := (J : Measure (ℝ × ℝ))) (hset j l))
    · intro j _
      exact integrable_finsetSum _ (fun l _ => hTi j l)
  have hc := shifted_product J hg (lawMean J true) (lawMean J false)
  change lawCovariance J = _ at hc
  have hm := shifted_product J hg A B
  rw [hm1, hm0] at hc hm
  rw [← hint, hm]
  linarith [hc]

end
end AronowAudit.P022.Wave1.SharpBounds
