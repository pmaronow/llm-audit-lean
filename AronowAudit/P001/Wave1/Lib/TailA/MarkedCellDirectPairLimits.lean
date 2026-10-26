import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectLimits

/-! The joint direct-kernel limit, with overlap of original donor sites.
The common category is counted twice in the exponential, yielding `exp(-2)`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectPairLimits (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Three disjoint donor categories: shared, exclusive to replica one,
and exclusive to replica two.  Both replicas use the same original counts. -/
theorem marked_direct_pair_category_limits
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (E : ℕ → Fin 3 → Set MatchUnit) (hE : ∀ n i, MeasurableSet (E n i))
    (hdis : ∀ n i j, i ≠ j → Disjoint (E n i) (E n j))
    (rates : Fin 3 → ℝ≥0)
    (hrate : ∀ i, Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n i)) atTop
      (𝓝 (rates i : ℝ))) (k l : ℕ) :
    let S := Real.exp ((rates 0 : ℝ)*(Real.exp (-2)-1) +
      ((rates 1 : ℝ)+(rates 2 : ℝ))*(Real.exp (-1)-1))
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedDrawPower (N n) (markedWindowCount (E n 0 ∪ E n 1) z) k *
        markedDrawPower (N n) (markedWindowCount (E n 0 ∪ E n 2) z) l)) atTop (𝓝 S) ∧
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n) (markedWindowCount (E n 0 ∪ E n 1) z) k *
        markedRetainedDrawPower (N n) (markedWindowCount (E n 0 ∪ E n 2) z) l))
      atTop (𝓝 (matchS^2*S)) := by
  dsimp only
  let X : (n : ℕ) → (Fin (m n) → MatchUnit) → Fin 3 → ℕ :=
    fun n z i => markedWindowCount (E n i) z
  have hX (n : ℕ) : Measurable (X n) :=
    measurable_pi_lambda (fun i => marked_window_count_measurable _ _ (hE n i))
  have hw := rare_partition_counts 3 m hm (fun _ => matchingUnitLaw)
    (fun _ => inferInstance) E hE hdis rates hrate
  let f : (Fin 3 → ℕ) → ℝ := fun v =>
    Real.exp (-((v 0+v 1 : ℕ) : ℝ))*Real.exp (-((v 0+v 2 : ℕ) : ℝ))
  let S := Real.exp ((rates 0 : ℝ)*(Real.exp (-2)-1) +
    ((rates 1 : ℝ)+(rates 2 : ℝ))*(Real.exp (-1)-1))
  have he : (∫ v, f v ∂Measure.pi (fun i => poissonMeasure (rates i))) = S := by
    let z : Fin 3 → ℝ := ![Real.exp (-2),Real.exp (-1),Real.exp (-1)]
    have hz0 : z 0 = Real.exp (-2) := rfl
    have hz1 : z 1 = Real.exp (-1) := rfl
    have hz2 : z 2 = Real.exp (-1) := rfl
    have hh := marked_poisson_product_power_integral 3 rates z
    have hf (v : Fin 3 → ℕ) : f v = ∏ i, (z i)^(v i) := by
      simp only [f,Fin.prod_univ_three,hz0,hz1,hz2,← Real.exp_nat_mul,← Real.exp_add,Nat.cast_add]
      congr 1
      ring
    simp only [hf]
    rw [hh]
    congr 1
    simp only [S,Fin.sum_univ_three,hz0,hz1,hz2]
    ring
  have hdrawlim (v : Fin 3 → ℕ) : Tendsto (fun n =>
      markedDrawPower (N n) (v 0+v 1) k*markedDrawPower (N n) (v 0+v 2) l)
      atTop (𝓝 (f v)) :=
    (marked_draw_power_limit N hN _ _).mul (marked_draw_power_limit N hN _ _)
  have hretlim (v : Fin 3 → ℕ) : Tendsto (fun n =>
      markedRetainedDrawPower (N n) (v 0+v 1) k*
        markedRetainedDrawPower (N n) (v 0+v 2) l)
      atTop (𝓝 (matchS^2*f v)) := by
    convert (marked_retained_draw_power_limit N hN (v 0+v 1) k).mul
      (marked_retained_draw_power_limit N hN (v 0+v 2) l) using 1
    dsimp only [f]
    ring
  have hdrawb (n : ℕ) (v : Fin 3 → ℕ) :
      |markedDrawPower (N n) (v 0+v 1) k*markedDrawPower (N n) (v 0+v 2) l| ≤ 1 := by
    obtain ⟨h0,h1⟩ := marked_draw_power_bounds (N n) (v 0+v 1) k
    obtain ⟨h2,h3⟩ := marked_draw_power_bounds (N n) (v 0+v 2) l
    rw [abs_of_nonneg (mul_nonneg h0 h2)]
    exact mul_le_one₀ h1 h2 h3
  have hretb (n : ℕ) (v : Fin 3 → ℕ) :
      |markedRetainedDrawPower (N n) (v 0+v 1) k*
        markedRetainedDrawPower (N n) (v 0+v 2) l| ≤ 1 := by
    obtain ⟨h0,h1⟩ := marked_retained_draw_power_bounds (N n) (v 0+v 1) k
    obtain ⟨h2,h3⟩ := marked_retained_draw_power_bounds (N n) (v 0+v 2) l
    rw [abs_of_nonneg (mul_nonneg h0 h2)]
    exact mul_le_one₀ h1 h2 h3
  have hdraw := marked_discrete_varying_test_limit (fun n => MatchProduct (m n))
    (fun _ => inferInstance) X hX _ hw _ f (by norm_num : (0 : ℝ) ≤ 1) hdrawb hdrawlim
  have hret := marked_discrete_varying_test_limit (fun n => MatchProduct (m n))
    (fun _ => inferInstance) X hX _ hw _ (fun v => matchS^2*f v)
    (by norm_num : (0 : ℝ) ≤ 1) hretb hretlim
  have hcount1 (n : ℕ) (z : Fin (m n) → MatchUnit) :
      markedWindowCount (E n 0 ∪ E n 1) z = X n z 0+X n z 1 :=
    marked_window_count_union _ _ _ (hdis n 0 1 (by decide)) z
  have hcount2 (n : ℕ) (z : Fin (m n) → MatchUnit) :
      markedWindowCount (E n 0 ∪ E n 2) z = X n z 0+X n z 2 :=
    marked_window_count_union _ _ _ (hdis n 0 2 (by decide)) z
  simp only [he,integral_const_mul] at hdraw hret
  simpa only [mean,S,hcount1,hcount2] using And.intro hdraw hret


end AronowAudit.P001.TailA
