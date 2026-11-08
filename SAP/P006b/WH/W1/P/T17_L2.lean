import SAP.P006b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P006b.WH.W1.P.T17_L2

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem finiteConditionalLaw_probability {X : Type} [MeasurableSpace X] {K : ℕ}
    (Q : Measure X) [IsProbabilityMeasure Q] (p : X → Fin K → ℝ)
    (hpm : ∀ u, Measurable (fun x => p x u)) (hp : ∀ x u, 0 < p x u) (hsum : ∀ x, ∑ u, p x u = 1) :
    IsProbabilityMeasure (SAP.P006b.finiteConditionalLaw Q p) := by
  rw [MeasureTheory.isProbabilityMeasure_iff]
  unfold SAP.P006b.finiteConditionalLaw
  have hsumE (x : X) : (∑ u : Fin K, ENNReal.ofReal (p x u)) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun u _ => (hp x u).le), hsum x]
    norm_num
  have heval (u : Fin K) :
      (Measure.map (fun x : X => (x,u)) (Q.withDensity (fun x => ENNReal.ofReal (p x u)))) Set.univ =
      ∫⁻ x, ENNReal.ofReal (p x u) ∂Q := by
    rw [Measure.map_apply (f := fun x : X => (x,u)) (Measurable.prodMk measurable_id measurable_const) MeasurableSet.univ]
    simp [withDensity_apply]
  rw [Measure.finsetSum_apply Finset.univ]
  simp_rw [heval]
  rw [← lintegral_finsetSum Finset.univ]
  · simp_rw [hsumE]
    simp
  · intro u hu
    exact (hpm u).ennreal_ofReal

theorem finiteMaximum_nonneg {K : ℕ} (m : Fin K → ℝ) (u : Fin K)
    (hK : Nonempty (Fin K)) :
    0 ≤ sSup (Set.range (fun v : Fin K => |m u - m v|)) := by
  have hb : BddAbove (Set.range (fun v : Fin K => |m u - m v|)) :=
    (Set.finite_range _).bddAbove
  obtain ⟨v⟩ := hK
  exact le_trans (abs_nonneg _) (le_csSup hb ⟨v, rfl⟩)

theorem finiteMaximum_bound {K : ℕ} (m : Fin K → ℝ) (u v : Fin K) :
    |m u - m v| ≤ sSup (Set.range (fun w : Fin K => |m u - m w|)) := by
  exact le_csSup ((Set.finite_range _).bddAbove) ⟨v, rfl⟩

theorem finiteWeightedDeviation_bound {K : ℕ} (p m : Fin K → ℝ)
    (hp : ∀ v, 0 < p v) (hsum : ∑ v, p v = 1) (hK : Nonempty (Fin K)) (u : Fin K) :
    |(∑ v, p v * m v) - m u| ≤ sSup (Set.range (fun v : Fin K => |m u - m v|)) := by
  have hM : 0 ≤ sSup (Set.range (fun v : Fin K => |m u - m v|)) :=
    finiteMaximum_nonneg m u hK
  have hd (v : Fin K) : |m v - m u| ≤ sSup (Set.range (fun w : Fin K => |m u - m w|)) := by
    simpa [abs_sub_comm] using finiteMaximum_bound m u v
  have hrepr : (∑ v, p v * m v) - m u = ∑ v, p v * (m v - m u) := by
    calc
      (∑ v, p v * m v) - m u =
          (∑ v, p v * m v) - (∑ v, p v) * m u := by rw [hsum]; ring
      _ = ∑ v, (p v * m v - p v * m u) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      _ = ∑ v, p v * (m v - m u) := by
          apply Finset.sum_congr rfl
          intro v hv
          ring
  rw [hrepr]
  calc
    |∑ v, p v * (m v - m u)| ≤ ∑ v, |p v * (m v - m u)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v, p v * sSup (Set.range (fun w : Fin K => |m u - m w|)) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [abs_mul, abs_of_pos (hp v)]
      exact mul_le_mul_of_nonneg_left (hd v) (le_of_lt (hp v))
    _ = sSup (Set.range (fun w : Fin K => |m u - m w|)) := by
      rw [← Finset.sum_mul, hsum]
      ring

theorem finiteMarginalDeviation_measurable {X : Type} [MeasurableSpace X] {K : ℕ}
    (p : X → Fin K → ℝ) (m : X × Fin K → ℝ)
    (hpm : ∀ u, Measurable (fun x => p x u)) (hm : Measurable m) :
    Measurable (fun c : X × Fin K => SAP.P006b.finiteMarginalDeviation p m c) := by
  have hmSection (u : Fin K) : Measurable (fun x : X => m (x,u)) := by
    exact hm.comp (Measurable.prodMk measurable_id measurable_const)
  have hmean : Measurable (fun x : X => SAP.P006b.publicFiniteMean p m x) := by
    unfold SAP.P006b.publicFiniteMean
    apply Finset.measurable_sum Finset.univ
    intro u hu
    exact (hpm u).mul (hmSection u)
  have hmeanComp : Measurable (fun c : X × Fin K => SAP.P006b.publicFiniteMean p m c.1) :=
    hmean.comp measurable_fst
  have hm' : Measurable m := hm
  simpa [SAP.P006b.finiteMarginalDeviation] using (hmeanComp.sub hm').abs

end

end SAP.P006b.WH.W1.P.T17_L2

open MeasureTheory ProbabilityTheory Filter

theorem SAP.P006b.WH.W1.T17_L2_proof : SAP.P006b.WH.W1.T17_L2 := by
  change SAP.P006b.T17ComparisonStatement
  intro X mX K Q hQ p m hpm hm hp hsum hmax
  letI : IsProbabilityMeasure Q := hQ
  have hX : Nonempty X := MeasureTheory.nonempty_of_isProbabilityMeasure Q
  have hKpos : 0 < K := by
    by_contra hn
    have hK0 : K = 0 := by omega
    subst K
    obtain ⟨x⟩ := hX
    have hh := hsum x
    simp at hh
  have hK : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hKpos
  have hprob := SAP.P006b.WH.W1.P.T17_L2.finiteConditionalLaw_probability Q p hpm hp hsum
  have hpoint (x : X) (u : Fin K) :
      |SAP.P006b.publicFiniteMean p m x - m (x,u)| ≤ SAP.P006b.maximumDeviation m (x,u) := by
    have hh := SAP.P006b.WH.W1.P.T17_L2.finiteWeightedDeviation_bound
      (fun v => p x v) (fun v => m (x,v)) (fun v => hp x v) (hsum x) hK u
    simpa [SAP.P006b.publicFiniteMean, SAP.P006b.maximumDeviation] using hh
  have hdevMeas := SAP.P006b.WH.W1.P.T17_L2.finiteMarginalDeviation_measurable p m hpm hm
  have hdom (c : X × Fin K) :
      SAP.P006b.finiteMarginalDeviation p m c ≤ SAP.P006b.maximumDeviation m c := by
    simpa [SAP.P006b.finiteMarginalDeviation] using hpoint c.1 c.2
  have hdevInt : Integrable (SAP.P006b.finiteMarginalDeviation p m)
      (SAP.P006b.finiteConditionalLaw Q p) := by
    apply Integrable.mono' hmax hdevMeas.aestronglyMeasurable
    filter_upwards with c
    simpa [Real.norm_eq_abs, SAP.P006b.finiteMarginalDeviation] using hdom c
  refine ⟨hpoint, hprob, hdevInt, ?_⟩
  exact integral_mono hdevInt hmax hdom
