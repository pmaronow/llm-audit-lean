import SAP.P037a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ENNReal NNReal Classical Topology
open MeasureTheory Set

namespace SAP.P037a.WH.W1.P.T4_L3

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal Classical Topology

theorem positiveOrthant_measurable (n : ℕ) :
    MeasurableSet (SAP.P037a.positiveOrthant n) := by
  apply measurableSet_setOfPred.2
  fun_prop

theorem openSimplex_measurable (m : ℕ) :
    MeasurableSet (SAP.P037a.openSimplex m) := by
  apply measurableSet_setOfPred.2
  fun_prop

theorem simplexCone_measurable (n : ℕ) :
    MeasurableSet (SAP.P037a.simplexCone n) := by
  unfold SAP.P037a.simplexCone
  apply measurableSet_setOfPred.2
  have hs : Measurable (fun p : Fin (n + 1) → ℝ =>
      p ∈ SAP.P037a.openSimplex (n + 1)) :=
    (measurableSet_setOfPred).1 (openSimplex_measurable (n + 1))
  have hp : Measurable (fun x : Fin (n + 2) → ℝ =>
      fun i : Fin (n + 1) => x i.castSucc) := by fun_prop
  have ht : Measurable (fun x : Fin (n + 2) → ℝ => 0 < x (Fin.last (n + 1))) := by
    fun_prop
  exact (hs.comp hp).and ht

theorem simplexConeInverse_measurable (n : ℕ) :
    Measurable (SAP.P037a.simplexConeInverse n) := by
  fun_prop [SAP.P037a.simplexConeInverse]

theorem simplexConeMap_measurable (n : ℕ) :
    Measurable (SAP.P037a.simplexConeMap n) := by
  apply measurable_pi_iff.2
  intro i
  change Measurable (fun x : Fin (n + 2) → ℝ =>
    x (Fin.last (n + 1)) *
      SAP.P037a.appendSimplex (n + 1) (fun j : Fin (n + 1) => x j.castSucc) i)
  have hp : Measurable (fun x : Fin (n + 2) → ℝ =>
      fun j : Fin (n + 1) => x j.castSucc) := by fun_prop
  have ha : Measurable (fun x : Fin (n + 2) → ℝ =>
      SAP.P037a.appendSimplex (n + 1) (fun j : Fin (n + 1) => x j.castSucc)) := by
    apply measurable_pi_iff.2
    intro j
    unfold SAP.P037a.appendSimplex
    split_ifs with hj
    · have hj' : j.val < n + 1 := by simpa using hj
      let j' : Fin (n + 1) := ⟨j.val, hj'⟩
      change Measurable (fun x : Fin (n + 2) → ℝ => x j'.castSucc)
      exact measurable_pi_apply j'.castSucc
    · fun_prop
  exact (measurable_pi_apply (Fin.last (n + 1))).mul
    ((measurable_pi_apply i).comp ha)

end SAP.P037a.WH.W1.P.T4_L3

open SAP.P037a.WH.W1.P.T4_L3

theorem SAP.P037a.WH.W1.T4_L3_proof : SAP.P037a.WH.W1.T4_L3 := by
  intro hgeom hdensity n
  classical
  let f := SAP.P037a.simplexConeMap n
  let g := SAP.P037a.simplexConeInverse n
  let C := SAP.P037a.simplexCone n
  let O := SAP.P037a.positiveOrthant n
  let k := n + 1
  let d : (Fin (n + 2) → ℝ) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (x (Fin.last (n + 1)) ^ k * Real.exp (-x (Fin.last (n + 1))))
  rcases hgeom n with ⟨hbij, horth, hcone⟩
  have hC : MeasurableSet C := by simpa [C] using simplexCone_measurable n
  have hO : MeasurableSet O := by simpa [O] using positiveOrthant_measurable n
  have hgm : Measurable g := by simpa [g] using simplexConeInverse_measurable n
  have hfm : Measurable f := by simpa [f] using simplexConeMap_measurable n
  have himage : f '' C = O := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hbij.1 hx
    · intro he
      obtain ⟨x, hx, hfx⟩ := hbij.2.2 he
      exact ⟨x, hx, hfx⟩
  have hsum (x : Fin (n + 2) → ℝ) (hx : x ∈ C) :
      ∑ i, f x i = x (Fin.last (n + 1)) := by
    have hi := (hcone x (by simpa [C] using hx)).1
    have hlast := congrFun hi (Fin.last (n + 1))
    simpa [g, SAP.P037a.simplexConeInverse, f, SAP.P037a.simplexConeMap] using hlast
  have hchange (s : Set (Fin (n + 2) → ℝ)) :
      (∫⁻ e in f '' C, (if g e ∈ s then ENNReal.ofReal (Real.exp (-(∑ i, e i))) else 0)
          ∂ volume) =
        ∫⁻ x in C, ENNReal.ofReal |(Matrix.toLin'
          (SAP.P037a.simplexConeJacobian n x)).det| *
          (if g (f x) ∈ s then ENNReal.ofReal (Real.exp (-(∑ i, f x i))) else 0)
          ∂ volume := by
    exact lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hC
      (fun x hx => (hcone x (by simpa [C] using hx)).2.1.hasFDerivWithinAt)
      (by simpa [f, C] using hbij.2.1)
      (fun e => if g e ∈ s then ENNReal.ofReal (Real.exp (-(∑ i, e i))) else 0)
  have hright (s : Set (Fin (n + 2) → ℝ)) :
      (∫⁻ x in C, ENNReal.ofReal |(Matrix.toLin'
          (SAP.P037a.simplexConeJacobian n x)).det| *
          (if g (f x) ∈ s then ENNReal.ofReal (Real.exp (-(∑ i, f x i))) else 0)
          ∂ volume) = ∫⁻ x in C, s.indicator d x ∂ volume := by
    apply setLIntegral_congr_fun hC
    intro x hx
    dsimp
    have hx' : x ∈ SAP.P037a.simplexCone n := by simpa [C] using hx
    have htx : 0 < x (Fin.last (n + 1)) := by
      have hh := hx'
      simp only [SAP.P037a.simplexCone, Set.mem_setOf_eq] at hh
      exact hh.2
    have hinv := hcone x hx'
    have hsumx : ∑ i, f x i = x (Fin.last (n + 1)) := by
      simpa [f, C] using hsum x hx
    have hdet : |LinearMap.det (Matrix.toLin'
        (SAP.P037a.simplexConeJacobian n x))| =
        x (Fin.last (n + 1)) ^ (n + 1) := by
      simpa only [LinearMap.det_toLin'] using hinv.2.2
    have hinvEq : g (f x) = x := by simpa [f, g] using hinv.1
    rw [hdet, hinvEq, hsumx]
    by_cases hs : x ∈ s
    · simp only [Set.indicator_of_mem hs, d, if_pos hs]
      rw [← ENNReal.ofReal_mul (by positivity :
        0 ≤ x (Fin.last (n + 1)) ^ (n + 1))]
    · simp [d, hs]
  have hsource (s : Set (Fin (n + 2) → ℝ)) (hs : MeasurableSet s) :
      (∫⁻ e in g ⁻¹' s,
        ENNReal.ofReal (Real.exp (-(∑ i, e i))) ∂ volume.restrict O) =
        ∫⁻ e in O, (g ⁻¹' s).indicator
          (fun e => ENNReal.ofReal (Real.exp (-(∑ i, e i)))) e ∂ volume := by
    have hpre : MeasurableSet (g ⁻¹' s) := hgm hs
    rw [Measure.restrict_restrict hpre]
    simpa [Set.inter_comm] using
      (setLIntegral_indicator hpre
        (fun e => ENNReal.ofReal (Real.exp (-(∑ i, e i))))).symm
  have htarget (s : Set (Fin (n + 2) → ℝ)) (hs : MeasurableSet s) :
      SAP.P037a.exponentialConeDensityLaw n s =
        ∫⁻ x in C, s.indicator d x ∂ volume := by
    rw [SAP.P037a.exponentialConeDensityLaw, withDensity_apply _ hs]
    change ∫⁻ x in s, d x ∂ volume.restrict C = _
    rw [Measure.restrict_restrict hs]
    simpa [Set.inter_comm] using (setLIntegral_indicator hs d).symm
  apply Measure.ext
  intro s hs
  rw [hdensity n, Measure.map_apply_of_aemeasurable hgm.aemeasurable hs,
    withDensity_apply _ (hgm hs)]
  calc
    (∫⁻ e in g ⁻¹' s, ENNReal.ofReal (Real.exp (-(∑ i, e i)))
        ∂ volume.restrict O) =
      ∫⁻ e in O, (g ⁻¹' s).indicator
        (fun e => ENNReal.ofReal (Real.exp (-(∑ i, e i)))) e ∂ volume := hsource s hs
    _ = ∫⁻ x in C, s.indicator d x ∂ volume := by
      rw [← himage]
      exact (hchange s).trans (hright s)
    _ = SAP.P037a.exponentialConeDensityLaw n s := (htarget s hs).symm
