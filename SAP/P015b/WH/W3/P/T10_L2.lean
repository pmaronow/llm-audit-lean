import SAP.P015b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

open SAP.P015b Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal

theorem SAP.P015b.WH.W3.T10_L2_proof : SAP.P015b.WH.W3.T10_L2 := by
  classical
  intro hL Ω _ P hP K D Y₀ τ X hX hD hY hτ hunconf ω hlinear hiD hiY hiτ hiDY himY hirτ hirmτ
  let E := ℝ × (ℝ × (ℝ × (Fin K → ℝ)))
  let T : Ω → E := fun s => (D s, (Y₀ s, (τ s, X s)))
  let Q : Measure E := P.map T
  let d : E → ℝ := fun z => z.1
  let y : E → ℝ := fun z => z.2.1
  let t : E → ℝ := fun z => z.2.2.1
  let x : E → Fin K → ℝ := fun z => z.2.2.2
  let M : E → ℝ := fun z => dotProduct (controlVector (x z)) ω
  have hT : Measurable T := by fun_prop
  have hx : Measurable x := by fun_prop
  have hd : Measurable d := by dsimp [d]; exact measurable_fst
  have hy : Measurable y := by dsimp [y]; exact measurable_snd.fst
  have ht : Measurable t := by dsimp [t]; exact measurable_snd.snd.fst
  have hcv : Measurable (fun z => controlVector (x z)) := by
    apply measurable_pi_lambda
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · exact measurable_const
    · exact (measurable_pi_apply i).comp hx
  have hM : Measurable M := by
    dsimp [M, dotProduct]
    exact Finset.measurable_sum Finset.univ
      (fun j _ => ((measurable_pi_apply j).comp hcv).mul_const (ω j))
  haveI : IsProbabilityMeasure Q := by
    dsimp [Q]
    infer_instance
  letI : StandardBorelSpace E := inferInstance

  have hiDq : Integrable d Q := by
    apply (integrable_map_measure hd.aestronglyMeasurable hT.aemeasurable).mpr
    simpa [d, T, Function.comp_def] using hiD
  have hiYq : Integrable y Q := by
    apply (integrable_map_measure hy.aestronglyMeasurable hT.aemeasurable).mpr
    simpa [y, T, Function.comp_def] using hiY
  have hiTq : Integrable t Q := by
    apply (integrable_map_measure ht.aestronglyMeasurable hT.aemeasurable).mpr
    simpa [t, T, Function.comp_def] using hiτ

  have hiDYq : Integrable (fun z => d z * y z) Q := by
    apply (integrable_map_measure (hd.mul hy).aestronglyMeasurable hT.aemeasurable).mpr
    simpa [d, y, T, Function.comp_def] using hiDY
  have hiMYq : Integrable (fun z => M z * y z) Q := by
    apply (integrable_map_measure (hM.mul hy).aestronglyMeasurable hT.aemeasurable).mpr
    simpa [M, d, y, x, T, controlVector, Function.comp_def] using himY
  have hiRTq : Integrable (fun z => (d z - M z) * t z) Q := by
    apply (integrable_map_measure ((hd.sub hM).mul ht).aestronglyMeasurable hT.aemeasurable).mpr
    simpa [M, d, t, x, T, controlVector, Function.comp_def] using hirτ
  have hiRMTq : Integrable (fun z => (d z - M z) * M z * t z) Q := by
    apply (integrable_map_measure (((hd.sub hM).mul hM).mul ht).aestronglyMeasurable
      hT.aemeasurable).mpr
    simpa [M, d, t, x, T, controlVector, Function.comp_def] using hirmτ

  have hceD : Measurable (Q[d | MeasurableSpace.comap x inferInstance]) := by
    exact (stronglyMeasurable_condExp (m := MeasurableSpace.comap x inferInstance)).measurable
      |>.mono hx.comap_le le_rfl
  have hlinQ : Q[d | MeasurableSpace.comap x inferInstance] =ᵐ[Q] M := by
    have hpull := hL P T hT x hx d hd hiDq
    apply (ae_map_iff hT.aemeasurable (measurableSet_eq_fun hceD hM)).2
    filter_upwards [hlinear, hpull] with s hs hp
    have hp' : Q[d | MeasurableSpace.comap x inferInstance] (T s) =
        P[D | MeasurableSpace.comap X inferInstance] s := by
      simpa [T, d, x] using hp.symm
    simpa [M, T, x] using hp'.trans hs

  have hXT : (fun s => x (T s)) = X := by
    funext s
    rfl

  have hunconfQ : CondIndepFun (MeasurableSpace.comap x inferInstance)
      (Measurable.comap_le hx) (fun z => (y z, t z)) d Q := by
    rw [condIndepFun_iff_condExp_inter_preimage_eq_mul
      (by fun_prop : Measurable (fun z : E => (y z, t z))) hd]
    intro C J hC hJ
    let f₁ : E → ℝ := ((fun z : E => (y z, t z)) ⁻¹' C).indicator (fun _ => (1 : ℝ))
    let f₂ : E → ℝ := (d ⁻¹' J).indicator (fun _ => (1 : ℝ))
    let f₃ : E → ℝ := (((fun z : E => (y z, t z)) ⁻¹' C) ∩ (d ⁻¹' J)).indicator
      (fun _ => (1 : ℝ))
    have hpair : Measurable (fun z : E => (y z, t z)) := hy.prodMk ht
    have hs₁ : MeasurableSet ((fun z : E => (y z, t z)) ⁻¹' C) := hpair hC
    have hs₂ : MeasurableSet (d ⁻¹' J) := hd hJ
    have hs₃ : MeasurableSet ((fun z : E => (y z, t z)) ⁻¹' C ∩ d ⁻¹' J) := hs₁.inter hs₂
    have hf₁ : Measurable f₁ := measurable_const.indicator hs₁
    have hf₂ : Measurable f₂ := measurable_const.indicator hs₂
    have hf₃ : Measurable f₃ := measurable_const.indicator hs₃
    have hpull₁ := hL P T hT x hx f₁ hf₁ ((integrable_const (1 : ℝ)).indicator hs₁)
    have hpull₂ := hL P T hT x hx f₂ hf₂ ((integrable_const (1 : ℝ)).indicator hs₂)
    have hpull₃ := hL P T hT x hx f₃ hf₃ ((integrable_const (1 : ℝ)).indicator hs₃)
    have hsource := hunconf C J hC hJ
    let g₁ : Ω → ℝ := ((fun s => (Y₀ s, τ s)) ⁻¹' C).indicator (fun _ => (1 : ℝ))
    let g₂ : Ω → ℝ := (D ⁻¹' J).indicator (fun _ => (1 : ℝ))
    let g₃ : Ω → ℝ := (((fun s => (Y₀ s, τ s)) ⁻¹' C) ∩ (D ⁻¹' J)).indicator
      (fun _ => (1 : ℝ))
    have hcomp₁ : f₁ ∘ T = g₁ := by
      funext s
      rfl
    have hcomp₂ : f₂ ∘ T = g₂ := by
      funext s
      rfl
    have hcomp₃ : f₃ ∘ T = g₃ := by
      funext s
      rfl
    have hsource' : P[f₃ ∘ T | MeasurableSpace.comap (fun s => x (T s)) inferInstance] =ᵐ[P]
        fun s => P[f₁ ∘ T | MeasurableSpace.comap (fun s => x (T s)) inferInstance] s *
          P[f₂ ∘ T | MeasurableSpace.comap (fun s => x (T s)) inferInstance] s := by
      simpa only [hXT, hcomp₁, hcomp₂, hcomp₃] using hsource
    have hce₁ : Measurable (Q[f₁ | MeasurableSpace.comap x inferInstance]) :=
      (stronglyMeasurable_condExp (m := MeasurableSpace.comap x inferInstance)).measurable
        |>.mono hx.comap_le le_rfl
    have hce₂ : Measurable (Q[f₂ | MeasurableSpace.comap x inferInstance]) :=
      (stronglyMeasurable_condExp (m := MeasurableSpace.comap x inferInstance)).measurable
        |>.mono hx.comap_le le_rfl
    have hce₃ : Measurable (Q[f₃ | MeasurableSpace.comap x inferInstance]) :=
      (stronglyMeasurable_condExp (m := MeasurableSpace.comap x inferInstance)).measurable
        |>.mono hx.comap_le le_rfl
    apply (ae_map_iff hT.aemeasurable (measurableSet_eq_fun hce₃ (hce₁.mul hce₂))).2
    filter_upwards [hsource', hpull₁, hpull₂, hpull₃] with s hs h1 h2 h3
    have hs' := hs
    have h1' : Q[f₁ | MeasurableSpace.comap x inferInstance] (T s) =
        P[f₁ ∘ T | MeasurableSpace.comap (fun s => x (T s)) inferInstance] s := by
      exact h1.symm
    have h2' : Q[f₂ | MeasurableSpace.comap x inferInstance] (T s) =
        P[f₂ ∘ T | MeasurableSpace.comap (fun s => x (T s)) inferInstance] s := by
      exact h2.symm
    have h3' : Q[f₃ | MeasurableSpace.comap x inferInstance] (T s) =
        P[f₃ ∘ T | MeasurableSpace.comap (fun s => x (T s)) inferInstance] s := by
      exact h3.symm
    calc
      Q[f₃ | MeasurableSpace.comap x inferInstance] (T s) =
          P[f₃ ∘ T | MeasurableSpace.comap (fun s => x (T s)) inferInstance] s := h3'
      _ = P[f₁ ∘ T | MeasurableSpace.comap (fun s => x (T s)) inferInstance] s *
          P[f₂ ∘ T | MeasurableSpace.comap (fun s => x (T s)) inferInstance] s := hs'
      _ = Q[f₁ | MeasurableSpace.comap x inferInstance] (T s) *
          Q[f₂ | MeasurableSpace.comap x inferInstance] (T s) := by rw [← h1', ← h2']

  have hz := AronowAudit.P015.unconfounded_zero_terms Q K d y t x hx hd hy ht
    hunconfQ ω hlinQ hiDq hiYq hiTq hiDYq hiMYq hiRTq hiRMTq
  have hzero₁ : (∫ z, d z * y z ∂Q) - (∫ z, M z * y z ∂Q) = 0 := by
    change (∫ s, d s * y s ∂Q) -
      (∫ s, AronowAudit.P015.controlRow (x s) ⬝ᵥ ω * y s ∂Q) = 0
    exact hz.2.2.1
  have hzero₂ : (∫ z, (d z - M z) * M z * t z ∂Q) = 0 := by
    change (∫ s, (d s - AronowAudit.P015.controlRow (x s) ⬝ᵥ ω) *
      AronowAudit.P015.controlRow (x s) ⬝ᵥ ω * t s ∂Q) = 0
    exact hz.2.2.2
  have hmapDY : (∫ z, d z * y z ∂Q) = ∫ s, D s * Y₀ s ∂P := by
    simpa [Q, d, y, T, Function.comp_def] using
      (integral_map (μ := P) (φ := T) hT.aemeasurable
        ((hd.mul hy).aestronglyMeasurable))
  have hmapMY : (∫ z, M z * y z ∂Q) =
      ∫ s, dotProduct (controlVector (X s)) ω * Y₀ s ∂P := by
    change (∫ z, M z * y z ∂P.map T) = _
    simpa [Q, M, y, T, d, x, controlVector, Function.comp_def] using
      (integral_map (μ := P) (φ := T) hT.aemeasurable
        ((hM.mul hy).aestronglyMeasurable))
  have hmapRMT : (∫ z, (d z - M z) * M z * t z ∂Q) =
      ∫ s, (D s - dotProduct (controlVector (X s)) ω) *
        dotProduct (controlVector (X s)) ω * τ s ∂P := by
    simpa [Q, M, d, t, x, T, controlVector, Function.comp_def] using
      (integral_map (μ := P) (φ := T) hT.aemeasurable
        ((((hd.sub hM).mul hM).mul ht).aestronglyMeasurable))
  constructor
  · rw [← hmapDY, ← hmapMY]
    exact hzero₁
  · rw [← hmapRMT]
    exact hzero₂

