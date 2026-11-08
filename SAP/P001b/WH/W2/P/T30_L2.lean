import SAP.P001b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem SAP.P001b.WH.W2.T30_L2_proof : SAP.P001b.WH.W2.T30_L2 := by
  classical
  intro Ω mΩ μ hμ X Y hX hY hcountX hcountY
  constructor
  · intro h x y
    have hmul := (indepFun_iff_measure_inter_preimage_eq_mul.mp h)
      ({x} : Set ℝ) ({y} : Set ℝ) (measurableSet_singleton x) (measurableSet_singleton y)
    have hevent : {ω | X ω = x ∧ Y ω = y} = X ⁻¹' {x} ∩ Y ⁻¹' {y} := by
      ext ω
      simp
    change (μ {ω | X ω = x ∧ Y ω = y}).toReal =
      (μ {ω | X ω = x}).toReal * (μ {ω | Y ω = y}).toReal
    rw [hevent, ← ENNReal.toReal_mul]
    exact congrArg ENNReal.toReal (by
      simpa only [Set.preimage, Set.mem_singleton_iff] using hmul)
  · intro hpmf
    let S := Set.range X
    let T := Set.range Y
    letI : Countable S := hcountX.to_subtype
    letI : Countable T := hcountY.to_subtype
    let Xs : Ω → S := fun ω => ⟨X ω, ⟨ω, rfl⟩⟩
    let Ys : Ω → T := fun ω => ⟨Y ω, ⟨ω, rfl⟩⟩
    have hXs : Measurable Xs := by
      change Measurable (fun ω => (⟨X ω, ⟨ω, rfl⟩⟩ : S))
      exact Measurable.subtype_mk hX
    have hYs : Measurable Ys := by
      change Measurable (fun ω => (⟨Y ω, ⟨ω, rfl⟩⟩ : T))
      exact Measurable.subtype_mk hY
    have hatom (x y : ℝ) :
        μ {ω | X ω = x ∧ Y ω = y} = μ {ω | X ω = x} * μ {ω | Y ω = y} := by
      have h := hpmf x y
      simp only [SAP.P001b.probability] at h
      rw [← ENNReal.toReal_mul] at h
      exact (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top μ _) (ENNReal.mul_ne_top (measure_ne_top μ _) (measure_ne_top μ _))).mp h
    have hjoint : μ.map (fun ω => (Xs ω, Ys ω)) = (μ.map Xs).prod (μ.map Ys) := by
      apply Measure.ext_of_singleton
      rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      rw [Measure.map_apply (hXs.prodMk hYs) (measurableSet_singleton _),
        ← Set.singleton_prod_singleton, Measure.prod_prod,
        Measure.map_apply hXs (measurableSet_singleton _),
        Measure.map_apply hYs (measurableSet_singleton _)]
      have hpre : (fun ω => (Xs ω, Ys ω)) ⁻¹'
          (({(⟨x, hx⟩ : S)} : Set S) ×ˢ ({(⟨y, hy⟩ : T)} : Set T)) =
          {ω | X ω = x ∧ Y ω = y} := by
        ext ω
        change Xs ω = ⟨x, hx⟩ ∧ Ys ω = ⟨y, hy⟩ ↔ X ω = x ∧ Y ω = y
        constructor
        · rintro ⟨h₁, h₂⟩
          exact ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
        · rintro ⟨h₁, h₂⟩
          exact ⟨Subtype.ext h₁, Subtype.ext h₂⟩
      have hpreX : Xs ⁻¹' {(⟨x, hx⟩ : S)} = {ω | X ω = x} := by
        ext ω
        change Xs ω = ⟨x, hx⟩ ↔ X ω = x
        constructor
        · exact congrArg Subtype.val
        · intro h
          exact Subtype.ext h
      have hpreY : Ys ⁻¹' {(⟨y, hy⟩ : T)} = {ω | Y ω = y} := by
        ext ω
        change Ys ω = ⟨y, hy⟩ ↔ Y ω = y
        constructor
        · exact congrArg Subtype.val
        · intro h
          exact Subtype.ext h
      rw [hpre, hpreX, hpreY]
      exact hatom x y
    have hXsYs : IndepFun Xs Ys μ :=
      (indepFun_iff_map_prod_eq_prod_map_map hXs.aemeasurable hYs.aemeasurable).2 hjoint
    have hreal : IndepFun (fun ω => (Xs ω : ℝ)) (fun ω => (Ys ω : ℝ)) μ :=
      hXsYs.comp measurable_subtype_coe measurable_subtype_coe
    simpa [Xs, Ys] using hreal
