import SAP.P001f.WH.W1.Leaves
import AronowAudit.P001.Wave1.MarDiscrete

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem SAP.P001f.WH.W1.T111_L2_proof : SAP.P001f.WH.W1.T111_L2 := by
  classical
  intro Ω E _ _ hSingleton μ hμ X hX hcount m hm hmi
  let support : Set E := wholeMassSupport μ X
  let I := support
  have hsupport_range : support ⊆ Set.range X := by
    intro x hx
    by_contra hxr
    have hempty : {ω | X ω = x} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hω
      exact hxr ⟨ω, hω⟩
    have hzero : (μ {ω | X ω = x}).toReal = 0 := by
      rw [hempty, measure_empty]
      simp
    change 0 < (μ {ω | X ω = x}).toReal at hx
    rw [hzero] at hx
    exact (lt_irrefl 0) hx
  have hsupport_countable : support.Countable := hcount.mono hsupport_range
  letI : Countable I := Set.countable_coe_iff.mp hsupport_countable
  letI : Countable (Set.range X) := Set.countable_coe_iff.mp hcount
  let cell : I → Set Ω := fun x => {ω | X ω = (x : E)}
  let U : Set Ω := ⋃ x : I, cell x

  have hbadcell : ∀ x : {y : Set.range X // ¬ (y : E) ∈ support},
      μ {ω | X ω = (x.val : Set.range X)} = 0 := by
    intro x
    have hnot : ¬ 0 < (μ {ω | X ω = (x.val : Set.range X)}).toReal := x.property
    have hreal : (μ {ω | X ω = (x.val : Set.range X)}).toReal = 0 :=
      le_antisymm (le_of_not_gt hnot) ENNReal.toReal_nonneg
    have htop : μ {ω | X ω = (x.val : Set.range X)} ≠ ∞ := measure_ne_top μ _
    rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with hzero | htop'
    · exact hzero
    · exact (htop htop').elim

  let J := {y : Set.range X // ¬ (y : E) ∈ support}
  let V : Set Ω := ⋃ x : J, {ω | X ω = (x.val : E)}
  have hVnull : μ V = 0 := by
    rw [show V = ⋃ x : J, {ω | X ω = (x.val : E)} by rfl, measure_iUnion_null]
    intro x
    exact hbadcell x
  have hcompl : Uᶜ ⊆ V := by
    intro ω hω
    change ω ∉ U at hω
    have hnotU : ∀ x : I, X ω ≠ (x : E) := by
      intro x hx
      apply hω
      exact Set.mem_iUnion.mpr ⟨x, hx⟩
    have hnot : X ω ∉ support := by
      intro hx
      exact hnotU ⟨X ω, hx⟩ rfl
    simp only [V, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨⟨⟨X ω, ⟨ω, rfl⟩⟩, hnot⟩, rfl⟩
  have hUcomp : μ Uᶜ = 0 := measure_mono_null hcompl hVnull
  have hUmem : ∀ᵐ ω ∂μ, ω ∈ U := by
    rw [ae_iff]
    simpa [Set.compl_def] using hUcomp
  have hUae : U =ᵐ[μ] Set.univ := by
    filter_upwards [hUmem] with ω hω
    simp [hω]

  have hUnionIntegral (f : Ω → ℝ) :
      (∫ ω in U, f ω ∂μ) = ∫ ω, f ω ∂μ := by
    calc
      (∫ ω in U, f ω ∂μ) = ∫ ω in Set.univ, f ω ∂μ := setIntegral_congr_set hUae
      _ = ∫ ω, f ω ∂μ := setIntegral_univ

  have hcell : ∀ x : I,
      (∫ ω in cell x, m (X ω) ∂μ) =
        m x * (μ {ω | X ω = (x : E)}).toReal := by
    intro x
    change (∫ ω in {ω | X ω = (x : E)}, m (X ω) ∂μ) = _
    calc
      (∫ ω in {ω | X ω = (x : E)}, m (X ω) ∂μ) =
          ∫ ω in {ω | X ω = (x : E)}, m (x : E) ∂μ := by
        apply setIntegral_congr_fun (hX (measurableSet_singleton (x : E)))
        intro ω hω
        exact congrArg m hω
      _ = m x * (μ {ω | X ω = (x : E)}).toReal := by
        rw [setIntegral_const, smul_eq_mul]
        exact mul_comm _ _

  have hsum : HasSum
      (fun x : I => m x * (μ {ω | X ω = (x : E)}).toReal)
      (∫ ω, m (X ω) ∂μ) := by
    have hcells := hasSum_integral_iUnion
      (fun x : I => hX (measurableSet_singleton (x : E)))
      (by
        intro x y hxy
        apply Set.disjoint_left.mpr
        intro ω hx hy
        exact hxy (Subtype.ext (hx.symm.trans hy)))
      (hmi.integrableOn.mono_set (by intro ω hω; exact Set.mem_univ ω))
    change HasSum (fun x : I => ∫ ω in cell x, m (X ω) ∂μ)
      (∫ ω in U, m (X ω) ∂μ) at hcells
    rw [hUnionIntegral (fun ω => m (X ω))] at hcells
    simpa only [hcell] using hcells

  have hcell_abs : ∀ x : I,
      (∫ ω in cell x, |m (X ω)| ∂μ) =
        |m x| * (μ {ω | X ω = (x : E)}).toReal := by
    intro x
    change (∫ ω in {ω | X ω = (x : E)}, |m (X ω)| ∂μ) = _
    calc
      (∫ ω in {ω | X ω = (x : E)}, |m (X ω)| ∂μ) =
          ∫ ω in {ω | X ω = (x : E)}, |m (x : E)| ∂μ := by
        apply setIntegral_congr_fun (hX (measurableSet_singleton (x : E)))
        intro ω hω
        exact congrArg abs (congrArg m hω)
      _ = |m x| * (μ {ω | X ω = (x : E)}).toReal := by
        rw [setIntegral_const, smul_eq_mul]
        exact mul_comm _ _

  have hmi_abs : Integrable (fun ω => |m (X ω)|) μ := by
    simpa using hmi.abs
  have hsum_abs : HasSum
      (fun x : I => |m x| * (μ {ω | X ω = (x : E)}).toReal)
      (∫ ω, |m (X ω)| ∂μ) := by
    have hcells := hasSum_integral_iUnion
      (fun x : I => hX (measurableSet_singleton (x : E)))
      (by
        intro x y hxy
        apply Set.disjoint_left.mpr
        intro ω hx hy
        exact hxy (Subtype.ext (hx.symm.trans hy)))
      (hmi_abs.integrableOn.mono_set (by intro ω hω; exact Set.mem_univ ω))
    change HasSum (fun x : I => ∫ ω in cell x, |m (X ω)| ∂μ)
      (∫ ω in U, |m (X ω)| ∂μ) at hcells
    rw [hUnionIntegral (fun ω => |m (X ω)|)] at hcells
    simpa only [hcell_abs] using hcells

  refine ⟨hsum.summable, hsum_abs.summable, hsum.tsum_eq.symm⟩
