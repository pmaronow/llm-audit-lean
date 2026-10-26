import AronowAudit.P047.Wave1.Impossibility.N13

set_option autoImplicit false

universe u

namespace AronowAudit.P047.Wave1.Impossibility

open AronowAudit.P047 MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

noncomputable section

theorem n18_proof : N18.{u} := by
  classical
  intro hF s13 s14 R _ Q _ lo hi hlo hhi n M
  let c : ℝ := randCoverage Q lo hi n
  let p : ℝ := (1 / 2 : ℝ) ^ (M + 1)
  let θ : Bool → (Fin (M + 1) → Bool) → ℝ := fun f σ => familyEffect f (M + 1) σ
  let bad : Bool → (Fin (M + 1) → Bool) → ℝ := fun f σ =>
    if (1 / 12 : ℝ) ≤ |θ f σ - familyCenter f| then 1 else 0
  let μ : Bool → (Fin (M + 1) → Bool) → Measure ((ℕ → UnitData) × R) :=
    fun f σ => (sampleLaw (familyMeasure M f σ)).prod Q
  let S : Measure ((ℕ → UnitData) × R) := (sampleLaw baselineLaw).prod Q
  let D : Bool → Set ((Fin n → ObservedUnit) × R) := fun f =>
    if f then {o | ((7 / 12 : ℝ) : EReal) < hi n o}
      else {o | lo n o < ((5 / 12 : ℝ) : EReal)}
  let D' : Bool → Set ((ℕ → UnitData) × R) := fun f =>
    {z | (observedSample n z.1, z.2) ∈ D f}
  have hD (f : Bool) : MeasurableSet (D f) := by
    cases f
    · exact measurableSet_lt (hlo n) measurable_const
    · exact measurableSet_lt measurable_const (hhi n)
  have hD' (f : Bool) : MeasurableSet (D' f) :=
    (hD f).preimage (measurable_sample_seed n)
  have hb (f : Bool) : (∑ σ : Fin (M + 1) → Bool, p * bad f σ) ≤ 16 / (M + 1 : ℝ) :=
    s14 f M
  have hcbounded : BddBelow
      (insert (1 : ℝ) {x | ∃ L : CausalLaw, UnknownModel L ∧
        x = ((sampleLaw L.measure).prod Q).real
          {z | lo n (observedSample n z.1, z.2) ≤ (ate L : EReal) ∧
            (ate L : EReal) ≤ hi n (observedSample n z.1, z.2)}}) := by
    refine ⟨0, ?_⟩
    rintro x (rfl | ⟨L, _hL, rfl⟩)
    · norm_num
    · exact measureReal_nonneg
  have hcleone : c ≤ 1 := csInf_le hcbounded (Set.mem_insert _ _)
  have hmodel (f : Bool) (σ : Fin (M + 1) → Bool) :
      c ≤ (μ f σ).real
        {z | lo n (observedSample n z.1, z.2) ≤ (θ f σ : EReal) ∧
          (θ f σ : EReal) ≤ hi n (observedSample n z.1, z.2)} := by
    obtain ⟨L, hmeasure, hL, hate⟩ := hF M f σ
    have hh : randCoverage Q lo hi n ≤ ((sampleLaw L.measure).prod Q).real
        {z | lo n (observedSample n z.1, z.2) ≤ (ate L : EReal) ∧
          (ate L : EReal) ≤ hi n (observedSample n z.1, z.2)} :=
      csInf_le hcbounded (Set.mem_insert_of_mem _ ⟨L, hL, rfl⟩)
    simpa only [hmeasure, hate] using hh
  have hfamily (f : Bool) (σ : Fin (M + 1) → Bool) :
      c - bad f σ ≤ (μ f σ).real (D' f) := by
    by_cases hbad : (1 / 12 : ℝ) ≤ |θ f σ - familyCenter f|
    · have hnonneg : 0 ≤ (μ f σ).real (D' f) := measureReal_nonneg
      simp only [bad, if_pos hbad]
      linarith
    · have hgood : |θ f σ - familyCenter f| < (1 / 12 : ℝ) := lt_of_not_ge hbad
      have hincl :
          {z | lo n (observedSample n z.1, z.2) ≤ (θ f σ : EReal) ∧
            (θ f σ : EReal) ≤ hi n (observedSample n z.1, z.2)} ⊆ D' f := by
        intro z hz
        change lo n (observedSample n z.1, z.2) ≤ (θ f σ : EReal) ∧
          (θ f σ : EReal) ≤ hi n (observedSample n z.1, z.2) at hz
        cases f
        · have hhigh := (abs_lt.mp hgood).2
          change θ false σ - 1 / 3 < (1 / 12 : ℝ) at hhigh
          have hband : θ false σ < (5 / 12 : ℝ) := by linarith
          change lo n (observedSample n z.1, z.2) < ((5 / 12 : ℝ) : EReal)
          exact hz.1.trans_lt (EReal.coe_lt_coe_iff.mpr hband)
        · have hlow := (abs_lt.mp hgood).1
          change -(1 / 12 : ℝ) < θ true σ - 2 / 3 at hlow
          have hband : (7 / 12 : ℝ) < θ true σ := by linarith
          change ((7 / 12 : ℝ) : EReal) < hi n (observedSample n z.1, z.2)
          exact (EReal.coe_lt_coe_iff.mpr hband).trans_le hz.2
      have hh := (hmodel f σ).trans (measureReal_mono hincl)
      simpa only [bad, if_neg hbad, sub_zero] using hh
  let pF : Bool → ℝ := fun f =>
    ∑ σ : Fin (M + 1) → Bool, p * (μ f σ).real (D' f)
  let sF : Bool → ℝ := fun f => S.real (D' f)
  have hprior (f : Bool) : c - 16 / (M + 1 : ℝ) ≤ pF f := by
    have hp : 0 ≤ p := by positivity
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (M + 1) → Bool)))
      (fun σ _ => mul_le_mul_of_nonneg_left (hfamily f σ) hp)
    have heq : (∑ σ : Fin (M + 1) → Bool, p * (c - bad f σ)) =
        c - (∑ σ : Fin (M + 1) → Bool, p * bad f σ) := by
      simp only [p, mul_sub, Finset.sum_sub_distrib, prior_average_const]
    rw [heq] at hh
    change c - 16 / (M + 1 : ℝ) ≤
      ∑ σ : Fin (M + 1) → Bool, p * (μ f σ).real (D' f)
    linarith [hb f]
  let d : ℝ := (n : ℝ) * (n - 1) / (2 * (M + 1))
  have htransfer (f : Bool) : |pF f - sF f| ≤ d := s13 Q M f n (D f) (hD f)
  have hbase (f : Bool) : c - 16 / (M + 1 : ℝ) - d ≤ sF f := by
    have ht := (abs_le.mp (htransfer f)).2
    linarith [hprior f]
  have hintersection : sF true + sF false - 1 ≤ S.real (D' true ∩ D' false) := by
    have heq := measureReal_union_add_inter (μ := S) (s := D' true) (hD' false)
    have hu : S.real (D' true ∪ D' false) ≤ 1 := measureReal_le_one
    change S.real (D' true) + S.real (D' false) - 1 ≤ _
    linarith
  have hwidth : S.real (D' true ∩ D' false) ≤ widthProb Q lo hi n := by
    have hSfin : IsFiniteMeasure S := by
      dsimp only [S]
      infer_instance
    refine measureReal_mono ?_ (measure_ne_top S _)
    intro z hz
    have hA : ((7 / 12 : ℝ) : EReal) < hi n (observedSample n z.1, z.2) := hz.1
    have hB : lo n (observedSample n z.1, z.2) < ((5 / 12 : ℝ) : EReal) := hz.2
    have hadd := EReal.add_lt_add_right_coe hB (1 / 6 : ℝ)
    have hnum : ((5 / 12 : ℝ) : EReal) + ((1 / 6 : ℝ) : EReal) =
        ((7 / 12 : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      norm_num
    rw [hnum] at hadd
    exact hadd.trans hA
  have hd : (n : ℝ) * (n - 1) / (M + 1) = 2 * d := by
    have hden : (M : ℝ) + 1 ≠ 0 := by positivity
    dsimp [d]
    field_simp [hden] <;> ring
  have h32 : (32 : ℝ) / (M + 1) = 2 * (16 / (M + 1)) := by ring
  change 2 * c - 1 - 32 / (M + 1) - (n : ℝ) * (n - 1) / (M + 1) ≤ widthProb Q lo hi n
  rw [hd, h32]
  linarith [hbase true, hbase false]

end

end AronowAudit.P047.Wave1.Impossibility
