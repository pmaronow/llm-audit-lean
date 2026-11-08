import SAP.P001e.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology Classical

namespace SAP.P001e.WH.W2
universe u v
noncomputable section

/-- Group the unit data, apply the certified cell algebra, and realize arbitrary
cell sums for the reverse implication of the saturation criterion. -/
theorem T85_assembly (h1 : T85_L1.{u}) (h2 : T85_L2.{u}) : T85WholeStatement.{u} := by
  intro n E _ hn X R q hb hr hq
  let C := wholeCells X
  let N : C → ℝ := fun x => wholeCellN X x
  let r : C → ℝ := fun x => wholeCellR X R x
  let qc : C → ℝ := fun x => q x
  obtain ⟨hN,htotal,hw,hform⟩ := h1 hn X R q hb
  have hrc : ∀ x : C, 0 < r x := fun x => hr x x.property
  have hqc : ∀ x : C, 0 < qc x := fun x => hq x x.property
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have core := cell85 N r qc n hnR hN hrc hqc htotal
  have hsize : (∑ x ∈ wholeCells X, wholeCellN X x)=(n : ℝ) := by
    simpa only [Finset.sum_coe_sort] using htotal
  have hequiv : (∀ Y : Fin n → ℝ, wholeSampleIPW X R Y q=wholeSamplePlugIn X R Y) ↔
      ∀ x ∈ wholeCells X, q x=wholeCellR X R x/wholeCellN X x := by
    constructor
    · intro ha
      have hs : ∀ x : C, qc x=r x/N x := by
        apply core.2.1.mp
        intro S
        obtain ⟨Y,hY⟩ := h2 X R hb hr S
        have hSY : (fun x : C => wholeCellS X R Y x)=S := funext hY
        have h := ha Y
        rw [(hform Y).1,(hform Y).2.1,hSY] at h
        exact h
      exact fun x hx => hs ⟨x,hx⟩
    · intro hs Y
      have ha := core.2.1.mpr (fun x : C => hs x x.property) (fun x : C => wholeCellS X R Y x)
      rw [(hform Y).1,(hform Y).2.1]
      exact ha
  refine ⟨?_,hequiv,?_⟩
  · intro Y
    refine ⟨?_,?_,?_⟩
    · exact (hform Y).1.trans (congrArg (fun z : ℝ => z/(n : ℝ))
        (Finset.sum_coe_sort C (fun x => wholeCellS X R Y x/q x)))
    · exact (hform Y).2.1.trans (congrArg (fun z : ℝ => z/(n : ℝ))
        (Finset.sum_coe_sort C (fun x => wholeCellN X x*wholeCellS X R Y x/wholeCellR X R x)))
    · rw [(hform Y).1,(hform Y).2.1]
      exact (core.1 (fun x : C => wholeCellS X R Y x)).trans
        (congrArg (fun z : ℝ => z/(n : ℝ)) (Finset.sum_coe_sort C
          (fun x => wholeCellS X R Y x*(1/q x-wholeCellN X x/wholeCellR X R x))))
  · intro hs
    obtain ⟨hw1,ha⟩ := core.2.2 (fun x : C => hs x x.property)
    have hwunit : wholeSampleWeight X R q=1 := hw.trans hw1
    refine ⟨?_,hwunit,?_⟩
    · rw [hwunit,hsize]
      exact (div_self hnR.ne').symm
    · intro Y
      refine ⟨hequiv.mpr hs Y,?_⟩
      rw [wholeSampleStabilized,(hform Y).2.2,hwunit,div_one]

/-- The CEF construction and selection theorem are already proved; only the
stable-outcome transport and respondent-to-population L1 comparison are leaves. -/
theorem T87_assembly (h1 : T87_L1.{u,0}) (h2 : T87_L2.{u,0}) : T87WholeStatement.{u} := by
  intro Ω _ K μ _ X hX Y R hY hR hYi hb
  refine ⟨exists_conditionalMean (μ.restrict {ω | R ω=1}) X hX Y hYi.integrableOn,?_⟩
  intro m hm
  obtain ⟨hrespond,hzero,hfull⟩ := h1 μ X hX Y R hY hR hYi hb m hm
  refine ⟨hrespond,hzero,hfull,?_⟩
  intro p hp hpos hind
  have hmi : Integrable (m ∘ X) μ := h2 μ X hX R hR hb p m hp hm.1 hpos hm.2.2.1
  exact ⟨hmi,mar_transfer μ X hX Y R hY hR hYi hb p m hp hpos hind hm hmi⟩


/-- Integrate the arm CEFs, transport versions across equal observable laws, and
compute empirical expectations. Every dependency is an explicit leaf argument. -/
theorem T94_assembly (h1 : T94_L1.{u,0}) (h2 : T94_L2.{u,0})
    (h3 : T94_L3.{u}) (h4 : T94_L4.{u,0}) (h5 : T94_L5.{u}) : T94WholeStatement.{u} := by
  have population : WholePotentialPopulation.{u} := by
    intro Ω _ μ _ K τ X D Y0 Y1 p model g θ correct
    let O : Ω → ℝ := fun ω => realizedOutcome (Y0 ω) (Y1 ω) (D ω)
    let F : ℝ × (Fin K → ℝ) → ℝ := fun dx => integratedModelMean g dx.1 dx.2 θ
    have hO : Measurable O := by
      dsimp [O,realizedOutcome]
      exact (model.hY1.mul model.hD).add (model.hY0.mul (measurable_const.sub model.hD))
    have hOi : Integrable O μ := potential_observed_integrable μ X D Y0 Y1 p model
    have hobs : IsConditionalMean μ (fun ω => (D ω,X ω)) O F :=
      h1 μ _ (model.hD.prodMk model.hX) O hO hOi (fun dx y => g y dx.1 dx.2 θ) correct.1
    have harm := h3 h2 μ X D Y0 Y1 p model F hobs correct.2.2
    intro d hd
    have hm := harm d hd
    have hmean := mean_of_conditionalMean μ X (if d=0 then Y0 else Y1) _ hm
    have hmap : expectation μ (fun ω => integratedModelMean g d (X ω) θ)=
        ∫ x, integratedModelMean g d x θ ∂μ.map X :=
      (integral_map model.hX.aemeasurable hm.1.aestronglyMeasurable).symm
    refine ⟨hm,hmean,hmap,?_⟩
    intro fX hfX hnonneg hlaw
    calc
      expectation μ (if d=0 then Y0 else Y1) =
          ∫ x, integratedModelMean g d x θ ∂μ.map X := hmean.trans hmap
      _ = ∫ x, integratedModelMean g d x θ ∂volume.withDensity (fun x => ENNReal.ofReal (fX x)) := by rw [hlaw]
      _ = ∫ x, integratedModelMean g d x θ*fX x := by
        rw [integral_withDensity_eq_integral_toReal_smul hfX.ennreal_ofReal
          (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
        simp only [ENNReal.toReal_ofReal (hnonneg _),smul_eq_mul,mul_comm]
  refine ⟨population,?_,?_⟩
  · intro Ω Ω' _ _ μ ν _ _ K τ τ' X D Y0 Y1 p X' D' Y0' Y1' p' model model' g θ g' θ' correct correct' hlaw
    obtain ⟨hXlaw,he⟩ := h5 h4 μ ν X D Y0 Y1 p X' D' Y0' Y1' p' model model' g θ g' θ' correct correct' hlaw
    have hi (d : ℝ) (hd : d ∈ ({0,1} : Set ℝ)) :
        expectation μ (if d=0 then Y0 else Y1)=expectation ν (if d=0 then Y0' else Y1') := by
      have ha := population μ X D Y0 Y1 p model g θ correct d hd
      have hb := population ν X' D' Y0' Y1' p' model' g' θ' correct' d hd
      calc
        _ = ∫ x, integratedModelMean g d x θ ∂μ.map X := ha.2.1.trans ha.2.2.1
        _ = ∫ x, integratedModelMean g' d x θ' ∂μ.map X := integral_congr_ae (he d hd)
        _ = ∫ x, integratedModelMean g' d x θ' ∂ν.map X' := by rw [hXlaw]
        _ = _ := (hb.2.1.trans hb.2.2.1).symm
    exact ⟨by simpa using hi 0 (by simp),by simpa using hi 1 (by simp)⟩
  · intro n K τ hn g Y D X Θ θhat hfit hi
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    refine ⟨?_,?_⟩
    · intro d hd
      refine ⟨Bridge.fitted_formula g d X θhat,?_,?_⟩
      · unfold wholeEmpiricalCovariates
        rw [integral_smul_measure,integral_finsetSum_measure
          (fun i _ => integrable_dirac (by simp))]
        simp only [integral_dirac,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
        unfold fittedPotentialAverage
        ring
      · intro x hx
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        field_simp
    · unfold fittedPotentialAverage
      rw [Finset.sum_sub_distrib]
      ring

/-- The two-point counterexample needs no deferred mathematics. -/
theorem T93_assembly : T93WholeStatement := by
  have hprob : IsProbabilityMeasure wholeCoinLaw := ⟨by
    norm_num [wholeCoinLaw]
    simpa only [one_div] using ENNReal.add_halves 1⟩
  have : IsProbabilityMeasure wholeCoinLaw := hprob
  have hd : Measurable wholeCoinD := measurable_of_countable _
  have hb : ∀ i, wholeCoinD i=0 ∨ wholeCoinD i=1 := by
    intro i
    fin_cases i <;> norm_num [wholeCoinD]
  have hi : Integrable wholeCoinD wholeCoinLaw :=
    Integrable.of_bound hd.aestronglyMeasurable 1 (ae_of_all _ (by
      intro i
      rcases hb i with h | h <;> simp [h]))
  have he : ∫ i, wholeCoinD i ∂wholeCoinLaw=(1/2 : ℝ) := by
    unfold wholeCoinLaw
    rw [integral_add_measure]
    · norm_num [integral_smul_measure, wholeCoinD]
    · exact hi.mono_measure (Measure.le_add_right le_rfl)
    · exact hi.mono_measure (Measure.le_add_left le_rfl)
  have hc : ∀ i, realizedOutcome (wholeCoinD i) (wholeCoinD i) (wholeCoinD i)=wholeCoinD i := by
    intro i
    rcases hb i with h | h <;> simp [realizedOutcome,h]
  have hp : IsConditionalMean wholeCoinLaw (fun _ : Fin 2 => (0 : ℝ)) wholeCoinD (fun _ => 1/2) := by
    refine ⟨measurable_const,hi,integrable_const _,?_⟩
    intro A hA
    by_cases h : (0 : ℝ)∈A
    · simp [h,he]
    · simp [h]
  refine ⟨hprob,hd,hi,hb,?_,?_,hc,hp,?_,?_,?_,?_,by norm_num⟩
  · norm_num [probability,wholeCoinLaw,wholeCoinD,Measure.add_apply]
  · norm_num [probability,wholeCoinLaw,wholeCoinD,Measure.add_apply]
  · intro i
    norm_num
  · apply conditionalMean_of_eq _ _ _ _ (by fun_prop)
      (hi.congr (ae_of_all _ (fun i => (hc i).symm)))
    funext i
    simp [hc i]
  · apply conditionalMean_of_eq _ _ _ _ measurable_const
    · simp only [sub_self]
      exact integrable_const 0
    · funext i
      simp
  · simp [expectation]

/-- All assertions for the six-atom example reduce to the certified donors and
short exact finite calculations, so there are no deferred leaves. -/
theorem T89_assembly : T89WholeStatement := by
  have hold : T89Statement := by
    rcases Bridge.post_latent with ⟨hi,hp,hc,hz,hn⟩
    rcases Bridge.post_numbers with ⟨hm,hpx,h01,h11,h00,h10,ha⟩
    have hpx1 : finiteProbability postWeights (fun i => postCovariate i=1)=1/2 := by
      norm_num [finiteProbability,postWeights,postCovariate,Fin.sum_univ_succ]
    refine ⟨hi,hp,hc,hz,hn,hm,hpx,hpx1,?_,h01,h11,h00,h10,?_⟩
    · intro x hx d hd
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx hd
      rcases hx with rfl | rfl <;> rcases hd with rfl | rfl <;>
        norm_num [finiteProbability,postWeights,postCovariate,postAssignment,Fin.sum_univ_succ]
    · simpa only [postAdjustedContrast,h01,h11,h00,h10,hpx,hpx1] using ha
  refine ⟨hold,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    norm_num [postWeights]
  · norm_num [postWeights,Fin.sum_univ_succ]
  · funext i
    fin_cases i <;> norm_num [postOutcome,postCovariate1,postCovariate0,postAssignment]
  · intro i
    fin_cases i <;> norm_num [realizedOutcome,postOutcome,postAssignment]
  · norm_num [finiteProbability,postWeights,postCovariate1,postCovariate0,Fin.sum_univ_succ]
  · intro y x d
    simp only [finiteProbability,postWeights,postOutcome,postCovariate,postAssignment,
      Fin.sum_univ_succ,wholePostPMF]
    norm_num only [Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.mk_one,
      Finset.sum_singleton] 
    split_ifs <;> ring
  · norm_num [wholePostCells]
  · norm_num [wholePostCells,wholePostPMF,Finset.sum_insert,Finset.sum_singleton]
  · norm_num [wholePostCells]
  all_goals norm_num [finiteProbability,postWeights,postOutcome,postCovariate,postAssignment,Fin.sum_univ_succ]

end
end SAP.P001e.WH.W2
