import SAP.P029b.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W2.P.T27_L2

open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open SAP.P029b.WH.W2

noncomputable section

def profile (a : CancelAtomW2) : Bool := (cancelUnitW2 a).x

def compInd (a : CancelAtomW2) : ℝ :=
  if (cancelUnitW2 a).complier then 1 else 0

def compTau (a : CancelAtomW2) : ℝ :=
  if (cancelUnitW2 a).complier then (cancelUnitW2 a).tau else 0

def complierSet : Set CancelAtomW2 := {a | (cancelUnitW2 a).complier}

def popTau (a : CancelAtomW2) : ℝ := (cancelUnitW2 a).tau

def compProfile (x : Bool) : Set CancelAtomW2 :=
  {a | (cancelUnitW2 a).complier ∧ (cancelUnitW2 a).x = x}

def profileFiber (x : Bool) : Set CancelAtomW2 := {a | (cancelUnitW2 a).x = x}

def sampleProfileFiber (i : ℕ) (x : Bool) : Set CancelSpaceW2 :=
  {ω | (cancelDrawW2 i ω).x = x}

def sampleCompInd (i : ℕ) (ω : CancelSpaceW2) : ℝ := compInd (ω i)
def sampleCompTau (i : ℕ) (ω : CancelSpaceW2) : ℝ := compTau (ω i)
def sampleTau (i : ℕ) (ω : CancelSpaceW2) : ℝ := popTau (ω i)

lemma cancelLaw_probability : IsProbabilityMeasure cancelLawW2 := by
  infer_instance

lemma cancelSample_probability : IsProbabilityMeasure cancelSampleLawW2 := by
  let μ : ℕ → Measure CancelAtomW2 := fun _ => cancelLawW2
  haveI : ∀ j, IsProbabilityMeasure (μ j) := fun _ => cancelLaw_probability
  change IsProbabilityMeasure (Measure.infinitePi μ)
  exact inferInstance

lemma coord_setIntegral (i : ℕ) (F : CancelAtomW2 → ℝ) (T : Set Bool) :
    (∫ ω in {ω | (cancelUnitW2 (ω i)).x ∈ T}, F (ω i) ∂cancelSampleLawW2) =
      ∫ a in {a | (cancelUnitW2 a).x ∈ T}, F a ∂cancelLawW2 := by
  let ev : CancelSpaceW2 → CancelAtomW2 := fun ω => ω i
  let S : Set CancelAtomW2 := {a | (cancelUnitW2 a).x ∈ T}
  have hmap : Measure.map ev cancelSampleLawW2 = cancelLawW2 := by
    simpa [ev, cancelSampleLawW2] using
      (Measure.infinitePi_map_eval (μ := fun _ : ℕ => cancelLawW2) i)
  have hset : ev ⁻¹' S = {ω | (cancelUnitW2 (ω i)).x ∈ T} := by
    ext ω
    rfl
  rw [← hset, ← hmap]
  symm
  exact setIntegral_map MeasurableSet.of_discrete (by fun_prop)
    (measurable_pi_apply i).aemeasurable

lemma coord_integrable (i : ℕ) (F : CancelAtomW2 → ℝ) :
    Integrable (fun ω : CancelSpaceW2 => F (ω i)) cancelSampleLawW2 := by
  haveI : IsProbabilityMeasure cancelLawW2 := cancelLaw_probability
  haveI : IsProbabilityMeasure cancelSampleLawW2 := cancelSample_probability
  have hm : Measurable (fun ω : CancelSpaceW2 => F (ω i)) :=
    (Measurable.of_discrete : Measurable F).comp (measurable_pi_apply i)
  exact Integrable.of_bound hm.aestronglyMeasurable ‖F‖
    (ae_of_all _ fun ω => norm_le_pi_norm F (ω i))

lemma finite_profile_integrals_all (F G : CancelAtomW2 → ℝ)
    (hfalse : ∫ a in profileFiber false, F a ∂cancelLawW2 =
      ∫ a in profileFiber false, G a ∂cancelLawW2)
    (htrue : ∫ a in profileFiber true, F a ∂cancelLawW2 =
      ∫ a in profileFiber true, G a ∂cancelLawW2) :
    ∀ T : Set Bool,
      ∫ a in {a | (cancelUnitW2 a).x ∈ T}, F a ∂cancelLawW2 =
      ∫ a in {a | (cancelUnitW2 a).x ∈ T}, G a ∂cancelLawW2 := by
  intro T
  by_cases ht : true ∈ T <;> by_cases hf : false ∈ T
  · have hT : T = Set.univ := by
      ext b
      cases b <;> simp [ht, hf]
    subst T
    letI : IsProbabilityMeasure cancelLawW2 := cancelLaw_probability
    have hF : Integrable F cancelLawW2 := Integrable.of_finite
    have hG : Integrable G cancelLawW2 := Integrable.of_finite
    have hUnion : profileFiber false ∪ profileFiber true = Set.univ := by
      ext a
      cases (cancelUnitW2 a).x <;> simp [profileFiber]
    have hDisj : Disjoint (profileFiber false) (profileFiber true) := by
      refine Set.disjoint_left.mpr ?_
      intro a ha hb
      exact Bool.noConfusion (ha.symm.trans hb)
    have hMTrue : MeasurableSet (profileFiber true) := MeasurableSet.of_discrete
    have hMFalse : MeasurableSet (profileFiber false) := MeasurableSet.of_discrete
    have hTset : {a : CancelAtomW2 | (cancelUnitW2 a).x ∈ (Set.univ : Set Bool)} = Set.univ := by
      ext a
      simp
    rw [hTset]
    rw [← hUnion]
    rw [setIntegral_union hDisj hMTrue
      hF.integrableOn hF.integrableOn]
    rw [setIntegral_union hDisj hMTrue
      hG.integrableOn hG.integrableOn]
    rw [hfalse, htrue]
  · have hT : T = {true} := by
      ext b
      cases b <;> simp [ht, hf]
    subst T
    simpa [profileFiber] using htrue
  · have hT : T = {false} := by
      ext b
      cases b <;> simp [ht, hf]
    subst T
    simpa [profileFiber] using hfalse
  · have hT : T = ∅ := by
      ext b
      cases b <;> simp [ht, hf]
    subst T
    simp

lemma sample_profile_integrals_all (i : ℕ) (F G : CancelAtomW2 → ℝ)
    (hfalse : ∫ ω in sampleProfileFiber i false, F (ω i) ∂cancelSampleLawW2 =
      ∫ ω in sampleProfileFiber i false, G (ω i) ∂cancelSampleLawW2)
    (htrue : ∫ ω in sampleProfileFiber i true, F (ω i) ∂cancelSampleLawW2 =
      ∫ ω in sampleProfileFiber i true, G (ω i) ∂cancelSampleLawW2) :
    ∀ T : Set Bool,
      ∫ ω in {ω | (cancelDrawW2 i ω).x ∈ T}, F (ω i) ∂cancelSampleLawW2 =
      ∫ ω in {ω | (cancelDrawW2 i ω).x ∈ T}, G (ω i) ∂cancelSampleLawW2 := by
  intro T
  have hf : ∫ a in profileFiber false, F a ∂cancelLawW2 =
      ∫ a in profileFiber false, G a ∂cancelLawW2 := by
    calc
      _ = ∫ ω in sampleProfileFiber i false, F (ω i) ∂cancelSampleLawW2 := by
        simpa [profileFiber, sampleProfileFiber, cancelDrawW2] using
          (coord_setIntegral i F {false}).symm
      _ = ∫ ω in sampleProfileFiber i false, G (ω i) ∂cancelSampleLawW2 := hfalse
      _ = _ := by
        simpa [profileFiber, sampleProfileFiber, cancelDrawW2] using
          (coord_setIntegral i G {false})
  have ht : ∫ a in profileFiber true, F a ∂cancelLawW2 =
      ∫ a in profileFiber true, G a ∂cancelLawW2 := by
    calc
      _ = ∫ ω in sampleProfileFiber i true, F (ω i) ∂cancelSampleLawW2 := by
        simpa [profileFiber, sampleProfileFiber, cancelDrawW2] using
          (coord_setIntegral i F {true}).symm
      _ = ∫ ω in sampleProfileFiber i true, G (ω i) ∂cancelSampleLawW2 := htrue
      _ = _ := by
        simpa [profileFiber, sampleProfileFiber, cancelDrawW2] using
          (coord_setIntegral i G {true})
  calc
    _ = ∫ a in {a | (cancelUnitW2 a).x ∈ T}, F a ∂cancelLawW2 := by
      change ∫ ω in {ω | (cancelUnitW2 (ω i)).x ∈ T}, F (ω i) ∂cancelSampleLawW2 = _
      exact coord_setIntegral i F T
    _ = ∫ a in {a | (cancelUnitW2 a).x ∈ T}, G a ∂cancelLawW2 :=
      finite_profile_integrals_all F G hf ht T
    _ = _ := by
      change ∫ a in {a | (cancelUnitW2 a).x ∈ T}, G a ∂cancelLawW2 =
        ∫ ω in {ω | (cancelUnitW2 (ω i)).x ∈ T}, G (ω i) ∂cancelSampleLawW2
      exact (coord_setIntegral i G T).symm

lemma finite_compiler_mass (hpop : CancellationPopulationW2) (x : Bool) :
    mP cancelLawW2 (compProfile x) = 1/6 := by
  rcases hpop.2.1 x with ⟨hprof, hscore, -, -, -⟩
  have hscore' : mP cancelLawW2 (compProfile x) /
      mP cancelLawW2 {a | (cancelUnitW2 a).x = x} = 1/3 := by
    simpa [scoreAt, compProfile] using hscore
  have hdiv : mP cancelLawW2 (compProfile x) /
      (1/2 : ℝ) = 1/3 := by
    rw [hprof] at hscore'
    exact hscore'
  have hmul : mP cancelLawW2 (compProfile x) = (1/3 : ℝ) * (1/2) :=
    (div_eq_iff (by norm_num : (1/2 : ℝ) ≠ 0)).mp hdiv
  norm_num at hmul
  exact hmul

lemma finite_compInd_integral (hpop : CancellationPopulationW2) (x : Bool) :
    ∫ a in profileFiber x, compInd a ∂cancelLawW2 = 1/6 := by
  have hind : compInd = complierSet.indicator (fun _ => (1 : ℝ)) := by
    funext a
    by_cases hc : (cancelUnitW2 a).complier <;> simp [compInd, Set.indicator, hc, complierSet]
  rw [hind, setIntegral_indicator MeasurableSet.of_discrete]
  have hset : profileFiber x ∩ complierSet = compProfile x := by
    ext a
    simp [profileFiber, compProfile, complierSet, and_comm]
  rw [hset, setIntegral_const, smul_eq_mul]
  change mP cancelLawW2 (compProfile x) * (1 : ℝ) = 1/6
  simpa using finite_compiler_mass hpop x

lemma finite_compTau_integral (hpop : CancellationPopulationW2) (x : Bool) :
    ∫ a in profileFiber x, compTau a ∂cancelLawW2 = 0 := by
  rcases hpop.2.1 x with ⟨-, -, hce, -, -⟩
  have hnum : ∫ a in compProfile x, (cancelUnitW2 a).tau ∂cancelLawW2 = 0 := by
    have hmass := finite_compiler_mass hpop x
    change (∫ a in compProfile x, (cancelUnitW2 a).tau ∂cancelLawW2) /
      mP cancelLawW2 (compProfile x) = 0 at hce
    rw [hmass] at hce
    have hdiv : (∫ a in compProfile x, (cancelUnitW2 a).tau ∂cancelLawW2) /
        (1/6 : ℝ) = 0 := hce
    have hh := (div_eq_iff (by norm_num : (1/6 : ℝ) ≠ 0)).mp hdiv
    simpa using hh
  have hind : compTau = complierSet.indicator (fun a => (cancelUnitW2 a).tau) := by
    funext a
    by_cases hc : (cancelUnitW2 a).complier <;>
      simp [compTau, Set.indicator, hc, complierSet]
  rw [hind, setIntegral_indicator MeasurableSet.of_discrete]
  have hset : profileFiber x ∩ complierSet = compProfile x := by
    ext a
    simp [profileFiber, compProfile, complierSet, and_comm]
  rw [hset]
  exact hnum

lemma finite_profile_tau_integral (hpop : CancellationPopulationW2) (x : Bool) :
    ∫ a in profileFiber x, popTau a ∂cancelLawW2 = if x then 2/3 else -2/3 := by
  rcases hpop.2.1 x with ⟨hprof, -, -, hmean, -⟩
  have hdiv : (∫ a in profileFiber x, (cancelUnitW2 a).tau ∂cancelLawW2) /
      (1/2 : ℝ) = (if x then 4/3 else -4/3) := by
    change (∫ a in {a | (cancelUnitW2 a).x = x}, (cancelUnitW2 a).tau ∂cancelLawW2) /
      mP cancelLawW2 {a | (cancelUnitW2 a).x = x} = _ at hmean
    rw [hprof] at hmean
    exact hmean
  have hh := (div_eq_iff (by norm_num : (1/2 : ℝ) ≠ 0)).mp hdiv
  cases x <;> norm_num at hh ⊢
  · exact hh
  · exact hh

lemma finite_const_profile_integral (hpop : CancellationPopulationW2) (x : Bool) :
    ∫ a in profileFiber x, (1/3 : ℝ) ∂cancelLawW2 = 1/6 := by
  rcases hpop.2.1 x with ⟨hprof, -, -, -, -⟩
  rw [setIntegral_const, smul_eq_mul]
  change mP cancelLawW2 {a | (cancelUnitW2 a).x = x} * (1/3 : ℝ) = 1/6
  rw [hprof]
  norm_num

lemma finite_zero_profile_integral (hpop : CancellationPopulationW2) (x : Bool) :
    ∫ a in profileFiber x, (0 : ℝ) ∂cancelLawW2 = 0 := by
  simp

lemma coordinate_measurable (i : ℕ) :
    Measurable (fun ω : CancelSpaceW2 => (cancelDrawW2 i ω).x) := by
  fun_prop

lemma profile_condExp_indicator (i : ℕ) (hpop : CancellationPopulationW2) :
    (fun _ : CancelSpaceW2 => (1/3 : ℝ)) =ᵐ[cancelSampleLawW2]
      condExp (covariateSigma (cancelDrawW2 i)) cancelSampleLawW2 (sampleCompInd i) := by
  let f := sampleCompInd i
  let g : CancelSpaceW2 → ℝ := fun _ => 1/3
  have hm : covariateSigma (cancelDrawW2 i) ≤
      (inferInstance : MeasurableSpace CancelSpaceW2) := by
    exact (coordinate_measurable i).comap_le
  haveI : IsProbabilityMeasure cancelLawW2 := cancelLaw_probability
  haveI : IsProbabilityMeasure cancelSampleLawW2 := cancelSample_probability
  haveI : SigmaFinite (cancelSampleLawW2.trim hm) := by
    apply MeasureTheory.Measure.sigmaFinite_of_countable (S := {Set.univ})
    · exact Set.countable_singleton Set.univ
    · intro s hs
      simp only [Set.mem_singleton_iff] at hs
      subst s
      exact measure_lt_top _ _
    · simp
  have hf : Integrable f cancelSampleLawW2 := by
    change Integrable (fun ω => compInd (ω i)) cancelSampleLawW2
    exact coord_integrable i compInd
  have hgm : AEStronglyMeasurable[covariateSigma (cancelDrawW2 i)] g cancelSampleLawW2 := by
    exact stronglyMeasurable_const.aestronglyMeasurable
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_ hgm
  · intro s hs hμs
    exact IntegrableOn.of_bound hμs (stronglyMeasurable_const.aestronglyMeasurable) 1
      (ae_of_all _ fun _ => by norm_num)
  · intro s hs hμs
    rcases (MeasurableSpace.measurableSet_comap).mp hs with ⟨T, hT, rfl⟩
    have hfalse :
        ∫ ω in sampleProfileFiber i false, (fun _ => (1/3 : ℝ)) (ω i) ∂cancelSampleLawW2 =
          ∫ ω in sampleProfileFiber i false, compInd (ω i) ∂cancelSampleLawW2 := by
      calc
        _ = ∫ a in profileFiber false, (1/3 : ℝ) ∂cancelLawW2 := by
          simpa [sampleProfileFiber, profileFiber, profile, cancelDrawW2] using
            (coord_setIntegral i (fun _ => (1/3 : ℝ)) {false})
        _ = ∫ a in profileFiber false, compInd a ∂cancelLawW2 := by
          rw [finite_const_profile_integral hpop false, finite_compInd_integral hpop false]
        _ = _ := by
          simpa [sampleProfileFiber, profileFiber, profile, cancelDrawW2] using
            (coord_setIntegral i compInd {false}).symm
    have htrue :
        ∫ ω in sampleProfileFiber i true, (fun _ => (1/3 : ℝ)) (ω i) ∂cancelSampleLawW2 =
          ∫ ω in sampleProfileFiber i true, compInd (ω i) ∂cancelSampleLawW2 := by
      calc
        _ = ∫ a in profileFiber true, (1/3 : ℝ) ∂cancelLawW2 := by
          simpa [sampleProfileFiber, profileFiber, profile, cancelDrawW2] using
            (coord_setIntegral i (fun _ => (1/3 : ℝ)) {true})
        _ = ∫ a in profileFiber true, compInd a ∂cancelLawW2 := by
          rw [finite_const_profile_integral hpop true, finite_compInd_integral hpop true]
        _ = _ := by
          simpa [sampleProfileFiber, profileFiber, profile, cancelDrawW2] using
            (coord_setIntegral i compInd {true}).symm
    change (∫ ω in {ω | (cancelDrawW2 i ω).x ∈ T}, (1/3 : ℝ) ∂cancelSampleLawW2) =
      ∫ ω in {ω | (cancelDrawW2 i ω).x ∈ T}, sampleCompInd i ω ∂cancelSampleLawW2
    simpa [sampleCompInd] using
      sample_profile_integrals_all i (fun _ => (1/3 : ℝ)) compInd hfalse htrue T

lemma profile_condExp_compTau (i : ℕ) (hpop : CancellationPopulationW2) :
    (fun _ : CancelSpaceW2 => (0 : ℝ)) =ᵐ[cancelSampleLawW2]
      condExp (covariateSigma (cancelDrawW2 i)) cancelSampleLawW2
        (fun ω => compTau (ω i)) := by
  let f : CancelSpaceW2 → ℝ := fun ω => compTau (ω i)
  let g : CancelSpaceW2 → ℝ := fun _ => 0
  have hm : covariateSigma (cancelDrawW2 i) ≤
      (inferInstance : MeasurableSpace CancelSpaceW2) := by
    exact (coordinate_measurable i).comap_le
  haveI : IsProbabilityMeasure cancelLawW2 := cancelLaw_probability
  haveI : IsProbabilityMeasure cancelSampleLawW2 := cancelSample_probability
  haveI : SigmaFinite (cancelSampleLawW2.trim hm) := by
    apply MeasureTheory.Measure.sigmaFinite_of_countable (S := {Set.univ})
    · exact Set.countable_singleton Set.univ
    · intro s hs
      simp only [Set.mem_singleton_iff] at hs
      subst s
      exact measure_lt_top _ _
    · simp
  have hf : Integrable f cancelSampleLawW2 := by
    change Integrable (fun ω => compTau (ω i)) cancelSampleLawW2
    exact coord_integrable i compTau
  have hgm : AEStronglyMeasurable[covariateSigma (cancelDrawW2 i)] g cancelSampleLawW2 := by
    exact stronglyMeasurable_const.aestronglyMeasurable
  refine ae_eq_condExp_of_forall_setIntegral_eq hm hf ?_ ?_ hgm
  · intro s hs hμs
    exact IntegrableOn.of_bound hμs (stronglyMeasurable_const.aestronglyMeasurable) 1
      (ae_of_all _ fun _ => by norm_num)
  · intro s hs hμs
    rcases (MeasurableSpace.measurableSet_comap).mp hs with ⟨T, hT, rfl⟩
    have hfalse :
        ∫ ω in sampleProfileFiber i false, (fun _ => (0 : ℝ)) (ω i) ∂cancelSampleLawW2 =
          ∫ ω in sampleProfileFiber i false, compTau (ω i) ∂cancelSampleLawW2 := by
      calc
        _ = ∫ a in profileFiber false, (0 : ℝ) ∂cancelLawW2 := by
          simpa [sampleProfileFiber, profileFiber, profile, cancelDrawW2] using
            (coord_setIntegral i (fun _ => (0 : ℝ)) {false})
        _ = ∫ a in profileFiber false, compTau a ∂cancelLawW2 := by
          rw [finite_zero_profile_integral hpop false, finite_compTau_integral hpop false]
        _ = _ := by
          simpa [sampleProfileFiber, profileFiber, profile, cancelDrawW2] using
            (coord_setIntegral i compTau {false}).symm
    have htrue :
        ∫ ω in sampleProfileFiber i true, (fun _ => (0 : ℝ)) (ω i) ∂cancelSampleLawW2 =
          ∫ ω in sampleProfileFiber i true, compTau (ω i) ∂cancelSampleLawW2 := by
      calc
        _ = ∫ a in profileFiber true, (0 : ℝ) ∂cancelLawW2 := by
          simpa [sampleProfileFiber, profileFiber, profile, cancelDrawW2] using
            (coord_setIntegral i (fun _ => (0 : ℝ)) {true})
        _ = ∫ a in profileFiber true, compTau a ∂cancelLawW2 := by
          rw [finite_zero_profile_integral hpop true, finite_compTau_integral hpop true]
        _ = _ := by
          simpa [sampleProfileFiber, profileFiber, profile, cancelDrawW2] using
            (coord_setIntegral i compTau {true}).symm
    change (∫ ω in {ω | (cancelDrawW2 i ω).x ∈ T}, (0 : ℝ) ∂cancelSampleLawW2) =
      ∫ ω in {ω | (cancelDrawW2 i ω).x ∈ T}, sampleCompTau i ω ∂cancelSampleLawW2
    simpa [sampleCompTau] using
      sample_profile_integrals_all i (fun _ => (0 : ℝ)) compTau hfalse htrue T

end
end SAP.P029b.WH.W2.P.T27_L2

open SAP.P029b.WH.W2
open SAP.P029b.WH.W2.P.T27_L2
open scoped BigOperators Classical Topology ENNReal
open MeasureTheory ProbabilityTheory Filter Set

theorem SAP.P029b.WH.W2.T27_L2_proof : SAP.P029b.WH.W2.T27_L2 := by
  intro hpop
  constructor
  · intro i
    constructor
    · exact measurable_const
    constructor
    · exact measurable_const
    constructor
    · change (fun _ : CancelSpaceW2 => (1/3 : ℝ)) =ᵐ[cancelSampleLawW2]
        condExp (covariateSigma (cancelDrawW2 i)) cancelSampleLawW2 (sampleCompInd i)
      exact profile_condExp_indicator i hpop
    · have hprod : (fun _ : CancelSpaceW2 => (1/3 : ℝ) * (0 : ℝ)) =ᵐ[cancelSampleLawW2]
          (fun _ => (0 : ℝ)) := by
        filter_upwards [] with ω
        simp
      change (fun ω : CancelSpaceW2 =>
        (fun _ : Bool => (1/3 : ℝ)) ((cancelDrawW2 i ω).x) *
          (fun _ : Bool => (0 : ℝ)) ((cancelDrawW2 i ω).x)) =ᵐ[cancelSampleLawW2]
        condExp (covariateSigma (cancelDrawW2 i)) cancelSampleLawW2
          (fun ω => if (cancelDrawW2 i ω).complier then (cancelDrawW2 i ω).tau else 0)
      exact hprod.trans (profile_condExp_compTau i hpop)
  · intro i hA1
    have hTauInt : Integrable (sampleTau i) cancelSampleLawW2 := by
      change Integrable (fun ω => popTau (ω i)) cancelSampleLawW2
      exact coord_integrable i popTau
    have hm : covariateSigma (cancelDrawW2 i) ≤
        (inferInstance : MeasurableSpace CancelSpaceW2) :=
      (coordinate_measurable i).comap_le
    haveI : IsProbabilityMeasure cancelSampleLawW2 := cancelSample_probability
    haveI : SigmaFinite (cancelSampleLawW2.trim hm) := by
      apply MeasureTheory.Measure.sigmaFinite_of_countable (S := {Set.univ})
      · exact Set.countable_singleton Set.univ
      · intro s hs
        simp only [Set.mem_singleton_iff] at hs
        subst s
        exact measure_lt_top _ _
      · simp
    have hsetAmb : MeasurableSet (sampleProfileFiber i false) := by
      exact measurableSet_eq_fun (coordinate_measurable i) measurable_const
    have hsetSigma : MeasurableSet[covariateSigma (cancelDrawW2 i)]
        (sampleProfileFiber i false) := by
      change MeasurableSet[MeasurableSpace.comap
        (fun ω => (cancelDrawW2 i ω).x) inferInstance] (sampleProfileFiber i false)
      refine (MeasurableSpace.measurableSet_comap).2
        ⟨{false}, MeasurableSet.of_discrete, ?_⟩
      ext ω
      simp [sampleProfileFiber]
    have hsetIntegral := setIntegral_congr_ae hsetAmb (by
      filter_upwards [hA1] with ω hω
      exact fun _ => hω)
    have hce := setIntegral_condExp hm hTauInt hsetSigma
    have hfin : ∫ ω in sampleProfileFiber i false, sampleTau i ω ∂cancelSampleLawW2 = -2/3 := by
      calc
        _ = ∫ a in profileFiber false, popTau a ∂cancelLawW2 := by
          simpa [sampleProfileFiber, sampleTau, profile, profileFiber, cancelDrawW2] using
            (coord_setIntegral i popTau {false})
        _ = -2/3 := by simpa using finite_profile_tau_integral hpop false
    have : (0 : ℝ) = -2/3 := by
      calc
        0 = ∫ ω in sampleProfileFiber i false, (0 : ℝ) ∂cancelSampleLawW2 := by simp
        _ = ∫ ω in sampleProfileFiber i false,
            condExp (covariateSigma (cancelDrawW2 i)) cancelSampleLawW2 (sampleTau i) ω
              ∂cancelSampleLawW2 := hsetIntegral
        _ = ∫ ω in sampleProfileFiber i false, sampleTau i ω ∂cancelSampleLawW2 := hce
        _ = -2/3 := hfin
    norm_num at this
