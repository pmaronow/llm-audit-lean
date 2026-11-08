import SAP.P028.WH.W1.Leaves
import AronowAudit.P028.P028_MissingOutcomes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

namespace SAP.P028.WH.W1.P.T2_L2

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge
noncomputable section
open Classical

def stratumOf (a : BinaryAtom) : Fin 3 :=
  if a.d0 then 0 else if a.d1 then 2 else 1

def latentVector (B : BinaryLaw) (i : Fin 17) : Fin 3 × ℝ × ℝ :=
  (stratumOf (B.atom i), (bit (B.atom i).y0 : ℝ), (bit (B.atom i).y1 : ℝ))

def latentMeasure (B : BinaryLaw) : Measure (Fin 17) :=
  ∑ i : Fin 17, ENNReal.ofReal (B.mass i : ℝ) • Measure.dirac i

def coinMeasure : Measure Bool :=
  ∑ z : Bool, ENNReal.ofReal (assignmentMass z : ℝ) • Measure.dirac z

lemma coinMass_pos (z : Bool) : 0 < assignmentMass z := by
  cases z <;> norm_num [assignmentMass]

lemma latentMeasure_probability (B : BinaryLaw) (hB : finiteValid B) :
    IsProbabilityMeasure (latentMeasure B) := by
  refine ⟨?_⟩
  have hsum : (∑ i : Fin 17, (B.mass i : ℝ)) = 1 := by
    exact_mod_cast hB.2.1
  have hnonneg : ∀ i : Fin 17, 0 ≤ (B.mass i : ℝ) := fun i => le_of_lt (by exact_mod_cast hB.1 i)
  unfold latentMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.mem_univ, if_true, Set.indicator_univ,
    ENNReal.smul_def, smul_eq_mul, mul_one]
  simp only [Pi.one_apply, mul_one]
  change (∑ i : Fin 17, ENNReal.ofReal (B.mass i : ℝ)) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (fun i _ => hnonneg i), hsum]
  norm_num

lemma coinMeasure_probability : IsProbabilityMeasure coinMeasure := by
  refine ⟨?_⟩
  unfold coinMeasure
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.mem_univ, if_true, Set.indicator_univ,
    ENNReal.smul_def, smul_eq_mul, mul_one]
  simp only [Pi.one_apply, mul_one]
  change (∑ z : Bool, ENNReal.ofReal (assignmentMass z : ℝ)) = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
    (fun z _ => le_of_lt (by exact_mod_cast coinMass_pos z))]
  norm_num [assignmentMass, Fintype.sum_bool]

lemma latentMeasure_singleton_measure (B : BinaryLaw) (hB : finiteValid B) (i : Fin 17) :
    latentMeasure B {i} = ENNReal.ofReal (B.mass i : ℝ) := by
  have hnonneg : 0 ≤ (B.mass i : ℝ) := le_of_lt (by exact_mod_cast hB.1 i)
  simp [latentMeasure, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply, Set.indicator_singleton, ENNReal.smul_def, smul_eq_mul,
    Pi.single_apply, hnonneg]

lemma coinMeasure_singleton_measure (z : Bool) :
    coinMeasure {z} = ENNReal.ofReal (assignmentMass z : ℝ) := by
  cases z <;> norm_num [coinMeasure, assignmentMass, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply, Set.indicator_singleton,
    ENNReal.smul_def, smul_eq_mul, Pi.single_apply]

lemma latentMeasure_real_singleton (B : BinaryLaw) (hB : finiteValid B) (i : Fin 17) :
    (latentMeasure B).real {i} = (B.mass i : ℝ) := by
  rw [Measure.real, latentMeasure_singleton_measure B hB]
  exact ENNReal.toReal_ofReal (le_of_lt (by exact_mod_cast hB.1 i))

lemma finiteJoint_eq_prod (B : BinaryLaw) (hB : finiteValid B) :
    wholeFiniteMeasure B = (latentMeasure B).prod coinMeasure := by
  apply Measure.ext_of_singleton
  intro x
  rcases x with ⟨i, z⟩
  have hrect : ({(i, z)} : Set (Fin 17 × Bool)) = ({i} : Set (Fin 17)) ×ˢ ({z} : Set Bool) := by
    ext y
    rcases y with ⟨j, w⟩
    simp
  rw [hrect, Measure.prod_prod, latentMeasure_singleton_measure B hB,
    coinMeasure_singleton_measure]
  have hmass : 0 ≤ (B.mass i : ℝ) := le_of_lt (by exact_mod_cast hB.1 i)
  have hassign : 0 ≤ (assignmentMass z : ℝ) := le_of_lt (by exact_mod_cast coinMass_pos z)
  rw [← ENNReal.ofReal_mul hmass]
  cases z <;> simp [wholeFiniteMeasure, jointMass, hmass, hassign, Rat.cast_mul,
    Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.indicator_singleton, ENNReal.smul_def, smul_eq_mul, Pi.single_apply, assignmentMass]

lemma latentComplierMass (B : BinaryLaw) (hB : finiteValid B) :
    (latentMeasure B).real {i | fc (B.atom i)} = (fpc B : ℝ) := by
  letI : IsProbabilityMeasure (latentMeasure B) := latentMeasure_probability B hB
  have hsum := MeasureTheory.sum_measureReal_preimage_singleton
    (μ := latentMeasure B)
    (s := Finset.univ.filter (fun i : Fin 17 => fc (B.atom i)))
    (f := id)
    (hf := fun i _ => measurableSet_singleton i)
  have hsum' : (latentMeasure B).real {i | fc (B.atom i)} =
      ∑ i ∈ Finset.univ.filter (fun i : Fin 17 => fc (B.atom i)),
        (latentMeasure B).real {i} := by
    convert hsum.symm using 1 <;> simp
  calc
    (latentMeasure B).real {i | fc (B.atom i)} =
        ∑ i ∈ Finset.univ.filter (fun i : Fin 17 => fc (B.atom i)),
          (latentMeasure B).real {i} := hsum'
    _ = ∑ i, if fc (B.atom i) then (B.mass i : ℝ) else 0 := by
      change (∑ i ∈ Finset.univ.filter (fun i : Fin 17 => fc (B.atom i)),
        (latentMeasure B).real {i}) = _
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hc : fc (B.atom i)
      · simp [hc, latentMeasure_real_singleton B hB]
      · simp [hc]
    _ = (fpc B : ℝ) := by
      have hq : (∑ i, if fc (B.atom i) then B.mass i else 0) = fpc B := by
        rfl
      calc
        (∑ i, if fc (B.atom i) then (B.mass i : ℝ) else 0) =
            ∑ i, ((if fc (B.atom i) then B.mass i else 0 : ℚ) : ℝ) := by
          apply Finset.sum_congr rfl
          intro i hi
          by_cases hc : fc (B.atom i) <;> simp [hc]
        _ = ((∑ i, if fc (B.atom i) then B.mass i else 0 : ℚ) : ℝ) := by simp
        _ = (fpc B : ℝ) := congrArg (fun q : ℚ => (q : ℝ)) hq

lemma complierMass (B : BinaryLaw) (hB : finiteValid B) :
    (wholeFiniteMeasure B).real {ω | fc (B.atom ω.1)} = (fpc B : ℝ) := by
  letI : IsProbabilityMeasure (latentMeasure B) := latentMeasure_probability B hB
  letI : IsProbabilityMeasure coinMeasure := coinMeasure_probability
  rw [finiteJoint_eq_prod B hB]
  have hset : {ω : Fin 17 × Bool | fc (B.atom ω.1)} =
      {i : Fin 17 | fc (B.atom i)} ×ˢ (Set.univ : Set Bool) := by
    ext ω
    rcases ω with ⟨i, z⟩
    simp
  rw [hset]
  change ENNReal.toReal ((latentMeasure B).prod coinMeasure
    ({i : Fin 17 | fc (B.atom i)} ×ˢ (Set.univ : Set Bool))) = _
  rw [Measure.prod_prod, measure_univ, mul_one]
  exact latentComplierMass B hB

lemma stratum_first_stage (B : BinaryLaw) (hB : finiteValid B) (i : Fin 17) :
    realBit (treatment (stratumOf (B.atom i)) true) -
      realBit (treatment (stratumOf (B.atom i)) false) =
        if fc (B.atom i) then 1 else 0 := by
  rcases B.atom i with ⟨d0, d1, y0, y1, r0, r1⟩
  have hmono := hB.2.2.1 i
  cases d0 <;> cases d1 <;>
    simp [stratumOf, treatment, realBit, bit, fc] at hmono ⊢ <;> norm_num at hmono ⊢

theorem realize (B : BinaryLaw) (hB : finiteValid B) :
    ∃ (M : CausalModel (Fin 17 × Bool)) (T : Response (Fin 17 × Bool)), wholeRealizes B M T := by
  let μ := wholeFiniteMeasure B
  let ν := latentMeasure B
  let ξ := coinMeasure
  have hν : IsProbabilityMeasure ν := latentMeasure_probability B hB
  have hξ : IsProbabilityMeasure ξ := coinMeasure_probability
  have hprod : μ = ν.prod ξ := finiteJoint_eq_prod B hB
  letI : IsProbabilityMeasure ν := hν
  letI : IsProbabilityMeasure ξ := hξ
  letI : IsProbabilityMeasure μ := hprod ▸ (show IsProbabilityMeasure (ν.prod ξ) from inferInstance)
  let M : CausalModel (Fin 17 × Bool) := {
    μ := μ
    probability := hprod ▸ (show IsProbabilityMeasure (ν.prod ξ) from inferInstance)
    S := fun ω => stratumOf (B.atom ω.1)
    Y := fun d ω => (bit (if d then (B.atom ω.1).y1 else (B.atom ω.1).y0) : ℝ)
    Z := Prod.snd
    measurableS := Measurable.of_discrete
    measurableY := fun _ => Measurable.of_discrete
    integrableY := fun _ => Integrable.of_finite
    measurableZ := measurable_snd
    randomAssignment := by
      rw [hprod]
      simpa [latentVector, stratumOf] using
        (indepFun_prod (μ := ν) (ν := ξ)
          (X := latentVector B) (Y := id)
          (Measurable.of_discrete : Measurable (latentVector B)) measurable_id)
    armPositive := by
      intro z
      have hset : {ω : Fin 17 × Bool | ω.2 = z} =
          (Set.univ : Set (Fin 17)) ×ˢ ({z} : Set Bool) := by
        ext ω
        rcases ω with ⟨i, w⟩
        simp
      rw [hprod, hset]
      change 0 < ENNReal.toReal ((ν.prod ξ) (Set.univ ×ˢ ({z} : Set Bool)))
      rw [Measure.prod_prod, measure_univ, one_mul]
      have hsimp : ξ {z} = ENNReal.ofReal (assignmentMass z : ℝ) :=
        coinMeasure_singleton_measure z
      have hreal : 0 < (assignmentMass z : ℝ) := by exact_mod_cast coinMass_pos z
      change 0 < (ξ {z}).toReal
      rw [hsimp, ENNReal.toReal_ofReal (le_of_lt hreal)]
      exact hreal
    nonzeroFirstStage := by
      have hmain :
          (∫ ω : Fin 17 × Bool,
            realBit (treatment (stratumOf (B.atom ω.1)) true) -
              realBit (treatment (stratumOf (B.atom ω.1)) false) ∂μ) = (fpc B : ℝ) := by
        calc
          _ = ∫ ω : Fin 17 × Bool,
              ({ω | fc (B.atom ω.1)} : Set (Fin 17 × Bool)).indicator (fun _ => (1 : ℝ)) ω ∂μ := by
                apply integral_congr_ae
                filter_upwards with ω
                rw [Set.indicator_apply]
                by_cases hc : fc (B.atom ω.1)
                · simp [hc, stratum_first_stage B hB ω.1]
                · simp [hc, stratum_first_stage B hB ω.1]
          _ = μ.real {ω | fc (B.atom ω.1)} :=
                integral_indicator_one (MeasurableSet.of_discrete)
          _ = (fpc B : ℝ) := by simpa [μ] using complierMass B hB
      rw [hmain]
      exact ne_of_gt (by exact_mod_cast hB.2.2.2.2)
  }
  let T : Response (Fin 17 × Bool) := {
    R := fun ω => fr (B.atom ω.1) ω.2
    measurableR := Measurable.of_discrete
  }
  refine ⟨M, T, ?_⟩
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  rfl

end
end SAP.P028.WH.W1.P.T2_L2

theorem SAP.P028.WH.W1.T2_L2_proof : SAP.P028.WH.W1.T2_L2 := by
  intro B hB
  exact SAP.P028.WH.W1.P.T2_L2.realize B hB
