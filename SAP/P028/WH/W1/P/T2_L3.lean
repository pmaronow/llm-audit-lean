import SAP.P028.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P028.WH.W1.P.T2_L3

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge
noncomputable section
open Classical

lemma integral_wholeFiniteMeasure (B : BinaryLaw)
    (hB : ∀ i z, 0 ≤ (jointMass B i z : ℝ)) (f : Fin 17 × Bool → ℝ) :
    (∫ x, f x ∂wholeFiniteMeasure B) =
      ∑ i, ∑ z, (jointMass B i z : ℝ) * f (i,z) := by
  classical
  unfold wholeFiniteMeasure
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    rw [integral_finsetSum_measure]
    · refine Finset.sum_congr rfl ?_
      intro z hz
      rw [integral_smul_measure, integral_dirac, smul_eq_mul,
        ENNReal.toReal_ofReal (hB i z)]
    · intro z hz
      exact (integrable_dirac (by simp)).smul_measure (by simp)
  · intro i hi
    apply integrable_finsetSum_measure.mpr
    intro z hz
    exact (integrable_dirac (by simp)).smul_measure (by simp)

lemma joint_nonneg (B : BinaryLaw) (h : ∀ i, 0 < B.mass i) (i : Fin 17) (z : Bool) :
    0 ≤ (jointMass B i z : ℝ) := by
  have hp : 0 < assignmentMass z := by cases z <;> norm_num [assignmentMass]
  exact_mod_cast (mul_pos (h i) hp).le

lemma sum_joint_weighted (B : BinaryLaw) (E : Fin 17 → Prop) (f : Fin 17 → ℚ) :
    (∑ i, ∑ z, if E i then jointMass B i z * f i else 0) =
      ∑ i, if E i then B.mass i * f i else 0 := by
  classical
  rw [Finset.sum_comm]
  unfold jointMass
  calc
    (∑ z, ∑ i, if E i then (B.mass i * assignmentMass z) * f i else 0) =
        ∑ z, (∑ i, if E i then B.mass i * f i else 0) * assignmentMass z := by
      apply Finset.sum_congr rfl
      intro z hz
      calc
        (∑ i, if E i then (B.mass i * assignmentMass z) * f i else 0) =
            ∑ i, (if E i then B.mass i * f i else 0) * assignmentMass z := by
          apply Finset.sum_congr rfl
          intro i hi
          split_ifs <;> ring
        _ = _ := by rw [Finset.sum_mul]
    _ = (∑ i, if E i then B.mass i * f i else 0) * ∑ z, assignmentMass z := by
      rw [Finset.mul_sum]
    _ = _ := by norm_num [Fintype.sum_bool, assignmentMass]

lemma sum_joint_event (B : BinaryLaw) (E : Fin 17 → Prop) :
    (∑ i, ∑ z, if E i then jointMass B i z else 0) = fprob B E := by
  simpa [fprob] using sum_joint_weighted B E (fun _ => 1)

lemma ratCastIfZero (P : Prop) [Decidable P] (q : ℚ) :
    ((if P then q else 0 : ℚ) : ℝ) = if P then (q : ℝ) else 0 := by
  by_cases h : P <;> simp [h]

lemma sum_joint_arm_weighted (B : BinaryLaw) (z : Bool) (E : Fin 17 → Prop)
    [DecidablePred E] (f : Fin 17 → ℚ) :
    (∑ i, ∑ z', if z' = z ∧ E i then jointMass B i z' * f i else 0) =
      (∑ i, if E i then B.mass i * f i else 0) * assignmentMass z := by
  classical
  calc
    (∑ i, ∑ z', if z' = z ∧ E i then jointMass B i z' * f i else 0) =
        ∑ i, if E i then jointMass B i z * f i else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      cases z <;> simp
    _ = (∑ i, if E i then B.mass i * f i else 0) * assignmentMass z := by
      calc
        (∑ i, if E i then jointMass B i z * f i else 0) =
            ∑ i, (if E i then B.mass i * f i else 0) * assignmentMass z := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [jointMass]
          split_ifs <;> ring
        _ = _ := by rw [Finset.sum_mul]

lemma real_sum_joint_arm_weighted (B : BinaryLaw) (z : Bool) (E : Fin 17 → Prop)
    [DecidablePred E] (f : Fin 17 → ℚ) :
    (∑ i, ∑ z', if z' = z ∧ E i then
        (jointMass B i z' : ℝ) * (f i : ℝ) else 0) =
      (((∑ i, if E i then B.mass i * f i else 0 : ℚ) : ℝ) *
        (assignmentMass z : ℝ)) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_joint_arm_weighted B z E f)
  simpa only [Rat.cast_sum, ratCastIfZero, Rat.cast_mul] using h

lemma real_sum_joint_arm_event (B : BinaryLaw) (z : Bool) (E : Fin 17 → Prop) :
    (∑ i, ∑ z', if z' = z ∧ E i then (jointMass B i z' : ℝ) else 0) =
      (fprob B E : ℝ) * (assignmentMass z : ℝ) := by
  simpa [fprob] using real_sum_joint_arm_weighted B z E (fun _ => 1)

lemma real_sum_cond_mul (E : Fin 17 → Prop) [DecidablePred E]
    (f : Fin 17 → ℚ) (c : ℚ) :
    (∑ i, if E i then (f i : ℝ) * (c : ℝ) else 0) =
      ((∑ i, if E i then f i else 0 : ℚ) : ℝ) * (c : ℝ) := by
  have hq : (∑ i, if E i then f i * c else 0) =
      (∑ i, if E i then f i else 0) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> ring
  have h := congrArg (fun q : ℚ => (q : ℝ)) hq
  simpa only [Rat.cast_sum, ratCastIfZero, Rat.cast_mul] using h

lemma finite_assignment_independent (B : BinaryLaw) (E : Fin 17 → Prop)
    [DecidablePred E] (z : Bool) :
    (∑ i, if E i then jointMass B i z else 0) = fprob B E * assignmentMass z := by
  unfold jointMass fprob
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

lemma real_mass_wholeFiniteMeasure (B : BinaryLaw)
    (hB : ∀ i z, 0 ≤ (jointMass B i z : ℝ)) (E : Set (Fin 17 × Bool))
    (hE : MeasurableSet E) :
    (wholeFiniteMeasure B).real E =
      ∑ i, ∑ z, if (i,z) ∈ E then (jointMass B i z : ℝ) else 0 := by
  calc
    (wholeFiniteMeasure B).real E =
        ∫ x, E.indicator (fun _ : Fin 17 × Bool => (1 : ℝ)) x ∂wholeFiniteMeasure B :=
      (integral_indicator_one hE).symm
    _ = ∑ i, ∑ z, (jointMass B i z : ℝ) *
        E.indicator (fun _ : Fin 17 × Bool => (1 : ℝ)) (i,z) :=
      integral_wholeFiniteMeasure B hB _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hx : (i,z) ∈ E <;> simp [Set.indicator, hx]

lemma setIntegral_wholeFiniteMeasure (B : BinaryLaw)
    (hB : ∀ i z, 0 ≤ (jointMass B i z : ℝ)) (E : Set (Fin 17 × Bool))
    (hE : MeasurableSet E) (f : Fin 17 × Bool → ℝ) :
    (∫ x in E, f x ∂wholeFiniteMeasure B) =
      ∑ i, ∑ z, if (i,z) ∈ E then (jointMass B i z : ℝ) * f (i,z) else 0 := by
  rw [← integral_indicator hE]
  rw [integral_wholeFiniteMeasure B hB]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hx : (i,z) ∈ E <;> simp [Set.indicator, hx]

lemma real_sum_joint_event (B : BinaryLaw) (E : Fin 17 → Prop) :
    (∑ i, ∑ z, if E i then (jointMass B i z : ℝ) else 0) = (fprob B E : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_joint_event B E)
  simpa only [Rat.cast_sum, ratCastIfZero] using h

lemma real_sum_joint_weighted (B : BinaryLaw) (E : Fin 17 → Prop) (f : Fin 17 → ℚ) :
    (∑ i, ∑ z, if E i then (jointMass B i z : ℝ) * (f i : ℝ) else 0) =
      ((∑ i, if E i then B.mass i * f i else 0 : ℚ) : ℝ) := by
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_joint_weighted B E f)
  simpa only [Rat.cast_sum, ratCastIfZero, Rat.cast_mul] using h

lemma sum_joint_arm (B : BinaryLaw) (hTotal : (∑ i, B.mass i) = 1) (z : Bool) :
    (∑ i, ∑ z', if z' = z then jointMass B i z' else 0) = assignmentMass z := by
  calc
    (∑ i, ∑ z', if z' = z then jointMass B i z' else 0) =
        ∑ i, jointMass B i z := by
      apply Finset.sum_congr rfl
      intro i hi
      cases z <;> simp [Fintype.sum_bool]
    _ = fprob B (fun _ => True) * assignmentMass z := by
      simpa using finite_assignment_independent B (fun _ => True) z
    _ = assignmentMass z := by simp [fprob, hTotal]

lemma real_arm_mass (B : BinaryLaw) (hTotal : (∑ i, B.mass i) = 1)
    (hB : ∀ i z, 0 ≤ (jointMass B i z : ℝ)) (z : Bool) :
    (wholeFiniteMeasure B).real {x | x.2 = z} = (assignmentMass z : ℝ) := by
  rw [real_mass_wholeFiniteMeasure B hB _
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  simp only [Set.mem_setOf_eq]
  have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_joint_arm B hTotal z)
  simpa only [Rat.cast_sum, ratCastIfZero, Rat.cast_mul] using h

lemma treatment_code (a : BinaryAtom) (hmono : bit a.d0 ≤ bit a.d1) (z : Bool) :
    treatment (if a.d0 then 0 else if a.d1 then 2 else 1) z = fd a z := by
  have hnot : ¬ (a.d0 = true ∧ a.d1 = false) := by
    intro hbad
    rw [hbad.1, hbad.2, bit] at hmono
    norm_num [bit] at hmono
  by_cases h0 : a.d0 = true
  · by_cases h1 : a.d1 = true
    · cases z <;> simp [treatment, fd, h0, h1]
    · have : False := hnot ⟨h0, Bool.eq_false_iff.mpr h1⟩
      exact this.elim
  · by_cases h1 : a.d1 = true
    · cases z <;> simp [treatment, fd, h0, h1]
    · cases z <;> simp [treatment, fd, h0, h1]

lemma code_complier (a : BinaryAtom) :
    (if a.d0 then (0 : Fin 3) else if a.d1 then 2 else 1) = 2 ↔ fc a := by
  cases h0 : a.d0 <;> cases h1 : a.d1 <;> simp [fc, h0, h1]

lemma assignmentMass_pos (z : Bool) : 0 < (assignmentMass z : ℝ) := by
  cases z <;> norm_num [assignmentMass]

def binaryObservationCode (B : BinaryLaw) (x : Fin 17 × Bool) : Bool × Bool × Bool × Bool :=
  (x.2, fd (B.atom x.1) x.2, fr (B.atom x.1) x.2,
    fr (B.atom x.1) x.2 && fy (B.atom x.1) x.2)

def binaryObservationValue (o : Bool × Bool × Bool × Bool) :
    Bool × Bool × Bool × ℝ :=
  (o.1, o.2.1, o.2.2.1, (bit o.2.2.2 : ℝ))

lemma wholeFiniteObservation_code (B : BinaryLaw) (x : Fin 17 × Bool) :
    wholeFiniteObservation B x = binaryObservationValue (binaryObservationCode B x) := by
  rcases x with ⟨i,z⟩
  cases hr : fr (B.atom i) z <;> cases hy : fy (B.atom i) z <;>
    simp [wholeFiniteObservation, binaryObservationCode, binaryObservationValue, hr, hy, bit]

lemma sum_binaryObservationCode (B : BinaryLaw) (o : Bool × Bool × Bool × Bool) :
    (∑ x : Fin 17 × Bool,
      if binaryObservationCode B x = o then jointMass B x.1 x.2 else 0) = observedLaw B o := by
  classical
  rcases o with ⟨z,d,r,v⟩
  rw [Fintype.sum_prod_type]
  have hsum :
      (∑ i, ∑ z', if binaryObservationCode B (i,z') = (z,d,r,v)
        then jointMass B i z' else 0) =
        ∑ i, if fd (B.atom i) z = d ∧ fr (B.atom i) z = r ∧
            (fr (B.atom i) z && fy (B.atom i) z) = v
          then jointMass B i z else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    cases z <;> simp [binaryObservationCode, Fintype.sum_bool]
  rw [hsum]
  unfold observedLaw
  calc
    (∑ i, if fd (B.atom i) z = d ∧ fr (B.atom i) z = r ∧
        (fr (B.atom i) z && fy (B.atom i) z) = v
      then jointMass B i z else 0) =
        fprob B (fun i => fd (B.atom i) z = d ∧ fr (B.atom i) z = r ∧
          (fr (B.atom i) z && fy (B.atom i) z) = v) * assignmentMass z :=
      finite_assignment_independent B _ z
    _ = assignmentMass z * fprob B (fun i => fd (B.atom i) z = d ∧
        fr (B.atom i) z = r ∧ (fr (B.atom i) z && fy (B.atom i) z) = v) := by ring

lemma map_fintype_sum {α β ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Fintype ι] (f : α → β) (hf : Measurable f) (μ : ι → Measure α) :
    (∑ i, μ i).map f = ∑ i, (μ i).map f := by
  classical
  have hsum (s : Finset ι) :
      (∑ i ∈ s, μ i).map f = ∑ i ∈ s, (μ i).map f := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.map_add _ _ hf, ih]
  simpa using hsum Finset.univ

lemma sum_pair_type {α β γ : Type*} [Fintype α] [Fintype β] [AddCommMonoid γ]
    (f : α × β → γ) : (∑ a, ∑ b, f (a,b)) = ∑ x, f x := by
  symm
  exact Fintype.sum_prod_type f

end
end SAP.P028.WH.W1.P.T2_L3

open SAP.P028.WH.W1.P.T2_L3
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open SAP.P028 SAP.P028.Bridge

theorem SAP.P028.WH.W1.T2_L3_proof : SAP.P028.WH.W1.T2_L3 := by
  classical
  intro B M T hvalid hrealizes
  rcases hrealizes with ⟨hμ, hS, hY, hZ, hR⟩
  have htotal : (∑ i, B.mass i) = 1 := hvalid.2.1
  have hjoint : ∀ i z, 0 ≤ (jointMass B i z : ℝ) := joint_nonneg B hvalid.1
  have hmono : ∀ i, bit (B.atom i).d0 ≤ bit (B.atom i).d1 := hvalid.2.2.1
  have hcomp : complierEvent M = {x | fc (B.atom x.1)} := by
    ext ⟨i,z⟩
    change M.S (i,z) = 2 ↔ fc (B.atom i)
    rw [hS]
    simpa using code_complier (B.atom i)
  have hD (i : Fin 17) (z : Bool) : observedD M (i,z) = fd (B.atom i) z := by
    unfold observedD
    rw [hS, hZ]
    exact treatment_code (B.atom i) (hmono i) z
  have hYobs (i : Fin 17) (z : Bool) :
      observedY M (i,z) = (bit (fy (B.atom i) z) : ℝ) := by
    unfold observedY
    rw [hD i z, hY]
    simp [fy]
  have hRobs (i : Fin 17) (z : Bool) : T.R (i,z) = fr (B.atom i) z := by
    rw [hR]
  have hDpair : observedD M = fun x => fd (B.atom x.1) x.2 := by
    funext x
    rcases x with ⟨i,z⟩
    exact hD i z
  have hYpair : observedY M = fun x => (bit (fy (B.atom x.1) x.2) : ℝ) := by
    funext x
    rcases x with ⟨i,z⟩
    exact hYobs i z
  have hRpair : T.R = fun x => fr (B.atom x.1) x.2 := by
    funext x
    rcases x with ⟨i,z⟩
    exact hRobs i z
  have harm (z : Bool) : armEvent M z = {x | x.2 = z} := by
    ext ⟨i,z'⟩
    simp [armEvent, hZ]
  have hpc : complierProbability M = (fpc B : ℝ) := by
    unfold complierProbability
    rw [hμ, hcomp]
    rw [real_mass_wholeFiniteMeasure B hjoint _ MeasurableSet.of_discrete]
    simp only [Set.mem_setOf_eq]
    simpa [fpc] using real_sum_joint_event B (fun i => fc (B.atom i))
  have hdenC : (wholeFiniteMeasure B).real {x | fc (B.atom x.1)} = (fpc B : ℝ) := by
    have h := hpc
    unfold complierProbability at h
    rw [hμ, hcomp] at h
    exact h
  have hbitbounds (b : Bool) :
      0 ≤ (bit b : ℝ) ∧ (bit b : ℝ) ≤ 1 := by
    cases b <;> norm_num [bit]
  have hbounded : boundedOutcomes M := by
    intro d ⟨i,z⟩
    rw [hY]
    exact hbitbounds _
  refine ⟨hbounded, hpc, ?_, ?_, ?_⟩
  · intro d
    unfold complierMean eventMean
    rw [hμ, hY, hcomp]
    have hnum :
        (∫ x in {x | fc (B.atom x.1)},
          (bit (if d then (B.atom x.1).y1 else (B.atom x.1).y0) : ℝ)
          ∂wholeFiniteMeasure B) =
          ((∑ i, if fc (B.atom i) then B.mass i *
            bit (if d then (B.atom i).y1 else (B.atom i).y0) else 0 : ℚ) : ℝ) := by
      rw [setIntegral_wholeFiniteMeasure B hjoint _ MeasurableSet.of_discrete]
      simp only [Set.mem_setOf_eq]
      simpa [fc] using real_sum_joint_weighted B (fun i => fc (B.atom i))
        (fun i => bit (if d then (B.atom i).y1 else (B.atom i).y0))
    rw [hnum, hdenC]
    simp [fcy, fmean, fprob, fpc]
  · intro d z
    have hcell :
        (∑ i, if fr (B.atom i) z = true ∧ fd (B.atom i) z = d then
          B.mass i * bit (fy (B.atom i) z) else 0) = recordedCell B z d true := by
      unfold recordedCell fprob
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hd : fd (B.atom i) z = d
      · by_cases hr : fr (B.atom i) z = true
        · by_cases hy : fy (B.atom i) z = true <;> simp [hd, hr, hy, bit]
        · simp [hd, hr, bit]
      · simp [hd, bit]
    have hnumR :
        (∫ x in {x | x.2 = z},
          realBit (fr (B.atom x.1) x.2) *
            (if fd (B.atom x.1) x.2 = d then
              (bit (fy (B.atom x.1) x.2) : ℝ) else 0)
          ∂wholeFiniteMeasure B) =
          (recordedCell B z d true : ℝ) * (assignmentMass z : ℝ) := by
      rw [setIntegral_wholeFiniteMeasure B hjoint _ MeasurableSet.of_discrete]
      simp only [Set.mem_ofPred_eq]
      have heq :
          (∑ i, ∑ z', if z' = z then
            (jointMass B i z' : ℝ) *
              (realBit (fr (B.atom i) z') *
                (if fd (B.atom i) z' = d then
                  (bit (fy (B.atom i) z') : ℝ) else 0)) else 0) =
          (∑ i, ∑ z', if z' = z ∧
              (fr (B.atom i) z = true ∧ fd (B.atom i) z = d) then
            (jointMass B i z' : ℝ) * (bit (fy (B.atom i) z) : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro z' hz'
        by_cases hzz : z' = z
        · subst z'
          by_cases hr : fr (B.atom i) z = true <;>
            by_cases hd : fd (B.atom i) z = d <;> simp [realBit, hr, hd]
        · simp [hzz]
      rw [heq]
      calc
        (∑ i, ∑ z', if z' = z ∧
            (fr (B.atom i) z = true ∧ fd (B.atom i) z = d) then
          (jointMass B i z' : ℝ) * (bit (fy (B.atom i) z) : ℝ) else 0) =
            ((∑ i, if fr (B.atom i) z = true ∧ fd (B.atom i) z = d then
              B.mass i * bit (fy (B.atom i) z) else 0 : ℚ) : ℝ) *
              (assignmentMass z : ℝ) := by
          simpa only [and_assoc] using real_sum_joint_arm_weighted B z
            (fun i => fr (B.atom i) z = true ∧ fd (B.atom i) z = d)
            (fun i => bit (fy (B.atom i) z))
        _ = _ := by
          exact congrArg (fun q : ℚ => (q : ℝ) * (assignmentMass z : ℝ)) hcell
    have hnumMiss :
        (wholeFiniteMeasure B).real
          {x | fr (B.atom x.1) x.2 = false ∧ fd (B.atom x.1) x.2 = d ∧ x.2 = z} =
          (missingCell B z d : ℝ) * (assignmentMass z : ℝ) := by
      rw [real_mass_wholeFiniteMeasure B hjoint _ MeasurableSet.of_discrete]
      simp only [Set.mem_ofPred_eq]
      cases z with
      | false =>
        let E : Fin 17 → Prop := fun i =>
          fd (B.atom i) false = d ∧ fr (B.atom i) false = false
        letI : DecidablePred E := fun i => Classical.propDecidable (E i)
        simpa [E, Fintype.sum_bool, jointMass, assignmentMass, missingCell, fprob,
          and_comm, and_left_comm, and_assoc] using
          real_sum_cond_mul E (fun i => B.mass i) (assignmentMass false)
      | true =>
        let E : Fin 17 → Prop := fun i =>
          fd (B.atom i) true = d ∧ fr (B.atom i) true = false
        letI : DecidablePred E := fun i => Classical.propDecidable (E i)
        simpa [E, Fintype.sum_bool, jointMass, assignmentMass, missingCell, fprob,
          and_comm, and_left_comm, and_assoc] using
          real_sum_cond_mul E (fun i => B.mass i) (assignmentMass true)
    constructor
    · unfold recordedOutcomeMoment eventMean
      rw [hμ, hRpair, hDpair, hYpair, harm z, hnumR,
        real_arm_mass B htotal hjoint z]
      field_simp [ne_of_gt (assignmentMass_pos z)] <;> ring
    · unfold missingOutcomeProbability
      rw [hμ, hRpair, hDpair, hZ, harm z, hnumMiss,
        real_arm_mass B htotal hjoint z]
      field_simp [ne_of_gt (assignmentMass_pos z)] <;> ring
  ·
    have hObsAtom (i : Fin 17) (z : Bool) :
        wholeObservation M T (i,z) = wholeFiniteObservation B (i,z) := by
      cases hr : fr (B.atom i) z <;> cases hy : fy (B.atom i) z <;>
        simp [wholeObservation, wholeFiniteObservation, hZ, hDpair, hYpair, hRpair,
          hr, hy, realBit, bit]
    have hmap : wholeObservedLaw M T =
        ∑ i, ∑ z, ENNReal.ofReal (jointMass B i z : ℝ) •
          Measure.dirac (wholeFiniteObservation B (i,z)) := by
      unfold wholeObservedLaw
      rw [hμ]
      unfold wholeFiniteMeasure
      rw [map_fintype_sum (wholeObservation M T) (by fun_prop)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_fintype_sum (wholeObservation M T) (by fun_prop)]
      apply Finset.sum_congr rfl
      intro z hz
      rw [Measure.map_smul _ (by fun_prop), Measure.map_dirac' (by fun_prop), hObsAtom]
    have hobsReal (o : Bool × Bool × Bool × Bool) :
        (∑ x : Fin 17 × Bool,
          if binaryObservationCode B x = o then (jointMass B x.1 x.2 : ℝ) else 0) =
          (observedLaw B o : ℝ) := by
      have h := congrArg (fun q : ℚ => (q : ℝ)) (sum_binaryObservationCode B o)
      simpa only [Rat.cast_sum, ratCastIfZero] using h
    have hweight (o : Bool × Bool × Bool × Bool) :
        (∑ x ∈ Finset.univ.filter (fun x : Fin 17 × Bool =>
          binaryObservationCode B x = o),
          ENNReal.ofReal (jointMass B x.1 x.2 : ℝ)) =
          ENNReal.ofReal (observedLaw B o : ℝ) := by
      calc
        (∑ x ∈ Finset.univ.filter (fun x : Fin 17 × Bool =>
            binaryObservationCode B x = o),
            ENNReal.ofReal (jointMass B x.1 x.2 : ℝ)) =
          ∑ x : Fin 17 × Bool, ENNReal.ofReal
            (if binaryObservationCode B x = o then
              (jointMass B x.1 x.2 : ℝ) else 0) := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hcode : binaryObservationCode B x = o <;> simp [hcode]
        _ = ENNReal.ofReal (∑ x : Fin 17 × Bool,
            if binaryObservationCode B x = o then
              (jointMass B x.1 x.2 : ℝ) else 0) := by
            symm
            exact ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
              (f := fun x => if binaryObservationCode B x = o then
                (jointMass B x.1 x.2 : ℝ) else 0) (by
                  intro x hx
                  split_ifs
                  · exact hjoint x.1 x.2
                  · exact le_rfl)
        _ = ENNReal.ofReal (observedLaw B o : ℝ) := by rw [hobsReal o]
    have hagg :
        (∑ i, ∑ z, ENNReal.ofReal (jointMass B i z : ℝ) •
          Measure.dirac (wholeFiniteObservation B (i,z))) = wholeFiniteObservedLaw B := by
      classical
      calc
        (∑ i, ∑ z, ENNReal.ofReal (jointMass B i z : ℝ) •
            Measure.dirac (wholeFiniteObservation B (i,z))) =
          ∑ x : Fin 17 × Bool, ENNReal.ofReal (jointMass B x.1 x.2 : ℝ) •
            Measure.dirac (wholeFiniteObservation B x) := by
          exact sum_pair_type (fun x : Fin 17 × Bool =>
            ENNReal.ofReal (jointMass B x.1 x.2 : ℝ) •
              Measure.dirac (wholeFiniteObservation B x))
        _ = ∑ x : Fin 17 × Bool, ENNReal.ofReal (jointMass B x.1 x.2 : ℝ) •
            Measure.dirac (binaryObservationValue (binaryObservationCode B x)) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [wholeFiniteObservation_code]
        _ = ∑ o : Bool × Bool × Bool × Bool,
            ∑ x ∈ Finset.univ.filter (fun x : Fin 17 × Bool =>
              binaryObservationCode B x = o),
              ENNReal.ofReal (jointMass B x.1 x.2 : ℝ) •
                Measure.dirac (binaryObservationValue (binaryObservationCode B x)) := by
          symm
          exact Finset.sum_fiberwise_of_maps_to
            (s := Finset.univ) (t := Finset.univ)
            (g := binaryObservationCode B)
            (fun x hx => Finset.mem_univ _)
            (fun x => ENNReal.ofReal (jointMass B x.1 x.2 : ℝ) •
              Measure.dirac (binaryObservationValue (binaryObservationCode B x)))
        _ = ∑ o : Bool × Bool × Bool × Bool,
            (∑ x ∈ Finset.univ.filter (fun x : Fin 17 × Bool =>
              binaryObservationCode B x = o),
              ENNReal.ofReal (jointMass B x.1 x.2 : ℝ)) •
              Measure.dirac (binaryObservationValue o) := by
          apply Finset.sum_congr rfl
          intro o ho
          calc
            (∑ x ∈ Finset.univ.filter (fun x : Fin 17 × Bool =>
                binaryObservationCode B x = o),
                ENNReal.ofReal (jointMass B x.1 x.2 : ℝ) •
                  Measure.dirac (binaryObservationValue (binaryObservationCode B x))) =
              ∑ x ∈ Finset.univ.filter (fun x : Fin 17 × Bool =>
                binaryObservationCode B x = o),
                ENNReal.ofReal (jointMass B x.1 x.2 : ℝ) •
                  Measure.dirac (binaryObservationValue o) := by
                apply Finset.sum_congr rfl
                intro x hx
                have hxcode : binaryObservationCode B x = o := (Finset.mem_filter.mp hx).2
                rw [hxcode]
            _ = (∑ x ∈ Finset.univ.filter (fun x : Fin 17 × Bool =>
                  binaryObservationCode B x = o),
                  ENNReal.ofReal (jointMass B x.1 x.2 : ℝ)) •
                  Measure.dirac (binaryObservationValue o) := Finset.sum_smul.symm
        _ = ∑ o : Bool × Bool × Bool × Bool,
            ENNReal.ofReal (observedLaw B o : ℝ) •
              Measure.dirac (binaryObservationValue o) := by
          apply Finset.sum_congr rfl
          intro o ho
          rw [hweight o]
        _ = wholeFiniteObservedLaw B := by
          unfold wholeFiniteObservedLaw binaryObservationValue
          rfl
    exact hmap.trans hagg
