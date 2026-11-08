import SAP.P029b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P029b.WH.W1.P.T18_L1

open scoped BigOperators Classical Topology
open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

lemma mCE_bit_eq_mP_inter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (D : Ω → Bool) (hD : Measurable D) :
    mCE μ (fun ω => bit (D ω)) A = mP μ (A ∩ {ω | D ω = true}) / mP μ A := by
  have hDset : MeasurableSet {ω | D ω = true} := by
    exact (measurableSet_singleton true).preimage hD
  have hbit : (fun ω => bit (D ω)) = ({ω | D ω = true}.indicator fun _ => (1 : ℝ)) := by
    funext ω
    simp [bit, Set.indicator]
  have hi : (∫ ω in A, bit (D ω) ∂μ) = mP μ (A ∩ {ω | D ω = true}) := by
    rw [hbit, MeasureTheory.setIntegral_indicator hDset]
    simp [mP, Measure.real]
  unfold mCE
  rw [hi]

lemma mP_inter_arm_factor {Ω : Type*} {X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hind : IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1)) μ)
    (x : X) (b0 b1 z : Bool) :
    mP μ ({ω | (U ω).x = x ∧ (U ω).d0 = b0 ∧ (U ω).d1 = b1} ∩
      {ω | Z ω = z}) =
      mP μ {ω | (U ω).x = x ∧ (U ω).d0 = b0 ∧ (U ω).d1 = b1} *
        mP μ {ω | Z ω = z} := by
  let F : Ω → X × Bool × Bool := fun ω => ((U ω).x, (U ω).d0, (U ω).d1)
  let B : Set (X × Bool × Bool) := {t | t.1 = x ∧ t.2.1 = b0 ∧ t.2.2 = b1}
  have hB : MeasurableSet B := by
    change MeasurableSet ({t : X × Bool × Bool | t.1 = x} ∩
      ({t | t.2.1 = b0} ∩ {t | t.2.2 = b1}))
    apply MeasurableSet.inter
    · exact (measurableSet_singleton x).preimage measurable_fst
    · apply MeasurableSet.inter
      · exact (measurableSet_singleton b0).preimage (measurable_fst.comp measurable_snd)
      · exact (measurableSet_singleton b1).preimage (measurable_snd.comp measurable_snd)
  have hZs : MeasurableSet ({z} : Set Bool) := measurableSet_singleton z
  have hf := hind.measure_inter_preimage_eq_mul {z} B hZs hB
  have hpre : F ⁻¹' B = {ω | (U ω).x = x ∧ (U ω).d0 = b0 ∧ (U ω).d1 = b1} := by
    ext ω
    simp [F, B]
  have hzpre : Z ⁻¹' ({z} : Set Bool) = {ω | Z ω = z} := by
    ext ω
    simp
  rw [hzpre, hpre, Set.inter_comm] at hf
  simpa [mP, ENNReal.toReal_mul, mul_comm] using congrArg ENNReal.toReal hf

lemma mP_profile_arm_factor {Ω : Type*} {X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hind : IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1)) μ)
    (x : X) (z : Bool) :
    mP μ ({ω | (U ω).x = x} ∩ {ω | Z ω = z}) =
      mP μ {ω | (U ω).x = x} * mP μ {ω | Z ω = z} := by
  let F : Ω → X × Bool × Bool := fun ω => ((U ω).x, (U ω).d0, (U ω).d1)
  let B : Set (X × Bool × Bool) := {t | t.1 = x}
  have hB : MeasurableSet B := by
    dsimp [B]
    exact (measurableSet_singleton x).preimage measurable_fst
  have hZs : MeasurableSet ({z} : Set Bool) := measurableSet_singleton z
  have hf := hind.measure_inter_preimage_eq_mul {z} B hZs hB
  have hpre : F ⁻¹' B = {ω | (U ω).x = x} := by
    ext ω
    simp [F, B]
  have hzpre : Z ⁻¹' ({z} : Set Bool) = {ω | Z ω = z} := by
    ext ω
    simp
  rw [hzpre, hpre, Set.inter_comm] at hf
  simpa [mP, ENNReal.toReal_mul, mul_comm] using congrArg ENNReal.toReal hf

lemma mP_profile_d0_arm_factor {Ω : Type*} {X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hind : IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1)) μ)
    (x : X) (b : Bool) :
    mP μ ({ω | (U ω).x = x ∧ (U ω).d0 = true} ∩ {ω | Z ω = b}) =
      mP μ {ω | (U ω).x = x ∧ (U ω).d0 = true} * mP μ {ω | Z ω = b} := by
  let F : Ω → X × Bool × Bool := fun ω => ((U ω).x, (U ω).d0, (U ω).d1)
  let B : Set (X × Bool × Bool) := {t | t.1 = x ∧ t.2.1 = true}
  have hB : MeasurableSet B := by
    change MeasurableSet ({t : X × Bool × Bool | t.1 = x} ∩ {t | t.2.1 = true})
    exact MeasurableSet.inter ((measurableSet_singleton x).preimage measurable_fst)
      ((measurableSet_singleton true).preimage (measurable_fst.comp measurable_snd))
  have hZs : MeasurableSet ({b} : Set Bool) := measurableSet_singleton b
  have hf := hind.measure_inter_preimage_eq_mul {b} B hZs hB
  have hpre : F ⁻¹' B = {ω | (U ω).x = x ∧ (U ω).d0 = true} := by
    ext ω
    simp [F, B]
  have hzpre : Z ⁻¹' ({b} : Set Bool) = {ω | Z ω = b} := by
    ext ω
    simp
  rw [hzpre, hpre, Set.inter_comm] at hf
  simpa [mP, ENNReal.toReal_mul, mul_comm] using congrArg ENNReal.toReal hf

lemma mP_profile_d1_arm_factor {Ω : Type*} {X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSingletonClass X]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → PotentialUnit X) (Z : Ω → Bool)
    (hind : IndepFun Z (fun ω => ((U ω).x, (U ω).d0, (U ω).d1)) μ)
    (x : X) (b : Bool) :
    mP μ ({ω | (U ω).x = x ∧ (U ω).d1 = true} ∩ {ω | Z ω = b}) =
      mP μ {ω | (U ω).x = x ∧ (U ω).d1 = true} * mP μ {ω | Z ω = b} := by
  let F : Ω → X × Bool × Bool := fun ω => ((U ω).x, (U ω).d0, (U ω).d1)
  let B : Set (X × Bool × Bool) := {t | t.1 = x ∧ t.2.2 = true}
  have hB : MeasurableSet B := by
    change MeasurableSet ({t : X × Bool × Bool | t.1 = x} ∩ {t | t.2.2 = true})
    exact MeasurableSet.inter ((measurableSet_singleton x).preimage measurable_fst)
      ((measurableSet_singleton true).preimage (measurable_snd.comp measurable_snd))
  have hZs : MeasurableSet ({b} : Set Bool) := measurableSet_singleton b
  have hf := hind.measure_inter_preimage_eq_mul {b} B hZs hB
  have hpre : F ⁻¹' B = {ω | (U ω).x = x ∧ (U ω).d1 = true} := by
    ext ω
    simp [F, B]
  have hzpre : Z ⁻¹' ({b} : Set Bool) = {ω | Z ω = b} := by
    ext ω
    simp
  rw [hzpre, hpre, Set.inter_comm] at hf
  simpa [mP, ENNReal.toReal_mul, mul_comm] using congrArg ENNReal.toReal hf

end

end SAP.P029b.WH.W1.P.T18_L1

open SAP.P029b.WH.W1.P.T18_L1

theorem SAP.P029b.WH.W1.T18_L1_proof : SAP.P029b.WH.W1.T18_L1 := by
  classical
  intro Ω X _ _ _ μ hμ U Z hcond x hxpos
  rcases hcond with ⟨hx, hd0, hd1, hZ, hdef, hind, hzpos, hzlt⟩
  let P : Set Ω := {ω | (U ω).x = x}
  let D0 : Set Ω := {ω | (U ω).d0 = true}
  let D1 : Set Ω := {ω | (U ω).d1 = true}
  let C : Set Ω := {ω | (U ω).complier}
  let R : Ω → Bool := fun ω => (U ω).receipt (Z ω)
  have hP : MeasurableSet P := by
    dsimp [P]
    exact (measurableSet_singleton x).preimage hx
  have hD0 : MeasurableSet D0 := by
    dsimp [D0]
    exact (measurableSet_singleton true).preimage hd0
  have hD1 : MeasurableSet D1 := by
    dsimp [D1]
    exact (measurableSet_singleton true).preimage hd1
  have hC : MeasurableSet C := by
    dsimp [C, PotentialUnit.complier]
    exact (measurableSet_singleton false).preimage hd0 |>.inter
      ((measurableSet_singleton true).preimage hd1)
  have hR : Measurable R := by
    dsimp [R]
    simp only [PotentialUnit.receipt]
    exact Measurable.ite ((measurableSet_singleton true).preimage hZ) hd1 hd0
  have hnotdef : ∀ᵐ ω ∂μ, ¬ (U ω).defier :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hdef
  have hpartAE : P ∩ D1 =ᵐ[μ] (P ∩ D0) ∪ (P ∩ C) := by
    filter_upwards [hnotdef] with ω hω
    change (ω ∈ P ∩ D1) = (ω ∈ (P ∩ D0) ∪ (P ∩ C))
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_setOf_eq, P, D0, D1, C]
    have htypes := (SAP.P029b.Bridge.compliance_type_partition (U ω) hω).2
    apply propext
    constructor
    · rintro ⟨hp, hd1ω⟩
      rcases htypes.mpr hd1ω with hc | hd0ω
      · exact Or.inr ⟨hp, hc⟩
      · exact Or.inl ⟨hp, hd0ω⟩
    · rintro (⟨hp, hd0ω⟩ | ⟨hp, hc⟩)
      · exact ⟨hp, htypes.mp (Or.inr hd0ω)⟩
      · exact ⟨hp, htypes.mp (Or.inl hc)⟩
  have hdis : Disjoint (P ∩ D0) (P ∩ C) := by
    refine Set.disjoint_left.mpr ?_
    intro ω h0 hc
    have hd0ω : (U ω).d0 = true := h0.2
    have hfalse : (U ω).d0 = false := hc.2.1
    exact Bool.noConfusion (hfalse.symm.trans hd0ω)
  have hpartition : mP μ (P ∩ D1) = mP μ (P ∩ D0) + mP μ (P ∩ C) := by
    change μ.real (P ∩ D1) = μ.real (P ∩ D0) + μ.real (P ∩ C)
    rw [MeasureTheory.measureReal_congr hpartAE,
      MeasureTheory.measureReal_union hdis (hP.inter hC) (by finiteness) (by finiteness)]
  have hcompBool : Measurable fun ω => if (U ω).complier then true else false := by
    exact Measurable.ite hC measurable_const measurable_const
  have hcompmean :
      mCE μ (fun ω => bit (if (U ω).complier then true else false)) P =
        mP μ (P ∩ C) / mP μ P := by
    have hset :
        {ω | (if (U ω).complier then true else false) = true} = C := by
      ext ω
      by_cases hc : (U ω).complier <;> simp [hc, C]
    rw [mCE_bit_eq_mP_inter μ P
      (fun ω => if (U ω).complier then true else false) hcompBool, hset]
  have hidentity :
      mCE μ (fun ω => bit ((U ω).d1)) P =
        mCE μ (fun ω => bit ((U ω).d0)) P + scoreAt μ U x := by
    rw [mCE_bit_eq_mP_inter μ P (fun ω => (U ω).d1) hd1,
      mCE_bit_eq_mP_inter μ P (fun ω => (U ω).d0) hd0]
    have hcompSet : {ω | (U ω).complier ∧ (U ω).x = x} = P ∩ C := by
      ext ω
      simp [P, C, Set.inter_comm]
    unfold scoreAt
    rw [hcompSet]
    rw [hpartition]
    have hpne : mP μ P ≠ 0 := ne_of_gt hxpos
    field_simp [hpne]
    ring
  have hqcompl : {ω | Z ω = false} = ({ω | Z ω = true})ᶜ := by
    ext ω
    cases Z ω <;> simp
  have hqsum : mP μ {ω | Z ω = true} + mP μ {ω | Z ω = false} = 1 := by
    rw [hqcompl]
    have ht : MeasurableSet {ω | Z ω = true} :=
      (measurableSet_singleton true).preimage hZ
    change μ.real {ω | Z ω = true} + μ.real ({ω | Z ω = true}ᶜ) = 1
    rw [MeasureTheory.measureReal_add_measureReal_compl ht]
    simp [mP]
  have hqfalse_pos : 0 < mP μ {ω | Z ω = false} := by
    linarith
  have hdenT :
      mP μ (P ∩ {ω | Z ω = true}) =
        mP μ P * mP μ {ω | Z ω = true} := by
    simpa [P] using mP_profile_arm_factor μ U Z hind x true
  have hdenF :
      mP μ (P ∩ {ω | Z ω = false}) =
        mP μ P * mP μ {ω | Z ω = false} := by
    simpa [P] using mP_profile_arm_factor μ U Z hind x false
  have hnumT :
      mP μ ((P ∩ D1) ∩ {ω | Z ω = true}) =
        mP μ (P ∩ D1) * mP μ {ω | Z ω = true} := by
    have hEq : {ω | (U ω).x = x ∧ (U ω).d1 = true} = P ∩ D1 := by
      ext ω
      rfl
    simpa [hEq] using mP_profile_d1_arm_factor μ U Z hind x true
  have hnumF :
      mP μ ((P ∩ D0) ∩ {ω | Z ω = false}) =
        mP μ (P ∩ D0) * mP μ {ω | Z ω = false} := by
    have hEq : {ω | (U ω).x = x ∧ (U ω).d0 = true} = P ∩ D0 := by
      ext ω
      rfl
    simpa [hEq] using mP_profile_d0_arm_factor μ U Z hind x false
  have hrec : ∀ z,
      mCE μ (fun ω => bit (R ω)) {ω | (U ω).x = x ∧ Z ω = z} =
        scoreAt μ U x * bit z + mCE μ (fun ω => bit ((U ω).d0)) P := by
    intro z
    cases z
    · let S := P ∩ {ω | Z ω = false}
      have hSset : {ω | (U ω).x = x ∧ Z ω = false} = S := by
        ext ω
        rfl
      have hevent : S ∩ {ω | R ω = true} = (P ∩ D0) ∩ {ω | Z ω = false} := by
        ext ω
        cases hz : Z ω <;> simp [S, P, D0, R, hz, PotentialUnit.receipt]
      have hratio :
          mP μ ((P ∩ D0) ∩ {ω | Z ω = false}) / mP μ S =
            mP μ (P ∩ D0) / mP μ P := by
        dsimp [S]
        rw [hnumF, hdenF]
        field_simp [ne_of_gt hxpos, ne_of_gt hqfalse_pos]
      calc
        mCE μ (fun ω => bit (R ω)) {ω | (U ω).x = x ∧ Z ω = false} =
            mCE μ (fun ω => bit (R ω)) S := by rw [hSset]
        _ = mP μ (S ∩ {ω | R ω = true}) / mP μ S :=
          mCE_bit_eq_mP_inter μ S R hR
        _ = mP μ (P ∩ D0) / mP μ P := by rw [hevent, hratio]
        _ = mCE μ (fun ω => bit ((U ω).d0)) P :=
          (mCE_bit_eq_mP_inter μ P (fun ω => (U ω).d0) hd0).symm
        _ = scoreAt μ U x * bit false + mCE μ (fun ω => bit ((U ω).d0)) P := by simp [bit]
    · let S := P ∩ {ω | Z ω = true}
      have hSset : {ω | (U ω).x = x ∧ Z ω = true} = S := by
        ext ω
        rfl
      have hevent : S ∩ {ω | R ω = true} = (P ∩ D1) ∩ {ω | Z ω = true} := by
        ext ω
        cases hz : Z ω <;> simp [S, P, D1, R, hz, PotentialUnit.receipt]
      have hratio :
          mP μ ((P ∩ D1) ∩ {ω | Z ω = true}) / mP μ S =
            mP μ (P ∩ D1) / mP μ P := by
        dsimp [S]
        rw [hnumT, hdenT]
        field_simp [ne_of_gt hxpos, ne_of_gt hzpos]
      calc
        mCE μ (fun ω => bit (R ω)) {ω | (U ω).x = x ∧ Z ω = true} =
            mCE μ (fun ω => bit (R ω)) S := by rw [hSset]
        _ = mP μ (S ∩ {ω | R ω = true}) / mP μ S :=
          mCE_bit_eq_mP_inter μ S R hR
        _ = mP μ (P ∩ D1) / mP μ P := by rw [hevent, hratio]
        _ = mCE μ (fun ω => bit ((U ω).d1)) P :=
          (mCE_bit_eq_mP_inter μ P (fun ω => (U ω).d1) hd1).symm
        _ = scoreAt μ U x * bit true + mCE μ (fun ω => bit ((U ω).d0)) P := by
          rw [hidentity]
          simp [bit, add_comm]
  have hS1pos : 0 < mP μ (P ∩ {ω | Z ω = true}) := by
    rw [hdenT]
    exact mul_pos hxpos hzpos
  have hS0pos : 0 < mP μ (P ∩ {ω | Z ω = false}) := by
    rw [hdenF]
    exact mul_pos hxpos hqfalse_pos
  have hN1 :
      mP μ ((P ∩ {ω | Z ω = true}) ∩ {ω | R ω = true}) =
        (mCE μ (fun ω => bit ((U ω).d0)) P + scoreAt μ U x) *
          mP μ (P ∩ {ω | Z ω = true}) := by
    let S := P ∩ {ω | Z ω = true}
    have hSset : {ω | (U ω).x = x ∧ Z ω = true} = S := by
      ext ω
      rfl
    have hevent : S ∩ {ω | R ω = true} = (P ∩ D1) ∩ {ω | Z ω = true} := by
      ext ω
      cases hz : Z ω <;> simp [S, P, D1, R, hz, PotentialUnit.receipt]
    have hevent' : (P ∩ {ω | Z ω = true}) ∩ {ω | R ω = true} =
        (P ∩ D1) ∩ {ω | Z ω = true} := by
      simpa [S] using hevent
    have hr := mCE_bit_eq_mP_inter μ S R hR
    have hmean : mCE μ (fun ω => bit (R ω)) S =
        mCE μ (fun ω => bit ((U ω).d0)) P + scoreAt μ U x := by
      rw [← hSset]
      simpa [bit, add_comm] using hrec true
    have hratio :
        mP μ ((P ∩ D1) ∩ {ω | Z ω = true}) /
            mP μ S =
          mCE μ (fun ω => bit ((U ω).d0)) P + scoreAt μ U x := by
      calc
        _ = mP μ (S ∩ {ω | R ω = true}) / mP μ S := by rw [← hevent]
        _ = mCE μ (fun ω => bit (R ω)) S := hr.symm
        _ = _ := hmean
    calc
      mP μ ((P ∩ {ω | Z ω = true}) ∩ {ω | R ω = true}) =
          mP μ ((P ∩ D1) ∩ {ω | Z ω = true}) := by rw [hevent']
      _ = (mP μ ((P ∩ D1) ∩ {ω | Z ω = true}) / mP μ S) * mP μ S := by
        exact (div_mul_cancel₀ _ (ne_of_gt hS1pos)).symm
      _ = _ := by rw [hratio]
  have hN0 :
      mP μ ((P ∩ {ω | Z ω = false}) ∩ {ω | R ω = true}) =
        mCE μ (fun ω => bit ((U ω).d0)) P *
          mP μ (P ∩ {ω | Z ω = false}) := by
    let S := P ∩ {ω | Z ω = false}
    have hSset : {ω | (U ω).x = x ∧ Z ω = false} = S := by
      ext ω
      rfl
    have hevent : S ∩ {ω | R ω = true} = (P ∩ D0) ∩ {ω | Z ω = false} := by
      ext ω
      cases hz : Z ω <;> simp [S, P, D0, R, hz, PotentialUnit.receipt]
    have hevent' : (P ∩ {ω | Z ω = false}) ∩ {ω | R ω = true} =
        (P ∩ D0) ∩ {ω | Z ω = false} := by
      simpa [S] using hevent
    have hr := mCE_bit_eq_mP_inter μ S R hR
    have hmean : mCE μ (fun ω => bit (R ω)) S =
        mCE μ (fun ω => bit ((U ω).d0)) P := by
      rw [← hSset]
      simpa [bit] using hrec false
    have hratio :
        mP μ ((P ∩ D0) ∩ {ω | Z ω = false}) /
            mP μ S =
          mCE μ (fun ω => bit ((U ω).d0)) P := by
      calc
        _ = mP μ (S ∩ {ω | R ω = true}) / mP μ S := by rw [← hevent]
        _ = mCE μ (fun ω => bit (R ω)) S := hr.symm
        _ = _ := hmean
    calc
      mP μ ((P ∩ {ω | Z ω = false}) ∩ {ω | R ω = true}) =
          mP μ ((P ∩ D0) ∩ {ω | Z ω = false}) := by rw [hevent']
      _ = (mP μ ((P ∩ D0) ∩ {ω | Z ω = false}) / mP μ S) * mP μ S := by
        exact (div_mul_cancel₀ _ (ne_of_gt hS0pos)).symm
      _ = _ := by rw [hratio]
  have htotal :
      mP μ (P ∩ {ω | R ω = true}) =
        mP μ ((P ∩ {ω | Z ω = true}) ∩ {ω | R ω = true}) +
          mP μ ((P ∩ {ω | Z ω = false}) ∩ {ω | R ω = true}) := by
    have hset : P ∩ {ω | R ω = true} =
        ((P ∩ {ω | Z ω = true}) ∩ {ω | R ω = true}) ∪
          ((P ∩ {ω | Z ω = false}) ∩ {ω | R ω = true}) := by
      ext ω
      simp [Set.mem_inter_iff]
      cases Z ω <;> simp
    have hdis : Disjoint
        ((P ∩ {ω | Z ω = true}) ∩ {ω | R ω = true})
        ((P ∩ {ω | Z ω = false}) ∩ {ω | R ω = true}) := by
      refine Set.disjoint_left.mpr ?_
      intro ω h1 h0
      exact Bool.noConfusion (h1.1.2.symm.trans h0.1.2)
    rw [hset]
    exact MeasureTheory.measureReal_union hdis (by measurability)
      (by finiteness) (by finiteness)
  have hmargin :
      mCE μ (fun ω => bit (R ω)) P =
        mCE μ (fun ω => bit ((U ω).d0)) P +
          mP μ {ω | Z ω = true} * scoreAt μ U x := by
    rw [mCE_bit_eq_mP_inter μ P R hR, htotal, hN1, hN0, hdenT, hdenF]
    have hpne : mP μ P ≠ 0 := ne_of_gt hxpos
    field_simp [hpne]
    have hq0 : mP μ {ω | Z ω = false} = 1 - mP μ {ω | Z ω = true} := by
      linarith [hqsum]
    rw [hq0]
    ring
  have hnull : μ D0 = 0 → mCE μ (fun ω => bit ((U ω).d0)) P = 0 := by
    intro hz
    have hzero : mP μ (P ∩ D0) = 0 := by
      have hμzero : μ (P ∩ D0) = 0 :=
        MeasureTheory.measure_mono_null Set.inter_subset_right hz
      simp [mP, hμzero]
    rw [mCE_bit_eq_mP_inter μ P (fun ω => (U ω).d0) hd0]
    simp [D0, hzero]
  change
    (mCE μ (fun ω => bit ((U ω).d1)) P =
      mCE μ (fun ω => bit ((U ω).d0)) P + scoreAt μ U x) ∧
    (∀ z, mCE μ (fun ω => bit ((U ω).receipt (Z ω)))
      {ω | (U ω).x = x ∧ Z ω = z} =
        scoreAt μ U x * bit z + mCE μ (fun ω => bit ((U ω).d0)) P) ∧
    mCE μ (fun ω => bit ((U ω).receipt (Z ω))) P =
      mCE μ (fun ω => bit ((U ω).d0)) P +
        mP μ {ω | Z ω = true} * scoreAt μ U x ∧
    (μ {ω | (U ω).d0 = true} = 0 →
      mCE μ (fun ω => bit ((U ω).d0)) P = 0)
  exact ⟨hidentity, hrec, hmargin, hnull⟩
