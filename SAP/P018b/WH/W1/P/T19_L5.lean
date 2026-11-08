import SAP.P018b.WH.W1.Leaves
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018b.WH.W1.P.T19_L5

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

abbrev RareEventCode (N m : ℕ) :=
  (Fin N ↪ Fin (m+1)) × ((Fin N → Bool) × (Fin N → Bool))

def rareEventEncode (N m : ℕ)
    (x : {ω : Fin N → AronowAudit.P018.RareUnit // ω ∈ wholeRareEvent rareModel N m}) :
    RareEventCode N m :=
    (⟨fun i => ⟨(x.val i).label.val, by
        have h := (x.val i).label.isLt
        have hlvl : (x.val i).m = m := by simpa [rareModel] using x.property.1 i
        omega⟩, by
      intro i j hij
      exact x.property.2 (congrArg Fin.val hij)⟩,
      (fun i => (x.val i).A, fun i => (x.val i).B))

def rareEventDecode (N m : ℕ) (y : RareEventCode N m) :
    {ω : Fin N → AronowAudit.P018.RareUnit // ω ∈ wholeRareEvent rareModel N m} :=
    ⟨(fun i => ⟨m, y.1 i, y.2.1 i, y.2.2 i⟩), by
      constructor
      · intro i
        rfl
      · intro i j h
        apply y.1.injective
        exact Fin.ext h⟩

def rareEventEquiv (N m : ℕ) :
    {ω : Fin N → AronowAudit.P018.RareUnit //
      ω ∈ wholeRareEvent rareModel N m} ≃ RareEventCode N m where
  toFun := rareEventEncode N m
  invFun := rareEventDecode N m
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    dsimp [rareEventDecode, rareEventEncode]
    cases hui : x.val i with
    | mk lm lab aa bb =>
      have hm : lm = m := by
        simpa [wholeRareEvent, rareModel, hui] using x.property.1 i
      subst lm
      simp [hui]
      apply Fin.ext
      change (x.val i).label.val = lab.val
      rw [hui]
  right_inv := by
    intro y
    rcases y with ⟨e, a, b⟩
    dsimp [rareEventDecode, rareEventEncode]
    apply Prod.ext
    · ext i
      rfl
    · apply Prod.ext
      · ext i
        rfl
      · ext i
        rfl

noncomputable instance rareEventFintype (N m : ℕ) :
    Fintype {ω : Fin N → AronowAudit.P018.RareUnit //
      ω ∈ wholeRareEvent rareModel N m} := by
  classical
  exact Fintype.ofEquiv _ (rareEventEquiv N m).symm

lemma rareEvent_eq (N m : ℕ) :
    wholeRareEvent rareModel N m =
      AronowAudit.P018.Wave1.TailB_rare_event N m := by
  ext ω
  simp [wholeRareEvent, rareModel, AronowAudit.P018.Wave1.TailB_rare_event]

lemma rareEvent_atom {N m : ℕ} (ω : Fin N → AronowAudit.P018.RareUnit)
    (hω : ω ∈ wholeRareEvent rareModel N m) :
    AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N {ω} =
      (ENNReal.ofReal (AronowAudit.P018.Wave1.TailB_rare_p m))^N := by
  have hω' : ω ∈ AronowAudit.P018.Wave1.TailB_rare_event N m := by
    simpa [rareEvent_eq] using hω
  have hlev : ∀ i, (ω i).m = m := hω'.1
  rw [AronowAudit.P018.Wave1.TailB_rare_row_atom]
  simp [hlev]

lemma rareEvent_measure_as_sum (N m : ℕ) :
    AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N
        (wholeRareEvent rareModel N m) =
      ∑ x : {ω : Fin N → AronowAudit.P018.RareUnit //
        ω ∈ wholeRareEvent rareModel N m},
        AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N {x.val} := by
  classical
  have hcount : (wholeRareEvent rareModel N m).Countable :=
    Set.countable_univ.mono (Set.subset_univ _)
  have hmeas : MeasurableSet (wholeRareEvent rareModel N m) := hcount.measurableSet
  have hlin : (∫⁻ ω in wholeRareEvent rareModel N m, (1 : ℝ≥0∞)
        ∂AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) =
      ∑ x : {ω : Fin N → AronowAudit.P018.RareUnit //
        ω ∈ wholeRareEvent rareModel N m},
        AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N {x.val} := by
    rw [lintegral_countable _ hcount, tsum_fintype]
    simp
  calc
    AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N
        (wholeRareEvent rareModel N m) =
        ∫⁻ ω in wholeRareEvent rareModel N m, (1 : ℝ≥0∞)
          ∂AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N := by
      rw [lintegral_const]
      simp [Measure.restrict_apply, hmeas]
    _ = _ := hlin

lemma rareEvent_sum_reindex (N m : ℕ)
    (f : {ω : Fin N → AronowAudit.P018.RareUnit //
      ω ∈ wholeRareEvent rareModel N m} → ℝ≥0∞) :
    (∑ x, f x) = ∑ y : RareEventCode N m,
      f ((rareEventEquiv N m).symm y) := by
  classical
  let e := rareEventEquiv N m
  exact (e.symm.sum_comp f).symm

lemma rareEvent_code_card (N m : ℕ) :
    Fintype.card (RareEventCode N m) = Nat.descFactorial (m+1) N * 4^N := by
  classical
  simp [RareEventCode, Fintype.card_fun, Fintype.card_embedding_eq,
    Nat.card_eq_fintype_card]
  left
  rw [← Nat.mul_pow]

lemma rareEvent_measure_formula (N m : ℕ) :
    AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N
        (wholeRareEvent rareModel N m) =
      ENNReal.ofReal ((Nat.descFactorial (m+1) N : ℝ) *
        (AronowAudit.P018.Wave1.TailB_rare_p m)^N * 4^N) := by
  classical
  have hp : 0 < AronowAudit.P018.Wave1.TailB_rare_p m :=
    AronowAudit.P018.Wave1.TailB_rare_p_pos m
  rw [rareEvent_measure_as_sum]
  rw [rareEvent_sum_reindex]
  have hatom (y : RareEventCode N m) :
      AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N
          {((rareEventEquiv N m).symm y).val} =
        ENNReal.ofReal ((AronowAudit.P018.Wave1.TailB_rare_p m)^N) := by
    rw [rareEvent_atom _ ((rareEventEquiv N m).symm y).property,
      ENNReal.ofReal_pow hp.le]
  simp_rw [hatom]
  rw [show (∑ y : RareEventCode N m,
      ENNReal.ofReal ((AronowAudit.P018.Wave1.TailB_rare_p m)^N)) =
      (Fintype.card (RareEventCode N m) : ℝ≥0∞) *
        ENNReal.ofReal ((AronowAudit.P018.Wave1.TailB_rare_p m)^N) by simp]
  have hcardcast : (Fintype.card (RareEventCode N m) : ℝ≥0∞) =
      ENNReal.ofReal (Fintype.card (RareEventCode N m) : ℝ) := by simp
  rw [hcardcast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [rareEvent_code_card]
  push_cast
  ring

lemma rare_p4 (m : ℕ) :
    AronowAudit.P018.Wave1.TailB_rare_p m * 4 =
      (2 : ℝ)^(-(m+1 : ℤ))/(m+1 : ℝ) := by
  unfold AronowAudit.P018.Wave1.TailB_rare_p
  field_simp

lemma rare_p4_pow (m N : ℕ) :
    (AronowAudit.P018.Wave1.TailB_rare_p m)^N * 4^N =
      (2 : ℝ)^(-((m+1 : ℤ)*N))/(m+1 : ℝ)^N := by
  rw [← mul_pow, rare_p4, div_pow]
  have hz : ((2 : ℝ)^(-(m+1 : ℤ)))^N =
      (2 : ℝ)^(-((m+1 : ℤ)*N)) := by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
  rw [hz]

lemma rareEvent_probability_formula (N m : ℕ) :
    (AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N
      (wholeRareEvent rareModel N m)).toReal =
      (2 : ℝ)^(-((m+1 : ℤ)*N)) *
        (Nat.descFactorial (m+1) N : ℝ)/(m+1 : ℝ)^N := by
  rw [rareEvent_measure_formula]
  have hnonneg : 0 ≤ (Nat.descFactorial (m+1) N : ℝ) *
      (AronowAudit.P018.Wave1.TailB_rare_p m)^N * 4^N :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg
      (AronowAudit.P018.Wave1.TailB_rare_p_pos m).le _)) (by positivity)
  rw [ENNReal.toReal_ofReal hnonneg]
  calc
    (Nat.descFactorial (m+1) N : ℝ) *
        (AronowAudit.P018.Wave1.TailB_rare_p m)^N * 4^N =
      (Nat.descFactorial (m+1) N : ℝ) *
        ((AronowAudit.P018.Wave1.TailB_rare_p m)^N * 4^N) := by ring
    _ = (Nat.descFactorial (m+1) N : ℝ) *
        ((2 : ℝ)^(-((m+1 : ℤ)*N))/(m+1 : ℝ)^N) := by rw [rare_p4_pow]
    _ = _ := by ring

lemma fair_sign_sum_square (N : ℕ) :
    (∑ a : Fin N → Bool, (∑ i, AronowAudit.P018.signValue (a i))^2) =
      (2 : ℝ)^N * N := by
  classical
  let μ := AronowAudit.P018.unitSampleLaw AronowAudit.P018.signKernel N
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact AronowAudit.P018.Wave1.printed_sign_probability N
  have hsecond := AronowAudit.P018.Wave1.printed_S_second N
  have hmass (a : Fin N → Bool) : μ.real {a} = (1/2 : ℝ)^N := by
    letI : IsProbabilityMeasure AronowAudit.P018.fairLaw :=
      AronowAudit.P018.Wave1.printed_fair_probability
    change (Measure.pi (fun _ : Fin N => AronowAudit.P018.fairLaw) {a}).toReal = _
    rw [Measure.pi_singleton]
    norm_num [AronowAudit.P018.fairLaw, PMF.toMeasure_uniformOfFintype_apply,
      Fintype.card_bool]
  change (∫ a : Fin N → Bool,
      (∑ i, AronowAudit.P018.signValue (a i))^2 ∂μ) = (N : ℝ) at hsecond
  rw [integral_fintype
    (AronowAudit.P018.Wave1.printed_finite_integrable μ _)] at hsecond
  simp_rw [hmass] at hsecond
  simp only [smul_eq_mul] at hsecond
  rw [← Finset.mul_sum] at hsecond
  have hInv : (1/2 : ℝ)^N * (2 : ℝ)^N = 1 := by
    rw [div_pow]
    field_simp
    norm_num
  calc
    (∑ a : Fin N → Bool, (∑ i, AronowAudit.P018.signValue (a i))^2) =
        ((1/2 : ℝ)^N * ∑ a : Fin N → Bool,
          (∑ i, AronowAudit.P018.signValue (a i))^2) * (2 : ℝ)^N := by
            calc
              _ = 1 * ∑ a : Fin N → Bool,
                  (∑ i, AronowAudit.P018.signValue (a i))^2 := by ring
              _ = ((1/2 : ℝ)^N * (2 : ℝ)^N) *
                  ∑ a : Fin N → Bool, (∑ i, AronowAudit.P018.signValue (a i))^2 := by
                    rw [hInv]
              _ = _ := by ring
    _ = (N : ℝ) * (2 : ℝ)^N := by rw [hsecond]
    _ = (2 : ℝ)^N * N := by ring

lemma rareRepeatedLaw_eq (N : ℕ) :
    repeatedLaw (wholeRareKernel rareModel) N =
      AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N := by rfl

lemma rareOLS_eq {N : ℕ} (ω : Fin N → AronowAudit.P018.RareUnit) :
    repeatedOLS (wholeRareKernel rareModel) ω =
      AronowAudit.P018.repeatedOLS AronowAudit.P018.rareRepeated ω := by rfl

lemma rareEvent_slope_code (N m : ℕ) (hN : 3 ≤ N)
    (y : RareEventCode N m) :
    AronowAudit.P018.repeatedOLS AronowAudit.P018.rareRepeated
        ((rareEventEquiv N m).symm y).val 1 =
      2*((∑ i, AronowAudit.P018.signValue (y.2.1 i))/(N : ℝ)) /
        AronowAudit.P018.rareDelta (m+1) := by
  have he : ((rareEventEquiv N m).symm y).val ∈
      AronowAudit.P018.Wave1.TailB_rare_event N m := by
    simpa [rareEvent_eq] using ((rareEventEquiv N m).symm y).property
  have hs := AronowAudit.P018.Wave1.TailB_rare_event_slope (by omega) he
  simpa [AronowAudit.P018.Wave1.TailB_rare_Abar, rareEventDecode,
    rareEventEquiv] using hs

lemma rareEvent_sign_slope_sq_sum (N m : ℕ) (hN : 3 ≤ N) :
    (∑ a : Fin N → Bool,
      (2*((∑ i, AronowAudit.P018.signValue (a i))/(N : ℝ)) /
        AronowAudit.P018.rareDelta (m+1))^2) =
      (4/((N : ℝ)*(AronowAudit.P018.rareDelta (m+1))^2))*(2 : ℝ)^N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hdpos : 0 < AronowAudit.P018.rareDelta (m+1) :=
    AronowAudit.P018.Wave1.TailB_rare_delta_pos _ (by omega)
  have hterm (a : Fin N → Bool) :
      (2*((∑ i, AronowAudit.P018.signValue (a i))/(N : ℝ)) /
        AronowAudit.P018.rareDelta (m+1))^2 =
      (4/((N : ℝ)^2*(AronowAudit.P018.rareDelta (m+1))^2)) *
        (∑ i, AronowAudit.P018.signValue (a i))^2 := by
    field_simp [hNne, ne_of_gt hdpos]
    <;> ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, fair_sign_sum_square]
  field_simp [hNne, ne_of_gt hdpos]
  <;> ring

lemma rareEvent_code_sum (N m : ℕ) (g : (Fin N → Bool) → ℝ) :
    (∑ y : RareEventCode N m, g y.2.1) =
      (Nat.descFactorial (m+1) N : ℝ) * (2 : ℝ)^N *
        (∑ a : Fin N → Bool, g a) := by
  classical
  simp only [RareEventCode, Fintype.sum_prod_type]
  simp [Fintype.card_fun, Fintype.card_embedding_eq,
    Nat.card_eq_fintype_card]
  rw [← Finset.mul_sum]
  ring

lemma rareEvent_square_lintegral_sum (N m : ℕ) :
    (∫⁻ ω, ENNReal.ofReal
      ((AronowAudit.P018.repeatedOLS AronowAudit.P018.rareRepeated ω 1)^2)
      ∂(AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N).restrict
        (wholeRareEvent rareModel N m)) =
      ∑ x : {ω : Fin N → AronowAudit.P018.RareUnit //
        ω ∈ wholeRareEvent rareModel N m},
        ENNReal.ofReal
          ((AronowAudit.P018.repeatedOLS AronowAudit.P018.rareRepeated x.val 1)^2) *
        AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N {x.val} := by
  classical
  have hcount : (wholeRareEvent rareModel N m).Countable :=
    Set.countable_univ.mono (Set.subset_univ _)
  change (∫⁻ ω in wholeRareEvent rareModel N m,
    ENNReal.ofReal ((AronowAudit.P018.repeatedOLS
      AronowAudit.P018.rareRepeated ω 1)^2)
    ∂AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N) = _
  rw [lintegral_countable _ hcount, tsum_fintype]

lemma rareEvent_square_lintegral_formula (N m : ℕ) (hN : 3 ≤ N) :
    (∫⁻ ω, ENNReal.ofReal
      ((repeatedOLS (wholeRareKernel rareModel) ω 1)^2)
      ∂(repeatedLaw (wholeRareKernel rareModel) N).restrict
        (wholeRareEvent rareModel N m)) =
      ENNReal.ofReal ((Nat.descFactorial (m+1) N : ℝ) * (2 : ℝ)^N *
        (AronowAudit.P018.Wave1.TailB_rare_p m)^N *
        (4/((N : ℝ)*(AronowAudit.P018.rareDelta (m+1))^2))*(2 : ℝ)^N) := by
  classical
  let g : (Fin N → Bool) → ℝ := fun a =>
    (2*((∑ i, AronowAudit.P018.signValue (a i))/(N : ℝ)) /
      AronowAudit.P018.rareDelta (m+1))^2
  have hp : 0 < AronowAudit.P018.Wave1.TailB_rare_p m :=
    AronowAudit.P018.Wave1.TailB_rare_p_pos m
  simp_rw [rareOLS_eq, rareRepeatedLaw_eq]
  rw [rareEvent_square_lintegral_sum, rareEvent_sum_reindex]
  calc
    (∑ y : RareEventCode N m,
        ENNReal.ofReal ((AronowAudit.P018.repeatedOLS
          AronowAudit.P018.rareRepeated ((rareEventEquiv N m).symm y).val 1)^2) *
          AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N
            {((rareEventEquiv N m).symm y).val}) =
      ∑ y : RareEventCode N m, ENNReal.ofReal (g y.2.1 *
        (AronowAudit.P018.Wave1.TailB_rare_p m)^N) := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [rareEvent_slope_code N m hN y,
            rareEvent_atom _ ((rareEventEquiv N m).symm y).property,
            ← ENNReal.ofReal_pow hp.le,
            ENNReal.ofReal_mul (sq_nonneg _)]
    _ = ENNReal.ofReal (∑ y : RareEventCode N m,
        g y.2.1 * (AronowAudit.P018.Wave1.TailB_rare_p m)^N) := by
          symm
          have hnonneg : ∀ y : RareEventCode N m, 0 ≤
              g y.2.1 * (AronowAudit.P018.Wave1.TailB_rare_p m)^N := by
            intro y
            exact mul_nonneg (sq_nonneg _) (pow_nonneg hp.le _)
          have hs := ENNReal.ofReal_sum_of_nonneg
            (s := Finset.univ)
            (f := fun y : RareEventCode N m =>
              g y.2.1 * (AronowAudit.P018.Wave1.TailB_rare_p m)^N)
            (by intro y hy; exact hnonneg y)
          simpa using hs
    _ = ENNReal.ofReal
        ((Nat.descFactorial (m+1) N : ℝ) * (2 : ℝ)^N *
          (AronowAudit.P018.Wave1.TailB_rare_p m)^N *
          (4 / ((N : ℝ) * (AronowAudit.P018.rareDelta (m+1))^2)) *
          (2 : ℝ)^N) := by
          congr 1
          calc
            (∑ y : RareEventCode N m,
                g y.2.1 * (AronowAudit.P018.Wave1.TailB_rare_p m)^N) =
              (Nat.descFactorial (m+1) N : ℝ) * (2 : ℝ)^N *
                (∑ a : Fin N → Bool, g a *
                  (AronowAudit.P018.Wave1.TailB_rare_p m)^N) :=
                    rareEvent_code_sum N m (fun a =>
                      g a * (AronowAudit.P018.Wave1.TailB_rare_p m)^N)
            _ = _ := by
              rw [← Finset.sum_mul, rareEvent_sign_slope_sq_sum N m hN]
              ring

lemma prod_one_sub_ge_one_sub_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx0 : ∀ i ∈ s, 0 ≤ x i) (hx1 : ∀ i ∈ s, x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1-x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
      have ha0 := hx0 a (Finset.mem_insert_self _ _)
      have ha1 := hx1 a (Finset.mem_insert_self _ _)
      have hx0' : ∀ i ∈ s, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
      have hx1' : ∀ i ∈ s, x i ≤ 1 := fun i hi => hx1 i (Finset.mem_insert_of_mem hi)
      have hs0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg (fun i hi => hx0' i hi)
      rw [Finset.sum_insert has, Finset.prod_insert has]
      have hmul := mul_le_mul_of_nonneg_right (ih hx0' hx1') (sub_nonneg.mpr ha1)
      nlinarith [mul_nonneg hs0 ha0]

lemma rare_distinct_label_bound (N M : ℕ) (hN : 3 ≤ N)
    (hNM : N*(N-1) ≤ M) :
    (1/2 : ℝ) ≤ (Nat.descFactorial M N : ℝ)/(M : ℝ)^N := by
  have hNMpos : 0 < M := by
    have hp : 0 < N*(N-1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hNm1 : 1 ≤ N-1 := by omega
  have hNle : N ≤ M := by
    have hmul : N*1 ≤ N*(N-1) := Nat.mul_le_mul_left N hNm1
    exact le_trans (by simpa using hmul) hNM
  have hMr : (0 : ℝ) < M := by exact_mod_cast hNMpos
  have hprod : (Nat.descFactorial M N : ℝ)/(M : ℝ)^N =
      ∏ i ∈ Finset.range N, (1-(i : ℝ)/(M : ℝ)) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    rw [show (M : ℝ)^N = ∏ i ∈ Finset.range N, (M : ℝ) by simp]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    have hiM : i ≤ M := Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hNle
    rw [Nat.cast_sub hiM]
    field_simp
    <;> ring
  rw [hprod]
  apply le_trans ?_ (prod_one_sub_ge_one_sub_sum _ _ ?_ ?_)
  · have hsum : (∑ i ∈ Finset.range N, (i : ℝ)/(M : ℝ)) =
        ((N : ℝ)*((N : ℝ)-1))/(2*(M : ℝ)) := by
      rw [← Finset.sum_div]
      have hs : 2 * (∑ i ∈ Finset.range N, (i : ℝ)) =
          (N : ℝ)*((N : ℝ)-1) := by
        have hn := Finset.sum_range_id_mul_two N
        have hncast : (∑ i ∈ Finset.range N, (i : ℝ))*2 =
            ((N*(N-1) : ℕ) : ℝ) := by
          rw [← Nat.cast_sum]
          exact_mod_cast hn
        have hn1 : 1 ≤ N := by omega
        have hnc : ((N*(N-1) : ℕ) : ℝ) = (N : ℝ)*((N : ℝ)-1) := by
          rw [Nat.cast_mul, Nat.cast_sub hn1]
          norm_num
        rw [mul_comm] at hncast
        rw [hnc] at hncast
        linarith
      rw [show (∑ i ∈ Finset.range N, (i : ℝ)) =
          ((N : ℝ)*((N : ℝ)-1))/2 by linarith [hs]]
      field_simp
    rw [hsum]
    have hden : 0 < 2*(M : ℝ) := by positivity
    have hcast : (N : ℝ)*((N : ℝ)-1) ≤ M := by
      have hn1 : 1 ≤ N := by omega
      have hnreal : ((N*(N-1) : ℕ) : ℝ) ≤ M := by exact_mod_cast hNM
      rw [Nat.cast_mul, Nat.cast_sub hn1] at hnreal
      norm_num at hnreal
      exact hnreal
    have hfrac : ((N : ℝ)*((N : ℝ)-1))/(2*(M : ℝ)) ≤ (1/2 : ℝ) := by
      apply (div_le_iff₀ hden).2
      nlinarith
    linarith
  · intro i hi
    apply div_nonneg
    · exact_mod_cast (Nat.zero_le i)
    · positivity
  · intro i hi
    apply (div_le_one (by positivity)).2
    have hiM : i ≤ M := Nat.le_trans (Nat.le_of_lt (Finset.mem_range.mp hi)) hNle
    exact_mod_cast hiM

lemma rare_growth_power_bound (N M : ℕ) (hN : 3 ≤ N)
    (hNM : N*(N-1) ≤ M) :
    (2 : ℝ)^(M^2) ≤ (32/(N : ℝ))*(M : ℝ)^4*
      (2 : ℝ)^(2*(M : ℤ)^2-(M : ℤ)*(N : ℤ)) := by
  have hNpos : 0 < N := by omega
  have hMpos : 0 < M := by
    have hp : 0 < N*(N-1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hNm1 : 1 ≤ N-1 := by omega
  have hNM' : N ≤ M := by
    have hmul : N*1 ≤ N*(N-1) := Nat.mul_le_mul_left N hNm1
    exact le_trans (by simpa using hmul) hNM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hcoef : 1 ≤ (32/(N : ℝ))*(M : ℝ)^4 := by
    have hNleM : (N : ℝ) ≤ M := by exact_mod_cast hNM'
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hNr).2
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hMpos
    have hM3 := one_le_pow₀ (n := 3) hM1
    have hM4 : (M : ℝ) ≤ (M : ℝ)^4 := by
      have hmul := mul_le_mul_of_nonneg_left hM3 hMr.le
      nlinarith
    have hNleM : (N : ℝ) ≤ M := by exact_mod_cast hNM'
    nlinarith
  have hexp : (M : ℤ)^2 ≤ 2*(M : ℤ)^2-(M : ℤ)*(N : ℤ) := by
    have hNMcast : (N : ℤ) ≤ M := by exact_mod_cast hNM'
    nlinarith
  have hpow : (2 : ℝ)^(M^2 : ℤ) ≤
      (2 : ℝ)^(2*(M : ℤ)^2-(M : ℤ)*(N : ℤ)) :=
    zpow_le_zpow_right₀ (by norm_num) hexp
  have hpowpos : 0 ≤ (2 : ℝ)^(M^2 : ℤ) := by positivity
  have hpow' : (2 : ℝ)^(M^2 : ℤ) ≤
      ((32/(N : ℝ))*(M : ℝ)^4)*(2 : ℝ)^(2*(M : ℤ)^2-(M : ℤ)*(N : ℤ)) :=
    le_trans hpow (le_mul_of_one_le_left (by positivity) hcoef)
  have hpoweq : (2 : ℝ)^(M^2) = (2 : ℝ)^((M : ℤ)^2) := by
    calc
      (2 : ℝ)^(M^2) = (2 : ℝ)^((M^2 : ℕ) : ℤ) :=
        (zpow_natCast (2 : ℝ) (M^2 : ℕ)).symm
      _ = (2 : ℝ)^((M : ℤ)^2) := by congr 1 <;> norm_num
  rw [hpoweq]
  exact hpow'

lemma rare_square_argument_bound (N m : ℕ) (hN : 3 ≤ N)
    (hNM : N*(N-1) ≤ m+1) :
    (32/(N : ℝ))*(m+1 : ℝ)^4*
      (2 : ℝ)^(2*(m+1 : ℤ)^2-(m+1 : ℤ)*(N : ℤ)) ≤
    (Nat.descFactorial (m+1) N : ℝ) * (2 : ℝ)^N *
      (AronowAudit.P018.Wave1.TailB_rare_p m)^N *
      (4/((N : ℝ)*(AronowAudit.P018.rareDelta (m+1))^2))*(2 : ℝ)^N := by
  let M : ℕ := m+1
  have hNpos : 0 < N := by omega
  have hMpos : 0 < M := by
    have hp : 0 < N*(N-1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hq : (1/2 : ℝ) ≤ (Nat.descFactorial M N : ℝ)/(M : ℝ)^N :=
    rare_distinct_label_bound N M hN (by simpa [M] using hNM)
  have hpow : (2 : ℝ)^N *
      (AronowAudit.P018.Wave1.TailB_rare_p m)^N * (2 : ℝ)^N =
      (AronowAudit.P018.Wave1.TailB_rare_p m)^N * 4^N := by
    calc
      _ = ((2 : ℝ)^N * (2 : ℝ)^N) *
          (AronowAudit.P018.Wave1.TailB_rare_p m)^N := by ring
      _ = ((2 : ℝ) * 2)^N *
          (AronowAudit.P018.Wave1.TailB_rare_p m)^N := by rw [mul_pow]
      _ = _ := by norm_num; ring
  have hdelta : 4/((N : ℝ)*(AronowAudit.P018.rareDelta M)^2) =
      (4/(N : ℝ))*(M : ℝ)^4*(2 : ℝ)^(2*(M*M+2)) := by
    rw [show AronowAudit.P018.rareDelta M =
      1/((M : ℝ)^2*(2 : ℝ)^(M*M+2)) by rfl]
    field_simp [ne_of_gt hNr, ne_of_gt hMr]
    <;> ring
  have hz : (2 : ℝ)^(-((M : ℤ)*(N : ℤ))) *
      (2 : ℝ)^(2*(M*M+2)) =
      16*(2 : ℝ)^(2*(M : ℤ)^2-(M : ℤ)*(N : ℤ)) := by
    rw [← zpow_natCast (2 : ℝ) (2*(M*M+2))]
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    have he : -((M : ℤ)*(N : ℤ)) + ((2*(M*M+2) : ℕ) : ℤ) =
        2*(M : ℤ)^2-(M : ℤ)*(N : ℤ)+4 := by push_cast; ring
    rw [he, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num [zpow_natCast]
    ring
  have hEq :
      (Nat.descFactorial M N : ℝ) * (2 : ℝ)^N *
        (AronowAudit.P018.Wave1.TailB_rare_p m)^N *
        (4/((N : ℝ)*(AronowAudit.P018.rareDelta M)^2))*(2 : ℝ)^N =
      ((32/(N : ℝ))*(M : ℝ)^4*
        (2 : ℝ)^(2*(M : ℤ)^2-(M : ℤ)*(N : ℤ))) *
        (2*((Nat.descFactorial M N : ℝ)/(M : ℝ)^N)) := by
    calc
      _ = (Nat.descFactorial M N : ℝ) *
          ((2 : ℝ)^N*(AronowAudit.P018.Wave1.TailB_rare_p m)^N*(2 : ℝ)^N) *
          (4/((N : ℝ)*(AronowAudit.P018.rareDelta M)^2)) := by ring
      _ = (Nat.descFactorial M N : ℝ) *
          ((AronowAudit.P018.Wave1.TailB_rare_p m)^N*4^N) *
          (4/((N : ℝ)*(AronowAudit.P018.rareDelta M)^2)) := by rw [hpow]
      _ = (Nat.descFactorial M N : ℝ) *
          ((2 : ℝ)^(-((M : ℤ)*(N : ℤ)))/(M : ℝ)^N) *
          (4/((N : ℝ)*(AronowAudit.P018.rareDelta M)^2)) := by
            have hMcast : (m+1 : ℝ) = (M : ℝ) := by simp [M]
            have hMcastZ : (m+1 : ℤ) = (M : ℤ) := by simp [M]
            have hp4 := rare_p4_pow m N
            rw [hMcast, hMcastZ] at hp4
            rw [hp4]
      _ = (Nat.descFactorial M N : ℝ)/(M : ℝ)^N *
          (4/(N : ℝ))*(M : ℝ)^4 *
          ((2 : ℝ)^(-((M : ℤ)*(N : ℤ))) *
            (2 : ℝ)^(2*(M*M+2))) := by rw [hdelta]; ring
      _ = _ := by rw [hz]; ring
  have htarget : 0 ≤ (32/(N : ℝ))*(M : ℝ)^4*
      (2 : ℝ)^(2*(M : ℤ)^2-(M : ℤ)*(N : ℤ)) := by positivity
  rw [show (m+1 : ℝ) = (M : ℝ) by simp [M]]
  calc
    (32/(N : ℝ))*(M : ℝ)^4*
        (2 : ℝ)^(2*(M : ℤ)^2-(M : ℤ)*(N : ℤ)) =
      ((32/(N : ℝ))*(M : ℝ)^4*
        (2 : ℝ)^(2*(M : ℤ)^2-(M : ℤ)*(N : ℤ))) * 1 := by ring
    _ ≤ ((32/(N : ℝ))*(M : ℝ)^4*
        (2 : ℝ)^(2*(M : ℤ)^2-(M : ℤ)*(N : ℤ))) *
          (2*((Nat.descFactorial M N : ℝ)/(M : ℝ)^N)) := by
            apply mul_le_mul_of_nonneg_left _ htarget
            linarith
    _ = _ := hEq.symm

end SAP.P018b.WH.W1.P.T19_L5

theorem SAP.P018b.WH.W1.T19_L5_proof : SAP.P018b.WH.W1.T19_L5 := by
  intro N m hN hNM
  let M : ℕ := m+1
  have hM : M = m+1 := rfl
  have hN' : 3 ≤ N := hN
  have hNM' : N*(N-1) ≤ M := by simpa [M] using hNM
  refine ⟨?_, ?_, ?_⟩
  · simpa [M] using SAP.P018b.WH.W1.P.T19_L5.rare_distinct_label_bound N M hN' hNM'
  · rw [SAP.P018b.WH.W1.P.T19_L5.rareEvent_square_lintegral_formula N m hN']
    apply ENNReal.ofReal_le_ofReal
    exact SAP.P018b.WH.W1.P.T19_L5.rare_square_argument_bound N m hN' hNM
  · simpa [M] using SAP.P018b.WH.W1.P.T19_L5.rare_growth_power_bound N M hN' hNM'
