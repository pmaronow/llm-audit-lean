import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.Wave1.Gap.TailBSignSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W2.P.T7_L1

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

private def firstSign {N : ℕ} (ω : Fin N → Bool × Bool) : Fin N → ℝ :=
  fun i => signValue (ω i).1

private def dyadEquiv {N : ℕ} : Dyad N ≃ AronowAudit.P018.Dyad N where
  toFun d := ⟨d.val, by simpa [SAP.P018a.Bridge.dyads_agree] using d.property⟩
  invFun d := ⟨d.val, by simpa [SAP.P018a.Bridge.dyads_agree] using d.property⟩
  left_inv d := by apply Subtype.ext; rfl
  right_inv d := by apply Subtype.ext; rfl

private lemma firstSign_sq {N : ℕ} (ω : Fin N → Bool × Bool) (i : Fin N) :
    (firstSign ω i)^2 = 1 := by
  cases h : (ω i).1 <;> simp [firstSign, signValue, h]

private lemma pair_design_eq {N : ℕ} (ω : Fin N → Bool × Bool) :
    SAP.P018a.sampleGram (design signPairKernel ω) =
      AronowAudit.P018.sampleGram
        (AronowAudit.P018.Wave1.TailBSign.tb05_design (firstSign ω)) := by
  unfold SAP.P018a.sampleGram AronowAudit.P018.sampleGram
  apply Fintype.sum_equiv dyadEquiv
  intro d
  have he := SAP.P018a.Bridge.endpoints_agree d
  have hfirst : AronowAudit.P018.firstUnit (dyadEquiv d) = firstUnit d := by
    change AronowAudit.P018.firstUnit d = firstUnit d
    exact he.1.symm
  have hsecond : AronowAudit.P018.secondUnit (dyadEquiv d) = secondUnit d := by
    change AronowAudit.P018.secondUnit d = secondUnit d
    exact he.2.symm
  simp [design, signPairKernel,
    AronowAudit.P018.Wave1.TailBSign.tb05_design, firstSign, hfirst, hsecond]
  rfl

private lemma pair_det_formula {N : ℕ} (ω : Fin N → Bool × Bool) :
    (sampleGram (design signPairKernel ω)).det =
      (Dreal N)^2 -
        (AronowAudit.P018.Wave1.TailBSign.tb05_T (firstSign ω))^2 := by
  rw [pair_design_eq]
  rw [AronowAudit.P018.Wave1.TailBSign.tb05_sample_gram
    (firstSign ω) (firstSign_sq ω)]
  rw [Matrix.det_fin_two]
  norm_num [Matrix.of_apply]
  simp only [SAP.P018a.Dreal, AronowAudit.P018.Dreal]
  ring_nf

private lemma all_first_signs_iff_sum_extreme {N : ℕ}
    (ω : Fin N → Bool × Bool) (hN : 3 ≤ N) :
    (∃ b : Bool, ∀ i, (ω i).1 = b) ↔
      (∑ i, firstSign ω i = (N : ℝ) ∨ ∑ i, firstSign ω i = -(N : ℝ)) := by
  constructor
  · rintro ⟨b, hb⟩
    cases b
    · right
      simp [firstSign, signValue, hb]
    · left
      simp [firstSign, signValue, hb]
  · intro hs
    rcases hs with hs | hs
    · have hle (i : Fin N) : firstSign ω i ≤ 1 := by
        rcases sq_eq_one_iff.mp (firstSign_sq ω i) with h | h <;> linarith
      have heq := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (f := firstSign ω) (g := fun _ : Fin N => (1 : ℝ))
        (fun i _ => hle i)).mp (by simpa using hs)
      refine ⟨true, ?_⟩
      intro i
      by_contra hn
      have hf : (ω i).1 = false := by cases h : (ω i).1 <;> simp_all
      have hv := heq i (Finset.mem_univ i)
      simp [firstSign, signValue, hf] at hv
      norm_num at hv
    · have hle (i : Fin N) : -firstSign ω i ≤ 1 := by
        rcases sq_eq_one_iff.mp (firstSign_sq ω i) with h | h <;> linarith
      have heq := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
        (f := fun i => -firstSign ω i) (g := fun _ : Fin N => (1 : ℝ))
        (fun i _ => hle i)).mp (by simpa using neg_eq_iff_eq_neg.mpr hs)
      refine ⟨false, ?_⟩
      intro i
      by_contra hn
      have ht : (ω i).1 = true := by cases h : (ω i).1 <;> simp_all
      have hv := heq i (Finset.mem_univ i)
      simp [firstSign, signValue, ht] at hv
      norm_num at hv

private lemma pair_det_zero_iff {N : ℕ} (ω : Fin N → Bool × Bool)
    (hN : 3 ≤ N) :
    (sampleGram (design signPairKernel ω)).det = 0 ↔
      ∃ b : Bool, ∀ i, (ω i).1 = b := by
  rw [pair_det_formula]
  let T := AronowAudit.P018.Wave1.TailBSign.tb05_T (firstSign ω)
  have hT := AronowAudit.P018.Wave1.TailBSign.tb05_T_formula
    (firstSign ω) (firstSign_sq ω)
  have hD : Dreal N = ((N : ℝ) * ((N : ℝ) - 1)) / 2 := rfl
  constructor
  · intro hdet
    have hfactor : (Dreal N - T) * (Dreal N + T) = 0 := by
      dsimp [T]
      nlinarith [hdet]
    rcases mul_eq_zero.mp hfactor with ht | ht
    · have hsumSq : (∑ i, firstSign ω i)^2 = (N : ℝ)^2 := by
        change Dreal N - AronowAudit.P018.Wave1.TailBSign.tb05_T (firstSign ω) = 0 at ht
        rw [hT] at ht
        rw [hD] at ht
        nlinarith
      have hs : (∑ i, firstSign ω i = (N : ℝ)) ∨
          (∑ i, firstSign ω i = -(N : ℝ)) := by
        have hprod : ((∑ i, firstSign ω i) - N) *
            ((∑ i, firstSign ω i) + N) = 0 := by nlinarith [hsumSq]
        rcases mul_eq_zero.mp hprod with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      exact (all_first_signs_iff_sum_extreme ω hN).2 hs
    · have hsumSq : (∑ i, firstSign ω i)^2 = (N : ℝ) * (2 - N) := by
        change Dreal N + AronowAudit.P018.Wave1.TailBSign.tb05_T (firstSign ω) = 0 at ht
        rw [hT] at ht
        rw [hD] at ht
        nlinarith
      have hn : (N : ℝ) * (2 - N) < 0 := by
        have hn' : (3 : ℝ) ≤ N := by exact_mod_cast hN
        nlinarith
      nlinarith [sq_nonneg (∑ i, firstSign ω i)]
  · rintro ⟨b, hb⟩
    have hsum : ∑ i, firstSign ω i = (N : ℝ) * signValue b := by
      simp [firstSign, hb, Finset.sum_const, Finset.card_fin]
    have hTval : T = Dreal N := by
      change AronowAudit.P018.Wave1.TailBSign.tb05_T (firstSign ω) = Dreal N
      rw [hT, hsum, hD]
      have hb2 : (signValue b)^2 = 1 := by cases b <;> norm_num [signValue]
      nlinarith
    change (Dreal N)^2 - T^2 = 0
    rw [hTval]
    ring

private lemma first_coordinate_measure (b : Bool) :
    signPairKernel.μ {u : Bool × Bool | u.1 = b} = (1 / 2 : ℝ≥0∞) := by
  letI : IsProbabilityMeasure fairLaw := AronowAudit.P018.Wave1.printed_fair_probability
  letI : IsProbabilityMeasure signPairKernel.μ := by
    change IsProbabilityMeasure (fairLaw.prod fairLaw)
    infer_instance
  change (fairLaw.prod fairLaw) {u : Bool × Bool | u.1 = b} = _
  rw [show {u : Bool × Bool | u.1 = b} = ({b} : Set Bool) ×ˢ Set.univ by
    ext u
    simp]
  rw [Measure.prod_prod]
  have hb : fairLaw ({b} : Set Bool) = (1 / 2 : ℝ≥0∞) := by
    rw [fairLaw, PMF.toMeasure_uniformOfFintype_apply (s := ({b} : Set Bool)) (by simp)]
    norm_num
  rw [hb, MeasureTheory.measure_univ]
  norm_num

private def constantFirst (N : ℕ) (b : Bool) : Set (Fin N → Bool × Bool) :=
  Set.univ.pi (fun _ : Fin N => {u : Bool × Bool | u.1 = b})

private lemma constant_first_measure (N : ℕ) (b : Bool) :
    unitSampleLaw signPairKernel N (constantFirst N b) = (1 / 2 : ℝ≥0∞)^N := by
  letI : IsProbabilityMeasure fairLaw := AronowAudit.P018.Wave1.printed_fair_probability
  letI : IsProbabilityMeasure signPairKernel.μ := by
    change IsProbabilityMeasure (fairLaw.prod fairLaw)
    infer_instance
  rw [unitSampleLaw]
  change (Measure.pi (fun _ : Fin N => signPairKernel.μ))
    (Set.univ.pi (fun _ : Fin N => {u : Bool × Bool | u.1 = b})) = _
  rw [Measure.pi_pi]
  simp_rw [first_coordinate_measure]
  simp [Finset.prod_const, Finset.card_fin]

end SAP.P018a.WH.W2.P.T7_L1

theorem SAP.P018a.WH.W2.T7_L1_proof : SAP.P018a.WH.W2.T7_L1 := by
  classical
  change SAP.P018a.T7Rank
  intro N hN
  refine ⟨?_, ?_⟩
  · intro ω
    exact SAP.P018a.WH.W2.P.T7_L1.pair_det_zero_iff ω hN
  · let A := SAP.P018a.WH.W2.P.T7_L1.constantFirst N true
    let B := SAP.P018a.WH.W2.P.T7_L1.constantFirst N false
    have hset : {ω : Fin N → Bool × Bool |
        (sampleGram (design signPairKernel ω)).det = 0} = A ∪ B := by
      ext ω
      change (sampleGram (design signPairKernel ω)).det = 0 ↔ ω ∈ A ∪ B
      rw [SAP.P018a.WH.W2.P.T7_L1.pair_det_zero_iff ω hN]
      simp [A, B, SAP.P018a.WH.W2.P.T7_L1.constantFirst, or_comm]
    have hdisj : Disjoint A B := by
      apply Set.disjoint_left.mpr
      intro ω ha hb
      have ha' : ∀ i, (ω i).1 = true := by simpa [A, SAP.P018a.WH.W2.P.T7_L1.constantFirst] using ha
      have hb' : ∀ i, (ω i).1 = false := by simpa [B, SAP.P018a.WH.W2.P.T7_L1.constantFirst] using hb
      exact Bool.noConfusion ((ha' ⟨0, by omega⟩).symm.trans (hb' ⟨0, by omega⟩))
    have hmeasA : MeasurableSet A := by
      change MeasurableSet (Set.univ.pi fun _ : Fin N => {u : Bool × Bool | u.1 = true})
      apply MeasurableSet.pi Set.countable_univ
      intro i hi
      exact measurableSet_eq_fun measurable_fst measurable_const
    have hmeasB : MeasurableSet B := by
      change MeasurableSet (Set.univ.pi fun _ : Fin N => {u : Bool × Bool | u.1 = false})
      apply MeasurableSet.pi Set.countable_univ
      intro i hi
      exact measurableSet_eq_fun measurable_fst measurable_const
    rw [hset, MeasureTheory.measure_union hdisj hmeasB,
      SAP.P018a.WH.W2.P.T7_L1.constant_first_measure,
      SAP.P018a.WH.W2.P.T7_L1.constant_first_measure]
    have hreal : (2 : ℝ) * (1 / 2 : ℝ)^N =
        (2 : ℝ) / (2 : ℝ)^N := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow, div_eq_mul_inv]
    have hp : (1 / 2 : ENNReal)^N = ENNReal.ofReal ((1 / 2 : ℝ)^N) := by
      have hh : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [hh, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [hp, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply congrArg ENNReal.ofReal
    nlinarith [hreal]
