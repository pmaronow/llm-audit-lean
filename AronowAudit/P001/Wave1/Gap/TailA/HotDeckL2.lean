import AronowAudit.P001.Wave1.Lib.TailA.ReuseMoments

/-! Fourth fair-sign moments for the hot-deck bootstrap. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace AronowAudit.P001.Wave1.TailA
open AronowAudit.P001.TailA
local instance instDecidableHotDeckL2 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Integrating one fair sign cancels the odd powers, with its original coefficient. -/
theorem hotdeck_one_sign_fourth (c x : ℝ) :
    (∫ b, (c*noise b+x)^4 ∂matchingFairSign) = c^4+6*c^2*x^2+x^4 := by
  rw [integral_fintype Integrable.of_finite,Fintype.sum_bool]
  norm_num [matchingFairSign,Wave1.t14_signLaw,measureReal_def,
    Measure.add_apply,Measure.smul_apply,noise]
  <;> ring

/-- The fourth moment of independent original-label signs, with arbitrary real weights. -/
theorem hotdeck_sign_fourth (n : ℕ) (c : Fin n → ℝ) :
    mean (signProductLaw n) (fun e => (∑ j, c j*noise (e j))^4) ≤
      3*(∑ j, (c j)^2)^2 := by
  induction n with
  | zero => simp [mean]
  | succ n ih =>
    let S (e : Fin n → Bool) : ℝ := ∑ j, c j.succ*noise (e j)
    have hsplit : mean (signProductLaw (n+1)) (fun e => (∑ j, c j*noise (e j))^4) =
        ∫ e : Fin n → Bool, ∫ b : Bool, (c 0*noise b+S e)^4
          ∂matchingFairSign ∂signProductLaw n := by
      unfold mean
      change (∫ e, (∑ j, c j*noise (e j))^4
        ∂Measure.pi (fun _ : Fin (n+1) => matchingFairSign)) = _
      rw [← ((measurePreserving_piFinSuccAbove
        (fun _ : Fin (n+1) => matchingFairSign) 0).symm).integral_comp']
      simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.sum_univ_succ,Fin.insertNth_zero,Fin.cons_zero,Fin.cons_succ]
      exact integral_prod_symm _ Integrable.of_finite
    rw [hsplit]
    simp_rw [hotdeck_one_sign_fourth]
    rw [integral_add Integrable.of_finite Integrable.of_finite,
      integral_add Integrable.of_finite Integrable.of_finite,integral_const,
      integral_const_mul]
    have hS : (∫ e, S e^2 ∂signProductLaw n) = ∑ j : Fin n, (c j.succ)^2 :=
      Wave1.t14_weighted_second n (fun j => c j.succ)
    rw [hS]
    simp only [probReal_univ,smul_eq_mul,one_mul,Fin.sum_univ_succ]
    have hi := ih (fun j => c j.succ)
    change (∫ e, S e^4 ∂signProductLaw n) ≤ 3*(∑ j : Fin n, (c j.succ)^2)^2 at hi
    nlinarith [sq_nonneg ((c 0)^2)]

/-- Finite Jensen for a square, under any finite probability law. -/
theorem hotdeck_mean_square_le {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsProbabilityMeasure μ] (f : A → ℝ) :
    (mean μ f)^2 ≤ mean μ (fun a => (f a)^2) := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub (show MemLp f 2 μ from MemLp.of_discrete)] at h
  exact sub_nonneg.mp h

/-- Centering a finite bootstrap variance can only decrease its fourth-moment bound. -/
theorem hotdeck_bootvar_square_le {n : ℕ} (T : (Fin n → MatchUnit) → ℝ)
    (z : Fin n → MatchUnit) (c : ℝ) :
    (bootVar T z)^2 ≤ mean (UniformResampling n) (fun a => (T (resample z a)-c)^4) := by
  let f (a : Fin n → Fin n) : ℝ := T (resample z a)
  have hmean : mean (UniformResampling n) f = bootMean T z := by
    rw [uniform_resampling_mean]
    rfl
  have hvar : variance f (UniformResampling n) = bootVar T z := by
    rw [variance_eq_integral (Measurable.of_discrete (f := f)).aemeasurable]
    change mean (UniformResampling n) (fun a => (f a-mean (UniformResampling n) f)^2) = _
    rw [hmean,uniform_resampling_mean]
    rfl
  have hle : bootVar T z ≤ mean (UniformResampling n) (fun a => (f a-c)^2) := by
    rw [← hvar,← variance_sub_const (Measurable.of_discrete (f := f)).aestronglyMeasurable c]
    exact variance_le_expectation_sq Measurable.of_discrete.aestronglyMeasurable
  have hnonneg : 0 ≤ bootVar T z := hvar ▸ variance_nonneg f _
  calc
    _ ≤ (mean (UniformResampling n) (fun a => (f a-c)^2))^2 :=
      pow_le_pow_left₀ hnonneg hle 2
    _ ≤ _ := by
      have hj := hotdeck_mean_square_le (UniformResampling n) (fun a => (f a-c)^2)
      have heq : (fun a : Fin n → Fin n => ((f a-c)^2)^2) = fun a => (f a-c)^4 := by
        funext a
        ring
      change (mean (UniformResampling n) (fun a => (f a-c)^2))^2 ≤
        mean (UniformResampling n) (fun a => ((f a-c)^2)^2) at hj
      rw [heq] at hj
      exact hj

/-- Copies of an original donor retain a single original sign in the linear statistic. -/
theorem hotdeck_bootstrap_linear {n : ℕ} (hn : 0 < n) (d : Fin n → MatchingDesign)
    (e : Fin n → Bool) (a : Fin n → Fin n) :
    hotDeck (resample (matchingAssemble d e) a)-50 =
      (∑ j, bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) a j * noise (e j))/(n : ℝ) := by
  rw [Wave1.t14_weight_regrouping hn]
  congr 1
  simp only [bootstrapOriginalReuse,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rfl

/-- The original-sign fourth bound for each bootstrap draw. -/
theorem hotdeck_bootstrap_sign_fourth {n : ℕ} (hn : 0 < n)
    (d : Fin n → MatchingDesign) (a : Fin n → Fin n) :
    mean (signProductLaw n) (fun e =>
      (hotDeck (resample (matchingAssemble d e) a)-50)^4) ≤
      3*(∑ j, (bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) a j)^4)/(n : ℝ)^3 := by
  simp_rw [hotdeck_bootstrap_linear hn,div_pow]
  rw [mean,integral_div]
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsign := hotdeck_sign_fourth n
    (fun j => bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) a j)
  have hsum := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n))
    (fun _ => (1 : ℝ))
    (fun j => (bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) a j)^2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,← pow_mul] at hsum
  have hbound : mean (signProductLaw n) (fun e =>
      (∑ j, bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) a j*noise (e j))^4) ≤
        3*(n : ℝ)*∑ j, (bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) a j)^4 := by
    nlinarith
  apply (div_le_iff₀ (pow_pos hnR 4)).mpr
  calc
    _ ≤ 3*(n : ℝ)*∑ j, (bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) a j)^4 := hbound
    _ = _ := by field_simp

/-- Conditional L2 control using fourth moments of aggregated original-label reuse. -/
theorem hotdeck_conditional_l2 {n : ℕ} (hn : 0 < n) (d : Fin n → MatchingDesign) :
    mean (signProductLaw n) (fun e => ((n : ℝ)*bootVar hotDeck (matchingAssemble d e))^2) ≤
      (3/(n : ℝ))*∑ j, reuseBootstrapMoment 4 (fun i => (d i).1) (fun i => (d i).2) j := by
  let Q (e : Fin n → Bool) (a : Fin n → Fin n) : ℝ :=
    (hotDeck (resample (matchingAssemble d e) a)-50)^4
  have hpoint (e : Fin n → Bool) :
      ((n : ℝ)*bootVar hotDeck (matchingAssemble d e))^2 ≤
        (n : ℝ)^2*mean (UniformResampling n) (Q e) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (hotdeck_bootvar_square_le hotDeck _ 50) (sq_nonneg _)
  have hsign (a : Fin n → Fin n) := hotdeck_bootstrap_sign_fourth hn d a
  calc
    _ ≤ mean (signProductLaw n) (fun e => (n : ℝ)^2*mean (UniformResampling n) (Q e)) :=
      integral_mono Integrable.of_finite Integrable.of_finite hpoint
    _ = (n : ℝ)^2*mean (UniformResampling n) (fun a => mean (signProductLaw n) (fun e => Q e a)) := by
      simp only [mean]
      rw [integral_const_mul,integral_integral_swap Integrable.of_finite]
    _ ≤ (n : ℝ)^2*mean (UniformResampling n) (fun a =>
        3*(∑ j, (bootstrapOriginalReuse (fun i => (d i).1) (fun i => (d i).2) a j)^4)/(n : ℝ)^3) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact integral_mono Integrable.of_finite Integrable.of_finite hsign
    _ = _ := by
      simp only [mean,integral_div,integral_const_mul,
        integral_finsetSum _ (fun _ _ => Integrable.of_finite),reuseBootstrapMoment]
      have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
      field_simp
      <;> ring

/-- Population L2 control, with its sole moment input stated explicitly. -/
theorem hotdeck_product_l2_of_fourth {n : ℕ} (hn : 0 < n) {C : ℝ}
    (hC : 0 ≤ C) (hU : ∀ j : Fin n,
      mean (MatchProduct n) (fun z => mean (UniformResampling n) (fun a => (U z a j)^4)) ≤ C) :
    mean (MatchProduct n) (fun z => ((n : ℝ)*bootVar hotDeck z)^2) ≤ 3*C := by
  let F (z : Fin n → MatchUnit) : ℝ := ((n : ℝ)*bootVar hotDeck z)^2
  let G (z : Fin n → MatchUnit) : ℝ :=
    (3/(n : ℝ))*∑ j, reuseBootstrapMoment 4 (fun i => (z i).1) (fun i => (z i).2.1) j
  let g (d : Fin n → MatchingDesign) : ℝ :=
    (3/(n : ℝ))*∑ j, reuseBootstrapMoment 4 (fun i => (d i).1) (fun i => (d i).2) j
  have hFm : Measurable F := (measurable_const.mul
    (matching_bootVar_measurable (matching_hotDeck_measurable n))).pow_const 2
  have hFi : Integrable F (MatchProduct n) :=
    ((matching_bootVar_memLp (MatchProduct n) (matching_hotDeck_measurable n) 51
      matching_hotDeck_bound 2).const_mul (n : ℝ)).integrable_sq
  have hGm : Measurable G := measurable_const.mul
    (Finset.measurable_sum _ (fun j _ => reuse_bootstrap_moment_measurable 4 j))
  have hGi : Integrable G (MatchProduct n) :=
    (integrable_finsetSum _ (fun j _ => reuse_bootstrap_moment_integrable _ 4 j)).const_mul _
  have hGinner (d : Fin n → MatchingDesign) :
      mean (signProductLaw n) (fun e => G (matchingAssemble d e)) = g d := by
    simp only [G,g,matchingAssemble,mean,integral_const,probReal_univ,smul_eq_mul,one_mul]
  have hgi : Integrable g (MatchingDesignProduct n) := by
    have hi := ((matching_sign_factorization n).integrable_comp_of_integrable hGi).integral_prod_left
    change Integrable (fun d => mean (signProductLaw n)
      (fun e => G (matchingAssemble d e))) (MatchingDesignProduct n) at hi
    simpa only [hGinner] using hi
  have hGexpect : mean (MatchProduct n) G = mean (MatchingDesignProduct n) g := by
    rw [matching_sign_expectation hGm hGi]
    simp only [hGinner]
  have hnonneg (d : Fin n → MatchingDesign) :
      0 ≤ mean (signProductLaw n) (fun e => F (matchingAssemble d e)) :=
    integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ = mean (MatchingDesignProduct n) (fun d =>
      mean (signProductLaw n) (fun e => F (matchingAssemble d e))) :=
        matching_sign_expectation hFm hFi
    _ ≤ mean (MatchingDesignProduct n) g :=
      integral_mono_of_nonneg (ae_of_all _ hnonneg) hgi
        (ae_of_all _ (hotdeck_conditional_l2 hn))
    _ = mean (MatchProduct n) G := hGexpect.symm
    _ = (3/(n : ℝ))*∑ j, mean (MatchProduct n)
        (fun z => reuseBootstrapMoment 4 (fun i => (z i).1) (fun i => (z i).2.1) j) := by
      simp only [mean,G,integral_const_mul,
        integral_finsetSum _ (fun j _ => reuse_bootstrap_moment_integrable _ 4 j)]
    _ ≤ (3/(n : ℝ))*∑ _j : Fin n, C := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun j _ => hU j)
    _ = 3*C := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      field_simp

/-- The scaled bootstrap variance has a uniform population second moment. -/
theorem hot_deck_bootstrap_uniform_second_moment_final :
    (∀ {Ω : Type*}
      [MeasurableSpace Ω]
      (μ : Measure Ω)
      [IsProbabilityMeasure μ]
      (Z : ℕ → Ω → ℝ × Bool × Bool)
      (hiid : IID μ Z)
      (hlaw : μ.map (Z 0)=matchingUnitLaw),
      ∃ C : ℝ,0 ≤ C ∧ ∀ n : ℕ,
     mean μ (fun ω => ((n : ℝ)*bootVar hotDeck (firstSample Z n ω))^2) ≤ C) := by
  intro Ω _ μ _ Z hiid hlaw
  obtain ⟨C,hC,hMom,_hPinned⟩ := uniform_reuse_fourth_moments
  refine ⟨3*C,by positivity,?_⟩
  intro n
  have hmeas : Measurable (fun z : Fin n → MatchUnit => ((n : ℝ)*bootVar hotDeck z)^2) :=
    (measurable_const.mul (matching_bootVar_measurable (matching_hotDeck_measurable n))).pow_const 2
  rw [matching_expectation μ Z hiid hlaw n hmeas]
  by_cases hn : 0 < n
  · exact hotdeck_product_l2_of_fourth hn hC.le (fun j => (hMom n j).2)
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    simp only [Nat.cast_zero,zero_mul,zero_pow (by decide : 2 ≠ 0),mean,integral_zero]
    positivity

end AronowAudit.P001.Wave1.TailA
