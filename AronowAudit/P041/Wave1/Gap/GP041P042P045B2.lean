import AronowAudit.P042.P042_Turnout
import AronowAudit.P045.P045_Spillover
import AronowAudit.External.Causalean.Experimentation.FinitePopulationMoments

open scoped BigOperators
open Finset

noncomputable section

set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option exponentiation.threshold 1024

namespace AronowAudit.P042.Wave1

/-- Regroup the two bounded treatment counts by their sum. -/
lemma coverage_treatment_pushforward (f : ℕ → ℚ) :
    (∑ a ∈ range 101, ∑ b ∈ range 101,
      (Nat.choose 100 a : ℚ) * Nat.choose 100 b * f (a+b)) =
    ∑ t ∈ range 201, (Nat.choose 200 t : ℚ) * f t := by
  classical
  rw [← Finset.sum_product (f := fun p : ℕ × ℕ =>
    (Nat.choose 100 p.1 : ℚ) * Nat.choose 100 p.2 * f (p.1+p.2))]
  calc
    _ = ∑ t ∈ range 201, ∑ p ∈ (range 101 ×ˢ range 101).filter
        (fun p : ℕ × ℕ => p.1+p.2=t),
        (Nat.choose 100 p.1 : ℚ) * Nat.choose 100 p.2 * f (p.1+p.2) := by
      symm
      apply Finset.sum_fiberwise_of_maps_to
      intro p hp
      simp only [mem_product, mem_range] at hp ⊢
      omega
    _ = ∑ t ∈ range 201, (Nat.choose 200 t : ℚ) * f t := by
      apply sum_congr rfl
      intro t ht
      have he : ((range 101 ×ˢ range 101).filter (fun p : ℕ × ℕ => p.1+p.2=t)) ⊆
          Finset.HasAntidiagonal.antidiagonal t := by
        intro p hp
        simpa only [Finset.HasAntidiagonal.mem_antidiagonal] using (mem_filter.mp hp).2
      calc
        _ = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal t,
            (Nat.choose 100 p.1 : ℚ) * Nat.choose 100 p.2 * f (p.1+p.2) := by
          apply sum_subset he
          intro p hp hnot
          have hs : p.1+p.2=t := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
          have hout : 100 < p.1 ∨ 100 < p.2 := by
            simp only [mem_filter, mem_product, mem_range, hs, and_true] at hnot
            omega
          rcases hout with h | h <;> simp [Nat.choose_eq_zero_of_lt h]
        _ = (∑ p ∈ Finset.HasAntidiagonal.antidiagonal t,
            (Nat.choose 100 p.1 : ℚ) * Nat.choose 100 p.2) * f t := by
          rw [sum_mul]
          apply sum_congr rfl
          intro p hp
          rw [Finset.HasAntidiagonal.mem_antidiagonal.mp hp]
        _ = _ := by
          have h : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal t,
              (Nat.choose 100 p.1 : ℚ) * Nat.choose 100 p.2) = (Nat.choose 200 t : ℚ) := by
            exact_mod_cast (Nat.add_choose_eq 100 100 t).symm
          rw [h]

lemma coverage_event_interval (x t r : ℕ) (ht : t ≤ 200) :
    |(t : ℤ)-2*(x : ℤ)| ≤ (r : ℤ) ↔
      t ∈ Icc (2*x-r) (min 200 (2*x+r)) := by
  rw [abs_le, mem_Icc, le_min_iff]
  omega

lemma coverage_inner (x r : ℕ) :
    (∑ a : Fin 101, binomialMass 100 a *
      ∑ b : Fin 101, binomialMass 100 b *
        (if |(a.val : ℤ)+(b.val : ℤ)-2*(x : ℤ)| ≤ (r : ℤ) then 1 else 0)) =
    (∑ t ∈ Icc (2*x-r) (min 200 (2*x+r)), (exactChoose 200 t : ℚ)) / 2^200 := by
  classical
  simp only [binomialMass, exactChoose_eq]
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ =>
    (Nat.choose 100 a : ℚ)/2^100 * ∑ b : Fin 101,
      (Nat.choose 100 b.val : ℚ)/2^100 *
        (if |(a : ℤ)+(b.val : ℤ)-2*(x : ℤ)| ≤ (r : ℤ) then 1 else 0)) 101]
  have hb (a : ℕ) := Fin.sum_univ_eq_sum_range (fun b : ℕ =>
    (Nat.choose 100 b : ℚ)/2^100 *
      (if |(a : ℤ)+(b : ℤ)-2*(x : ℤ)| ≤ (r : ℤ) then (1 : ℚ) else 0)) 101
  simp_rw [hb]
  have hf (a b : ℕ) :
      (Nat.choose 100 a : ℚ)/2^100 * ((Nat.choose 100 b : ℚ)/2^100 *
        (if |(a : ℤ)+(b : ℤ)-2*(x : ℤ)| ≤ (r : ℤ) then 1 else 0)) =
      ((Nat.choose 100 a : ℚ)*Nat.choose 100 b *
        (if |((a+b : ℕ) : ℤ)-2*(x : ℤ)| ≤ (r : ℤ) then 1 else 0))/2^200 := by
    push_cast
    norm_num [div_eq_mul_inv] <;> ring
  simp_rw [mul_sum, hf, ← sum_div]
  rw [coverage_treatment_pushforward (fun t : ℕ =>
    if |(t : ℤ)-2*(x : ℤ)| ≤ (r : ℤ) then (1 : ℚ) else 0)]
  congr 1
  calc
    _ = ∑ t ∈ (range 201).filter (fun t => t ∈ Icc (2*x-r) (min 200 (2*x+r))),
        (Nat.choose 200 t : ℚ) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro t ht
      have he := coverage_event_interval x t r (by simpa using Nat.le_of_lt_succ (mem_range.mp ht))
      by_cases h : |(t : ℤ)-2*(x : ℤ)| ≤ (r : ℤ)
      · simp [h, he.mp h]
      · simp [h, show t ∉ Icc (2*x-r) (min 200 (2*x+r)) from fun hi => h (he.mpr hi)]
    _ = _ := by
      congr 1
      ext t
      simp only [mem_filter, mem_range, mem_Icc, le_min_iff]
      omega

theorem binomial_coverage_from_arms_proof (r : ℕ) :
    binomialTripleExpectation (fun x0 x1 x2 =>
      if |(x1.val:ℤ)+(x2.val:ℤ)-2*(x0.val:ℤ)| ≤ (r:ℤ) then 1 else 0) =
      binomialCoverage r := by
  classical
  unfold binomialTripleExpectation
  have hi (x0 : Fin 101) := coverage_inner x0.val r
  simp_rw [hi]
  simp only [binomialMass]
  have hf (x : Fin 101) :
      (exactChoose 100 x.val : ℚ)/2^100 *
          ((∑ t ∈ Icc (2*x.val-r) (min 200 (2*x.val+r)), (exactChoose 200 t : ℚ))/2^200) =
      ((exactChoose 100 x.val : ℚ)*
          ∑ t ∈ Icc (2*x.val-r) (min 200 (2*x.val+r)), (exactChoose 200 t : ℚ))/2^300 := by
    norm_num [div_eq_mul_inv] <;> ring
  simp_rw [hf]
  rw [← sum_div, Fin.sum_univ_eq_sum_range (fun x : ℕ =>
    (exactChoose 100 x : ℚ)*∑ t ∈ Icc (2*x-r) (min 200 (2*x+r)),
      (exactChoose 200 t : ℚ)) 101]
  simp only [binomialCoverage, coverageCount, Nat.cast_sum, Nat.cast_mul]

end AronowAudit.P042.Wave1

namespace AronowAudit.P045.Wave1

open Causalean.Experimentation.DesignBased

lemma singleton_cr_bridge {G C : ℕ} (hCG : C ≤ G) (F : Finset (Fin G) → ℝ) :
    (completeRandomization (V := Fin G) C (by simpa using hCG)).E (fun S => F S.val) =
      average (firstStageSets G C) F := by
  classical
  have hs : (∑ S : {S : Finset (Fin G) // S.card=C}, F S.val) =
      ∑ S ∈ firstStageSets G C, F S := by
    apply sum_bij (fun S _ => S.val)
    · intro S _
      simp [firstStageSets, S.property]
    · intro S _ T _ h
      exact Subtype.ext h
    · intro S hS
      exact ⟨⟨S, (mem_powersetCard.mp hS).2⟩, mem_univ _, rfl⟩
    · intro S _
      rfl
  simp only [FiniteDesign.E, completeRandomization, ← mul_sum]
  rw [hs]
  simp [average, firstStageSets, completeRandomization_card, div_eq_mul_inv, mul_comm]

/-- Sampling variation cancels between the between-group term and squared error. -/
lemma singleton_firststage_identity {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (X : Fin G → ℝ) (c : ℝ) :
    average (firstStageSets G C) (fun H =>
      ((1-(C : ℝ)/G)/C)*rawSampleVar H X - (average H X-c)^2) =
      -(mean X-c)^2 := by
  classical
  have hCp : 0 < C := by omega
  have hGp : 0 < G := by omega
  have hCn : (C : ℝ) ≠ 0 := by positivity
  have hGn : (G : ℝ) ≠ 0 := by positivity
  have hCd : (C : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ C := by exact_mod_cast hC
    linarith
  have hGd : (G : ℝ)-1 ≠ 0 := by
    have : (2 : ℝ) ≤ G := by exact_mod_cast (show 2 ≤ G by omega)
    linarith
  let D := completeRandomization (V := Fin G) C (by simpa using hCG)
  let Y : {S : Finset (Fin G) // S.card=C} → ℝ := fun S => average S.val X
  have hY : Causalean.Experimentation.FinitePopulationMoments.sampleMean C X = Y := by
    funext S
    simp [Causalean.Experimentation.FinitePopulationMoments.sampleMean, Y, average,
      S.property, sum_ite, filter_mem_eq_inter]
  have hm : D.E Y = mean X := by
    have h := Causalean.Experimentation.FinitePopulationMoments.E_sampleMean
      (U := Fin G) C (by simpa using hCG) hCp X
    rw [hY] at h
    exact h
  have hv : D.Var Y = ((1-(C : ℝ)/G)/C)*popVar X := by
    have h := Causalean.Experimentation.FinitePopulationMoments.Var_sampleMean
      (U := Fin G) C (by simpa using hCG) hCp (by simpa using (show 2 ≤ G by omega)) X
    rw [hY] at h
    have hp : Causalean.Experimentation.FinitePopulationMoments.popVar X = popVar X := by
      simp [Causalean.Experimentation.FinitePopulationMoments.popVar,
        Causalean.Experimentation.FinitePopulationMoments.popMean,
        popVar, rawSampleVar, average]
    rw [hp] at h
    change D.Var Y = _ at h
    rw [h]
    simp only [Fintype.card_fin]
    field_simp
    <;> ring
  have hz : D.E (fun S => (Y S-mean X)^2) = ((1-(C : ℝ)/G)/C)*popVar X := by
    simpa only [FiniteDesign.Var, hm] using hv
  have hsum : D.E (fun S => ∑ g ∈ S.val, (X g-mean X)^2) =
      (C : ℝ)*((G : ℝ)-1)/G*popVar X := by
    rw [singleton_cr_bridge hCG (fun H => ∑ g ∈ H, (X g-mean X)^2)]
    have hu := uniform_first_stage_mean hCp hCG (fun g => (X g-mean X)^2)
    have ha : average (firstStageSets G C) (fun H => (∑ g ∈ H, (X g-mean X)^2)/C) =
        average (firstStageSets G C) (fun H => ∑ g ∈ H, (X g-mean X)^2)/C := by
      simp [average, sum_div, div_div, mul_comm, mul_assoc]
    rw [ha] at hu
    have hp : mean (fun g => (X g-mean X)^2) = ((G : ℝ)-1)/G*popVar X := by
      simp only [mean, popVar, rawSampleVar, average, card_univ, Fintype.card_fin]
      field_simp
      <;> simp only [mul_comm]
    rw [hp] at hu
    apply (div_eq_iff hCn).mp at hu
    rw [hu]
    ring
  have hr : D.E (fun S => rawSampleVar S.val X) = popVar X := by
    have he : (fun S : {S : Finset (Fin G) // S.card=C} => rawSampleVar S.val X) =
        fun S => ((∑ g ∈ S.val, (X g-mean X)^2) - C*(Y S-mean X)^2)/((C : ℝ)-1) := by
      funext S
      rw [raw_sample_variance_centered S.val (by rw [S.property]; omega) X (mean X)]
      simp only [S.property, Y]
    rw [he]
    simp only [div_eq_mul_inv, D.E_mul_const, D.E_sub, D.E_const_mul]
    rw [hsum, hz]
    field_simp
    <;> ring
  have hc : D.E (fun S => (Y S-c)^2) =
      ((1-(C : ℝ)/G)/C)*popVar X+(mean X-c)^2 := by
    have he : (fun S => (Y S-c)^2) = fun S => (Y S)^2 + (-2*c)*Y S+c^2 := by
      funext S
      ring
    rw [he, D.E_add, D.E_add, D.E_const_mul, D.E_const, hm]
    have hsq := D.Var_eq Y
    rw [hm, hv] at hsq
    linarith
  rw [← singleton_cr_bridge hCG]
  change D.E (fun S => ((1-(C : ℝ)/G)/C)*rawSampleVar S.val X-(Y S-c)^2) = _
  rw [D.E_sub, D.E_const_mul, hr, hc]
  ring

/-- A heterogeneous centered product sum has only diagonal second moments. -/
lemma singleton_centered_sum {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (q : Ω → ℝ) (hq : ∑ z, q z=1) (X : I → Ω → ℝ) :
    expect (fun w : I → Ω => ∏ g, q (w g))
      (fun w => (∑ g, (X g (w g)-expect q (X g)))^2) = ∑ g, variance q (X g) := by
  classical
  let Z := fun g z => X g z-expect q (X g)
  have hz (g : I) : expect q (Z g)=0 := by
    simp [Z, expect, mul_sub, sum_sub_distrib, ← sum_mul, hq]
  have hp (g h : I) : expect (fun w : I → Ω => ∏ j, q (w j))
      (fun w => Z g (w g)*Z h (w h)) = if g=h then variance q (X g) else 0 := by
    by_cases he : g=h
    · subst h
      simpa [variance, Z, pow_two] using
        independent_coordinate_expect (fun _ : I => q) (fun _ => hq) g
          (fun w => (X g w-expect q (X g))*(X g w-expect q (X g)))
    · rw [independent_pair_expect q hq g h he, hz]
      simp [he]
  have hpoly (w : I → Ω) : (∑ g, Z g (w g))^2 = ∑ g, ∑ h, Z g (w g)*Z h (w h) := by
    simp only [pow_two, sum_mul, mul_sum]
    exact sum_comm
  change expect (fun w : I → Ω => ∏ g, q (w g)) (fun w => (∑ g, Z g (w g))^2) = _
  simp_rw [hpoly]
  rw [expect_finset_sum]
  simp_rw [expect_finset_sum, hp]
  simp

lemma singleton_selected_swap {G n C : ℕ} (q : Assignment n → ℝ)
    (F : Finset (Fin G) × (Fin G → Assignment n) → ℝ) :
    expect (selectedLaw (fun _ : Fin G => n) C (fun _ => q)) F =
      expect (fun w : Fin G → Assignment n => ∏ g, q (w g))
        (fun w => average (firstStageSets G C) (fun H => F (H,w))) := by
  rw [selected_expect_average]
  simp only [average, expect, sum_div, mul_div_assoc, mul_sum]
  rw [sum_comm]

/-- The bias of the actual two-stage formula depends only on local W minus V. -/
lemma singleton_selected_bias {G C n : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (q : Assignment n → ℝ) (hq : ∑ z, q z=1) (a b : Fin G → Fin n → ℝ) :
    expect (selectedLaw (fun _ : Fin G => n) C (fun _ => q)) (directVarianceEstimate C a b) -
      variance (selectedLaw (fun _ : Fin G => n) C (fun _ => q))
        (selectedMean C (fun g => directGroup (a g) (b g))) =
      (∑ g, (expect q (droppedWithin (a g) (b g))-variance q (directGroup (a g) (b g))))/(G : ℝ)^2 := by
  classical
  have hCp : 0 < C := by omega
  have hGp : 0 < G := by omega
  have hCn : (C : ℝ) ≠ 0 := by positivity
  have hGn : (G : ℝ) ≠ 0 := by positivity
  let X := fun g => directGroup (a g) (b g)
  let μ := mean (fun g => expect q (X g))
  let P := fun w : Fin G → Assignment n => ∏ g, q (w g)
  let law := selectedLaw (fun _ : Fin G => n) C (fun _ => q)
  have hm : expect law (selectedMean C X)=μ := selected_mean_expect hCp hCG _ _ (fun _ => hq) X
  have he : expect law (directVarianceEstimate C a b) - variance law (selectedMean C X) =
      expect P (fun w => -(mean (fun g => X g (w g))-μ)^2 +
        mean (fun g => droppedWithin (a g) (b g) (w g))/(G : ℝ)) := by
    unfold variance
    rw [hm, ← expect_sub, singleton_selected_swap]
    apply congrArg (expect P)
    funext w
    have hc (H : Finset (Fin G)) (hH : H ∈ firstStageSets G C) : H.card=C :=
      (mem_powersetCard.mp hH).2
    have hh : average (firstStageSets G C) (fun H =>
        directVarianceEstimate C a b (H,w)-(selectedMean C X (H,w)-μ)^2) =
        average (firstStageSets G C) (fun H =>
          ((1-(C : ℝ)/G)/C)*rawSampleVar H (fun g => X g (w g)) -
            (average H (fun g => X g (w g))-μ)^2) +
          average (firstStageSets G C) (fun H =>
            ((∑ g ∈ H, droppedWithin (a g) (b g) (w g))/C)/G) := by
      rw [show (average (firstStageSets G C) (fun H =>
          ((1-(C : ℝ)/G)/C)*rawSampleVar H (fun g => X g (w g)) -
            (average H (fun g => X g (w g))-μ)^2) +
          average (firstStageSets G C) (fun H =>
            ((∑ g ∈ H, droppedWithin (a g) (b g) (w g))/C)/G)) =
        average (firstStageSets G C) (fun H =>
          (((1-(C : ℝ)/G)/C)*rawSampleVar H (fun g => X g (w g)) -
            (average H (fun g => X g (w g))-μ)^2) +
            ((∑ g ∈ H, droppedWithin (a g) (b g) (w g))/C)/G) by
          simp [average, sum_add_distrib, add_div]]
      unfold average
      congr 1
      apply sum_congr rfl
      intro H hH
      simp only [directVarianceEstimate, selectedMean, average, hc H hH, X]
      ring
    rw [hh, singleton_firststage_identity hC hCG]
    have hu := uniform_first_stage_mean hCp hCG (fun g => droppedWithin (a g) (b g) (w g))
    have hd : average (firstStageSets G C) (fun H =>
        ((∑ g ∈ H, droppedWithin (a g) (b g) (w g))/C)/G) =
        average (firstStageSets G C) (fun H =>
          (∑ g ∈ H, droppedWithin (a g) (b g) (w g))/C)/G := by
      simp [average, sum_div, div_div, mul_comm, mul_assoc]
    rw [hd, hu]
  rw [he, expect_add]
  have hv : expect P (fun w => -(mean (fun g => X g (w g))-μ)^2) =
      -(∑ g, variance q (X g))/(G : ℝ)^2 := by
    have hp (w : Fin G → Assignment n) : -(mean (fun g => X g (w g))-μ)^2 =
        -((∑ g, (X g (w g)-expect q (X g)))^2)/(G : ℝ)^2 := by
      simp only [mean, μ, Fintype.card_fin, sum_sub_distrib]
      ring
    simp_rw [hp]
    rw [expect_div]
    have hn : expect P (fun w => -((∑ g, (X g (w g)-expect q (X g)))^2)) =
        -expect P (fun w => (∑ g, (X g (w g)-expect q (X g)))^2) := by
      simp [expect, mul_neg, sum_neg_distrib]
    rw [hn, singleton_centered_sum q hq X]
  rw [hv, expect_div, expect_mean]
  dsimp only [P]
  simp_rw [independent_coordinate_expect (fun _ : Fin G => q) (fun _ => hq)]
  simp only [mean, Fintype.card_fin, sum_sub_distrib, X]
  ring

end AronowAudit.P045.Wave1

namespace AronowAudit.P045.Wave1

lemma singleton_local_bias (a b : Fin 3 → ℝ) :
    expect (crMass 3 2) (droppedWithin a b)-variance (crMass 3 2) (directGroup a b) =
      popVar (fun i => a i-b i)/3-popVar b ∧
    expect (crMass 3 1) (droppedWithin a b)-variance (crMass 3 1) (directGroup a b) =
      popVar (fun i => a i-b i)/3-popVar a := by
  simp only [variance, cr_expect_average, fixed_three_supports.1, fixed_three_supports.2]
  norm_num [average, directGroup, droppedWithin, rawSampleVar, treatedSet, popVar,
    Fin.univ_succ, Fin.sum_univ_succ, Finset.filter_insert, Finset.filter_singleton,
    Finset.sdiff_singleton_eq_erase, Finset.sdiff_insert, Finset.erase_insert,
    Finset.erase_insert_of_ne]
  constructor <;> ring

theorem singleton_drop_bias_proof {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (a b : Fin G → Fin 3 → ℝ) :
    let n : Fin G → ℕ := fun _ => 3
    let bias := fun m : ℕ =>
      expect (selectedLaw n C (fun _ => crMass 3 m)) (directVarianceEstimate (n := n) C a b) -
      variance (selectedLaw n C (fun _ => crMass 3 m))
        (selectedMean (n := n) C (fun g : Fin G => directGroup (a g) (b g)))
    bias 2 = (Finset.sum (univ : Finset (Fin G)) (fun g =>
      popVar (fun i : Fin 3 => a g i-b g i)/3 - popVar (b g)))/(G : ℝ)^2 ∧
    bias 1 = (Finset.sum (univ : Finset (Fin G)) (fun g =>
      popVar (fun i : Fin 3 => a g i-b g i)/3 - popVar (a g)))/(G : ℝ)^2 := by
  dsimp only
  constructor
  · rw [singleton_selected_bias hC hCG (crMass 3 2) (cr_mass_probability (n := 3) (k := 2) (by norm_num)).2 a b]
    simp_rw [(singleton_local_bias _ _).1]
  · rw [singleton_selected_bias hC hCG (crMass 3 1) (cr_mass_probability (n := 3) (k := 1) (by norm_num)).2 a b]
    simp_rw [(singleton_local_bias _ _).2]

theorem singleton_drop_dilated_bias_proof {G C : ℕ} (hC : 2 ≤ C) (hCG : C ≤ G)
    (x : Fin G → Fin 3 → ℝ) :
    let n : Fin G → ℕ := fun _ => 3
    let bias := fun (m : ℕ) (a b : Fin G → Fin 3 → ℝ) =>
      expect (selectedLaw n C (fun _ => crMass 3 m)) (directVarianceEstimate (n := n) C a b) -
      variance (selectedLaw n C (fun _ => crMass 3 m))
        (selectedMean (n := n) C (fun g : Fin G => directGroup (a g) (b g)))
    bias 2 (fun g i => 2*x g i) (fun g i => (5/4)*x g i) =
      -(11/(8*(G : ℝ)^2))*(∑ g, popVar (x g)) ∧
    bias 1 (fun g i => (3/2)*x g i) x =
      -(13/(6*(G : ℝ)^2))*(∑ g, popVar (x g)) ∧
    ((∃ g i j, x g i ≠ x g j) →
      bias 2 (fun g i => 2*x g i) (fun g i => (5/4)*x g i) < 0 ∧
      bias 1 (fun g i => (3/2)*x g i) x < 0) := by
  classical
  dsimp only
  have hfirst := (singleton_drop_bias_proof hC hCG
    (fun g i => 2*x g i) (fun g i => (5/4)*x g i)).1
  have hsecond := (singleton_drop_bias_proof hC hCG (fun g i => (3/2)*x g i) x).2
  dsimp only at hfirst hsecond
  have hf (g : Fin G) :
      popVar (fun i => 2*x g i-(5/4)*x g i)/3-popVar (fun i => (5/4)*x g i) =
        -(11/8)*popVar (x g) := by
    have he : (fun i => 2*x g i-(5/4)*x g i) = fun i => (3/4)*x g i := by
      funext i
      ring
    rw [he, pop_var_scale, pop_var_scale]
    ring
  have hs (g : Fin G) :
      popVar (fun i => (3/2)*x g i-x g i)/3-popVar (fun i => (3/2)*x g i) =
        -(13/6)*popVar (x g) := by
    have he : (fun i => (3/2)*x g i-x g i) = fun i => (1/2)*x g i := by
      funext i
      ring
    rw [he, pop_var_scale, pop_var_scale]
    ring
  simp_rw [hf, ← mul_sum] at hfirst
  simp_rw [hs, ← mul_sum] at hsecond
  have he1 := hfirst.trans (by ring : _ = -(11/(8*(G : ℝ)^2))*(∑ g, popVar (x g)))
  have he2 := hsecond.trans (by ring : _ = -(13/(6*(G : ℝ)^2))*(∑ g, popVar (x g)))
  refine ⟨he1, he2, ?_⟩
  rintro ⟨g,i,j,hne⟩
  have hnonneg (g : Fin G) : 0 ≤ popVar (x g) := pop_var_nonnegative (by simp) (x g)
  have hpos : 0 < popVar (x g) := by
    apply lt_of_le_of_ne (hnonneg g)
    intro he
    exact hne ((pop_var_zero_iff_constant (by simp) (x g)).mp he.symm i j)
  have hsum : 0 < ∑ g, popVar (x g) :=
    sum_pos' (fun g _ => hnonneg g) ⟨g, mem_univ _, hpos⟩
  have hG : 0 < (G : ℝ) := by exact_mod_cast (show 0 < G by omega)
  rw [he1, he2]
  constructor <;> apply mul_neg_of_neg_of_pos _ hsum <;>
    apply neg_neg_of_pos <;> positivity

end AronowAudit.P045.Wave1
