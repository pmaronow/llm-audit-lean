import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectMomentLimits

/-! Exact finite decompositions and assembly of the three pinned limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectAssembly (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

def markedSingleTotal {n : ℕ} (p : ℝ) (K : ℕ → ℝ) (z : Fin n → MatchUnit) : ℝ :=
  ∑ i, markedRecipientCountTest p K z i

def markedPairTotal {n : ℕ} (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ) (z : Fin n → MatchUnit) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else markedRecipientPairCountTest p K z i j

theorem marked_single_total_integrable (n : ℕ) (p : ℝ) (K : ℕ → ℝ)
    (hK : ∀ c, |K c| ≤ 1) : Integrable (markedSingleTotal p K) (MatchProduct n) :=
  integrable_finsetSum _ (fun i _ => marked_recipient_count_test_integrable p K i (by norm_num) hK)

theorem marked_pair_total_integrable (n : ℕ) (p : ℝ) (K : ℕ → ℕ → ℕ → ℝ)
    (hK : ∀ a b c, |K a b c| ≤ 1) : Integrable (markedPairTotal p K) (MatchProduct n) := by
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  by_cases hij : i = j
  · simp only [if_pos hij]; exact integrable_const _
  · simp only [if_neg hij]
    exact marked_recipient_pair_test_integrable p K i j (by norm_num) hK

theorem marked_forbidden_union_count {n : ℕ} (p x y : ℝ) (z : Fin n → MatchUnit) :
    (markedForbiddenLabels p z x ∪ markedForbiddenLabels p z y).card =
      markedWindowCount (markedCloserDonors p x ∪ markedCloserDonors p y) z := by
  simp only [markedForbiddenLabels,← Finset.map_union,Finset.card_map,markedWindowCount]
  congr 1
  ext i
  simp only [Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,Set.mem_union]

/-- The conditional one-replica square separates its two diagonal terms. -/
theorem marked_direct_second_split (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit) :
    markedDirectSecond p z = 1+markedPairCoefficient (n+1)+
      2*(markedPairCoefficient (n+1)*markedSingleTotal p (fun c => markedDrawPower (n+1) c 2) z)+
      markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 1) z+
      markedPairCoefficient (n+1)*markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 2) z+
      markedPairCoefficient (n+1)*markedPairTotal p (fun _ _ c => markedRetainedDrawPower (n+1) c 2) z := by
  have hs : (∑ i, if (z i).2.1 = false then markedPairCoefficient (n+1)*markedDrawPower (n+1)
      ((markedForbiddenLabels p z (z i).1).card) 2 else 0) =
      markedPairCoefficient (n+1)*markedSingleTotal p (fun c => markedDrawPower (n+1) c 2) z := by
    rw [markedSingleTotal,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [marked_forbidden_count]
    by_cases h : (z i).2.1 = false <;> simp [markedRecipientCountTest,h]
  have he (i j : Fin n) :
      (if (z i).2.1 = false ∧ (z j).2.1 = false then
        (if i = j then markedRetainedDrawPower (n+1)
          ((markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card) 1 else 0)+
        markedPairCoefficient (n+1)*markedRetainedDrawPower (n+1)
          ((markedForbiddenLabels p z (z i).1 ∪ markedForbiddenLabels p z (z j).1).card) 2 else 0) =
      (if i = j then markedRecipientCountTest p (fun c => markedRetainedDrawPower (n+1) c 1) z i+
        markedPairCoefficient (n+1)*markedRecipientCountTest p (fun c => markedRetainedDrawPower (n+1) c 2) z i else 0)+
        markedPairCoefficient (n+1)*(if i = j then 0 else
          markedRecipientPairCountTest p (fun _ _ c => markedRetainedDrawPower (n+1) c 2) z i j) := by
    by_cases hij : i = j
    · subst j
      simp only [if_pos rfl,Finset.union_self,marked_forbidden_count]
      by_cases h : (z i).2.1 = false <;> simp [markedRecipientCountTest,h]
    · simp only [if_neg hij,marked_forbidden_union_count]
      by_cases h : (z i).2.1 = false ∧ (z j).2.1 = false
      all_goals simp [markedRecipientPairCountTest,h]
  unfold markedDirectSecond
  rw [hs]
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    ← Finset.mul_sum,markedSingleTotal,markedPairTotal]
  ring

/-- The conditional replica square has a separate same-recipient square. -/
theorem marked_direct_first_square_split (n : ℕ) (p : ℝ) (z : Fin n → MatchUnit) :
    (markedDirectFirst p z)^2 = 1+
      2*markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 1) z+
      markedSingleTotal p (fun c => (markedRetainedDrawPower (n+1) c 1)^2) z+
      markedPairTotal p (fun a b _ => markedRetainedDrawPower (n+1) a 1*markedRetainedDrawPower (n+1) b 1) z := by
  have hfirst : markedDirectFirst p z = 1+markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 1) z := by
    simp only [markedDirectFirst,markedSingleTotal,markedRecipientCountTest,marked_forbidden_count]
  have hsq (i : Fin n) : (markedRecipientCountTest p (fun c => markedRetainedDrawPower (n+1) c 1) z i)^2 =
      markedRecipientCountTest p (fun c => (markedRetainedDrawPower (n+1) c 1)^2) z i := by
    unfold markedRecipientCountTest
    split_ifs <;> simp
  have hprod (i j : Fin n) :
      markedRecipientCountTest p (fun c => markedRetainedDrawPower (n+1) c 1) z i*
        markedRecipientCountTest p (fun c => markedRetainedDrawPower (n+1) c 1) z j =
      markedRecipientPairCountTest p (fun a b _ => markedRetainedDrawPower (n+1) a 1*markedRetainedDrawPower (n+1) b 1) z i j := by
    unfold markedRecipientCountTest markedRecipientPairCountTest
    split_ifs <;> simp_all
  have hh := marked_sum_square_split (fun i =>
    markedRecipientCountTest p (fun c => markedRetainedDrawPower (n+1) c 1) z i)
  simp only [hsq,hprod] at hh
  rw [hfirst]
  change (1+markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 1) z)^2 = _
  change (markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 1) z)^2 =
    markedSingleTotal p (fun c => (markedRetainedDrawPower (n+1) c 1)^2) z+
      markedPairTotal p (fun a b _ => markedRetainedDrawPower (n+1) a 1*markedRetainedDrawPower (n+1) b 1) z at hh
  nlinarith [hh]

/-- Linearity for the finite, integrable components of each decomposition. -/
theorem marked_mean_finite_affine {E I : Type*} [MeasurableSpace E] [Fintype I]
    (μ : Measure E) [IsProbabilityMeasure μ] (c : ℝ) (a : I → ℝ) (F : I → E → ℝ)
    (hi : ∀ i, Integrable (F i) μ) :
    mean μ (fun z => c+∑ i, a i*F i z) = c+∑ i, a i*mean μ (F i) := by
  rw [mean,integral_add (integrable_const _) (integrable_finsetSum _ (fun i _ => (hi i).const_mul _)),
    integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,mean]

/-- The exact original second moment in terms of the proved recipient sums. -/
theorem marked_pinned_original_second_expansion (n : ℕ) (p : ℝ) :
    mean (MatchProduct n) (fun z => (W (pin n p z) 0)^2) =
      1+3*mean (MatchProduct n) (markedSingleTotal p (fun c => if c = 0 then 1 else 0))+
        mean (MatchProduct n) (markedPairTotal p (fun _ _ c => if c = 0 then 1 else 0)) := by
  have h1 (z : Fin n → MatchUnit) (i : Fin n) : markedOriginalRecipient p z i =
      markedRecipientCountTest p (fun c => if c = 0 then 1 else 0) z i := by
    simp only [markedOriginalRecipient,markedRecipientCountTest,marked_forbidden_count]
    split_ifs <;> simp_all
  have h2 (z : Fin n → MatchUnit) (i j : Fin n) : markedOriginalRecipientPair p z i j =
      markedRecipientPairCountTest p (fun _ _ c => if c = 0 then 1 else 0) z i j := by
    simp only [markedOriginalRecipientPair,markedRecipientPairCountTest,marked_forbidden_union_count]
    split_ifs <;> simp_all
  rw [marked_pinned_W_second_integral_direct]
  simp_rw [h1,h2]
  let F : Fin 2 → (Fin n → MatchUnit) → ℝ :=
    ![markedSingleTotal p (fun c => if c = 0 then 1 else 0),markedPairTotal p (fun _ _ c => if c = 0 then 1 else 0)]
  have hi (i : Fin 2) : Integrable (F i) (MatchProduct n) := by
    fin_cases i
    · exact marked_single_total_integrable n p _ (by intro c; split_ifs <;> norm_num)
    · exact marked_pair_total_integrable n p _ (by intro a b c; split_ifs <;> norm_num)
  simpa only [Fin.sum_univ_two,F,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul,
    markedSingleTotal,markedPairTotal,add_assoc] using marked_mean_finite_affine (MatchProduct n) 1 ![3,1] F hi

/-- Exact one-replica second moment, including both diagonal multiplicities. -/
theorem marked_pinned_bootstrap_second_expansion (n : ℕ) (p : ℝ) :
    mean (MatchProduct n) (fun z => mean (UniformResampling (n+1)) (fun a => (U (pin n p z) a 0)^2)) =
      1+markedPairCoefficient (n+1)+
      2*(markedPairCoefficient (n+1)*mean (MatchProduct n) (markedSingleTotal p (fun c => markedDrawPower (n+1) c 2)))+
      mean (MatchProduct n) (markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 1))+
      markedPairCoefficient (n+1)*mean (MatchProduct n) (markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 2))+
      markedPairCoefficient (n+1)*mean (MatchProduct n) (markedPairTotal p (fun _ _ c => markedRetainedDrawPower (n+1) c 2)) := by
  have hd (c : ℕ) : |markedDrawPower (n+1) c 2| ≤ 1 := by
    rw [abs_of_nonneg (marked_draw_power_bounds _ _ _).1]; exact (marked_draw_power_bounds _ _ _).2
  have hr (c k : ℕ) : |markedRetainedDrawPower (n+1) c k| ≤ 1 := by
    rw [abs_of_nonneg (marked_retained_draw_power_bounds _ _ _).1]; exact (marked_retained_draw_power_bounds _ _ _).2
  let F : Fin 4 → (Fin n → MatchUnit) → ℝ :=
    ![markedSingleTotal p (fun c => markedDrawPower (n+1) c 2),
      markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 1),
      markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 2),
      markedPairTotal p (fun _ _ c => markedRetainedDrawPower (n+1) c 2)]
  have hi (i : Fin 4) : Integrable (F i) (MatchProduct n) := by
    fin_cases i
    · exact marked_single_total_integrable n p _ hd
    · exact marked_single_total_integrable n p _ (fun c => hr c 1)
    · exact marked_single_total_integrable n p _ (fun c => hr c 2)
    · exact marked_pair_total_integrable n p _ (fun a b c => hr c 2)
  rw [marked_pinned_U_second_integral_direct]
  have he : markedDirectSecond p = fun z : Fin n → MatchUnit =>
      1+markedPairCoefficient (n+1)+∑ i : Fin 4,
        (![2*markedPairCoefficient (n+1),1,markedPairCoefficient (n+1),markedPairCoefficient (n+1)] i)*F i z := by
    funext z
    rw [marked_direct_second_split]
    simp only [Fin.sum_univ_four,F,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,one_mul]
    ring
  rw [he]
  rw [marked_mean_finite_affine (MatchProduct n) _ _ F hi]
  simp only [Fin.sum_univ_four,F,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,one_mul]
  ring

/-- Exact shared-original two-replica second moment. -/
theorem marked_pinned_replica_second_expansion (n : ℕ) (p : ℝ) :
    mean (MatchProduct n) (fun z => mean (UniformResampling (n+1)) (fun a =>
      mean (UniformResampling (n+1)) (fun b => U (pin n p z) a 0*U (pin n p z) b 0))) =
      1+2*mean (MatchProduct n) (markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 1))+
      mean (MatchProduct n) (markedSingleTotal p (fun c => (markedRetainedDrawPower (n+1) c 1)^2))+
      mean (MatchProduct n) (markedPairTotal p (fun a b _ =>
        markedRetainedDrawPower (n+1) a 1*markedRetainedDrawPower (n+1) b 1)) := by
  have hr (c : ℕ) := marked_retained_draw_power_bounds (n+1) c 1
  let F : Fin 3 → (Fin n → MatchUnit) → ℝ :=
    ![markedSingleTotal p (fun c => markedRetainedDrawPower (n+1) c 1),
      markedSingleTotal p (fun c => (markedRetainedDrawPower (n+1) c 1)^2),
      markedPairTotal p (fun a b _ => markedRetainedDrawPower (n+1) a 1*markedRetainedDrawPower (n+1) b 1)]
  have hi (i : Fin 3) : Integrable (F i) (MatchProduct n) := by
    fin_cases i
    · exact marked_single_total_integrable n p _ (fun c => by rw [abs_of_nonneg (hr c).1]; exact (hr c).2)
    · apply marked_single_total_integrable
      intro c
      rw [abs_of_nonneg (sq_nonneg _)]
      nlinarith [(hr c).1,(hr c).2]
    · apply marked_pair_total_integrable
      intro a b c
      rw [abs_of_nonneg (mul_nonneg (hr a).1 (hr b).1)]
      exact mul_le_one₀ (hr a).2 (hr b).1 (hr b).2
  rw [marked_pinned_U_cross_integral_direct]
  have he : (fun z : Fin n → MatchUnit => (markedDirectFirst p z)^2) =
      fun z => 1+∑ i : Fin 3, (![2,1,1] i)*F i z := by
    funext z
    rw [marked_direct_first_square_split]
    simp [Fin.sum_univ_three,F,add_assoc]
  rw [he,marked_mean_finite_affine (MatchProduct n) 1 ![2,1,1] F hi]
  simp [Fin.sum_univ_three,F,add_assoc]

/-- Full original pinned second-moment limit. -/
theorem marked_pinned_original_second_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => (W (pin n p z) 0)^2))
      atTop (𝓝 (1+3*((1-p)/p)+3*((1-p)/p)^2/2)) := by
  simp_rw [marked_pinned_original_second_expansion]
  have hh := ((tendsto_const_nhds (x := (1 : ℝ))).add
    ((marked_original_recipient_sum_limit p hp).const_mul 3)).add
      (marked_original_recipient_pair_sum_limit p hp)
  unfold markedSingleTotal markedPairTotal
  exact hh

/-- Full one-replica pinned second-moment limit. -/
theorem marked_pinned_bootstrap_second_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => mean (UniformResampling (n+1))
      (fun a => (U (pin n p z) a 0)^2))) atTop
      (𝓝 (2+2*((1-p)/p)/matchS+2*((1-p)/p)+3*((1-p)/p)^2/(2*matchS))) := by
  simp_rw [marked_pinned_bootstrap_second_expansion]
  have hq := marked_pair_coefficient_limit (fun n => n+1) (tendsto_add_atTop_nat 1)
  have hP := marked_draw_recipient_sum_limit p hp 2 (by norm_num)
  have hR1 := marked_retained_recipient_sum_limit p hp 1 (by norm_num)
  have hR2 := marked_retained_recipient_sum_limit p hp 2 (by norm_num)
  have hPair := marked_retained_union_recipient_pair_sum_limit p hp 2 (by norm_num)
  have hA := ((tendsto_const_nhds (x := (1 : ℝ))).add hq).add ((hq.mul hP).const_mul 2)
  have hB := (hA.add hR1).add (hq.mul hR2)
  have hh := hB.add (hq.mul hPair)
  unfold markedSingleTotal markedPairTotal
  convert hh using 1
  congr 1
  ring

/-- Full shared-site two-replica pinned second-moment limit. -/
theorem marked_pinned_replica_second_limit (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) :
    Tendsto (fun n => mean (MatchProduct n) (fun z => mean (UniformResampling (n+1)) (fun a =>
      mean (UniformResampling (n+1)) (fun b => U (pin n p z) a 0*U (pin n p z) b 0)))) atTop
      (𝓝 (1+2*((1-p)/p)+matchS*((1-p)/p)/(2-matchS)+
        ((1-p)/p)^2*(4-matchS)/(2*(2-matchS)))) := by
  simp_rw [marked_pinned_replica_second_expansion]
  have hh := (((tendsto_const_nhds (x := (1 : ℝ))).add
    ((marked_retained_recipient_sum_limit p hp 1 (by norm_num)).const_mul 2)).add
      (marked_retained_square_recipient_sum_limit p hp)).add
        (marked_retained_product_recipient_pair_sum_limit p hp)
  unfold markedSingleTotal markedPairTotal
  exact hh

end AronowAudit.P001.TailA
