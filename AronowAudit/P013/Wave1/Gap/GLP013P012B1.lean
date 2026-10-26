import AronowAudit.P013.P013_Audit
import AronowAudit.P013.Wave1.CorrectedCoverage.N2
import AronowAudit.P013.Wave1.CorrectedCoverage.N6
import AronowAudit.P013.Wave1.CorrectedCoverage.N7

/-!
P013-T1: paired asymptotic counterexample and finite identities.
Expression (11) is reduced to its four-atom pair score before any
moment or limit calculation.
-/

namespace AronowAudit.P013.Wave1

open AronowAudit.P013 Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-- Pair and parity coordinates for the original unit indices. -/
def pfi_unit (r : ℕ) (a : Fin r) (b : Fin 2) : Fin (2*r) :=
  ⟨2*a.val+b.val, by omega⟩

def pfi_equiv (r : ℕ) : Fin r × Fin 2 ≃ Fin (2*r) where
  toFun x := pfi_unit r x.1 x.2
  invFun i := (pairIndex r i, ⟨i.val % 2, Nat.mod_lt _ (by omega)⟩)
  left_inv := by
    intro ⟨a,b⟩
    apply Prod.ext <;> apply Fin.ext <;> dsimp [pfi_unit, pairIndex] <;> omega
  right_inv := by
    intro i
    apply Fin.ext
    dsimp [pfi_unit, pairIndex]
    omega

lemma pfi_sum_units (r : ℕ) (f : Fin (2*r) → ℝ) :
    ∑ i, f i = ∑ a, (f (pfi_unit r a 0) + f (pfi_unit r a 1)) := by
  rw [← Equiv.sum_comp (pfi_equiv r) f, Fintype.sum_prod_type]
  simp [pfi_equiv, Fin.sum_univ_succ]

@[simp] lemma pfi_index (r : ℕ) (a : Fin r) (b : Fin 2) :
    pairIndex r (pfi_unit r a b) = a := by
  apply Fin.ext
  dsimp [pairIndex, pfi_unit]
  omega

@[simp] lemma pfi_unit_inj (r : ℕ) (a c : Fin r) (b d : Fin 2) :
    pfi_unit r a b = pfi_unit r c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hval := congrArg Fin.val h
    dsimp [pfi_unit] at hval
    constructor <;> apply Fin.ext <;> omega
  · rintro ⟨rfl,rfl⟩
    rfl

@[simp] lemma pfi_outcome (r : ℕ) (hr : 2 ≤ r) (a : Fin r) (b d : Fin 2) :
    (pairedPopulation r hr).outcome (pfi_unit r a b) d = if b = 0 then 1 else -1 := by
  change (if (2*a.val+b.val) % 2 = 0 then (1:ℝ) else -1) = _
  fin_cases b <;> simp

@[simp] lemma pfi_exposure (r : ℕ) (hr : 2 ≤ r) (a : Fin r) (b : Fin 2)
    (z : Fin r → Fin 4) :
    (pairedPopulation r hr).exposure z (pfi_unit r a b) =
      pairExposure (z a) (decide (b = 1)) := by
  change pairExposure (z (pairIndex r (pfi_unit r a b)))
    (decide ((2*a.val+b.val) % 2 = 1)) = _
  rw [pfi_index]
  fin_cases b <;> simp

lemma pfi_parameters (r : ℕ) (hr : 2 ≤ r) :
    0 < pairEpsilon (2*r) ∧ 0 < 1/2-pairEpsilon (2*r) ∧
      7/8 ≤ pairSplitProbability (2*r) ∧ 0 < pairSplitProbability (2*r) := by
  have hn : (4 : ℝ) ≤ (2*r : ℕ) := by exact_mod_cast (show 4 ≤ 2*r by omega)
  have hn2 : (16 : ℝ) ≤ ((2*r : ℕ) : ℝ)^2 := by nlinarith
  have he : 0 < pairEpsilon (2*r) := by unfold pairEpsilon; positivity
  have hel : pairEpsilon (2*r) ≤ 1/16 := by
    unfold pairEpsilon
    exact (div_le_iff₀ (by positivity)).2 (by nlinarith)
  dsimp [pairSplitProbability]
  exact ⟨he, by linarith, by linarith, by linarith⟩

lemma pfi_joint_pos (r : ℕ) (hr : 2 ≤ r) (i j : Fin (2*r)) (d e : Fin 2)
    (hij : i ≠ j) : 0 < jointPi (pairedPopulation r hr) i j d e := by
  rw [paired_joint r hr i j d e hij]
  split_ifs <;> first | exact (pfi_parameters r hr).1 | exact (pfi_parameters r hr).2.1 | norm_num

lemma pfi_pair_other (r : ℕ) (hr : 2 ≤ r) (i j : Fin (2*r)) (d e : Fin 2)
    (hij : pairIndex r i ≠ pairIndex r j) (z : Fin r → Fin 4) :
    pairTerm (pairedPopulation r hr) i j d e z = 0 := by
  have hne : i ≠ j := fun h => hij (congrArg (pairIndex r) h)
  norm_num [pairTerm, paired_joint r hr i j d e hne, hij, paired_pi]

@[simp] lemma pfi_rev_zero : Fin.rev (0 : Fin 2) = 1 := rfl

@[simp] lemma pfi_rev_one : Fin.rev (1 : Fin 2) = 0 := rfl

lemma pfi_off_sum (r : ℕ) (hr : 2 ≤ r) (a : Fin r) (b d e : Fin 2)
    (z : Fin r → Fin 4) :
    (∑ j ∈ univ.erase (pfi_unit r a b),
      pairTerm (pairedPopulation r hr) (pfi_unit r a b) j d e z) =
    pairTerm (pairedPopulation r hr) (pfi_unit r a b) (pfi_unit r a (Fin.rev b)) d e z := by
  classical
  have hrev : Fin.rev b ≠ b := by fin_cases b <;> decide
  apply Finset.sum_eq_single (pfi_unit r a (Fin.rev b))
  · intro j hj hne
    have hji : j ≠ pfi_unit r a b := (mem_erase.mp hj).1
    apply pfi_pair_other
    intro hindex
    have hv := congrArg Fin.val hindex
    dsimp [pairIndex, pfi_unit] at hv
    have hval : j.val = 2*a.val + b.val ∨ j.val = 2*a.val + (Fin.rev b).val := by
      fin_cases b <;> simp only [pfi_rev_zero, pfi_rev_one] <;> dsimp at * <;> omega
    rcases hval with hval | hval
    · exact hji (Fin.ext hval)
    · exact hne (Fin.ext hval)
  · intro hnot
    exfalso
    apply hnot
    simp [hrev]

lemma pfi_correction_zero (r : ℕ) (hr : 2 ≤ r) (d : Fin 2) (z : Fin r → Fin 4) :
    correctionA2 (pairedPopulation r hr) d z = 0 := by
  classical
  unfold correctionA2
  apply sum_eq_zero
  intro i _
  apply sum_eq_zero
  intro j hj
  rw [if_neg (ne_of_gt (pfi_joint_pos r hr i j d d (mem_erase.mp hj).1.symm))]

lemma pfi_covariance_reduction (r : ℕ) (hr : 2 ≤ r) (z : Fin r → Fin 4) :
    covarianceA (pairedPopulation r hr) 1 0 z =
      (∑ i, ∑ j ∈ univ.erase i, pairTerm (pairedPopulation r hr) i j 1 0 z) -
      ∑ i, (indicator (pairedPopulation r hr).exposure i 1 z +
        indicator (pairedPopulation r hr).exposure i 0 z) := by
  classical
  unfold covarianceA
  congr 1
  · apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j hj
    exact if_pos (pfi_joint_pos r hr i j 1 0 (mem_erase.mp hj).1.symm)
  · apply sum_congr rfl
    intro i _
    rw [sum_eq_single i]
    · rw [jointPi_cross_self _ i 1 0 (by decide)]
      simp only [ite_true, paired_pi]
      have hs : (pairedPopulation r hr).outcome i 1 ^ 2 = 1 ∧
          (pairedPopulation r hr).outcome i 0 ^ 2 = 1 := by
        change (if i.val % 2 = 0 then (1:ℝ) else -1)^2 = 1 ∧
          (if i.val % 2 = 0 then (1:ℝ) else -1)^2 = 1
        split_ifs <;> norm_num
      simp [hs]
    · intro j _ hji
      exact if_neg (ne_of_gt (pfi_joint_pos r hr i j 1 0 hji.symm))
    · simp

lemma pfi_linear_sum {ι : Type*} [Fintype ι] (D O E Q C I : ι → ℝ) :
    ((∑ i, D i) + ∑ i, O i) + ((∑ i, E i) + ∑ i, Q i) -
      2*((∑ i, C i) - ∑ i, I i) =
    ∑ i, (D i + O i + E i + Q i - 2*(C i-I i)) := by
  simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum]
  ring

lemma pfi_point_reduction (r : ℕ) (hr : 2 ≤ r) (z : Fin r → Fin 4) :
    htEffect (pairedPopulation r hr) 1 0 z = (∑ a, pairScore (z a))/((2*r : ℕ) : ℝ) ∧
    ((2*r : ℕ) : ℝ)^2 * effectVariance (pairedPopulation r hr) 1 0 z =
      ∑ a, pairVarianceScore (2*r) (z a) := by
  classical
  have hN : ((2*r : ℕ) : ℝ) ≠ 0 := by positivity
  have he := (pfi_parameters r hr).1.ne'
  have hq := (pfi_parameters r hr).2.1.ne'
  have ht := (pfi_parameters r hr).2.2.2.ne'
  have htn : 1-pairEpsilon (r*2)*2 ≠ 0 := by
    simpa only [pairSplitProbability, Nat.mul_comm, mul_comm] using ht
  constructor
  · unfold htEffect htTotal
    rw [← sum_sub_distrib, pfi_sum_units]
    congr 1
    apply sum_congr rfl
    intro a _
    simp only [paired_pi, indicator, pfi_exposure, pfi_outcome]
    generalize z a = x
    fin_cases x <;> norm_num [pairScore, pairExposure]
  · unfold effectVariance
    rw [pfi_correction_zero, pfi_correction_zero, pfi_covariance_reduction]
    simp only [add_zero, varianceHT]
    rw [mul_div_cancel₀ _ (pow_ne_zero _ hN)]
    rw [pfi_linear_sum]
    rw [pfi_sum_units]
    simp only [pfi_off_sum]
    apply sum_congr rfl
    intro a _
    simp only [pairTerm, paired_pi]
    have h01 : pfi_unit r a 0 ≠ pfi_unit r a 1 := by simp
    have h10 := h01.symm
    simp only [pfi_rev_zero, pfi_rev_one, paired_joint r hr _ _ _ _ h01,
      paired_joint r hr _ _ _ _ h10, pfi_index, ite_true, ↓reduceIte,
      pfi_outcome, indicator, pfi_exposure]
    generalize z a = x
    fin_cases x <;> norm_num [pairVarianceScore, pairExposure, pairSplitProbability]
      <;> field_simp [he, hq, ht]
      <;> ring_nf <;> field_simp [htn] <;> ring


/-- Independent finite coordinates add their means and their variances. -/
lemma pfi_sum_moments {Ω : Type*} [Fintype Ω] (P : Design Ω) (r : ℕ) (g : Ω → ℝ) :
    expectation (replicateDesign P r) (fun z => ∑ a, g (z a)) = (r : ℝ)*expectation P g ∧
    variance (replicateDesign P r) (fun z => ∑ a, g (z a)) = (r : ℝ)*variance P g := by
  classical
  constructor
  · simp only [expectation_sum, replicate_marginal, sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  · unfold variance
    rw [covariance_sum_sum]
    have hc (i j : Fin r) : covariance (replicateDesign P r)
        (fun z => g (z i)) (fun z => g (z j)) = if i=j then covariance P g g else 0 := by
      by_cases hij : i=j
      · subst j
        simp only [ite_true, covariance, replicate_marginal]
        rw [replicate_marginal P r i (fun x => g x*g x)]
      · rw [if_neg hij, covariance, replicate_pair_marginal P r i j hij,
          replicate_marginal, replicate_marginal]
        ring
    simp_rw [hc]
    simp

lemma pfi_score_pos (r : ℕ) (hr : 2 ≤ r) (x : Fin 4) :
    0 < pairVarianceScore (2*r) x := by
  have hp := pfi_parameters r hr
  unfold pairVarianceScore
  split_ifs
  · exact div_pos (by norm_num) hp.1
  · have hdiv : 4 / pairSplitProbability (2*r) < 16 := by
      apply (div_lt_iff₀ hp.2.2.2).2
      linarith [hp.2.2.1]
    linarith

lemma pfi_probability_compl {Ω : Type*} [Fintype Ω] (P : Design Ω) (A : Ω → Prop) :
    probability P (fun z => ¬ A z) = 1-probability P A := by
  classical
  rw [← P.total, probability, probability, ← sum_sub_distrib]
  apply sum_congr rfl
  intro z _
  by_cases hz : A z <;> simp [hz]

lemma pfi_one_sub_pow (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (r : ℕ) :
    1-t^r ≤ (r : ℝ)*(1-t) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, Nat.cast_succ]
    have hm := mul_le_mul_of_nonneg_left ih h0
    have hn := mul_nonneg (Nat.cast_nonneg r : (0:ℝ) ≤ r) (sq_nonneg (1-t))
    nlinarith

/-- Finite identities for the paired design. -/
lemma pfi_identities (r : ℕ) (hr : 2 ≤ r) :
    let F := pairedPopulation r hr
    let P := pairedDesign r hr
    let N := (2*r : ℕ)
    let t := pairSplitProbability N
    causalEffect F 1 0 = 0 ∧
    (∀ z, htEffect F 1 0 z = (∑ a, pairScore (z a))/(N : ℝ) ∧
      (N : ℝ)^2*effectVariance F 1 0 z = ∑ a, pairVarianceScore N (z a) ∧
      0 < effectVariance F 1 0 z) ∧
    variance P (htEffect F 1 0) = 8*t/(N : ℝ) ∧
    expectation P (effectVariance F 1 0) = variance P (htEffect F 1 0) ∧
    probability P (allPairsSplit r) = t^r ∧
    probability P (fun z => ¬ allPairsSplit r z) ≤ 1/(N : ℝ) ∧
    (∀ z, allPairsSplit r z → (N : ℝ)*effectVariance F 1 0 z = 8-2/t) ∧
    variance P (fun z => (N : ℝ)*effectVariance F 1 0 z) =
      4*((N : ℝ)-2)^4*((N : ℝ)+2)^4 / ((N : ℝ)^5*((N : ℝ)^2-2)) := by
  classical
  dsimp only
  let N := (2*r : ℕ)
  let t := pairSplitProbability N
  let P := pairedDesign r hr
  let F := pairedPopulation r hr
  have hN : (N : ℝ) ≠ 0 := by dsimp [N]; positivity
  have hr0 : 0 < r := by omega
  have he := (pfi_parameters r hr).1.ne'
  have ht := (pfi_parameters r hr).2.2.2.ne'
  have hpoint (z : Fin r → Fin 4) := pfi_point_reduction r hr z
  have hvhat (z : Fin r → Fin 4) : effectVariance F 1 0 z =
      (∑ a, pairVarianceScore N (z a))/(N : ℝ)^2 := by
    apply (eq_div_iff (pow_ne_zero _ hN)).2
    simpa only [N, F, mul_comm] using (hpoint z).2
  have hsumT := (pfi_sum_moments (pairAtomDesign N (by dsimp [N]; omega)) r pairScore).2
  have hsumR := pfi_sum_moments (pairAtomDesign N (by dsimp [N]; omega)) r
    (pairVarianceScore N)
  change variance P (fun z => ∑ a, pairScore (z a)) = _ at hsumT
  change expectation P (fun z => ∑ a, pairVarianceScore N (z a)) = _ ∧
    variance P (fun z => ∑ a, pairVarianceScore N (z a)) = _ at hsumR
  have hmT := pair_score_moments N (by dsimp [N]; omega)
  have hmR := pair_variance_score_moments N (by dsimp [N]; omega)
  have hV : variance P (htEffect F 1 0) = 8*t/(N : ℝ) := by
    simp_rw [show htEffect F 1 0 = fun z => (∑ a, pairScore (z a))/(N : ℝ) from
      funext (fun z => (hpoint z).1)]
    rw [variance_div, hsumT, hmT.2]
    dsimp [N, t]
    push_cast
    field_simp
    <;> ring
  have hPr : probability P (allPairsSplit r) = t^r := by
    change probability (replicateDesign (pairAtomDesign N (by dsimp [N]; omega)) r)
      (fun z => ∀ a, pairExposure (z a) false ≠ pairExposure (z a) true) = _
    rw [replicate_probability_product (pairAtomDesign N (by dsimp [N]; omega)) r
      (fun _ x => pairExposure x false ≠ pairExposure x true)]
    have hs : probability (pairAtomDesign N (by dsimp [N]; omega))
        (fun x => pairExposure x false ≠ pairExposure x true) = t := by
      norm_num [probability, pairAtomDesign, pairExposure, Fin.sum_univ_succ]
      dsimp [t, pairSplitProbability]
      ring
    simp only [hs, prod_const, card_univ, Fintype.card_fin]
  refine ⟨?_, ?_, hV, ?_, hPr, ?_, ?_, ?_⟩
  · simp [causalEffect, potentialMean, potentialTotal, pairedPopulation]
  · intro z
    refine ⟨(hpoint z).1, (hpoint z).2, ?_⟩
    rw [hvhat]
    apply div_pos
    · exact sum_pos (fun a _ => pfi_score_pos r hr (z a))
        ⟨⟨0, hr0⟩, mem_univ _⟩
    · positivity
  · change expectation P (effectVariance F 1 0) = variance P (htEffect F 1 0)
    rw [show effectVariance F 1 0 = fun z =>
      (∑ a, pairVarianceScore N (z a))/(N : ℝ)^2 from funext hvhat]
    simp only [div_eq_mul_inv, expectation_mul_const]
    rw [hsumR.1, hmR.1, hV]
    dsimp [N, t]
    push_cast
    field_simp
    <;> ring
  · rw [pfi_probability_compl, hPr]
    have hp := pfi_parameters r hr
    have ht1 : t ≤ 1 := by dsimp [t, pairSplitProbability]; linarith [hp.1]
    calc
      1-t^r ≤ (r : ℝ)*(1-t) := pfi_one_sub_pow t hp.2.2.2.le ht1 r
      _ = 1/(N : ℝ) := by
        dsimp [t, pairSplitProbability, pairEpsilon, N]
        push_cast
        field_simp
        <;> ring
  · intro z hz
    change (N : ℝ)*effectVariance F 1 0 z = 8-2/t
    rw [hvhat]
    have hs : (∑ a, pairVarianceScore N (z a)) = (r : ℝ)*(16-4/t) := by
      have hscore (a : Fin r) : pairVarianceScore N (z a) = 16-4/t := by
        exact if_neg (hz a)
      simp only [hscore, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [hs]
    have hrel : (r : ℝ) = (N : ℝ)/2 := by dsimp [N]; push_cast; ring
    rw [hrel]
    field_simp [hN]
    <;> ring
  · change variance P (fun z => (N : ℝ)*effectVariance F 1 0 z) =
      4*((N : ℝ)-2)^4*((N : ℝ)+2)^4 / ((N : ℝ)^5*((N : ℝ)^2-2))
    have hW : (fun z => (N : ℝ)*effectVariance F 1 0 z) =
        (fun z => (∑ a, pairVarianceScore N (z a))/(N : ℝ)) := by
      funext z
      rw [hvhat]
      field_simp
    rw [hW, variance_div, hsumR.2]
    have hvar : variance (pairAtomDesign N (by dsimp [N]; omega)) (pairVarianceScore N) =
        8/pairEpsilon N + t*(16-4/t)^2 - (16*t)^2 := by
      unfold variance covariance
      rw [show (fun x => pairVarianceScore N x * pairVarianceScore N x) =
        (fun x => pairVarianceScore N x ^ 2) by funext x; ring, hmR.1, hmR.2]
      dsimp only [t]
      ring
    rw [hvar]
    have hn : (4:ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 4 ≤ N by dsimp [N]; omega)
    have hn2 : (N : ℝ)^2-2 ≠ 0 := by nlinarith
    have hrel : (r : ℝ) = (N : ℝ)/2 := by dsimp [N]; push_cast; ring
    rw [hrel]
    have htf : t = ((N : ℝ)^2-2)/(N : ℝ)^2 := by
      dsimp [t, pairSplitProbability, pairEpsilon]
      field_simp
      <;> ring
    rw [htf]
    simp only [pairEpsilon]
    field_simp [hN, hn2]
    <;> ring


/-!
Asymptotic limits of the paired finite designs. -/

def pas_P (n : ℕ) := pairedDesign (n+2) (by omega)
def pas_F (n : ℕ) := pairedPopulation (n+2) (by omega)
def pas_N (n : ℕ) : ℝ := 2*(n+2)
def pas_t (n : ℕ) := pairSplitProbability (2*(n+2))
def pas_V (n : ℕ) := variance (pas_P n) (htEffect (pas_F n) 1 0)
def pas_W (n : ℕ) (z : Fin (n+2) → Fin 4) := pas_N n*effectVariance (pas_F n) 1 0 z

def pas_v (n : ℕ) : ℝ := (n+2)*16*pas_t n

def pas_Z (n : ℕ) (z : Fin (n+2) → Fin 4) : ℝ :=
  (∑ a, pairScore (z a))/Real.sqrt (pas_v n)

lemma pas_N_pos (n : ℕ) : 0 < pas_N n := by unfold pas_N; positivity

lemma pas_t_pos (n : ℕ) : 0 < pas_t n := (pfi_parameters (n+2) (by omega)).2.2.2

lemma pas_V_formula (n : ℕ) : pas_V n = 8*pas_t n/pas_N n := by
  simpa [pas_V, pas_P, pas_F, pas_N, pas_t] using
    (pfi_identities (n+2) (by omega)).2.2.1

lemma pas_V_pos (n : ℕ) : 0 < pas_V n := by
  rw [pas_V_formula]
  exact div_pos (mul_pos (by norm_num) (pas_t_pos n)) (pas_N_pos n)

lemma pas_W_on_split (n : ℕ) (z : Fin (n+2) → Fin 4) (hz : allPairsSplit (n+2) z) :
    pas_W n z = 8-2/pas_t n := by
  simpa [pas_W, pas_N, pas_F, pas_t] using
    (pfi_identities (n+2) (by omega)).2.2.2.2.2.2.1 z hz

lemma pas_bad_bound (n : ℕ) : probability (pas_P n) (fun z => ¬ allPairsSplit (n+2) z) ≤
    1/pas_N n := by
  simpa [pas_P, pas_N] using (pfi_identities (n+2) (by omega)).2.2.2.2.2.1

lemma pas_var_formula (n : ℕ) : variance (pas_P n) (pas_W n) =
    4*(pas_N n-2)^4*(pas_N n+2)^4 / ((pas_N n)^5*((pas_N n)^2-2)) := by
  change variance (pas_P n) (fun z => pas_W n z) = _
  simpa [pas_P, pas_W, pas_F, pas_N] using
    (pfi_identities (n+2) (by omega)).2.2.2.2.2.2.2

lemma pas_N_atTop : Tendsto pas_N atTop atTop := by
  apply tendsto_atTop_mono (f := fun n : ℕ => (n : ℝ))
    (fun n => by dsimp [pas_N]; linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
  exact tendsto_natCast_atTop_atTop

lemma pas_inv_limit : Tendsto (fun n => 1/pas_N n) atTop (𝓝 0) :=
  pas_N_atTop.const_div_atTop 1

lemma pas_t_limit : Tendsto pas_t atTop (𝓝 1) := by
  have he := pas_inv_limit.pow 2
  have h := (tendsto_const_nhds (x := (1:ℝ))).sub (he.const_mul 2)
  convert h using 1
  · funext n
    simp [pas_t, pairSplitProbability, pairEpsilon, pas_N, div_pow, inv_pow, mul_pow]
  · norm_num

lemma pas_bad_limit : Tendsto
    (fun n => probability (pas_P n) (fun z => ¬ allPairsSplit (n+2) z)) atTop (𝓝 0) :=
  squeeze_zero (fun n => probability_nonneg _ _) pas_bad_bound pas_inv_limit

lemma pas_prob_union {Ω : Type*} [Fintype Ω] (P : Design Ω) (A B C : Ω → Prop)
    (h : ∀ z, A z → B z ∨ C z) : probability P A ≤ probability P B + probability P C := by
  classical
  unfold probability
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro z _
  have hcase := h z
  by_cases ha : A z <;> by_cases hb : B z <;> by_cases hc : C z <;>
    simp [ha,hb,hc] <;> first | linarith [(P.positive z).le] | tauto

lemma pas_event_transfer {L : ℕ → Type*} [∀ n, Fintype (L n)] (P : ∀ n, Design (L n))
    (A B G : ∀ n, L n → Prop) (a : ℝ)
    (heq : ∀ n z, G n z → (A n z ↔ B n z))
    (hbad : Tendsto (fun n => probability (P n) (fun z => ¬ G n z)) atTop (𝓝 0))
    (hB : Tendsto (fun n => probability (P n) (B n)) atTop (𝓝 a)) :
    Tendsto (fun n => probability (P n) (A n)) atTop (𝓝 a) := by
  have hAB (n : ℕ) : probability (P n) (A n) ≤
      probability (P n) (B n) + probability (P n) (fun z => ¬ G n z) := by
    apply pas_prob_union
    intro z hz
    by_cases hg : G n z
    · exact Or.inl ((heq n z hg).1 hz)
    · exact Or.inr hg
  have hBA (n : ℕ) : probability (P n) (B n) ≤
      probability (P n) (A n) + probability (P n) (fun z => ¬ G n z) := by
    apply pas_prob_union
    intro z hz
    by_cases hg : G n z
    · exact Or.inl ((heq n z hg).2 hz)
    · exact Or.inr hg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa only [sub_zero] using hB.sub hbad)
    (by simpa only [add_zero] using hB.add hbad)
  · intro n
    linarith [hBA n]
  · exact hAB

lemma pas_exception_limit {L : ℕ → Type*} [∀ n, Fintype (L n)]
    (P : ∀ n, Design (L n)) (X : ∀ n, L n → ℝ) (G : ∀ n, L n → Prop)
    (a : ℕ → ℝ) (c : ℝ) (ha : Tendsto a atTop (𝓝 c))
    (heq : ∀ n z, G n z → X n z = a n)
    (hbad : Tendsto (fun n => probability (P n) (fun z => ¬ G n z)) atTop (𝓝 0)) :
    ConvergesInProbability P X c := by
  intro ε hε
  have he : ∀ᶠ n in atTop, |a n-c| < ε := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp ha ε hε
  apply squeeze_zero' (Eventually.of_forall (fun n => probability_nonneg _ _)) ?_ hbad
  filter_upwards [he] with n hn
  apply probability_mono
  intro z hz hg
  rw [heq n z hg] at hz
  linarith

/-- The equality graph certifies independence of the entire score vectors. -/
lemma pas_graph (r : ℕ) (hr : 2 ≤ r) :
    ∃ D : Causalean.Mathlib.Probability.SteinMethod.DepGraph
      (fun a (z : Fin r → Fin 4) => pairScore (z a)) (designMeasure (pairedDesign r hr)),
      ∀ i, (D.nbhd i).card ≤ 1 := by
  classical
  have hgen := coordinate_population_genuine_dependency (pairAtomDesign (2*r) (by omega)) r
    (fun a : Fin r => a) (fun _ x => x)
  let D : Causalean.Mathlib.Probability.SteinMethod.DepGraph
      (fun a (z : Fin r → Fin 4) => pairScore (z a)) (designMeasure (pairedDesign r hr)) := {
    G := Eq
    decG := inferInstance
    refl := fun _ => rfl
    symm := fun _ _ h => h.symm
    meas := fun _ => measurable_of_finite _
    indep := by
      intro A B hsep
      have hd : Disjoint A B := disjoint_left.mpr (by
        intro i hi hj
        exact hsep i hi i hj rfl)
      have hno : CorrectedNoEdge (fun i j : Fin r => decide (i=j)) A B := by
        rintro ⟨i,j,hij,hmem⟩
        have he : i=j := of_decide_eq_true hij
        subst j
        rcases hmem with hmem | hmem | hmem | hmem <;>
          exact disjoint_left.mp hd hmem.1 hmem.2
      have hvec := CorrectedCoverage.n2_proof (by norm_num : 0 < 4)
        (pairedDesign r hr) (fun z a => z a) A B (hgen A B hd hno)
      exact hvec.comp (measurable_of_finite (fun v : A → Fin 4 => fun i => pairScore (v i)))
        (measurable_of_finite (fun v : B → Fin 4 => fun i => pairScore (v i))) }
  refine ⟨D, ?_⟩
  intro i
  have hn : D.nbhd i = {i} := by
    ext j
    rw [D.mem_nbhd_iff]
    simp [D, eq_comm]
  simp [hn]


lemma pas_standard_normal : TendsNormal pas_P pas_Z 0 1 := by
  classical
  let μ := fun n => designMeasure (pas_P n)
  letI pas_instProbability (n : ℕ) : MeasureTheory.IsProbabilityMeasure (μ n) := (CorrectedCoverage.n1_proof (pas_P n)).1
  let X : ∀ n, Fin (n+2) → (Fin (n+2) → Fin 4) → ℝ :=
    fun _ a z => pairScore (z a)
  have hgraphs := fun n => pas_graph (n+2) (by omega)
  choose Dep hdeg using hgraphs
  have hbound : ∀ n i z, |X n i z| ≤ 4 := by
    intro n i z
    change |pairScore (z i)| ≤ 4
    generalize z i = x
    fin_cases x <;> norm_num [pairScore, pairExposure]
  have hmean : ∀ n i, (∫ z, X n i z ∂μ n) = 0 := by
    intro n i
    rw [integral_designMeasure]
    change expectation (replicateDesign (pairAtomDesign (2*(n+2)) (by omega)) (n+2))
      (fun z => pairScore (z i)) = 0
    rw [replicate_marginal]
    exact (pair_score_moments _ _).1
  have hsecond : ∀ n, (∫ z,
      (Causalean.Mathlib.Probability.SteinMethod.depSum (X n) z)^2 ∂μ n) = pas_v n := by
    intro n
    rw [integral_designMeasure]
    change expectation (pas_P n) (fun z => (∑ a, pairScore (z a))^2) = pas_v n
    have hs := pfi_sum_moments (pairAtomDesign (2*(n+2)) (by omega)) (n+2) pairScore
    have hm := pair_score_moments (2*(n+2)) (by omega)
    have hm0 : expectation (pas_P n) (fun z => ∑ a, pairScore (z a)) = 0 := by
      change expectation (replicateDesign _ _) _ = 0
      rw [hs.1, hm.1, mul_zero]
    have hvar : variance (pas_P n) (fun z => ∑ a, pairScore (z a)) = pas_v n := by
      change variance (replicateDesign _ _) _ = _
      rw [hs.2, hm.2]
      simp [pas_v, pas_t]
      ring
    rw [variance, covariance, hm0, mul_zero, sub_zero] at hvar
    simpa only [pow_two] using hvar
  have hfloor : ∀ᶠ n in atTop, 14*(Fintype.card (Fin (n+2)) : ℝ) ≤ pas_v n := by
    apply Eventually.of_forall
    intro n
    have ht : 7/8 ≤ pas_t n := (pfi_parameters (n+2) (by omega)).2.2.1
    simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_ofNat]
    dsimp [pas_v]
    nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  have hcard : Tendsto (fun n : ℕ => Fintype.card (Fin (n+2))) atTop atTop := by
    simpa only [Fintype.card_fin] using tendsto_add_atTop_nat 2
  intro x
  have hclt := Causalean.Mathlib.Probability.SteinMethod.bounded_degree_dependency_clt
    μ X Dep 1 hdeg 4 (by norm_num) hbound hmean pas_v hsecond 14 (by norm_num) hfloor hcard x
  rw [← ProbabilityTheory.cdf_eq_real (ProbabilityTheory.gaussianReal 0 1) x] at hclt
  apply hclt.congr
  intro n
  rw [MeasureTheory.map_measureReal_apply (measurable_of_finite _) measurableSet_Iic]
  change (designMeasure (pas_P n)).real {z | pas_Z n z ≤ x} =
    probability (pas_P n) (fun z => pas_Z n z ≤ x)
  exact (CorrectedCoverage.n1_proof (pas_P n)).2 _


lemma pas_standard_identity (n : ℕ) (z : Fin (n+2) → Fin 4) :
    pas_Z n z = htEffect (pas_F n) 1 0 z/Real.sqrt (pas_V n) := by
  have hv : pas_v n = (pas_N n)^2*pas_V n := by
    rw [pas_V_formula]
    dsimp [pas_v, pas_N]
    field_simp
    <;> ring
  have hs : Real.sqrt (pas_v n) = pas_N n*Real.sqrt (pas_V n) := by
    rw [hv, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pas_N_pos n).le]
  have hpoint := (pfi_point_reduction (n+2) (by omega) z).1
  have hhat : htEffect (pas_F n) 1 0 z = (∑ a, pairScore (z a))/pas_N n := by
    simpa [pas_F, pas_N] using hpoint
  rw [hhat]
  simp only [pas_Z, hs, div_div]

lemma pas_scale_identity (n : ℕ) (z : Fin (n+2) → Fin 4) :
    Real.sqrt (pas_N n)*htEffect (pas_F n) 1 0 z =
      pas_Z n z*Real.sqrt (8*pas_t n) := by
  have hsV : Real.sqrt (pas_V n) ≠ 0 := (Real.sqrt_pos.2 (pas_V_pos n)).ne'
  have hs : Real.sqrt (8*pas_t n) = Real.sqrt (pas_N n)*Real.sqrt (pas_V n) := by
    rw [← Real.sqrt_mul (pas_N_pos n).le, pas_V_formula]
    congr 1
    field_simp [(pas_N_pos n).ne']
  rw [pas_standard_identity, hs]
  field_simp [hsV]
  <;> ring

lemma pas_NV_limit : Tendsto (fun n => pas_N n*pas_V n) atTop (𝓝 8) := by
  have h := pas_t_limit.const_mul 8
  norm_num only [mul_one] at h
  apply h.congr
  intro n
  rw [pas_V_formula]
  field_simp [(pas_N_pos n).ne']

lemma pas_W_limit : ConvergesInProbability pas_P pas_W 6 := by
  have hw : Tendsto (fun n => 8-2/pas_t n) atTop (𝓝 6) := by
    convert (tendsto_const_nhds (x := (8:ℝ))).sub
      ((tendsto_const_nhds (x := (2:ℝ))).div pas_t_limit (by norm_num)) using 1 <;> norm_num
  exact pas_exception_limit pas_P pas_W (fun n => allPairsSplit (n+2)) _ 6 hw
    pas_W_on_split pas_bad_limit

lemma pas_ratio_on_split (n : ℕ) (z : Fin (n+2) → Fin 4) (hz : allPairsSplit (n+2) z) :
    effectVariance (pas_F n) 1 0 z/pas_V n = (8-2/pas_t n)/(8*pas_t n) := by
  rw [← pas_W_on_split n z hz]
  simp only [pas_W, pas_V_formula]
  field_simp [(pas_N_pos n).ne', (pas_t_pos n).ne']

lemma pas_ratio_scalar_limit : Tendsto (fun n => (8-2/pas_t n)/(8*pas_t n))
    atTop (𝓝 (3/4)) := by
  convert ((tendsto_const_nhds (x := (8:ℝ))).sub
    ((tendsto_const_nhds (x := (2:ℝ))).div pas_t_limit (by norm_num))).div
      (pas_t_limit.const_mul 8) (by norm_num) using 1 <;> norm_num

lemma pas_ratio_limit : ConvergesInProbability pas_P
    (fun n z => effectVariance (pas_F n) 1 0 z/pas_V n) (3/4) :=
  pas_exception_limit pas_P _ (fun n => allPairsSplit (n+2)) _ (3/4)
    pas_ratio_scalar_limit pas_ratio_on_split pas_bad_limit

lemma pas_normalized_var_limit : Tendsto (fun n => variance (pas_P n) (pas_W n)/(4*pas_N n))
    atTop (𝓝 1) := by
  have hi2 : Tendsto (fun n => (1/pas_N n)^2) atTop (𝓝 0) := by
    simpa using pas_inv_limit.pow 2
  have ht := ((tendsto_const_nhds (x := (1:ℝ))).sub (hi2.const_mul 4)).pow 4
  have hd := (tendsto_const_nhds (x := (1:ℝ))).sub (hi2.const_mul 2)
  have hh := ht.div hd (by norm_num)
  norm_num only [mul_zero, sub_zero, one_pow, div_one] at hh
  apply hh.congr
  intro n
  change (1-4*(1/pas_N n)^2)^4/(1-2*(1/pas_N n)^2) =
    variance (pas_P n) (pas_W n)/(4*pas_N n)
  rw [pas_var_formula]
  have hN := (pas_N_pos n).ne'
  have hn : 4 ≤ pas_N n := by dsimp [pas_N]; linarith [show (0:ℝ) ≤ n from Nat.cast_nonneg n]
  have hN2 : (pas_N n)^2-2 ≠ 0 := by nlinarith
  field_simp [hN, hN2]
  <;> ring

lemma pas_var_diverges : Tendsto (fun n => variance (pas_P n) (pas_W n)) atTop atTop := by
  have hlow : ∀ᶠ n in atTop, 1/2 ≤ variance (pas_P n) (pas_W n)/(4*pas_N n) :=
    (pas_normalized_var_limit.eventually (lt_mem_nhds (by norm_num : (1/2:ℝ) < 1))).mono
      (fun _ h => h.le)
  apply tendsto_atTop_mono' atTop ?_ (pas_N_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  filter_upwards [hlow] with n hn
  have hh := (le_div_iff₀ (mul_pos (by norm_num) (pas_N_pos n))).1 hn
  linarith

/-- A continuous limiting CDF permits a deterministic moving evaluation point. -/
lemma pas_moving_cdf {L : ℕ → Type*} [∀ n, Fintype (L n)]
    (P : ∀ n, Design (L n)) (X : ∀ n, L n → ℝ) (w : ℕ → ℝ) (a : ℝ)
    (hX : TendsNormal P X 0 1) (hw : Tendsto w atTop (𝓝 a)) :
    Tendsto (fun n => probability (P n) (fun z => X n z ≤ w n)) atTop (𝓝 (normalCDF a)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hc : ContinuousAt normalCDF a := CorrectedCoverage.n6_proof.1.continuousAt
  obtain ⟨δ,hδ,hcδ⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by linarith)
  have hleft := hcδ (x := a-δ/2) (by
    rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos (half_pos hδ)]
    linarith)
  have hright := hcδ (x := a+δ/2) (by
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos (half_pos hδ)]
    linarith)
  have hwl : ∀ᶠ n in atTop, |w n-a| < δ/2 := by
    simpa only [Real.dist_eq] using Metric.tendsto_nhds.mp hw (δ/2) (half_pos hδ)
  have hl := Metric.tendsto_nhds.mp (hX (a-δ/2)) (ε/2) (half_pos hε)
  have hu := Metric.tendsto_nhds.mp (hX (a+δ/2)) (ε/2) (half_pos hε)
  rw [Real.dist_eq, abs_lt] at hleft hright
  filter_upwards [hwl,hl,hu] with n hwn hln hun
  rw [Real.dist_eq, abs_lt] at hln hun ⊢
  have hlow := probability_mono (P n) (fun z => X n z ≤ a-δ/2)
    (fun z => X n z ≤ w n) (fun z hz => hz.trans (by linarith [(abs_lt.mp hwn).1]))
  have hhigh := probability_mono (P n) (fun z => X n z ≤ w n)
    (fun z => X n z ≤ a+δ/2) (fun z hz => hz.trans (by linarith [(abs_lt.mp hwn).2]))
  change probability (P n) (fun z => X n z ≤ a-δ/2) - normalCDF (a-δ/2) > -(ε/2) ∧
    probability (P n) (fun z => X n z ≤ a-δ/2) - normalCDF (a-δ/2) < ε/2 at hln
  change probability (P n) (fun z => X n z ≤ a+δ/2) - normalCDF (a+δ/2) > -(ε/2) ∧
    probability (P n) (fun z => X n z ≤ a+δ/2) - normalCDF (a+δ/2) < ε/2 at hun
  constructor <;> linarith

lemma pas_gaussian_eight_cdf (x : ℝ) :
    ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 8) x = normalCDF (x/Real.sqrt 8) := by
  have hs : 0 < Real.sqrt (8:ℝ) := by positivity
  have hm : (ProbabilityTheory.gaussianReal 0 1).map (fun y : ℝ => Real.sqrt 8*y) =
      ProbabilityTheory.gaussianReal 0 8 := by
    have hv : NNReal.mk ((Real.sqrt (8:ℝ))^2) (sq_nonneg _) * 1 = 8 := by
      apply NNReal.eq
      change (Real.sqrt (8:ℝ))^2 * 1 = 8
      norm_num
    have hh := ProbabilityTheory.gaussianReal_map_const_mul
      (μ := (0:ℝ)) (v := (1:ℝ≥0)) (Real.sqrt 8)
    rw [mul_zero, hv] at hh
    exact hh
  rw [ProbabilityTheory.cdf_eq_real, ← hm,
    MeasureTheory.map_measureReal_apply (by fun_prop : Measurable (fun y : ℝ => Real.sqrt 8*y))
      measurableSet_Iic, normalCDF, ProbabilityTheory.cdf_eq_real]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_Iic]
  simpa only [mul_comm] using (le_div_iff₀ hs : y ≤ x/Real.sqrt 8 ↔ y*Real.sqrt 8 ≤ x).symm

lemma pas_scaled_normal : TendsNormal pas_P
    (fun n z => Real.sqrt (pas_N n)*htEffect (pas_F n) 1 0 z) 0 8 := by
  intro x
  have hscale : Tendsto (fun n => Real.sqrt (8*pas_t n)) atTop (𝓝 (Real.sqrt 8)) := by
    simpa only [mul_one] using (pas_t_limit.const_mul 8).sqrt
  have hw := (tendsto_const_nhds (x := x)).div hscale (by positivity : Real.sqrt (8:ℝ) ≠ 0)
  have hlim := pas_moving_cdf pas_P pas_Z _ _ pas_standard_normal hw
  rw [pas_gaussian_eight_cdf]
  apply hlim.congr
  intro n
  congr 1
  funext z
  apply propext
  change pas_Z n z ≤ x/Real.sqrt (8*pas_t n) ↔
    Real.sqrt (pas_N n)*htEffect (pas_F n) 1 0 z ≤ x
  rw [pas_scale_identity]
  exact (le_div_iff₀ (Real.sqrt_pos.2 (mul_pos (by norm_num) (pas_t_pos n))))

lemma pas_coverage_limit (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun n => probability (pas_P n) (fun z =>
      |htEffect (pas_F n) 1 0 z-causalEffect (pas_F n) 1 0| ≤
        normalCritical α*Real.sqrt (effectVariance (pas_F n) 1 0 z))) atTop
      (𝓝 (2*normalCDF (normalCritical α*Real.sqrt (3/4))-1)) := by
  let w : ℕ → ℝ := fun n => normalCritical α*Real.sqrt ((8-2/pas_t n)/(8*pas_t n))
  have hw : Tendsto w atTop (𝓝 (normalCritical α*Real.sqrt (3/4))) :=
    pas_ratio_scalar_limit.sqrt.const_mul _
  have hq := (CorrectedCoverage.n6_proof.2.2.2 α hα hα1).1
  have hw0 : 0 < normalCritical α*Real.sqrt (3/4) := mul_pos hq (by positivity)
  have hinterval := CorrectedCoverage.n7_proof CorrectedCoverage.n6_proof
    pas_P pas_Z w _ pas_standard_normal hw0 hw
  apply pas_event_transfer pas_P _ (fun n z => |pas_Z n z| ≤ w n)
    (fun n => allPairsSplit (n+2)) _ ?_ pas_bad_limit hinterval
  intro n z hz
  have hτ : causalEffect (pas_F n) 1 0 = 0 := (pfi_identities (n+2) (by omega)).1
  have hhat : 0 < effectVariance (pas_F n) 1 0 z :=
    ((pfi_identities (n+2) (by omega)).2.1 z).2.2
  have hsV : 0 < Real.sqrt (pas_V n) := Real.sqrt_pos.2 (pas_V_pos n)
  have hratio := pas_ratio_on_split n z hz
  dsimp only [w]
  rw [hτ, sub_zero, ← hratio, pas_standard_identity, abs_div, abs_of_pos hsV,
    Real.sqrt_div hhat.le]
  rw [div_le_iff₀ hsV]
  have hh : normalCritical α*(Real.sqrt (effectVariance (pas_F n) 1 0 z)/Real.sqrt (pas_V n))*
      Real.sqrt (pas_V n) = normalCritical α*Real.sqrt (effectVariance (pas_F n) 1 0 z) := by
    field_simp
  rw [hh]

lemma pas_strict_undercoverage (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    2*normalCDF (normalCritical α*Real.sqrt (3/4))-1 < 1-α := by
  have hq := CorrectedCoverage.n6_proof.2.2.2 α hα hα1
  have hs : Real.sqrt (3/4:ℝ) < 1 := by
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  have hm := CorrectedCoverage.n6_proof.2.1
    (mul_lt_of_lt_one_right hq.1 hs)
  linarith [hq.2]

theorem paired_asymptotic_counterexample_proof :
    (∀ r (hr : 2 ≤ r),
      (∀ i d, pi (pairedPopulation r hr) i d = 1/2 ∧
        |(pairedPopulation r hr).outcome i d| = 1) ∧
      GenuineDependency (pairedDesign r hr) (pairedPopulation r hr).exposure
        (fun i j => decide (pairIndex r i = pairIndex r j)) ∧
      PrintedDependency (pairedDesign r hr) (pairedPopulation r hr).exposure
        (fun i j => decide (pairIndex r i = pairIndex r j)) ∧
      RowBound (fun i j : Fin (2*r) => decide (pairIndex r i = pairIndex r j)) 2) ∧
    (let P := fun n : ℕ => pairedDesign (n+2) (by omega)
     let F := fun n : ℕ => pairedPopulation (n+2) (by omega)
     let N := fun n : ℕ => (2*(n+2) : ℝ)
     let V := fun n : ℕ => variance (P n) (htEffect (F n) 1 0)
     let W := fun (n : ℕ) z => N n*effectVariance (F n) 1 0 z
     Tendsto (fun n : ℕ => N n*V n) atTop (𝓝 8) ∧
     ConvergesInProbability P W 6 ∧
     ConvergesInProbability P (fun (n : ℕ) z => effectVariance (F n) 1 0 z / V n) (3/4) ∧
     Tendsto (fun n : ℕ => variance (P n) (W n) / (4*N n)) atTop (𝓝 1) ∧
     Tendsto (fun n : ℕ => variance (P n) (W n)) atTop atTop ∧
     TendsNormal P (fun (n : ℕ) z => Real.sqrt (N n)*htEffect (F n) 1 0 z) 0 8 ∧
     (∀ α : ℝ, 0 < α → α < 1 →
       Tendsto (fun n : ℕ => probability (P n) (fun z =>
         |htEffect (F n) 1 0 z-causalEffect (F n) 1 0| ≤
           normalCritical α*Real.sqrt (effectVariance (F n) 1 0 z))) atTop
         (𝓝 (2*normalCDF (normalCritical α*Real.sqrt (3/4))-1)) ∧
       2*normalCDF (normalCritical α*Real.sqrt (3/4))-1 < 1-α)) := by
  constructor
  · intro r hr
    have h := paired_finite_hypotheses r hr
    exact ⟨h.1, h.2.2⟩
  · exact ⟨pas_NV_limit, pas_W_limit, pas_ratio_limit, pas_normalized_var_limit,
      pas_var_diverges, pas_scaled_normal, fun α hα hα1 =>
        ⟨pas_coverage_limit α hα hα1, pas_strict_undercoverage α hα hα1⟩⟩

theorem paired_finite_identities_proof (r : ℕ) (hr : 2 ≤ r) :
    let F := pairedPopulation r hr
    let P := pairedDesign r hr
    let N := (2*r : ℕ)
    let t := pairSplitProbability N
    causalEffect F 1 0 = 0 ∧
    (∀ z, htEffect F 1 0 z = (∑ a, pairScore (z a))/(N : ℝ) ∧
      (N : ℝ)^2*effectVariance F 1 0 z = ∑ a, pairVarianceScore N (z a) ∧
      0 < effectVariance F 1 0 z) ∧
    variance P (htEffect F 1 0) = 8*t/(N : ℝ) ∧
    expectation P (effectVariance F 1 0) = variance P (htEffect F 1 0) ∧
    probability P (allPairsSplit r) = t^r ∧
    probability P (fun z => ¬ allPairsSplit r z) ≤ 1/(N : ℝ) ∧
    (∀ z, allPairsSplit r z → (N : ℝ)*effectVariance F 1 0 z = 8-2/t) ∧
    variance P (fun z => (N : ℝ)*effectVariance F 1 0 z) =
      4*((N : ℝ)-2)^4*((N : ℝ)+2)^4 / ((N : ℝ)^5*((N : ℝ)^2-2)) := by
  exact pfi_identities r hr

end
end AronowAudit.P013.Wave1
