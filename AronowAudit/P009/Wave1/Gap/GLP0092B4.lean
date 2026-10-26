import AronowAudit.P009.P009_MinimizerCompletion
import AronowAudit.P009.P009_SharpnessCompletion

namespace AronowAudit.P009.Wave1

open scoped BigOperators Topology
open Filter

noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

/-- A square-root clique already satisfies every requested upper degree rate. -/
def t51_h (n : ℕ) : ℕ := ⌈Real.sqrt (n : ℝ)⌉₊

def t51_D (n h : ℕ) : ℝ := ((h : ℝ)^2 + n - h) / n

lemma t51_parameters {n : ℕ} (hn : 0 < n) :
    1 ≤ t51_h n ∧ t51_h n ≤ n ∧
    Real.sqrt (n : ℝ) ≤ t51_h n ∧
    (t51_h n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) ∧
    (n : ℝ) ≤ (t51_h n : ℝ)^2 ∧
    1 ≤ t51_D n (t51_h n) ∧ t51_D n (t51_h n) ≤ 5 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hs1 : 1 ≤ Real.sqrt (n : ℝ) := Real.one_le_sqrt.mpr hn1
  have hh1 : 1 ≤ t51_h n := Nat.one_le_ceil_iff.mpr (Real.sqrt_pos.mpr hnR)
  have hhn : t51_h n ≤ n := Nat.ceil_le.mpr (Real.sqrt_le_self_iff.mpr (Or.inr hn1))
  have hhlo : Real.sqrt (n : ℝ) ≤ t51_h n := Nat.le_ceil _
  have hhhi : (t51_h n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by
    have hc := Nat.ceil_lt_add_one (Real.sqrt_nonneg (n : ℝ))
    change (t51_h n : ℝ) < Real.sqrt (n : ℝ) + 1 at hc
    linarith
  have hsq : (n : ℝ) ≤ (t51_h n : ℝ)^2 := by
    nlinarith [Real.sq_sqrt hnR.le, Real.sqrt_nonneg (n : ℝ),
      sq_nonneg ((t51_h n : ℝ) - Real.sqrt (n : ℝ))]
  have hhR : (1 : ℝ) ≤ t51_h n := by exact_mod_cast hh1
  have hhnR : (t51_h n : ℝ) ≤ n := by exact_mod_cast hhn
  refine ⟨hh1, hhn, hhlo, hhhi, hsq, ?_, ?_⟩
  · rw [t51_D, le_div_iff₀ hnR]
    nlinarith
  · rw [t51_D, div_le_iff₀ hnR]
    have hsqhi : (t51_h n : ℝ)^2 ≤ 4 * n := by
      nlinarith [Real.sq_sqrt hnR.le, Real.sqrt_nonneg (n : ℝ),
        mul_nonneg (sub_nonneg.mpr hhhi)
          (show 0 ≤ 2 * Real.sqrt (n : ℝ) + (t51_h n : ℝ) by positivity)]
    linarith

lemma t51_h_grows (S : Study) : Tendsto (fun t => t51_h (S.N t)) atTop atTop :=
  tendsto_nat_ceil_atTop.comp
    (Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp S.grows))

lemma t51_regular_bounded {n : ℕ} (E : Experiment n) (k : ℝ) (hk : 0 < k)
    (hA : ∀ i, k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1-k⁻¹)
    (B : ℝ) (y : Fin n → Assignment n → ℝ)
    (hy : ∀ i z, |y i z| ≤ B) :
    Regular ({E with outcome := y} : Experiment n) (max k B) 4 1 := by
  let K := max k B
  have hK : 0 < K := hk.trans_le (le_max_left _ _)
  have hKi : K⁻¹ ≤ k⁻¹ := inv_le_inv₀ hK hk |>.mpr (le_max_left _ _)
  have hBK : B ≤ K := le_max_right _ _
  refine ⟨hK, by norm_num, by norm_num, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hKi.trans (hA i).1, (hA i).2.trans (by linarith)⟩
  · intro i
    calc
      _ ≤ mean E.design (fun _ => Real.rpow K 4) := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) ((hy i z).trans hBK) (by norm_num))
          (E.design.nonneg z)
      _ = _ := mean_const _ _
  · intro i b
    calc
      _ ≤ mean E.design (fun _ => Real.rpow K 1) := by
        apply Finset.sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _)
            ((hy i (Function.update z i b)).trans hBK) (by norm_num)) (E.design.nonneg z)
      _ = _ := mean_const _ _

lemma t51_zero_regular {n : ℕ} (E : Experiment n) (k : ℝ) (hk : 0 < k)
    (hA : ∀ i, k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1-k⁻¹) :
    Regular ({E with outcome := fun _ _ => 0} : Experiment n) k 4 1 := by
  simpa only [max_eq_left hk.le] using
    t51_regular_bounded E k hk hA 0 (fun _ _ => 0) (by simp)

/-- Altering two atoms changes every event probability by at most their total mass. -/
lemma t51_prob_edit {Ω : Type*} [Fintype Ω] (P : Law Ω) (A B : Ω → Prop)
    (a b : Ω) (h : ∀ w, w ≠ a → w ≠ b → (A w ↔ B w)) :
    |prob P A - prob P B| ≤ P.mass a + P.mass b := by
  classical
  unfold prob mean
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ w, |P.mass w * (if A w then 1 else 0) -
        P.mass w * (if B w then 1 else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, ((if w = a then P.mass w else 0) +
        (if w = b then P.mass w else 0)) := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hwa : w = a <;> by_cases hwb : w = b
      · subst w
        subst b
        by_cases ha : A a <;> by_cases hb : B a <;>
          simp [ha, hb, P.nonneg, abs_of_nonneg] <;> linarith [P.nonneg a]
      · subst w
        by_cases ha : A a <;> by_cases hb : B a <;>
          simp [ha, hb, hwb, P.nonneg, abs_of_nonneg]
      · subst w
        by_cases ha : A b <;> by_cases hb : B b <;>
          simp [ha, hb, hwa, P.nonneg, abs_of_nonneg]
      · simp only [hwa, hwb, ite_false, zero_add]
        have he : (if A w then (1 : ℝ) else 0) = (if B w then 1 else 0) :=
          if_congr (h w hwa hwb) rfl rfl
        rw [he, sub_self, abs_zero]
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Rare adjacent anchors make the common parent visible on the full cube. -/
lemma t51_anchored_map {b : ℕ} (hb : 0 < b) (P : Law (Assignment b))
    (δ α : ℝ) (hδ : ∀ w, P.mass w ≤ δ) (hα : 0 < α ∧ α < 1) :
    ∃ f : Assignment b → ℝ,
      (∀ w, f w = -1 ∨ f w = 0 ∨ f w = 1) ∧
      f (fun _ => false) = 0 ∧
      f (Function.update (fun _ => false) ⟨0,hb⟩ true) = 1 ∧
      |prob P (fun w => f w = 1)-α/2| ≤ 3*δ ∧
      |prob P (fun w => f w = -1)-α/2| ≤ 3*δ := by
  classical
  obtain ⟨g, hg, hp, hm⟩ := three_point_atom_approximation P δ α hδ hα
  let a : Assignment b := fun _ => false
  let c : Assignment b := Function.update a ⟨0,hb⟩ true
  have hac : a ≠ c := by
    intro he
    have ht := congrFun he ⟨0,hb⟩
    simp [a, c] at ht
  let f := Function.update (Function.update g a 0) c 1
  have he (w : Assignment b) (hwa : w ≠ a) (hwc : w ≠ c) : f w = g w := by
    simp [f, hwa, hwc]
  have hprob (v : ℝ) : |prob P (fun w => f w = v)-prob P (fun w => g w = v)| ≤ 2*δ := by
    calc
      _ ≤ P.mass a + P.mass c := t51_prob_edit P _ _ a c (by
        intro w hwa hwc
        rw [he w hwa hwc])
      _ ≤ _ := by linarith [hδ a, hδ c]
  refine ⟨f, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    by_cases hwc : w = c
    · simp [f, hwc]
    · by_cases hwa : w = a
      · simp [f, hwa, hac]
      · rw [he w hwa hwc]; exact hg w
  · simp [f, hac, a]
  · simp [f, c, a]
  · calc
      _ ≤ |prob P (fun w => f w = 1)-prob P (fun w => g w = 1)| +
          |prob P (fun w => g w = 1)-α/2| := abs_sub_le _ _ _
      _ ≤ _ := by linarith [hprob 1]
  · calc
      _ ≤ |prob P (fun w => f w = -1)-prob P (fun w => g w = -1)| +
          |prob P (fun w => g w = -1)-α/2| := abs_sub_le _ _ _
      _ ≤ _ := by linarith [hprob (-1)]

/-- Restriction to an initial segment, with its size bound explicit. -/
def t51_prefix {n : ℕ} (h : ℕ) (hh : h ≤ n) (z : Assignment n) : Assignment h :=
  fun i => z ⟨i.val, lt_of_lt_of_le i.isLt hh⟩

lemma t51_prefix_singleton {n h : ℕ} (hn : 0 < n) (hh0 : 0 < h) (hh : h ≤ n) :
    t51_prefix h hh (Function.update (fun _ => false) ⟨0,hn⟩ true) =
      Function.update (fun _ => false) ⟨0,hh0⟩ true := by
  funext i
  by_cases hi : i.val = 0
  · have he : i = ⟨0,hh0⟩ := Fin.ext hi
    subst i
    simp [t51_prefix]
  · have he : i ≠ ⟨0,hh0⟩ := by intro he; exact hi (congrArg Fin.val he)
    have he' : (⟨i.val, lt_of_lt_of_le i.isLt hh⟩ : Fin n) ≠ ⟨0,hn⟩ := by
      intro he; exact hi (congrArg Fin.val he)
    simp [t51_prefix, he, he']

def t51_outcome {n : ℕ} (E : Experiment n) (h : ℕ) (F : Assignment n → ℝ)
    (i : Fin n) (z : Assignment n) : ℝ :=
  if i.val < h then (1/(h:ℝ))*Real.sqrt n*Real.sqrt (t51_D n h)*
    (bit (z i)*marginal E i true-(1-bit (z i))*marginal E i false)*F z else 0

def t51_experiment {n : ℕ} (E : Experiment n) (h : ℕ) (F : Assignment n → ℝ) :
    Experiment n := {E with outcome := t51_outcome E h F}

lemma t51_scale_pos {n h : ℕ} (hn : 0 < n) (hh : 1 ≤ h) :
    0 < (1/(h:ℝ))*Real.sqrt n*Real.sqrt (t51_D n h) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh
  have hD : 0 < t51_D n h := by
    rw [t51_D]
    apply div_pos _ hnR
    nlinarith
  exact mul_pos (mul_pos (by positivity) (Real.sqrt_pos.mpr hnR)) (Real.sqrt_pos.mpr hD)

lemma t51_parent_upper {n : ℕ} (E : Experiment n) (h : ℕ)
    (F : Assignment n → ℝ) (hF : DependsOn F {i | i.val < h}) (l i : Fin n)
    (hI : Interferes (t51_experiment E h F) l i) :
    l = i ∨ l.val < h ∧ i.val < h := by
  rcases hI with hi | ⟨z, z', hagree, hne⟩
  · exact Or.inl hi
  · by_cases hli : l = i
    · exact Or.inl hli
    · have hi : i.val < h := by
        by_contra hi
        exact hne (by simp [t51_experiment, t51_outcome, hi])
      have hl : l.val < h := by
        by_contra hl
        have hFF : F z = F z' := hF (by
          intro j hj
          apply hagree j
          intro he
          subst j
          exact hl hj)
        apply hne
        simp only [t51_experiment, t51_outcome, hi, if_true]
        rw [hagree i (Ne.symm hli), hFF]
      exact Or.inr ⟨hl, hi⟩

lemma t51_zero_parent {n : ℕ} (hn : 0 < n) (E : Experiment n) (h : ℕ)
    (hh : 1 ≤ h) (hp : ∀ i b, 0 < marginal E i b) (F : Assignment n → ℝ)
    (hF0 : F (fun _ => false) = 0)
    (hF1 : F (Function.update (fun _ => false) ⟨0,hn⟩ true) = 1)
    (i : Fin n) (hi : i.val < h) :
    Interferes (t51_experiment E h F) ⟨0,hn⟩ i := by
  let o : Fin n := ⟨0,hn⟩
  have hA := t51_scale_pos hn hh
  refine Or.inr ⟨(fun _ => false), Function.update (fun _ => false) o true, ?_, ?_⟩
  · intro j hj
    simp [o, hj]
  · change t51_outcome E h F i (fun _ => false) ≠
      t51_outcome E h F i (Function.update (fun _ => false) o true)
    by_cases hio : i = o
    · subst i
      simpa [t51_outcome, o, show 0 < h by omega, bit, hF0, hF1] using
        (mul_ne_zero hA.ne' (hp o true).ne').symm
    · simpa [t51_outcome, hi, hF0,
        show F (Function.update (fun _ => false) o true) = 1 from hF1,
        bit, Function.update_of_ne hio] using
        (mul_ne_zero hA.ne' (neg_ne_zero.mpr (hp i false).ne')).symm

lemma t51_dependent_iff {n : ℕ} (hn : 0 < n) (E : Experiment n) (h : ℕ)
    (hh : 1 ≤ h) (hp : ∀ i b, 0 < marginal E i b)
    (F : Assignment n → ℝ) (hF : DependsOn F {i | i.val < h})
    (hF0 : F (fun _ => false) = 0)
    (hF1 : F (Function.update (fun _ => false) ⟨0,hn⟩ true) = 1) (i j : Fin n) :
    Dependent (t51_experiment E h F) i j ↔ i = j ∨ i.val < h ∧ j.val < h := by
  constructor
  · rintro ⟨l, hi, hj⟩
    rcases t51_parent_upper E h F hF l i hi with hi | ⟨hl, hi⟩ <;>
      rcases t51_parent_upper E h F hF l j hj with hj | ⟨hl', hj⟩
    · exact Or.inl (hi.symm.trans hj)
    · exact Or.inr ⟨by simpa [← hi] using hl', hj⟩
    · exact Or.inr ⟨hi, by simpa [← hj] using hl⟩
    · exact Or.inr ⟨hi, hj⟩
  · rintro (rfl | ⟨hi, hj⟩)
    · exact ⟨i, Or.inl rfl, Or.inl rfl⟩
    · exact ⟨⟨0,hn⟩, t51_zero_parent hn E h hh hp F hF0 hF1 i hi,
        t51_zero_parent hn E h hh hp F hF0 hF1 j hj⟩

/-- Counts for a prefix clique with all remaining vertices isolated. -/
lemma t51_graph_counts {n h : ℕ} (hn : 0 < n) (hh : 1 ≤ h ∧ h ≤ n)
    (E : Experiment n)
    (hgraph : ∀ i j, Dependent E i j ↔ i = j ∨ i.val < h ∧ j.val < h) :
    (∀ i, degree E i = if i.val < h then (h : ℝ) else 1) ∧
    dAvg E = t51_D n h ∧ dMax E = h := by
  have hrow (i : Fin n) : degree E i = if i.val < h then (h : ℝ) else 1 := by
    unfold degree d
    simp only [hgraph]
    by_cases hi : i.val < h
    · have he (j : Fin n) : (i = j ∨ i.val < h ∧ j.val < h) ↔ j.val < h := by
        constructor
        · rintro (rfl | ⟨_, hj⟩) <;> assumption
        · intro hj; exact Or.inr ⟨hi, hj⟩
      simp_rw [he]
      rw [SharpnessCompletion.prefix_count h hh.2]
      simp [hi]
    · simp [hi]
  refine ⟨hrow, ?_, ?_⟩
  · have hrow' (i : Fin n) : (if i.val < h then (h : ℝ) else 1) =
        1 + ((h : ℝ)-1)*(if i.val < h then 1 else 0) := by split_ifs <;> ring
    rw [dAvg]
    simp_rw [hrow, hrow']
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, SharpnessCompletion.prefix_count h hh.2]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    unfold t51_D
    congr 1
    ring
  · have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh.1
    have hb : BddAbove (Set.range (degree E)) := (Set.finite_range _).bddAbove
    apply le_antisymm
    · apply csSup_le (Set.range_nonempty_iff_nonempty.mpr ⟨⟨0,hn⟩⟩)
      rintro r ⟨i, rfl⟩
      rw [hrow]
      split_ifs <;> linarith
    · have he : degree E ⟨0,hn⟩ = h := by rw [hrow, if_pos (show (⟨0,hn⟩ : Fin n).val < h by change 0 < h; omega)]
      exact he ▸ le_csSup hb ⟨⟨0,hn⟩, rfl⟩

lemma t51_outcome_bound {n : ℕ} (hn : 0 < n) (E : Experiment n)
    (hBER : Bernoulli E) (F : Assignment n → ℝ) (hF : ∀ z, |F z| ≤ 1) :
    ∀ i z, |t51_outcome E (t51_h n) F i z| ≤ 2 := by
  let h := t51_h n
  have hpar := t51_parameters hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hhR : (0 : ℝ) < h := by exact_mod_cast (show 0 < h from hpar.1)
  let A : ℝ := (1/(h:ℝ))*Real.sqrt n*Real.sqrt (t51_D n h)
  have hA : 0 ≤ A := (t51_scale_pos hn hpar.1).le
  have hsN := Real.sq_sqrt hnR.le
  have hsD := Real.sq_sqrt (show 0 ≤ t51_D n h by linarith [hpar.2.2.2.2.2.1])
  have hA2 : A^2 ≤ 2 := by
    have he : A^2 = ((h : ℝ)^2 + n - h)/(h : ℝ)^2 := by
      dsimp [A]
      rw [mul_pow, mul_pow, hsN, hsD, t51_D]
      field_simp
    rw [he, div_le_iff₀ (sq_pos_of_pos hhR)]
    have := hpar.2.2.2.2.1
    change (n : ℝ) ≤ (h : ℝ)^2 at this
    nlinarith
  have hAhi : A ≤ 2 := by nlinarith
  have hp (i : Fin n) (b : Bool) : 0 ≤ marginal E i b ∧ marginal E i b ≤ 1 := by
    cases b
    · have := marginal_partition E i
      constructor <;> linarith [(hBER.1 i).1, (hBER.1 i).2]
    · exact ⟨(hBER.1 i).1.le, (hBER.1 i).2.le⟩
  intro i z
  have hcoef : |bit (z i)*marginal E i true-(1-bit (z i))*marginal E i false| ≤ 1 := by
    cases hz : z i
    · simpa [bit, hz, abs_of_nonneg (hp i false).1] using (hp i false).2
    · simpa [bit, hz, abs_of_nonneg (hp i true).1] using (hp i true).2
  by_cases hi : i.val < h
  · change |if i.val < h then A * _ * F z else 0| ≤ 2
    rw [if_pos hi, abs_mul, abs_mul, abs_of_nonneg hA]
    calc
      _ ≤ A * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hcoef hA) (hF z)
        (abs_nonneg _) (by simpa using hA)
      _ ≤ 2 := by simpa using hAhi
  · simp [t51_outcome, show ¬ i.val < t51_h n from hi]

lemma t51_prefix_depends {n h : ℕ} (hh : h ≤ n) (f : Assignment h → ℝ) :
    DependsOn (fun z => f (t51_prefix h hh z)) {i | i.val < h} := by
  intro z z' hagree
  apply congrArg f
  funext i
  exact hagree ⟨i.val, lt_of_lt_of_le i.isLt hh⟩ i.isLt

lemma t51_row_graph {n : ℕ} (hn : 0 < n) (E : Experiment n) (hBER : Bernoulli E)
    (f : Assignment (t51_h n) → ℝ) (hf0 : f (fun _ => false) = 0)
    (hf1 : f (Function.update (fun _ => false)
      ⟨0, (t51_parameters hn).1⟩ true) = 1) :
    let F := fun z => f (t51_prefix (t51_h n) (t51_parameters hn).2.1 z)
    dAvg (t51_experiment E (t51_h n) F) = t51_D n (t51_h n) ∧
      dMax (t51_experiment E (t51_h n) F) = t51_h n := by
  let F := fun z => f (t51_prefix (t51_h n) (t51_parameters hn).2.1 z)
  have hF0 : F (fun _ => false) = 0 := hf0
  have hF1 : F (Function.update (fun _ => false) ⟨0,hn⟩ true) = 1 := by
    dsimp [F]
    rw [t51_prefix_singleton hn (t51_parameters hn).1, hf1]
  have hp (i : Fin n) (b : Bool) : 0 < marginal E i b :=
    BernoulliCompletion.marginal_pos E hBER i b
  exact (t51_graph_counts hn ⟨(t51_parameters hn).1, (t51_parameters hn).2.1⟩ _
    (t51_dependent_iff hn E _ (t51_parameters hn).1 hp F
      (t51_prefix_depends _ f) hF0 hF1)).2

lemma t51_centered_ht {n h : ℕ} (hn : 0 < n) (E : Experiment n) (hBER : Bernoulli E)
    (hh : 1 ≤ h ∧ h ≤ n) (F : Assignment n → ℝ)
    (hDpos : 0 < t51_D n h)
    (hD : dAvg (t51_experiment E h F) = t51_D n h) (z : Assignment n) :
    Real.sqrt (n : ℝ) / Real.sqrt (dAvg (t51_experiment E h F)) *
      (ht (t51_experiment E h F) z -
        mean (t51_experiment E h F).design (ht (t51_experiment E h F))) =
      F z - mean E.design F := by
  have hht : ∀ z, ht (t51_experiment E h F) z =
      Real.sqrt (t51_D n h)/Real.sqrt (n : ℝ)*F z :=
    sharpness_HT_construction hn E hBER h hh F (t51_D n h)
  have hm : mean (t51_experiment E h F).design (ht (t51_experiment E h F)) =
      Real.sqrt (t51_D n h)/Real.sqrt (n : ℝ)*mean E.design F := by
    calc
      _ = mean E.design (fun z => Real.sqrt (t51_D n h)/Real.sqrt (n : ℝ)*F z) := by
        apply congrArg (mean E.design)
        funext z
        exact hht z
      _ = _ := mean_const_mul _ _ _
  rw [hD, hht z, hm]
  have hn0 : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by exact_mod_cast hn)
  have hD0 : Real.sqrt (t51_D n h) ≠ 0 := Real.sqrt_ne_zero'.mpr hDpos
  field_simp
  <;> ring

lemma t51_mean_three {Ω : Type*} [Fintype Ω] (P : Law Ω) (F : Ω → ℝ)
    (hF : ∀ w, F w = -1 ∨ F w = 0 ∨ F w = 1) :
    mean P F = prob P (fun w => F w = 1) - prob P (fun w => F w = -1) := by
  calc
    _ = mean P (fun w => (if F w = 1 then 1 else 0) -
        (if F w = -1 then 1 else 0)) := by
      apply congrArg (mean P)
      funext w
      rcases hF w with hw | hw | hw <;> norm_num [hw]
    _ = _ := mean_sub _ _ _

/-- All three jumps are positive, so every continuity point avoids the support. -/
lemma t51_continuity_point (α : ℝ) (hα : 0 < α ∧ α < 1) (u : ℝ)
    (hu : ContinuousAt (sharpCDF α) u) : u ≠ -1 ∧ u ≠ 0 ∧ u ≠ 1 := by
  let ε := fun t : ℕ => 1 / ((t : ℝ) + 1)
  have hε : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos (t : ℕ) : 0 < ε t := by dsimp [ε]; positivity
  have hε1 (t : ℕ) : ε t ≤ 1 := by
    dsimp [ε]
    rw [div_le_iff₀ (show (0 : ℝ) < (t : ℝ) + 1 by positivity)]
    linarith [show (0 : ℝ) ≤ (t : ℝ) from Nat.cast_nonneg t]
  refine ⟨?_, ?_, ?_⟩
  · intro he
    subst u
    have ht : Tendsto (fun t => (-1 : ℝ) - ε t) atTop (nhds (-1)) := by
      simpa using tendsto_const_nhds.sub hε
    have hleft : Tendsto (fun t => sharpCDF α ((-1 : ℝ)-ε t)) atTop (nhds 0) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0)) using 1
      funext t
      simp [sharpCDF, show (-1 : ℝ)-ε t < -1 by linarith [hεpos t]]
    have heq := tendsto_nhds_unique (hu.tendsto.comp ht) hleft
    norm_num [sharpCDF] at heq
    linarith [hα.1]
  · intro he
    subst u
    have ht : Tendsto (fun t => -ε t) atTop (nhds 0) := by simpa using hε.neg
    have hleft : Tendsto (fun t => sharpCDF α (-ε t)) atTop (nhds (α/2)) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => α/2) atTop (nhds (α/2))) using 1
      funext t
      simp [sharpCDF, show ¬ -ε t < -1 by linarith [hε1 t],
        show -ε t < 0 by linarith [hεpos t]]
    have heq := tendsto_nhds_unique (hu.tendsto.comp ht) hleft
    norm_num [sharpCDF] at heq
    linarith [hα.2]
  · intro he
    subst u
    have ht : Tendsto (fun t => (1 : ℝ) - ε t) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hε
    have hleft : Tendsto (fun t => sharpCDF α (1-ε t)) atTop (nhds (1-α/2)) := by
      convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1-α/2) atTop (nhds (1-α/2))) using 1
      funext t
      simp [sharpCDF, show ¬ 1-ε t < -1 by linarith [hε1 t],
        show ¬ 1-ε t < 0 by linarith [hε1 t], show 1-ε t < 1 by linarith [hεpos t]]
    have heq := tendsto_nhds_unique (hu.tendsto.comp ht) hleft
    norm_num [sharpCDF] at heq
    linarith [hα.1]

lemma t51_centered_cdf_limit (Ω : ℕ → Type*) [∀ t, Fintype (Ω t)]
    (P : (t : ℕ) → Law (Ω t)) (F : (t : ℕ) → Ω t → ℝ)
    (hF : ∀ t w, F t w = -1 ∨ F t w = 0 ∨ F t w = 1) (α : ℝ)
    (hα : 0 < α ∧ α < 1)
    (hm : Tendsto (fun t => prob (P t) (fun w => F t w = -1)) atTop (nhds (α/2)))
    (hp : Tendsto (fun t => prob (P t) (fun w => F t w = 1)) atTop (nhds (α/2))) :
    ∀ u, ContinuousAt (sharpCDF α) u → Tendsto
      (fun t => prob (P t) (fun w => F t w - mean (P t) (F t) ≤ u))
        atTop (nhds (sharpCDF α u)) := by
  have hμ : Tendsto (fun t => mean (P t) (F t)) atTop (nhds 0) := by
    have he (t) := t51_mean_three (P t) (F t) (hF t)
    simp_rw [he]
    simpa only [sub_self] using hp.sub hm
  intro u hu
  have hsupport := t51_continuity_point α hα u hu
  have hevent := centering_shift_eventually _ hμ u hsupport
  have heq : ∀ᶠ t in atTop,
      prob (P t) (fun w => F t w - mean (P t) (F t) ≤ u) =
        prob (P t) (fun w => F t w ≤ u) := by
    filter_upwards [hevent] with t ht
    exact three_point_centering (P t) (F t) (hF t) u hsupport ht
  exact (tendsto_congr' heq).mpr (three_point_CDF_limit Ω P F hF α hα hm hp u)

lemma t51_error_tendsto (p e : ℕ → ℝ) (a : ℝ)
    (he : Tendsto e atTop (nhds 0)) (hp : ∀ t, |p t-a| ≤ e t) :
    Tendsto p atTop (nhds a) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using tendsto_const_nhds.sub he) (by simpa using tendsto_const_nhds.add he)
  · intro t
    have := (abs_le.mp (hp t)).1
    linarith
  · intro t
    have := (abs_le.mp (hp t)).2
    linarith

theorem chebyshev_asymptotic_sharpness_proof (S : Study) (k α x : ℝ) (hk : 0 < k)
    (hA : ∀ t i, k⁻¹ ≤ marginal (S.experiment t) i true ∧
      marginal (S.experiment t) i true ≤ 1-k⁻¹)
    (hBER : ∀ t, Bernoulli (S.experiment t)) (hα : 0 < α ∧ α < 1)
    (hx : 0 ≤ x ∧ x < 1) :
    ∃ y : (t : ℕ) → Fin (S.N t) → Assignment (S.N t) → ℝ,
      let S' : Study := {S with experiment := fun t => {S.experiment t with outcome := y t}}
      (∃ K q s, RegularSequence S' K q s) ∧ Restricted S' ∧
      BigO (fun t => dAvg (S'.experiment t)) (fun t => Real.rpow (size S' t) x) ∧
      (x = 0 → BigO (fun t => dMax (S'.experiment t)) (fun t => Real.sqrt (size S' t))) ∧
      InDistribution S' (fun t z => Real.sqrt (size S' t)/Real.sqrt (dAvg (S'.experiment t))*
        (ht (S'.experiment t) z-mean (S'.experiment t).design (ht (S'.experiment t))))
        (sharpCDF α) := by
  let b := fun t => t51_h (S.N t)
  have hb (t) : 1 ≤ b t ∧ b t ≤ S.N t :=
    ⟨(t51_parameters (S.positive t)).1, (t51_parameters (S.positive t)).2.1⟩
  let R := fun t => t51_prefix (b t) (hb t).2
  let P := fun t => AtomCompletion.imageLaw (S.experiment t).design (R t)
  have hzero (t) : Regular ({S.experiment t with outcome := fun _ _ => 0} :
      Experiment (S.N t)) k 4 1 := t51_zero_regular _ k hk (hA t)
  have hatom (t) (w : Assignment (b t)) : (P t).mass w ≤ (1-k⁻¹)^b t := by
    exact AtomCompletion.prefix_atom_bound
      {S.experiment t with outcome := fun _ _ => 0} k 4 1 (hzero t) (hBER t)
        (b t) (hb t).2 w
  have hmaps (t) := t51_anchored_map (hb t).1 (P t) ((1-k⁻¹)^b t) α (hatom t) hα
  choose f hf hf0 hf1 hp hm using hmaps
  let F := fun t z => f t (R t z)
  have hF (t) (z) : F t z = -1 ∨ F t z = 0 ∨ F t z = 1 := hf t (R t z)
  have hFbound (t) (z) : |F t z| ≤ 1 := by
    rcases hF t z with hz | hz | hz <;> norm_num [hz]
  have hp' (t) : |prob (S.experiment t).design (fun z => F t z = 1)-α/2| ≤
      3*(1-k⁻¹)^b t := by
    simpa only [P, F, AtomCompletion.image_prob] using hp t
  have hm' (t) : |prob (S.experiment t).design (fun z => F t z = -1)-α/2| ≤
      3*(1-k⁻¹)^b t := by
    simpa only [P, F, AtomCompletion.image_prob] using hm t
  have hk2 := BernoulliCompletion.regular_k_ge_two (S.positive 0) _ k 4 1 (hzero 0)
  have hρ0 : 0 ≤ 1-k⁻¹ := by
    have hi : k⁻¹ ≤ 1 := (inv_le_one₀ hk).mpr (by linarith)
    linarith
  have hρ1 : 1-k⁻¹ < 1 := by linarith [inv_pos.mpr hk]
  have hδ : Tendsto (fun t => 3*(1-k⁻¹)^b t) atTop (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).comp
      (t51_h_grows S)).const_mul 3
  have hplus := t51_error_tendsto _ _ (α/2) hδ hp'
  have hminus := t51_error_tendsto _ _ (α/2) hδ hm'
  let S' : Study := {S with experiment := fun t => t51_experiment (S.experiment t) (b t) (F t)}
  have hgraph (t) : dAvg (S'.experiment t) = t51_D (S.N t) (b t) ∧
      dMax (S'.experiment t) = b t := by
    exact t51_row_graph (S.positive t) _ (hBER t) (f t) (hf0 t) (hf1 t)
  have hDbounds (t) : 1 ≤ t51_D (S.N t) (b t) ∧ t51_D (S.N t) (b t) ≤ 5 :=
    (t51_parameters (S.positive t)).2.2.2.2.2
  have hbounded : BigO (fun t => dAvg (S'.experiment t)) (fun _ => 1) := by
    refine ⟨5, by norm_num, Eventually.of_forall ?_⟩
    intro t
    change |dAvg (S'.experiment t)| ≤ 5 * |(1 : ℝ)|
    rw [(hgraph t).1, abs_of_nonneg (zero_le_one.trans (hDbounds t).1), abs_one, mul_one]
    exact (hDbounds t).2
  have hcentered (t) (z) :
      Real.sqrt (size S' t)/Real.sqrt (dAvg (S'.experiment t))*
        (ht (S'.experiment t) z-mean (S'.experiment t).design (ht (S'.experiment t))) =
      F t z - mean (S.experiment t).design (F t) := by
    exact t51_centered_ht (S.positive t) _ (hBER t) (hb t) (F t)
      (zero_lt_one.trans_le (hDbounds t).1) (hgraph t).1 z
  refine ⟨fun t => t51_outcome (S.experiment t) (b t) (F t), ?_⟩
  change (∃ K q s, RegularSequence S' K q s) ∧ Restricted S' ∧
    BigO (fun t => dAvg (S'.experiment t)) (fun t => Real.rpow (size S' t) x) ∧
    (x = 0 → BigO (fun t => dMax (S'.experiment t)) (fun t => Real.sqrt (size S' t))) ∧
    InDistribution S' (fun t z => Real.sqrt (size S' t)/Real.sqrt (dAvg (S'.experiment t))*
      (ht (S'.experiment t) z-mean (S'.experiment t).design (ht (S'.experiment t)))) (sharpCDF α)
  refine ⟨?_, BernoulliCompletion.restricted_of_bounded_degree S' hbounded, ?_, ?_, ?_⟩
  · refine ⟨max k 2, 4, 1, ?_⟩
    intro t
    exact t51_regular_bounded (S.experiment t) k hk (hA t) 2
      (t51_outcome (S.experiment t) (b t) (F t))
      (t51_outcome_bound (S.positive t) _ (hBER t) (F t) (hFbound t))
  · refine ⟨5, by norm_num, Eventually.of_forall ?_⟩
    intro t
    have hN : (1 : ℝ) ≤ size S' t := by
      change (1 : ℝ) ≤ S.N t
      exact_mod_cast S.positive t
    have hpow : 1 ≤ Real.rpow (size S' t) x := Real.one_le_rpow hN hx.1
    change |dAvg (S'.experiment t)| ≤ 5 * |Real.rpow (size S' t) x|
    rw [(hgraph t).1, abs_of_nonneg (zero_le_one.trans (hDbounds t).1),
      abs_of_nonneg (zero_le_one.trans hpow)]
    nlinarith [(hDbounds t).2]
  · intro _
    refine ⟨2, by norm_num, Eventually.of_forall ?_⟩
    intro t
    change |dMax (S'.experiment t)| ≤ 2 * |Real.sqrt (size S' t)|
    rw [(hgraph t).2, abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (t51_parameters (S.positive t)).2.2.2.1
  · intro u hu
    simp_rw [hcentered]
    exact t51_centered_cdf_limit (fun t => Assignment (S.N t))
      (fun t => (S.experiment t).design) F hF α hα hminus hplus u hu

end
end AronowAudit.P009.Wave1
