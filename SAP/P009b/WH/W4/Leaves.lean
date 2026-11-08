import SAP.P009b.Defs.WholeW4
import SAP.P009b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace SAP.P009b.WH.W4
noncomputable section
attribute [local instance] Classical.propDecidable

/-- A single unordered pair is closed under the pairing involution. -/
theorem own_pair_closed {n : ℕ} (ρ : Pairing n) (i ℓ : Fin n) :
    ρ.partner ℓ ∈ ({i, ρ.partner i} : Set (Fin n)) ↔
      ℓ ∈ ({i, ρ.partner i} : Set (Fin n)) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · right
      have hh := congrArg ρ.partner h
      simpa only [ρ.involution] using hh
    · left
      exact ρ.partner.injective h
  · rintro (h | h)
    · subst ℓ
      exact Or.inr rfl
    · rw [h, ρ.involution]
      exact Or.inl rfl

/-- Binary factorization of every closed block from its complement implies
mutual factorization of every finite disjoint family. Induct on the family;
the remaining product depends only on the complement of the first block. -/
theorem mutual_of_block {n : ℕ} (E : Experiment n) (ρ : Pairing n)
    (hblock : PairBlockFactorizationW4 E ρ) : PairBlocksMutuallyIndependentW4 E ρ := by
  intro m
  induction m with
  | zero =>
      intro S hS hdisj f hf
      simpa [mean] using E.design.total
  | succ m ih =>
      intro S hS hdisj f hf
      have htail := ih (fun a => S a.succ) (fun a => hS a.succ)
        (fun a b hab => hdisj a.succ b.succ (by simpa using hab))
        (fun a => f a.succ) (fun a => hf a.succ)
      have hdep : DependsOnW4 (fun z => ∏ a : Fin m, f a.succ z) (S 0)ᶜ := by
        intro z z' hagree
        apply Finset.prod_congr rfl
        intro a _
        apply hf a.succ z z'
        intro i hi
        apply hagree i
        show i ∉ S 0
        intro h0
        exact Set.disjoint_left.mp (hdisj 0 a.succ (Fin.succ_ne_zero a).symm) h0 hi
      have hprod := hblock (S 0) (hS 0) (f 0)
        (fun z => ∏ a : Fin m, f a.succ z) (hf 0) hdep
      simp only [Fin.prod_univ_succ]
      rw [hprod, htail]

/-- Complete proof blueprint for the corrected T34. No unproved leaves are
needed: the finite-law donors supply the probability and moment arguments;
the remaining proofs export their missing conclusions and assemble finite sums. -/
theorem T34_assembly : T34WholeStatement_W4 := by
  intro n hn E ρ hPair k q s hReg
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmask (i : Fin n) (z : Assignment n) :
      E.outcome i z = E.outcome i (masked E i z) ∧
        ∀ b, potential E i b z = potential E i b (maskedOthers E i z) := by
    constructor
    · apply AronowAudit.P009.BernoulliCompletion.outcome_dependsOn
        (Bridge.toExperiment E) i
      intro j hj
      change Interferes E j i at hj
      simp [masked, hj]
    · intro b
      change E.outcome i (Function.update z i b) =
        E.outcome i (Function.update (maskedOthers E i z) i b)
      apply AronowAudit.P009.BernoulliCompletion.outcome_dependsOn
        (Bridge.toExperiment E) i
      intro j hj
      change Interferes E j i at hj
      by_cases hji : j = i
      · subst j
        simp
      · simp [maskedOthers, masked, hji, hj]
  have hmarg (i : Fin n) (b : Bool) : marginal E i b = 1 / 2 :=
    AronowAudit.P009.PairedCompletion.marginal_half
      (Bridge.toExperiment E) (Bridge.toPairing ρ) hPair i b
  have hopposite (z : Assignment n) (hz : 0 < E.design.mass z) (i : Fin n) :
      z i = !(z (ρ.partner i)) := by
    have hne := AronowAudit.P009.PairedCompletion.supported_opposite
      (Bridge.toExperiment E) (Bridge.toPairing ρ) hPair z hz i
    change z i ≠ z (ρ.partner i) at hne
    cases hzi : z i <;> cases hzp : z (ρ.partner i) <;> simp_all
  have hblock : PairBlockFactorizationW4 E ρ := by
    intro S hS f g hf hg
    exact AronowAudit.P009.PairedCompletion.mean_product_of_closed_partition
      (Bridge.toExperiment E) (Bridge.toPairing ρ) hPair S hS f g hf hg
  have hindicator (i : Fin n) (b : Bool) :
      mean E.design (fun z => if z i = b then (1 : ℝ) else 0) = marginal E i b := by
    unfold marginal prob
    congr 1
    funext z
    by_cases hz : z i = b <;> simp [hz]
  have hdistinct (i j : Fin n) (hij : i ≠ j) (hijp : i ≠ ρ.partner j)
      (a b : Bool) :
      prob E.design (fun z => z i = a ∧ z j = b) =
        marginal E i a * marginal E j b := by
    have hjp : j ≠ ρ.partner i := by
      intro he
      have hh := congrArg ρ.partner he
      rw [ρ.involution] at hh
      exact hijp hh.symm
    let S : Set (Fin n) := {i, ρ.partner i}
    let f := fun z : Assignment n => if z i = a then (1 : ℝ) else 0
    let g := fun z : Assignment n => if z j = b then (1 : ℝ) else 0
    have hf : DependsOnW4 f S := by
      intro z z' h
      simp only [f, h i (by simp [S])]
    have hg : DependsOnW4 g Sᶜ := by
      intro z z' h
      simp only [g, h j (by simp [S, hij.symm, hjp])]
    have hfactor := hblock S (own_pair_closed ρ i) f g hf hg
    have hprod : prob E.design (fun z => z i = a ∧ z j = b) =
        mean E.design (fun z => f z * g z) := by
      unfold prob
      congr 1
      funext z
      by_cases hi : z i = a <;> by_cases hj : z j = b <;> simp [f, g, hi, hj]
    rw [hprod, hfactor]
    exact congrArg₂ (· * ·) (hindicator i a) (hindicator j b)
  have houtside (i : Fin n) (f : Assignment n → ℝ)
      (hf : DependsOnW4 f ({i, ρ.partner i} : Set (Fin n))ᶜ) (b : Bool) :
      mean E.design (fun z => (if z i = b then (1 : ℝ) else 0) * f z) =
        marginal E i b * mean E.design f := by
    have hdep : DependsOnW4
        (fun z => if z i = b then (1 : ℝ) else 0) {i, ρ.partner i} := by
      intro z z' h
      simp only [h i (by simp)]
    have hh := hblock {i, ρ.partner i} (own_pair_closed ρ i) _ f hdep hf
    rw [hindicator] at hh
    exact hh
  have hfair (i : Fin n) (b : Bool) :
      |potentialMeanShiftW4 E i b| =
          (1 / 2) * |cmean E.design (fun z => z i = b) (potential E i b) -
            cmean E.design (fun z => z i = !b) (potential E i b)| ∧
        |potentialMeanShiftW4 E i b| ≤ mean E.design (fun z => |potential E i b z|) :=
    AronowAudit.P009.PairedCompletion.fair_conditioning_bound
      (Bridge.toExperiment E) (Bridge.toPairing ρ) hPair i b (potential E i b)
  have hmoment (i : Fin n) (b : Bool) :
      mean E.design (fun z => |potential E i b z|) ≤ k :=
    AronowAudit.P009.BernoulliCompletion.mean_abs_of_moment
      (Bridge.toLaw E.design) (potential E i b) k s hReg.1 hReg.2.2.1
      (hReg.2.2.2.2.2 i b)
  have hnonpartner (i : Fin n) (b : Bool) (hi : ¬ Interferes E (ρ.partner i) i) :
      cmean E.design (fun z => z i = b) (potential E i b) =
        mean E.design (potential E i b) :=
    AronowAudit.P009.PairedCompletion.conditional_potential_eq_mean_of_nonpartner
      (Bridge.toExperiment E) (Bridge.toPairing ρ) hPair i b hi
  have hvanish (i : Fin n) (b : Bool) :
      (1 - I E (ρ.partner i) i) *
          cmean E.design (fun z => z i = b) (potential E i b) =
        (1 - I E (ρ.partner i) i) * mean E.design (potential E i b) := by
    by_cases hi : Interferes E (ρ.partner i) i
    · simp [I, hi]
    · rw [hnonpartner i b hi]
  have hk : 2 ≤ k := AronowAudit.P009.BernoulliCompletion.regular_k_ge_two
    hn (Bridge.toExperiment E) k q s hReg
  have hkk : 2 * k ≤ 2 * k ^ 2 := by nlinarith [sq_nonneg (k - 1)]
  have hB (i : Fin n) : twoArmShiftW4 E i ≤ 2 * k := by
    have h0 := (hfair i false).2.trans (hmoment i false)
    have h1 := (hfair i true).2.trans (hmoment i true)
    simp only [twoArmShiftW4, Fintype.sum_bool]
    linarith
  have hI (i : Fin n) : 0 ≤ I E (ρ.partner i) i := by
    unfold I
    split_ifs <;> norm_num
  have heate : eate E = (∑ i, (mean E.design (potential E i true) -
      mean E.design (potential E i false))) / n :=
    AronowAudit.P009.eate_finite_identity (Bridge.toExperiment E)
  have hc (i : Fin n) (b : Bool) :
      cmean E.design (fun z => z i = b) (potential E i b) =
        cmean E.design (fun z => z i = b) (E.outcome i) :=
    AronowAudit.P009.BernoulliCompletion.conditional_potential_eq_observed
      (Bridge.toExperiment E) i b
  have he : adse E - eate E =
      (∑ i, (potentialMeanShiftW4 E i true - potentialMeanShiftW4 E i false)) /
        (n : ℝ) := by
    rw [heate]
    simp only [adse, potentialMeanShiftW4, ← hc, Finset.sum_sub_distrib, sub_div]
    ring
  have htriangle : |adse E - eate E| ≤ (∑ i, twoArmShiftW4 E i) / (n : ℝ) := by
    rw [he, abs_div, abs_of_pos hnR]
    apply div_le_div_of_nonneg_right _ hnR.le
    calc
      _ ≤ ∑ i, |potentialMeanShiftW4 E i true - potentialMeanShiftW4 E i false| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, twoArmShiftW4 E i := by
        apply Finset.sum_le_sum
        intro i _
        simpa [twoArmShiftW4, Fintype.sum_bool, add_comm] using
          abs_sub_le (potentialMeanShiftW4 E i true) 0 (potentialMeanShiftW4 E i false)
  have htriangleW : |adse E - eate E| ≤
      (∑ i, (I E (ρ.partner i) i + (1 - I E (ρ.partner i) i)) *
        twoArmShiftW4 E i) / (n : ℝ) := by
    convert htriangle using 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hremove :
      (∑ i, (I E (ρ.partner i) i + (1 - I E (ρ.partner i) i)) *
          twoArmShiftW4 E i) / (n : ℝ) =
        (∑ i, I E (ρ.partner i) i * twoArmShiftW4 E i) / (n : ℝ) := by
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : Interferes E (ρ.partner i) i
    · simp [I, hi]
    · simp [I, hi, twoArmShiftW4, potentialMeanShiftW4, hnonpartner i _ hi]
  have hbound : (∑ i, I E (ρ.partner i) i * twoArmShiftW4 E i) / (n : ℝ) ≤
      2 * k * (∑ i, I E (ρ.partner i) i) / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR.le
    calc
      _ ≤ ∑ i, I E (ρ.partner i) i * (2 * k) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hB i) (hI i))
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hweaken : 2 * k * (∑ i, I E (ρ.partner i) i) / (n : ℝ) ≤
      2 * k ^ 2 * (∑ i, I E (ρ.partner i) i) / (n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR.le
    exact mul_le_mul_of_nonneg_right hkk (Finset.sum_nonneg (fun i _ => hI i))
  have hr : 2 * k ^ 2 * (∑ i, I E (ρ.partner i) i) / (n : ℝ) =
      2 * k ^ 2 * (n : ℝ)⁻¹ * rSum E ρ := by
    unfold rSum
    ring
  have hfinal : |adse E - eate E| ≤ 2 * k ^ 2 * (n : ℝ)⁻¹ * rSum E ρ := by
    calc
      _ ≤ _ := htriangleW
      _ = _ := hremove
      _ ≤ _ := hbound
      _ ≤ _ := hweaken
      _ = _ := hr
  exact ⟨hmask, hmarg, hopposite, hblock, mutual_of_block E ρ hblock, hdistinct, houtside,
    fun i b => ⟨(hfair i b).1, (hfair i b).2, hmoment i b, hvanish i b⟩,
    hk, hB, hkk, he, htriangleW, hremove, hbound, hweaken, hr, hfinal⟩

end
end SAP.P009b.WH.W4
