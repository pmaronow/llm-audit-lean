import SAP.P002a.Defs.WholeW1
import SAP.P002a.Bridge
import AronowAudit.P002.Wave1.Gap.GP0021B1
import AronowAudit.P002.Wave1.Gap.DecisionLemma12
import AronowAudit.P002.Wave1.E61Eigenvalue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace SAP.P002a.WH.W1
noncomputable section
open SAP.P002a SAP.P002a.Bridge Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

universe u

/-- Balanced sign moments, by splitting the two constant blocks. The positive-size
premise agrees with the model family; the cancellation also holds at size zero. -/
theorem balanced_sign_moments :
  ∀ m : ℕ, 0 < m →
    (∑ i, (signModel m).y i false) = 0 ∧
    (∀ i : Fin (2*m), ((signModel m).y i false)^2 = 1) := by
  intro m _hm
  constructor
  · have h : (∑ i : Fin (m+m), if i.val < m then (-1 : ℝ) else 1) = 0 := by
      rw [Fin.sum_univ_add]
      have hl (i : Fin m) : (Fin.castAdd m i).val < m := i.isLt
      have hr (i : Fin m) : ¬ (Fin.natAdd m i).val < m := by
        change ¬ m+i.val < m
        omega
      simp only [hl, hr, ite_true, ite_false, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    let f (N : ℕ) : ℝ := ∑ i : Fin N, if i.val < m then -1 else 1
    change f (2*m) = 0
    rw [two_mul]
    exact h
  · intro i
    dsimp [signModel]
    split_ifs <;> norm_num

/-- A centered scalar covariate of second moment one is fitted exactly by (0,1).
The pooled augmented Gram is the identity, so the nonsingular branch of OLS applies. -/
theorem scalar_exact_fit :
  ∀ (n : ℕ) (z : Fin n → ℝ), 0 < n → (∑ i, z i) = 0 →
    mean (fun i => z i^2) = 1 →
    ols (fun i (_ : Fin 1) => z i) Finset.univ z = T7ExactFitCoefficient := by
  intro n z hn hsum hsecond
  let x : Fin n → Fin 1 → ℝ := fun i _ => z i
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hG : gram x Finset.univ = 1 := by
    ext s t
    cases s with
    | none => cases t with
      | none => simp [gram, groupMean, augmented, hN]
      | some t => simp [gram, groupMean, augmented, x, hsum]
    | some s => cases t with
      | none => simp [gram, groupMean, augmented, x, hsum]
      | some t =>
        have hst : s=t := Subsingleton.elim _ _
        subst t
        simpa [gram, groupMean, mean, augmented, x, pow_two] using hsecond
  have hscore : score x Finset.univ z = T7ExactFitCoefficient := by
    ext s
    cases s with
    | none => simp [score, groupMean, augmented, T7ExactFitCoefficient, hsum]
    | some s =>
      simpa [score, groupMean, mean, augmented, x, pow_two, T7ExactFitCoefficient] using hsecond
  change ols x Finset.univ z = _
  simp [ols, hG, hscore]

/-- Alternating covariates cancel at every even size and have squares 4 and fourth
powers 16. The finite alternating-power sum is already available in Mathlib. -/
theorem alternating_moments :
  ∀ m : ℕ, 0 < m →
    (∀ s, ∑ i, T8AlternatingX m i s = 0) ∧
    (∀ (i : Fin (2*m)) (s : Fin 1), (T8AlternatingX m i s)^2 = 4 ∧
      (T8AlternatingX m i s)^4 = 16) := by
  intro m _hm
  constructor
  · intro s
    change (∑ i : Fin (2*m), 2*(-1 : ℝ)^(i.val+1)) = 0
    simp_rw [pow_succ]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    have hh := Fin.sum_neg_one_pow ℝ (2*m)
    have heven : Even (2*m) := ⟨m, by omega⟩
    simp only [heven, ite_true] at hh
    rw [hh]
    ring
  · intro i s
    dsimp [T8AlternatingX]
    constructor
    · rw [mul_pow, ← pow_mul, mul_comm (i.val+1) 2, pow_mul]
      norm_num
    · rw [mul_pow, ← pow_mul, mul_comm (i.val+1) 4, pow_mul]
      norm_num

/-- Constant population means at positive size. -/
theorem mean_const {n : ℕ} (hn : 0 < n) (c : ℝ) :
    mean (fun _ : Fin n => c) = c := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold mean
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Scalar form of the existing Gram quadratic identity in the package definitions. -/
theorem gram_quadratic {n k : ℕ} (x : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (b : Option (Fin k) → ℝ) :
    dotProduct b (gram x S *ᵥ b) =
      groupMean S (fun i => (dotProduct (augmented x i) b)^2) :=
  AronowAudit.P002.gram_quadratic x S b

/-- The sure event has finite uniform probability one for every valid design. -/
theorem probability_one {n : ℕ} (P : Population n) (hP : ValidDesign P)
    (E : Finset (Fin n) → Prop) (hE : ∀ S, E S) : probability P E = 1 := by
  have hne : (assignments P).Nonempty := by
    apply Finset.powersetCard_nonempty.mpr
    simpa using hP.2.2.le
  have hc : ((assignments P).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hne
  simp [probability, Finset.filter_true_of_mem (fun S _ => hE S), hc]

/-- T7 assembly: derive Xi and the exact variance from sign moments and the pooled
fit; E.58 is then a sure event even if an arm fit is singular. -/
theorem T7_assembly : T7WholeStatement := by
  have h1 := balanced_sign_moments
  have h2 := scalar_exact_fit
  have hfinite : T7FiniteCounterexample := by
    intro m hm
    let P := T7ExactFitModel m
    let z : Fin (2*m) → ℝ := fun i => (signModel m).y i false
    have hN : (0 : ℝ) < (2*m : ℕ) := by exact_mod_cast (show 0 < 2*m by omega)
    have hN1 : (0 : ℝ) < ((2*m : ℕ) : ℝ)-1 := by
      have : (2 : ℝ) ≤ (2*m : ℕ) := by exact_mod_cast (show 2 ≤ 2*m by omega)
      linarith
    have hsum : ∑ i, z i = 0 := (h1 m hm).1
    have hsq : ∀ i, z i^2 = 1 := (h1 m hm).2
    have hmean : mean z = 0 := by simp [mean, hsum]
    have hsecond : mean (fun i => z i^2) = 1 := by
      simp_rw [hsq]
      exact mean_const (by omega) 1
    have hvar : popVar z = ((2*m : ℕ) : ℝ)/(((2*m : ℕ) : ℝ)-1) := by
      simp [popVar, hmean, hsq]
    have hvarpos : 0 < popVar z := by rw [hvar]; exact div_pos hN hN1
    have hD : ValidDesign P.pop := by
      change 2 ≤ 2*m ∧ 0 < m ∧ m < 2*m
      omega
    have hlate : late P.pop = 0 := by
      simp [P, T7ExactFitModel, late, groupMean, signModel]
    have hw (a : Bool) : w P.pop a (late P.pop) = z := by
      rw [hlate]
      funext i
      simp [P, T7ExactFitModel, w, signModel, z]
    have hfit : ols P.x Finset.univ z = T7ExactFitCoefficient :=
      h2 (2*m) z (by omega) hsum hsecond
    have hpsi (a : Bool) : psi P a (late P.pop) = T7ExactFitCoefficient := by
      simpa only [psi, hw] using hfit
    have hres (a : Bool) : residual P a (late P.pop) = 0 := by
      funext i
      change w P.pop a (late P.pop) i -
        dotProduct (augmented P.x i) (psi P a (late P.pop)) = 0
      rw [hw, hpsi]
      simp only [dotProduct, Fintype.sum_option, augmented, T7ExactFitCoefficient,
        Fin.sum_univ_one]
      change z i - (1*0 + z i*1) = 0
      ring
    have hxi : Xi P 0 1 1 1 (1/2) := by
      refine ⟨hD, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [MonotoneReceipt, P, T7ExactFitModel, signModel]
      · have : Nonempty (Fin (2*m)) := ⟨⟨0, by omega⟩⟩
        simp [compliers, P, T7ExactFitModel, signModel]
      · dsimp [P, T7ExactFitModel, signModel]
        push_cast
        linarith
      · dsimp [P, T7ExactFitModel, signModel]
        push_cast
        linarith
      · simp [hres, popCov, popVar, mean]
      · intro a
        simp [hres, fourthNorm, popVar, mean]
      · intro s
        exact hsum
      · intro s
        have hfour : ∀ i, z i^4 = 1 := by
          intro i
          rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, hsq]
          norm_num
        change mean (fun i => z i^4) ≤ 1
        simp_rw [hfour]
        rw [mean_const (by omega)]
      · intro b
        have hf : (fun i => (dotProduct (P.x i) b)^2) =
            (fun i => b 0^2) := by
          funext i
          simp only [dotProduct, Fin.sum_univ_one]
          change (z i * b 0)^2 = b 0^2
          rw [mul_pow, hsq, one_mul]
        rw [hf]
        rw [mean_const (by omega)]
        simp [normSq]
    refine ⟨hxi, hlate, ?_, ?_, ?_⟩
    · intro a
      rw [hw]
      exact ⟨hvar, hvarpos⟩
    · intro a
      exact ⟨hpsi a, hres a⟩
    · intro S
      have hq : observedW P.pop (late P.pop) S = z := by
        rw [hlate]
        funext i
        simp [observedW, observedY, P, T7ExactFitModel, signModel, z]
      have horacle : ∀ T, oracleStar P (observedW P.pop (late P.pop) S) T = 0 := by
        intro T
        rw [hq]
        unfold oracleStar
        rw [hfit]
        have hz : (fun i => z i - slopeDot (P.x i) T7ExactFitCoefficient) = 0 := by
          funext i
          change z i - ∑ j : Fin 1, z i * T7ExactFitCoefficient (some j) = 0
          simp [T7ExactFitCoefficient]
        simp only [adjustedWith, hz]
        simp [groupMean]
      have hzero : designVariance P.pop (oracleStar P (observedW P.pop (late P.pop) S)) = 0 := by
        simp [designVariance, expectation, horacle]
      refine ⟨?_, ?_, horacle, hzero, ?_⟩
      · exact hq
      · rw [hq]; exact hfit
      · intro κ _hκ
        unfold E58Probability
        apply probability_one P.pop hD
        intro T
        rw [hzero, Real.sqrt_zero, mul_zero]
        exact abs_nonneg _
  refine ⟨hfinite, ?_, ?_⟩
  · intro a b hab
    change 2*(a+1) < 2*(b+1)
    omega
  · intro S κ hκ
    have hf : (fun j => E58Probability (T7ExactFitModel (j+1)) (S j) κ) =
        (fun _ : ℕ => (1 : ℝ)) := by
      funext j
      exact (hfinite (j+1) (by omega)).2.2.2.2 (S j) |>.2.2.2.2 κ hκ
    rw [hf]
    refine ⟨tendsto_const_nhds, ?_⟩
    intro hzero
    have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
    norm_num at this

/-- A scalar second moment determines its sole unit-vector Rayleigh value. -/
theorem scalar_leastRayleigh {n : ℕ} (x : Fin n → Fin 1 → ℝ) (c : ℝ)
    (hq : ∀ b : Fin 1 → ℝ, mean (fun i => (dotProduct (x i) b)^2) = c*normSq b) :
    leastRayleigh x = c := by
  have hset : {t : ℝ | ∃ b : Fin 1 → ℝ, normSq b = 1 ∧
      mean (fun i => (dotProduct (x i) b)^2) = t} = {c} := by
    ext t
    constructor
    · rintro ⟨b, hb, ht⟩
      simpa only [hq, hb, mul_one, Set.mem_singleton_iff] using ht.symm
    · intro ht
      have htc : t = c := Set.mem_singleton_iff.mp ht
      subst t
      refine ⟨fun _ => 1, ?_, ?_⟩
      · simp [normSq]
      · rw [hq]; simp [normSq]
  simp only [leastRayleigh, hset, csInf_singleton]

/-- T8 assembly: the alternating moments give the scalar Gram, and the existing
block-Gram and spectral theorems supply every augmented entry and eigenvalue. -/
theorem T8_assembly : T8WholeStatement := by
  have h1 := alternating_moments
  intro m hm
  let x := T8AlternatingX m
  have hn : 0 < 2*m := by omega
  have hx : ∀ s, ∑ i, x i s = 0 := (h1 m hm).1
  have hsq : ∀ i s, (x i s)^2 = 4 := fun i s => ((h1 m hm).2 i s).1
  have hfour : ∀ i s, (x i s)^4 = 16 := fun i s => ((h1 m hm).2 i s).2
  have hq (b : Fin 1 → ℝ) : mean (fun i => (dotProduct (x i) b)^2) = 4*normSq b := by
    simp only [dotProduct, Fin.sum_univ_one, mul_pow, hsq, normSq]
    rw [mean_const hn]
  have hl : leastRayleigh x = 4 := scalar_leastRayleigh x 4 hq
  have hb (b : Fin 1 → ℝ) : 2*normSq b ≤ mean (fun i => (dotProduct (x i) b)^2) := by
    rw [hq]
    have : 0 ≤ normSq b := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have hg := AronowAudit.P002.corrected_augmented_gram x hn 2 hx hb
  have hC : covariateGram x = (fun _ _ => 4) := by
    funext s t
    have hs : s = 0 := Subsingleton.elim _ _
    have ht : t = 0 := Subsingleton.elim _ _
    subst s; subst t
    simp only [covariateGram, ← pow_two, hsq]
    exact mean_const hn 4
  have hG : gram x Finset.univ = Matrix.diagonal (fun j : Option (Fin 1) =>
      match j with | none => 1 | some _ => 4) := by
    funext s t
    cases s with
    | none => cases t with
      | none => change gram x Finset.univ none none = 1; exact hg.1
      | some t => change gram x Finset.univ none (some t) = 0; exact (hg.2.1 t).1
    | some s => cases t with
      | none => change gram x Finset.univ (some s) none = 0; exact (hg.2.1 s).2
      | some t =>
        have hst : s = t := Subsingleton.elim _ _
        subst t
        simp only [Matrix.diagonal_apply_eq]
        change gram x Finset.univ (some s) (some s) = 4
        calc
          _ = mean (fun i => x i s * x i s) := hg.2.2.1 s s
          _ = 4 := congrFun (congrFun hC s) s
  have heigen : augmentedLeastRayleigh x = 1 := by
    have hh := AronowAudit.P002.corrected_min_eigenvalue x hn (by decide : 0 < 1) hx
    change augmentedLeastRayleigh x = min 1 (leastRayleigh x) at hh
    rw [hl] at hh
    norm_num at hh ⊢
    exact hh
  have hEigenBound : (2 : ℝ) ≤ leastRayleigh x := by rw [hl]; norm_num
  refine ⟨hx, ?_, hC, hl, hEigenBound, hb, hG, heigen, ?_⟩
  · intro s
    have hh : mean (fun i => x i s^4) = 16 := by
      simp_rw [hfour]
      exact mean_const hn 16
    exact ⟨hh, hh.le⟩
  · have hnn : gram (T8AlternatingX m) Finset.univ none none = 1 := hg.1
    simp [normSq, dotProduct, Matrix.mulVec, hnn]

/-- T9 assembly: existing finite spectral results plus the existing marginal-law
entrywise and uniform quadratic perturbation proofs; no new analytic step. -/
theorem T9_assembly : T9WholeStatement.{u} := by
  constructor
  · intro n k x hn hk e _he hx hRay
    have hb (b : Fin k → ℝ) : e*normSq b ≤ mean (fun i => (dotProduct (x i) b)^2) := by
      have hnrm : 0 ≤ normSq b := Finset.sum_nonneg fun _ _ => sq_nonneg _
      exact (mul_le_mul_of_nonneg_right hRay hnrm).trans
        (AronowAudit.P002.leastRayleigh_lower x b)
    have hg := AronowAudit.P002.corrected_augmented_gram x hn e hx hb
    have hs : augmentedLeastRayleigh x = min 1 (leastRayleigh x) :=
      AronowAudit.P002.corrected_min_eigenvalue x hn hk hx
    refine ⟨hg.1, hg.2.1, hg.2.2.1, hs, ?_, ?_⟩
    · rw [hs]
      exact min_le_min le_rfl hRay
    · intro b
      rw [gram_quadratic]
      have hgs : min 1 e * normSq b ≤
          mean (fun i => (dotProduct (augmented x i) b)^2) := hg.2.2.2 b
      simpa only [groupMean, mean, Finset.card_univ, Fintype.card_fin] using hgs
  · intro Ω _ μ _ sizes hsizes k P Z δ e A B r _hk _hδ _he hA _hB hr hP hZ sub hsub
    let Q := fun n => toCovPopulation (P n)
    have hae : AronowAudit.P002.Wave1.E61Eigenvalue.AEEntrywise.{u} := by
      open AronowAudit.P002.Wave1.E61Eigenvalue in
      exact n10_proof (n7_proof (n5_proof n1_proof (n4_proof n2_proof n3_proof)) n6_proof)
        n8_proof n9_proof
    have hω := hae μ sizes hsizes k Q Z δ e A B r hA hr.1 hP hZ sub hsub
    filter_upwards [hω] with ω hω
    have hG : ∀ j (b : Option (Fin k) → ℝ),
        min 1 e * normSq b ≤ dotProduct b (gram (P (sub j)).x Finset.univ *ᵥ b) := by
      intro j b
      obtain ⟨hD, -, -, -, -, -, -, hx, -, hray⟩ := hP (sub j)
      have hn : 0 < sizes (sub j) := by have := hD.1; omega
      have hg := (AronowAudit.P002.corrected_augmented_gram (P (sub j)).x hn e hx hray).2.2.2 b
      rw [gram_quadratic]
      have hgs : min 1 e * normSq b ≤
          mean (fun i => (dotProduct (augmented (P (sub j)).x i) b)^2) := hg
      simpa only [groupMean, mean, Finset.card_univ, Fintype.card_fin] using hgs
    obtain ⟨err, herr, hb⟩ :=
      AronowAudit.P002.Wave1.E61Eigenvalue.n12_proof
        AronowAudit.P002.Wave1.E61Eigenvalue.n11_proof k
        (fun j a => gram (P (sub j)).x (if a then Z (sub j) ω else (Z (sub j) ω)ᶜ))
        (fun j => gram (P (sub j)).x Finset.univ) (min 1 e) hω hG
    exact ⟨err, herr, Filter.Eventually.of_forall (fun j a => hb j a _)⟩

/-- T11 assembly: existing centering and rate results, followed by field cancellation
under exactly the positive denominator used in (C.17). -/
theorem T11_assembly : T11WholeStatement := by
  have hf : T11Finite := by
    intro n P hP β S hS
    exact AronowAudit.P002.Wave1.corrected_C17_proof (toPopulation P) hP β S hS
  have hn : T11Normalized := by
    intro n P hP β _hS2
    have hne : (assignments P).Nonempty := by
      apply Finset.powersetCard_nonempty.mpr
      simpa using hP.2.2.le
    obtain ⟨S, hS⟩ := hne
    calc
      _ = (expectation P (fun T => (groupMean T (w P true β) -
          mean (fun i => P.y i (P.d i true)) +
          β*mean (fun i => binary (P.d i true)))^2)) / S2 P β true :=
        AronowAudit.P002.expectation_div (toPopulation P) _ _
      _ = _ := congrArg (fun z : ℝ => z / S2 P β true) (hf P hP β S hS).2
  refine ⟨hf, hn, ?_, ?_⟩
  · intro n P hP β hS
    have hN1 : (n : ℝ)-1 ≠ 0 := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hP.1
      linarith
    have hmul : (fraction P)^2*(1-fraction P)^2 * popVar (w P true β) ≠ 0 := hS.ne'
    have hD : (fraction P)^2*(1-fraction P)^2 ≠ 0 := (mul_ne_zero_iff.mp hmul).1
    have hV : popVar (w P true β) ≠ 0 := (mul_ne_zero_iff.mp hmul).2
    have hsum : (∑ i, v P true β i^2) ≠ 0 := by
      intro hz
      apply hV
      change (∑ i, v P true β i^2) / ((n : ℝ)-1) = 0
      rw [hz, zero_div]
    have hquot : (∑ i, v P true β i^2) / S2 P β true =
        ((n : ℝ)-1)/((fraction P)^2*(1-fraction P)^2) := by
      change (∑ i, v P true β i^2) /
        ((fraction P)^2*(1-fraction P)^2 *
          ((∑ i, v P true β i^2)/((n : ℝ)-1))) = _
      rw [← mul_div_assoc, div_div_eq_mul_div]
      simpa only [mul_comm] using
        (mul_div_mul_right ((n : ℝ)-1) ((fraction P)^2*(1-fraction P)^2) hsum)
    refine ⟨hquot, ?_⟩
    rw [hn P hP β hS, mul_div_assoc, hquot]
    field_simp
  · intro sizes hsizes P δ r A hδ hr hA hP hS
    exact AronowAudit.P002.Wave1.corrected_C17_rate_proof sizes hsizes
      (fun n => toPopulation (P n)) δ r A hδ hr hA hP hS

/-- T15 assembly: transport the complete marginal-coupling theorem. The donor does
not assume positivity of every finite-size conditional variance. -/
theorem T15_assembly : T15WholeStatement.{u} := by
  intro Ω _ μ _ sizes hsizes P Z δ r A hδ hr hA hP hpositive hZ sub hsub
  exact AronowAudit.P002.Wave1.corrected_lemma12_proof μ sizes hsizes
    (fun n => toPopulation (P n)) Z δ r A hδ hr hA hP hpositive hZ sub hsub

end
end SAP.P002a.WH.W1
