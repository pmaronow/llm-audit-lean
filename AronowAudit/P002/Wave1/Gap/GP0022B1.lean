import AronowAudit.P002.Wave1.AlgorithmSupportBlueprint
import Mathlib.Topology.Order.IntermediateValue

/-!
P002-T23, P002-T26 and P002-T27: gap geometry, residual moments,
identification of arm fits, and interval validity.
-/

namespace AronowAudit.P002.Wave1
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

/-! ### T23: shared analytic layer and gap geometry -/

private theorem h1_open_preconnected (l u : EReal) :
    IsPreconnected (openInterval l u) := by
  apply Set.OrdConnected.isPreconnected
  constructor
  intro x hx y hy z hz
  exact ⟨hx.1.trans_le (EReal.coe_le_coe_iff.mpr hz.1),
    (EReal.coe_le_coe_iff.mpr hz.2).trans_lt hy.2⟩

/-- Every real point in the closed interval is a limit of its interior.
The nine endpoint cases include both half-lines and the whole line. -/
private theorem h1_closed_subset_closure (l u : EReal) (hlu : l < u) :
    closedInterval l u ⊆ closure (openInterval l u) := by
  induction l using EReal.rec with
  | bot =>
      induction u using EReal.rec with
      | bot => exact (lt_irrefl _ hlu).elim
      | coe b =>
          have hop : openInterval ⊥ (b : EReal) = Set.Iio b := by
            ext z
            simp [openInterval]
          have hcl : closedInterval ⊥ (b : EReal) = Set.Iic b := by
            ext z
            simp [closedInterval]
          rw [hop, hcl, closure_Iio] <;> exact Set.Subset.rfl
      | top => simp [closedInterval, openInterval]
  | coe a =>
      induction u using EReal.rec with
      | bot => exact (not_lt_bot hlu).elim
      | coe b =>
          have hab : a < b := EReal.coe_lt_coe_iff.mp hlu
          have hop : openInterval (a : EReal) (b : EReal) = Set.Ioo a b := by
            ext z
            simp [openInterval]
          have hcl : closedInterval (a : EReal) (b : EReal) = Set.Icc a b := by
            ext z
            simp [closedInterval]
          rw [hop, hcl, closure_Ioo hab.ne] <;> exact Set.Subset.rfl
      | top =>
          have hop : openInterval (a : EReal) ⊤ = Set.Ioi a := by
            ext z
            simp [openInterval]
          have hcl : closedInterval (a : EReal) ⊤ = Set.Ici a := by
            ext z
            simp [closedInterval]
          rw [hop, hcl, closure_Ioi] <;> exact Set.Subset.rfl
  | top => exact (not_top_lt hlu).elim

/-- A weak comparison cannot change inside a gap without a crossing.
Identical functions are handled separately, preserving ties. -/
private theorem h1_le_transport {M} (g : Fin M → ℝ → ℝ)
    (hg : ∀ m, Continuous (g m)) (l u : EReal)
    (hc : ∀ z ∈ openInterval l u, ¬crossing g z)
    (s t : Fin M) {x y : ℝ} (hx : x ∈ openInterval l u)
    (hy : y ∈ openInterval l u) (hxy : g s x ≤ g t x) :
    g s y ≤ g t y := by
  by_cases heq : g s = g t
  · simpa only [heq] using (le_refl (g t y))
  by_contra hn
  have hy' : g t y ≤ g s y := (lt_of_not_ge hn).le
  obtain ⟨z, hz, he⟩ := (h1_open_preconnected l u).intermediate_value₂
    hx hy (hg s).continuousOn (hg t).continuousOn hxy hy'
  exact hc z hz ⟨s, t, heq, he⟩

private theorem h1_weak_to_closed {M} (g : Fin M → ℝ → ℝ)
    (hg : ∀ m, Continuous (g m)) (l u : EReal) (hlu : l < u)
    (hc : ∀ z ∈ openInterval l u, ¬crossing g z)
    (s t : Fin M) {x a : ℝ} (hx : x ∈ openInterval l u)
    (ha : a ∈ closedInterval l u) (hst : g s x ≤ g t x) :
    g s a ≤ g t a := by
  have hall : openInterval l u ⊆ {z | g s z ≤ g t z} := by
    intro z hz
    exact h1_le_transport g hg l u hc s t hx hz hst
  exact closure_minimal hall (isClosed_le (hg s) (hg t))
    (h1_closed_subset_closure l u hlu ha)

/-- Endpoint rank directions: weak ranks grow and strict ranks shrink.
The strict direction follows by extending the reversed weak comparison. -/
private theorem h1_index_to_closed {M} (g : Fin M → ℝ → ℝ) (hM : 0 < M)
    (α : ℝ) (hα : 0 < α ∧ α < 1) (hg : ∀ m, Continuous (g m))
    (hn : ∀ m z, 0 ≤ g m z) (l u : EReal) (hlu : l < u)
    (hc : ∀ z ∈ openInterval l u, ¬crossing g z)
    {x a : ℝ} (hx : x ∈ openInterval l u) (ha : a ∈ closedInterval l u)
    {m : Fin M} (hm : m ∈ mcIndices g α x) : m ∈ mcIndices g α a := by
  have hweak : Finset.univ.filter (fun s => g s x ≤ g m x) ⊆
      Finset.univ.filter (fun s => g s a ≤ g m a) := by
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      h1_weak_to_closed g hg l u hlu hc s m hx ha (Finset.mem_filter.mp hs).2⟩
  have hstrict : Finset.univ.filter (fun s => g s a < g m a) ⊆
      Finset.univ.filter (fun s => g s x < g m x) := by
    intro s hs
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hnot
    have hrev := h1_weak_to_closed g hg l u hlu hc m s hx ha (le_of_not_gt hnot)
    exact (not_lt_of_ge hrev) (Finset.mem_filter.mp hs).2
  have hw : ((Finset.univ.filter (fun s => g s x ≤ g m x)).card : ℝ) ≤
      ((Finset.univ.filter (fun s => g s a ≤ g m a)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hweak
  have hs : ((Finset.univ.filter (fun s => g s a < g m a)).card : ℝ) ≤
      ((Finset.univ.filter (fun s => g s x < g m x)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hstrict
  have hr := (quantile_index_rank g hM α x hα (fun s => hn s x) m).mp hm
  apply (quantile_index_rank g hM α a hα (fun s => hn s a) m).mpr
  exact ⟨hr.1.trans hw, hs.trans_lt hr.2⟩

private theorem h1_sample_inside (l u : EReal) (hlu : l < u) :
    gapSample l u ∈ openInterval l u := by
  induction l using EReal.rec with
  | bot =>
      induction u using EReal.rec with
      | bot => exact (lt_irrefl _ hlu).elim
      | coe b =>
          simpa [gapSample, openInterval] using (show b - 1 < b by linarith)
      | top => simp [gapSample, openInterval]
  | coe a =>
      induction u using EReal.rec with
      | bot => exact (not_lt_bot hlu).elim
      | coe b =>
          have hab : a < b := EReal.coe_lt_coe_iff.mp hlu
          simp only [gapSample, EReal.coe_ne_bot, EReal.coe_ne_top,
            EReal.toReal_coe, if_false, openInterval, Set.mem_setOf_eq,
            EReal.coe_lt_coe_iff]
          constructor <;> linarith
      | top =>
          simpa [gapSample, openInterval] using (show a < a + 1 by linarith)
  | top => exact (not_top_lt hlu).elim

/-- Induct over the zip with a supplied lower sentinel.  The extra lower-bound
conclusion excludes the old head from all later gaps. -/
private theorem h1_gap_geometry_aux (J : List ℝ) (hJ : J.Pairwise (· < ·)) :
    ∀ a : EReal, a < ⊤ → (∀ b ∈ J, a < (b : EReal)) →
    ∀ lu ∈ (a :: J.map (fun b => (b : EReal))).zip
        (J.map (fun b => (b : EReal)) ++ [⊤]),
      lu.1 < lu.2 ∧ gapSample lu.1 lu.2 ∈ openInterval lu.1 lu.2 ∧
      a ≤ lu.1 ∧ ∀ z ∈ openInterval lu.1 lu.2, z ∉ J := by
  revert hJ
  induction J with
  | nil =>
      intro _ a ha _ lu hlu
      have he : lu = (a, ⊤) := by simpa using hlu
      subst lu
      exact ⟨ha, h1_sample_inside a ⊤ ha, le_rfl, by simp⟩
  | cons b J ih =>
      intro hJ
      have hhead : ∀ c ∈ J, b < c := (List.pairwise_cons.mp hJ).1
      have htail : J.Pairwise (· < ·) := (List.pairwise_cons.mp hJ).2
      intro a ha hab lu hlu
      have hab' : a < (b : EReal) := hab b (by simp)
      have hmem : lu = (a, (b : EReal)) ∨
          lu ∈ ((b : EReal) :: J.map (fun c => (c : EReal))).zip
            (J.map (fun c => (c : EReal)) ++ [⊤]) := by
        exact List.mem_cons.mp hlu
      rcases hmem with rfl | hmem
      · refine ⟨hab', h1_sample_inside a b hab', le_rfl, ?_⟩
        intro z hz hzJ
        have hzb : z < b := EReal.coe_lt_coe_iff.mp hz.2
        rcases List.mem_cons.mp hzJ with rfl | hzJ
        · exact (lt_irrefl _ hzb)
        · exact (not_lt_of_ge (hhead z hzJ).le) hzb
      · have H := ih htail (b : EReal) (EReal.coe_lt_top b)
          (fun c hc => EReal.coe_lt_coe_iff.mpr (hhead c hc)) lu hmem
        refine ⟨H.1, H.2.1, hab'.le.trans H.2.2.1, ?_⟩
        intro z hz hzJ
        rcases List.mem_cons.mp hzJ with hzb | hzJ
        · subst z
          exact (not_lt_of_ge H.2.2.1) hz.1
        · exact H.2.2.2 z hz hzJ

private theorem h1_gap_geometry (J : List ℝ) (hJ : J.Pairwise (· < ·))
    (lu : EReal × EReal) (hlu : lu ∈ gapEndpoints J) :
    lu.1 < lu.2 ∧ gapSample lu.1 lu.2 ∈ openInterval lu.1 lu.2 ∧
      ∀ z ∈ openInterval lu.1 lu.2, z ∉ J := by
  have H := h1_gap_geometry_aux J hJ ⊥ (by simp)
    (fun b _ => EReal.bot_lt_coe b) lu hlu
  exact ⟨H.1, H.2.1, H.2.2.2⟩

theorem corrected_H1_AR_proof {M} (Qf : QuadraticAR) (Qg : Fin M → QuadraticAR) (α : ℝ)
    (hM : 0 < M) (hα : 0 < α ∧ α < 1) (hf : PaperAR Qf)
    (hg : ∀ m, PaperAR (Qg m)) (hdata : DataGeneratedCoefficients Qf Qg) (J : List ℝ) (pieces : List (RecordedPiece M))
    (hJ : J ≠ []) (hRun : Algorithm1Run (fun m => arFunction (Qg m)) α J pieces) :
    let f := arFunction Qf
    let g := fun m => arFunction (Qg m)
    ∀ p ∈ pieces,
      (∀ β ∈ closedInterval p.left p.right,
        p.index ∈ mcIndices g α β ∧ g p.index β=(mcCritical g α β)^2) ∧
      pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right := by
  let f := arFunction Qf
  let g := fun m => arFunction (Qg m)
  change ∀ p ∈ pieces,
    (∀ β ∈ closedInterval p.left p.right,
      p.index ∈ mcIndices g α β ∧ g p.index β = (mcCritical g α β)^2) ∧
    pieceSet f g p = mcSet f g α ∩ closedInterval p.left p.right
  have hreg : CurveRegularity g :=
    arFamily_regular Qg (fun m => paperAR_regular (Qg m) (hg m))
  intro p hp
  have hpair : (p.left, p.right) ∈ gapEndpoints J := by
    rw [← hRun.2.1]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hgeom := h1_gap_geometry J hRun.1.1 (p.left, p.right) hpair
  have hcross : ∀ z ∈ openInterval p.left p.right, ¬crossing g z := by
    intro z hz hcz
    exact hgeom.2.2 z hz ((hRun.1.2 z).mpr hcz)
  have hindex : ∀ β ∈ closedInterval p.left p.right,
      p.index ∈ mcIndices g α β := by
    intro β hβ
    exact h1_index_to_closed g hM α hα hreg.1 hreg.2.1
      p.left p.right hgeom.1 hcross hgeom.2.1 hβ (hRun.2.2 p hp)
  have hsqrt (β : ℝ) (hβ : β ∈ closedInterval p.left p.right) :
      Real.sqrt (g p.index β) = mcCritical g α β :=
    (Finset.mem_filter.mp (hindex β hβ)).2
  constructor
  · intro β hβ
    refine ⟨hindex β hβ, ?_⟩
    calc
      g p.index β = (Real.sqrt (g p.index β))^2 := (Real.sq_sqrt (hreg.2.1 _ _)).symm
      _ = (mcCritical g α β)^2 := congrArg (fun t : ℝ => t^2) (hsqrt β hβ)
  · ext β
    change (β ∈ closedInterval p.left p.right ∧ f β ≤ g p.index β) ↔
      (Real.sqrt (f β) ≤ mcCritical g α β ∧ β ∈ closedInterval p.left p.right)
    constructor
    · rintro ⟨hβ, hle⟩
      refine ⟨?_, hβ⟩
      rw [← hsqrt β hβ]
      exact (Real.sqrt_le_sqrt_iff (hreg.2.1 _ _)).mpr hle
    · rintro ⟨hle, hβ⟩
      refine ⟨hβ, ?_⟩
      rw [← hsqrt β hβ] at hle
      exact (Real.sqrt_le_sqrt_iff (hreg.2.1 _ _)).mp hle

/-! ### T26: IV residual moments and identification of both arm fits -/

private def iv_armCoefficients {k} (θ : IVIndex k → ℝ) (a : Bool) :
    Option (Fin k) → ℝ
  | none => θ (.inl 1)
  | some s => θ (.inr (a, s))

private theorem iv_augmented_dot {n k} (x : Fin n → Fin k → ℝ)
    (i : Fin n) (c : Option (Fin k) → ℝ) :
    dotProduct (augmented x i) c = c none + slopeDot (x i) c := by
  simp [dotProduct, Fintype.sum_option, augmented, slopeDot]

private theorem iv_row_dot {n k} (P : CovPopulation n k) (D : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) (θ : IVIndex k → ℝ) :
    dotProduct (ivRow P D S i) θ =
      D i * θ (.inl 0) + θ (.inl 1) +
        slopeDot (P.x i) (iv_armCoefficients θ (decide (i ∈ S))) := by
  by_cases hi : i ∈ S <;>
    simp [dotProduct, ivRow, Fintype.sum_sum_type, Fin.sum_univ_two,
      Fintype.sum_prod_type, Fintype.sum_bool, slopeDot, iv_armCoefficients, hi]

/-- The inverse formula supplies actual zero residual sums, after removing 1/n. -/
private theorem iv_instrument_moments {n k} (P : CovPopulation n k)
    (Y D : Fin n → ℝ) (S : Finset (Fin n)) (hn : (n : ℝ) ≠ 0)
    (hcross : (ivCross P D S).det ≠ 0) :
    ∀ j : IVIndex k, ∑ i, instrumentRow P S i j *
      (Y i - dotProduct (ivRow P D S i) (ivCoefficients P Y D S)) = 0 := by
  let θ := ivCoefficients P Y D S
  have H : ivCross P D S *ᵥ θ =
      (fun j => mean fun i => instrumentRow P S i j * Y i) := by
    dsimp only [θ, ivCoefficients]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hcross), Matrix.one_mulVec]
  have hswap (j : IVIndex k) :
      mean (fun i => instrumentRow P S i j * dotProduct (ivRow P D S i) θ) =
        (ivCross P D S *ᵥ θ) j := by
    simp only [mean, ivCross, Matrix.mulVec, dotProduct, Finset.mul_sum,
      Finset.sum_div, div_mul_eq_mul_div, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro i hi
    ring
  intro j
  have hz : (∑ i, instrumentRow P S i j *
      (Y i - dotProduct (ivRow P D S i) θ)) / (n : ℝ) = 0 := by
    change mean (fun i => instrumentRow P S i j *
      (Y i - dotProduct (ivRow P D S i) θ)) = 0
    have he : mean (fun i => instrumentRow P S i j *
        (Y i - dotProduct (ivRow P D S i) θ)) =
        mean (fun i => instrumentRow P S i j * Y i) -
          mean (fun i => instrumentRow P S i j * dotProduct (ivRow P D S i) θ) := by
      simp only [mean, mul_sub, Finset.sum_sub_distrib, sub_div]
    rw [he, hswap, congrFun H j, sub_self]
  exact (div_eq_zero_iff.mp hz).resolve_right hn

/-- A nonempty full-rank arm is identified by its zero augmented residual scores.
The intercept equation also identifies the slope-adjusted arm mean. -/
private theorem iv_identify_arm {n k} (x : Fin n → Fin k → ℝ)
    (A : Finset (Fin n)) (q : Fin n → ℝ) (c : Option (Fin k) → ℝ)
    (hA : A.Nonempty) (hgram : (gram x A).det ≠ 0)
    (hmom : ∀ j, ∑ i ∈ A, augmented x i j *
      (q i - dotProduct (augmented x i) c) = 0) :
    ols x A q = c ∧ groupMean A (fun i => q i - slopeDot (x i) c) = c none := by
  have hscore : score x A (fun i => q i - dotProduct (augmented x i) c) = 0 := by
    ext j
    simp only [score, groupMean, hmom j, zero_div, Pi.zero_apply]
  have hfit : ols x A q = c := by
    have H := ols_error x A q c hgram
    rw [hscore, Matrix.mulVec_zero] at H
    exact sub_eq_zero.mp H
  have hsum : ∑ i ∈ A, (q i - dotProduct (augmented x i) c) = 0 := by
    simpa only [augmented, one_mul] using hmom none
  have hres : groupMean A (fun i => q i - dotProduct (augmented x i) c) = 0 := by
    simp only [groupMean, hsum, zero_div]
  have he : (fun i => q i - slopeDot (x i) c) =
      (fun i => (q i - dotProduct (augmented x i) c) + c none) := by
    funext i
    rw [iv_augmented_dot]
    ring
  refine ⟨hfit, ?_⟩
  rw [he, groupMean_add_const A _ _ hA, hres, zero_add]

theorem adjusted_wald_equals_IV_proof {n k} (P : CovPopulation n k) (Y D : Fin n → ℝ)
    (S : Finset (Fin n)) (hP : ValidDesign P.pop) (hS : S ∈ assignments P.pop)
    (hx : ∀ s, ∑ i, P.x i s = 0) (h1 : (gram P.x S).det ≠ 0)
    (h0 : (gram P.x Sᶜ).det ≠ 0) (hcross : (ivCross P D S).det ≠ 0)
    (hinst : (instrumentGram P S).det ≠ 0) (hd : adjustedTau P D S ≠ 0) :
    adjustedTau P D S * ivCoefficients P Y D S (.inl 0) = adjustedTau P Y S ∧
    ivCoefficients P Y D S (.inl 0) = adjustedWald P Y D S := by
  let θ := ivCoefficients P Y D S
  let b : ℝ := θ (.inl 0)
  let R : Fin n → ℝ := fun i => Y i - b * D i
  let r : Fin n → ℝ := fun i => Y i - dotProduct (ivRow P D S i) θ
  let A : Bool → Finset (Fin n) := fun a => if a then S else Sᶜ
  have hN : (n : ℝ) ≠ 0 := by
    have hn : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hP.1
    exact_mod_cast hn.ne'
  have hsizes : S.card = P.pop.n1 := (Finset.mem_powersetCard.mp hS).2
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hsizes]; exact hP.2.1)
  have hCne : Sᶜ.Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_compl, Fintype.card_fin, hsizes]
    exact Nat.sub_pos_of_lt hP.2.2
  have hmom : ∀ j, ∑ i, instrumentRow P S i j * r i = 0 :=
    iv_instrument_moments P Y D S hN hcross
  have hT : ∑ i ∈ S, r i = 0 := by
    simpa [instrumentRow, ivRow, ite_mul] using hmom (.inl 0)
  have hall : ∑ i, r i = 0 := by
    simpa [instrumentRow, ivRow] using hmom (.inl 1)
  have hC : ∑ i ∈ Sᶜ, r i = 0 := by
    have H := Finset.sum_add_sum_compl S r
    rw [hT, hall, zero_add] at H
    exact H
  have harms (a : Bool) : ∑ i ∈ A a, r i = 0 := by
    cases a
    · exact hC
    · exact hT
  have hcov (a : Bool) (s : Fin k) : ∑ i ∈ A a, P.x i s * r i = 0 := by
    have hrow (i : Fin n) : instrumentRow P S i (.inr (a, s)) =
        if i ∈ A a then P.x i s else 0 := by
      cases a <;> by_cases hi : i ∈ S <;> simp [A, instrumentRow, ivRow, hi]
    simpa only [hrow, ite_mul, zero_mul, Finset.sum_ite_mem_eq] using hmom (.inr (a, s))
  have hresidual (a : Bool) (i : Fin n) (hi : i ∈ A a) :
      R i - dotProduct (augmented P.x i) (iv_armCoefficients θ a) = r i := by
    have hia : decide (i ∈ S) = a := by
      cases a <;> simpa [A] using hi
    dsimp only [R, r]
    rw [iv_row_dot, hia, iv_augmented_dot]
    change Y i - b * D i - (θ (.inl 1) + slopeDot (P.x i) (iv_armCoefficients θ a)) =
      Y i - (D i * θ (.inl 0) + θ (.inl 1) + slopeDot (P.x i) (iv_armCoefficients θ a))
    dsimp only [b]
    ring
  have hfit (a : Bool) :
      ols P.x (A a) R = iv_armCoefficients θ a ∧
      groupMean (A a) (fun i => R i - slopeDot (P.x i) (iv_armCoefficients θ a)) =
        θ (.inl 1) := by
    have hne : (A a).Nonempty := by cases a <;> assumption
    have hg : (gram P.x (A a)).det ≠ 0 := by cases a <;> assumption
    apply iv_identify_arm P.x (A a) R (iv_armCoefficients θ a) hne hg
    intro j
    calc
      (∑ i ∈ A a, augmented P.x i j *
        (R i - dotProduct (augmented P.x i) (iv_armCoefficients θ a))) =
          ∑ i ∈ A a, augmented P.x i j * r i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hresidual a i hi]
      _ = 0 := by
        cases j with
        | none => simpa only [augmented, one_mul] using harms a
        | some s => exact hcov a s
  have hzero : adjustedTau P R S = 0 := by
    have ht := hfit true
    have hf := hfit false
    have hA1 : A true = S := if_pos rfl
    have hA0 : A false = Sᶜ := if_neg (by decide)
    rw [hA1] at ht
    rw [hA0] at hf
    simp only [adjustedTau, adjustedWith, fitted, ite_true, ite_false, Bool.false_eq_true,
      ↓reduceIte]
    rw [ht.1, hf.1, ht.2, hf.2, sub_self]
  have hlinear := (corrected_I1_I2 P S Y D b h1 h0).2.1
  have heq : adjustedTau P D S * b = adjustedTau P Y S := by
    change adjustedTau P R S = adjustedTau P Y S - b * adjustedTau P D S at hlinear
    rw [hzero] at hlinear
    nlinarith
  constructor
  · exact heq
  · change b = adjustedTau P Y S / adjustedTau P D S
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using heq

/-! ### T27: the four interval conclusions -/

private theorem t27_open_subset_closed (l u : EReal) :
    openInterval l u ⊆ closedInterval l u := by
  intro x hx
  exact ⟨hx.1.le, hx.2.le⟩

theorem quantile_index_interval_AR_proof {M} (Q : Fin M → QuadraticAR) (hM : 0 < M)
    (α : ℝ) (hα : 0 < α ∧ α < 1) (hQ : ∀ m, PaperAR (Q m))
    (hdata : ∃ Qf, DataGeneratedCoefficients Qf Q ∧ PaperAR Qf)
    (l u : EReal) (hlu : l < u)
    (hc : ∀ β ∈ openInterval l u, ¬crossing (fun m => arFunction (Q m)) β) :
    let g := fun m => arFunction (Q m)
    (∀ x ∈ openInterval l u, ∀ y ∈ openInterval l u, mcIndices g α x = mcIndices g α y) ∧
    (∀ x ∈ openInterval l u, ∀ a b : ℝ, l=(a : EReal) → u=(b : EReal) →
      mcIndices g α x ⊆ mcIndices g α a ∧ mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ b : ℝ, l=⊥ → u=(b : EReal) →
      mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ a : ℝ, u=⊤ → l=(a : EReal) →
      mcIndices g α x ⊆ mcIndices g α a) := by
  let g := fun m => arFunction (Q m)
  have hreg : CurveRegularity g :=
    arFamily_regular Q (fun m => paperAR_regular (Q m) (hQ m))
  have hcl : ∀ x ∈ openInterval l u, ∀ a ∈ closedInterval l u,
      mcIndices g α x ⊆ mcIndices g α a := by
    intro x hx a ha m hm
    exact h1_index_to_closed g hM α hα hreg.1 hreg.2.1 l u hlu hc hx ha hm
  change
    (∀ x ∈ openInterval l u, ∀ y ∈ openInterval l u, mcIndices g α x = mcIndices g α y) ∧
    (∀ x ∈ openInterval l u, ∀ a b : ℝ, l=(a : EReal) → u=(b : EReal) →
      mcIndices g α x ⊆ mcIndices g α a ∧ mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ b : ℝ, l=⊥ → u=(b : EReal) →
      mcIndices g α x ⊆ mcIndices g α b) ∧
    (∀ x ∈ openInterval l u, ∀ a : ℝ, u=⊤ → l=(a : EReal) →
      mcIndices g α x ⊆ mcIndices g α a)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    apply Finset.Subset.antisymm
    · exact hcl x hx y (t27_open_subset_closed l u hy)
    · exact hcl y hy x (t27_open_subset_closed l u hx)
  · intro x hx a b hl hu
    exact ⟨hcl x hx a ⟨hl.le, hl ▸ hlu.le⟩,
      hcl x hx b ⟨hu ▸ hlu.le, hu.symm.le⟩⟩
  · intro x hx b _ hu
    exact hcl x hx b ⟨hu ▸ hlu.le, hu.symm.le⟩
  · intro x hx a _ hl
    exact hcl x hx a ⟨hl.le, hl ▸ hlu.le⟩

end
end AronowAudit.P002.Wave1
