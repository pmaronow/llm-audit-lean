import SAP.P019b.Defs.WholeW1
import SAP.P019b.Bridge
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace SAP.P019b.WH.W1
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Bridge
noncomputable section
open Classical
/-- Encode the almost-sure finite observable profile on an arbitrary probability space. Clip W and V to their almost-sure bounds, form the finite tuple (W,X,Y,Z,V), enumerate it by Fin m, and use its pushforward atom probabilities as real masses. Measurability follows from the coordinate hypotheses; total mass one follows by the finite disjoint union of fibers. Recover all coordinates on the common full-measure boundedness event. Expected size: 150–250 lines. Useful tools: Fintype.equivFin, MeasureTheory.Measure.map_apply, MeasureTheory.sum_measure_preimage_singleton, ENNReal.toReal_sum. -/
def T12_L1 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω),
    ∃ (m : ℕ) (F : Study (Fin m)) (e : Ω → Fin m), WholeEncoding S F e
/-- Transport one-subject assumptions and quantities through a finite observable encoding. First prove the integral and event-probability formulas for arbitrary functions of the finite code. Almost-sure coordinate recovery then gives the moment, cell and conditional-atom equalities. Almost-sure statements become statements on positive-mass atoms. Conditional denominators are the identical probabilities on both sides; the equality of the totalized expressions also holds at zero, although the target statements use only defined conditional quantities. Expected size: 150–250 lines. -/
def T12_L2 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω)
    (m : ℕ) (F : Study (Fin m)) (e : Ω → Fin m),
    WholeEncoding S F e → WholePopulationAgreement S F
/-- Transport independence of (W,X,Y) and Z through the encoding. Use equality of their joint and marginal pushforward laws and the product-law characterization of IndepFun. Equivalently, use the integral characterization: the finite factorization for each z gives arbitrary Boolean test functions by their two indicator expansions. All functions of W,X,Y are integrable after composition because their joint range is almost surely finite. Independence of the larger code, which includes Z, is neither needed nor true in general. Expected size: 100–200 lines. -/
def T12_L3 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω)
    (m : ℕ) (F : Study (Fin m)) (e : Ω → Fin m),
    WholeEncoding S F e → (S.treatmentIndependent ↔ F.treatmentIndependent)
/-- Transport the finite-sample joint law of betaHat and betaVarianceHat, including empty samples and all completions. Push the IID product measure through the coordinatewise code with MeasureTheory.Measure.pi_map_pi. On the full-measure event that every sampled coordinate is recovered, the counts, means and variances agree term by term. The encoded product space is finite, so every real function of the two statistics is integrable, even without a global measurability or boundedness hypothesis on that function. The same argument gives null measurability and probabilities for arbitrary predicates of the pair, including behavior on the exceptional null set. No limit theorem is part of this leaf. Expected size: 200–350 lines. -/
def T12_L4 : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω)
    (m : ℕ) (F : Study (Fin m)) (e : Ω → Fin m),
    WholeEncoding S F e → WholeBetaSamplingAgreement S F
private theorem inference_of_sampling {Ω : Type} [MeasurableSpace Ω]
    (S : WholeStudy Ω) {m : ℕ} (F : Study (Fin m))
    (a : WholeBetaSamplingAgreement S F) (hs : F.standing) : S.betaInference := by
  intro c1 c0 cV
  have hi := AronowAudit.P019.Wave1.proposition_three_proof (toStudy F) hs c1 c0 cV
  constructor
  · intro f hc hb
    have heq : (fun n => ∫ s, f ((S.betaHat s c1 c0 - 1) /
          Real.sqrt (S.betaVarianceHat s cV)) ∂S.iid n) =
        (fun n => (F.law.iid n).mean (fun s => f ((F.betaHat s c1 c0 - 1) /
          Real.sqrt (F.betaVarianceHat s cV)))) := by
      funext n
      exact ((a n c1 c0 cV).1 (fun b v => f ((b - 1) / Real.sqrt v))).2
    rw [heq]
    exact hi.2.1 f hc hb
  · intro u hu0 hu1
    have heq : (fun n => S.sampleProb n (fun s =>
        normalPValue (S.betaHat s c1 c0) 1 (S.betaVarianceHat s cV) ≤ u)) =
        (fun n => (F.law.iid n).prob (fun s =>
          normalPValue (F.betaHat s c1 c0) 1 (F.betaVarianceHat s cV) ≤ u)) := by
      funext n
      exact ((a n c1 c0 cV).2 (fun b v => normalPValue b 1 v ≤ u)).2
    rw [heq]
    exact hi.2.2 u hu0 hu1
theorem T12_assembly (h1 : T12_L1) (h2 : T12_L2) (h3 : T12_L3) (h4 : T12_L4) :
    T12WholeStatement := by
  intro Ω _ S hm hd hi hc0 hc1
  obtain ⟨m, F, e, he⟩ := h1 Ω S
  have a := h2 Ω S m F e he
  have fm := a.monotone_iff.mp hm
  have fd := a.noLiarsDesign_iff.mp hd
  have fi := (h3 Ω S m F e he).mp hi
  have fc0 : 0 < F.law.prob (F.cell false true) := by
    simpa only [a.cellProb_eq] using hc0
  have fc1 : 0 < F.law.prob (F.cell true true) := by
    simpa only [a.cellProb_eq] using hc1
  constructor
  · rw [a.beta_eq]
    exact AronowAudit.P019.placebo_one_identity (toStudy F) fm fd fi fc0.ne' fc1.ne'
  · intro hn
    exact inference_of_sampling S F (h4 Ω S m F e he)
      ⟨fm, fd, fi, a.nondegenerate_iff.mp hn⟩
private theorem finite_prob_pos_iff {I : Type} [Fintype I]
    (P : FiniteLaw I) (D : I → Prop) [DecidablePred D] :
    0 < P.prob D ↔ ∃ i, 0 < P.mass i ∧ D i := by
  unfold FiniteLaw.prob FiniteLaw.mean
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ =>
    mul_nonneg (P.nonneg i) (by split_ifs <;> norm_num))]
  constructor
  · rintro ⟨i, _, hi⟩
    by_cases hD : D i
    · exact ⟨i, by simpa [hD] using hi, hD⟩
    · simp [hD] at hi
  · rintro ⟨i, hp, hD⟩
    exact ⟨i, Finset.mem_univ _, by simpa [hD] using hp⟩
private theorem finite_not_monotone_iff {I : Type} [Fintype I] (F : Study I) :
    ¬ F.monotone ↔ 0 < F.law.prob (fun i => F.X i = false ∧ F.Y i = true) := by
  rw [finite_prob_pos_iff]
  unfold Study.monotone
  constructor
  · intro h
    push Not at h
    obtain ⟨i, hp, hy, hx⟩ := h
    exact ⟨i, hp, Bool.eq_false_iff.mpr hx, hy⟩
  · rintro ⟨i, hp, hx, hy⟩ hm
    have := hm i hp hy
    simp_all
private theorem finite_false_mass_conditional {I : Type} [Fintype I]
    (F : Study I) (hy : 0 < F.law.prob (fun i => F.Y i = true)) :
    F.law.prob (fun i => F.X i = false ∧ F.Y i = true) =
      F.law.prob (fun i => F.Y i = true) *
        (1 - F.law.ce (fun i => bitVal (F.X i)) (fun i => F.Y i = true)) := by
  have he : (fun i => if F.X i = false ∧ F.Y i = true then (1 : ℝ) else 0) =
      (fun i => (if F.Y i = true then (1 : ℝ) else 0) -
        (if F.Y i = true then bitVal (F.X i) else 0)) := by
    funext i
    cases hx : F.X i <;> cases hy : F.Y i <;> simp [bitVal]
  change F.law.mean _ = _
  rw [he]
  change (toLaw F.law).mean _ = _
  rw [AronowAudit.P019.mean_sub]
  change F.law.prob (fun i => F.Y i = true) - _ = _
  unfold FiniteLaw.ce
  field_simp [hy.ne']
  rfl
theorem T17_assembly (h1 : T12_L1) (h2 : T12_L2) (h3 : T12_L3) : T17WholeStatement := by
  intro Ω _ S
  obtain ⟨m, F, e, he⟩ := h1 Ω S
  have a := h2 Ω S m F e he
  have ai := h3 Ω S m F e he
  constructor
  · intro hs
    rw [a.mu_eq, a.combined_eq]
    exact AronowAudit.P019.prevalence_identity (toStudy F)
      ⟨a.monotone_iff.mp hs.1, a.noLiarsDesign_iff.mp hs.2.1,
        ai.mp hs.2.2.1, a.nondegenerate_iff.mp hs.2.2.2⟩
  · intro hd hi hn
    have fd := a.noLiarsDesign_iff.mp hd
    have fi := ai.mp hi
    have fn := a.nondegenerate_iff.mp hn
    have hy : 0 < F.law.prob (fun i => F.Y i = true) :=
      (AronowAudit.P019.regularity_probabilities (toStudy F) fn).2 true
    have hc := finite_false_mass_conditional F hy
    have hmono := finite_not_monotone_iff F
    have hcond : 0 < F.law.prob (fun i => F.X i = false ∧ F.Y i = true) ↔
        F.law.ce (fun i => bitVal (F.X i)) (fun i => F.Y i = true) < 1 := by
      rw [hc, mul_pos_iff_of_pos_left hy, sub_pos]
    rw [a.confessorProb_eq, a.combined_eq, a.mu_eq, a.falseMass_eq,
      a.confessorX_eq, not_congr a.monotone_iff]
    refine ⟨hy, AronowAudit.P019.combined_excess (toStudy F) fd fi
      (fn.1 false false).1.ne' (fn.1 true false).1.ne', hc, hmono,
      hmono.trans hcond, ?_⟩
    intro hm
    have hf := hmono.mp hm
    exact ⟨AronowAudit.P019.false_confessions_strict (toStudy F) fd fi fn hf,
      hcond.mp hf⟩
private theorem finite_shift {I : Type} [Fintype I] (F : Study I)
    (hm : F.monotone) (hd : F.noLiarsDesign) (hi : F.treatmentIndependent)
    (hc0 : 0 < F.law.prob (F.cell false true))
    (hc1 : 0 < F.law.prob (F.cell true true)) (t : ℝ) :
    F.law.ce (fun i => if (F.V i : ℝ) = t then 1 else 0) (F.cell false true) =
      F.law.ce (fun i => if (F.V i : ℝ) = t + 1 then 1 else 0) (F.cell true true) := by
  have h := AronowAudit.P019.placebo_distribution_corrected (toStudy F)
    hm hd hi hc0.ne' hc1.ne' t
  have he : (fun i => if (F.V i : ℝ) - 1 = t then (1 : ℝ) else 0) =
      (fun i => if (F.V i : ℝ) = t + 1 then (1 : ℝ) else 0) := by
    funext i
    simp only [show (F.V i : ℝ) - 1 = t ↔ (F.V i : ℝ) = t + 1 by
      constructor <;> intro h <;> linarith]
  have hh : F.law.ce (fun i => if (F.V i : ℝ) = t then 1 else 0) (F.cell false true) =
      F.law.ce (fun i => if (F.V i : ℝ) - 1 = t then 1 else 0) (F.cell true true) :=
    h.1.trans h.2.symm
  simpa only [he] using hh
theorem T21_assembly (h1 : T12_L1) (h2 : T12_L2) (h3 : T12_L3) (h4 : T12_L4) :
    T21WholeStatement := by
  have hshift : ∀ (Ω : Type) [MeasurableSpace Ω] (S : WholeStudy Ω),
      S.monotone → S.noLiarsDesign → S.treatmentIndependent →
      0 < S.prob (S.cell false true) → 0 < S.prob (S.cell true true) → S.shiftedNull := by
    intro Ω _ S hm hd hi hc0 hc1
    obtain ⟨m, F, e, he⟩ := h1 Ω S
    have a := h2 Ω S m F e he
    refine ⟨hc0, hc1, ?_⟩
    intro t
    rw [a.controlAtom_eq, a.treatedAtom_eq]
    exact finite_shift F (a.monotone_iff.mp hm) (a.noLiarsDesign_iff.mp hd)
      ((h3 Ω S m F e he).mp hi) (by simpa only [a.cellProb_eq] using hc0)
      (by simpa only [a.cellProb_eq] using hc1) t
  refine ⟨hshift, ?_, ?_⟩
  · intro Ω _ S hs
    exact (T12_assembly h1 h2 h3 h4 Ω S hs.1 hs.2.1 hs.2.2.1
      (hs.2.2.2.1 false true).1 (hs.2.2.2.1 true true).1).imp_right (fun hi => hi hs.2.2.2)
  · intro n α reject _ _ hlevel Ω _ S hm hd hi hc0 hc1
    exact hlevel Ω S (hshift Ω S hm hd hi hc0 hc1)
set_option maxHeartbeats 2000000 in
theorem T13_assembly : T13WholeStatement := by
  have hbase : T13Statement := AronowAudit.P019.cnn_nonidentification_counterexample
  have hold := hbase
  rcases hbase with ⟨hs, hx, hqA, hqB, hmisA, hmisB, hC, hmu, hb, hd⟩
  refine ⟨hold, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t w z
    fin_cases t <;> fin_cases w <;> cases z <;>
      norm_num [cnnWitness, cnnLaw, fairBit, FiniteLaw.prob, FiniteLaw.mean,
        Fin.sum_univ_succ]
  · intro t
    fin_cases t <;> norm_num [cnnWitness, cnnLaw, FiniteLaw.prob, FiniteLaw.mean,
      Fin.sum_univ_succ]
  · intro w
    fin_cases w <;> norm_num [cnnWitness, cnnLaw, fairBit, FiniteLaw.prob,
      FiniteLaw.mean, Fin.sum_univ_succ]
  · intro z
    cases z <;> norm_num [cnnWitness, cnnLaw, fairBit, FiniteLaw.prob,
      FiniteLaw.mean, Fin.sum_univ_succ]
  · intro b ω
    cases b <;> fin_cases ω <;> norm_num [cnnWitness, cnnReading, cnnWatching]
  · intro ω
    fin_cases ω <;> norm_num [cnnWitness, fairBit]
  · intro z y
    cases z <;> cases y <;>
      norm_num [cnnWitness, cnnLaw, fairBit, Study.cell, Study.listMean,
        FiniteLaw.cv, FiniteLaw.ce, FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]
  · norm_num [cnnWitness, cnnLaw, fairBit, bitVal, FiniteLaw.variance,
      FiniteLaw.ce, FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]
  · rw [hC]; norm_num
  · intro z y v
    by_cases hv : v ≤ 3
    · interval_cases v <;> cases z <;> cases y <;>
        norm_num [cnnWitness, cnnLaw, fairBit, wholeCNNAtomMass, FiniteLaw.prob,
          FiniteLaw.mean, Fin.sum_univ_succ]
    · have h1 : v ≠ 1 := by omega
      have h2 : v ≠ 2 := by omega
      have h3 : v ≠ 3 := by omega
      cases z <;> cases y <;>
        norm_num [cnnWitness, cnnLaw, fairBit, wholeCNNAtomMass, FiniteLaw.prob,
          FiniteLaw.mean, Fin.sum_univ_succ, h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]
  · funext ω
    simp [cnnWitness, cnnWatching]
  · intro ω hx hy
    fin_cases ω <;> norm_num [cnnWitness, cnnReading, cnnWatching] at *
  · intro b
    cases b
    · rw [hC, hqA]; norm_num
    · rw [hC, hqB]; norm_num
  · intro b
    rw [hC]
    cases b <;> norm_num [cnnWitness, cnnLaw, cnnReading, cnnWatching,
      FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]
  · rintro ⟨F, hF⟩
    have he := (hF false).symm.trans (hF true)
    rw [hqA, hqB] at he
    norm_num at he
set_option maxHeartbeats 1000000 in
theorem T22_assembly : T22WholeStatement := by
  have hcore : T22Statement := by
    intro Ω _ S
    constructor
    · intro hi hc0 hc1
      exact AronowAudit.P019.placebo_two_identity (toStudy S) hi hc0.ne' hc1.ne'
    · intro hi hn c1 c0 cV
      exact AronowAudit.P019.Wave1.proposition_four_proof (toStudy S) hi hn c1 c0 cV
  have hcells (z y : Bool) :
      wholeOrderLaw.prob (wholeOrderStudy.cell z y) = (if z = y then 3/8 else 1/8) ∧
      wholeOrderLaw.cv (fun a => (wholeOrderStudy.V a : ℝ))
        (wholeOrderStudy.cell z y) = 1/4 := by
    cases z <;> cases y <;>
      norm_num [wholeOrderLaw, wholeOrderStudy, Study.cell, FiniteLaw.cv,
        FiniteLaw.ce, FiniteLaw.prob, FiniteLaw.mean, Fintype.sum_prod_type, Fintype.sum_bool]
  have hmarg :
      wholeOrderLaw.variance (fun a => bitVal (wholeOrderStudy.Y a)) = 1/4 ∧
      wholeOrderLaw.variance (fun a => bitVal (wholeOrderStudy.Z a)) = 1/4 := by
    constructor <;> norm_num [wholeOrderStudy, wholeOrderLaw, FiniteLaw.variance,
      FiniteLaw.mean, Fintype.sum_prod_type, Fintype.sum_bool, bitVal]
  refine ⟨hcore, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num,
    hcells, hmarg.1, hmarg.2, ?_, ?_⟩
  · intro a _ _; rfl
  · intro a _
    rcases a with ⟨r, b, z⟩
    cases b <;> cases z <;> norm_num [wholeOrderStudy, bitVal]
  · refine ⟨?_, ?_, ?_⟩
    · intro z y
      change 0 < wholeOrderLaw.prob (wholeOrderStudy.cell z y) ∧
        0 < wholeOrderLaw.cv (fun a => (wholeOrderStudy.V a : ℝ)) (wholeOrderStudy.cell z y)
      rw [(hcells z y).1, (hcells z y).2]
      split <;> norm_num
    · change 0 < wholeOrderLaw.variance (fun a => bitVal (wholeOrderStudy.Z a))
      rw [hmarg.2]; norm_num
    · change 0 < wholeOrderLaw.variance (fun a => bitVal (wholeOrderStudy.Y a))
      rw [hmarg.1]; norm_num
  · intro f z
    cases z <;> simp [wholeOrderStudy, wholeOrderLaw, FiniteLaw.mean,
      FiniteLaw.prob, Fintype.sum_prod_type] <;> ring
  · intro z
    cases z <;> norm_num [wholeOrderLaw, wholeOrderStudy, FiniteLaw.prob,
      FiniteLaw.mean, Fintype.sum_prod_type, Fintype.sum_bool]
  · rintro ⟨r, b, z⟩
    cases r <;> cases z <;> rfl
  · intro a
    refine ⟨by simp [wholeOrderHistory], by simp [wholeOrderHistory],
      by simp [wholeOrderHistory], ?_⟩
    intro t ht
    fin_cases t <;> simp_all [wholeOrderHistory]
  · norm_num [Study.delta, wholeOrderLaw, wholeOrderStudy, FiniteLaw.ce,
      FiniteLaw.prob, FiniteLaw.mean, Fintype.sum_prod_type, Fintype.sum_bool, bitVal]
  · intro h
    have h' := h (fun _ _ y => bitVal y) true
    norm_num [wholeOrderStudy, wholeOrderLaw, FiniteLaw.mean, FiniteLaw.prob,
      Fintype.sum_prod_type, Fintype.sum_bool, bitVal] at h'
end
end SAP.P019b.WH.W1
