import SAP.P018b.WH.W1.Leaves
import AronowAudit.P018.Wave1.Gap.TailBRareFinite
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018b.WH.W1.P.T19_L4

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

abbrev RUnit := AronowAudit.P018.RareUnit
abbrev rLaw := AronowAudit.P018.rareLaw
abbrev rRepeated := AronowAudit.P018.rareRepeated
abbrev rEvent (N m : ℕ) := AronowAudit.P018.Wave1.TailB_rare_event N m

lemma model_event_eq (N m : ℕ) :
    wholeRareEvent rareModel N m = rEvent N m := by
  ext ω
  simp [wholeRareEvent, rareModel, rEvent,
    AronowAudit.P018.Wave1.TailB_rare_event]

lemma model_kernel_eq : Bridge.toRepeated (wholeRareKernel rareModel) = rRepeated := rfl

lemma model_delta_eq (m : ℕ) : wholeRareDelta m = AronowAudit.P018.rareDelta m := rfl

abbrev Labels (N m : ℕ) := {c : Fin N → Fin (m+1) // Function.Injective (fun i => (c i).val)}
abbrev Index (N m : ℕ) := Labels N m × (Fin N → Bool) × (Fin N → Bool)

def decode {N m : ℕ} (x : Index N m) : Fin N → RUnit :=
  fun i => ⟨m, x.1.1 i, x.2.1 i, x.2.2 i⟩

def encodeIndex {N m : ℕ} (ω : {ω : Fin N → RUnit // ω ∈ rEvent N m}) : Index N m :=
  (⟨fun i => Fin.cast (congrArg (fun k : ℕ => k+1) (ω.2.1 i)) (ω.1 i).label,
    by intro i j hij; exact ω.2.2 (by simpa using hij)⟩,
    fun i => (ω.1 i).A, fun i => (ω.1 i).B)

def eventEquiv (N m : ℕ) : Index N m ≃ {ω : Fin N → RUnit // ω ∈ rEvent N m} := by
  classical
  refine Equiv.mk (fun x => ⟨decode x, ?_⟩) encodeIndex ?_ ?_
  · constructor
    · intro i
      rfl
    · intro i j hij
      apply x.1.2
      simpa [decode] using hij
  · intro x
    apply Prod.ext
    · apply Subtype.ext
      funext i
      apply Fin.ext
      rfl
    · apply Prod.ext <;> rfl
  · intro ω
    apply Subtype.ext
    funext i
    cases hunit : ω.1 i with
    | mk k c a b =>
      have hk : k = m := by simpa [hunit] using ω.2.1 i
      subst k
      change decode (encodeIndex ω) i = (⟨m, c, a, b⟩ : RUnit)
      simp only [decode, encodeIndex]
      simp only [hunit]
      congr 1
      apply Fin.ext
      simpa using congrArg (fun u : RUnit => u.label.val) hunit


lemma sign_flip (b : Bool) : AronowAudit.P018.signValue (!b) = -AronowAudit.P018.signValue b := by
  cases b <;> norm_num [AronowAudit.P018.signValue]

def flipAt {N : ℕ} (i : Fin N) : (Fin N → Bool) ≃ (Fin N → Bool) where
  toFun a j := if j = i then !a j else a j
  invFun a j := if j = i then !a j else a j
  left_inv a := by
    funext j
    by_cases h : j = i <;> simp [h]
  right_inv a := by
    funext j
    by_cases h : j = i <;> simp [h]

lemma signMean_square_sum (N : ℕ) (hN : 0 < N) :
    (∑ a : Fin N → Bool,
      ((∑ i : Fin N, AronowAudit.P018.signValue (a i)) / (N : ℝ))^2) =
      (Fintype.card (Fin N → Bool) : ℝ) / N := by
  classical
  let sv : (Fin N → Bool) → Fin N → ℝ := fun a i => AronowAudit.P018.signValue (a i)
  have hexp (a : Fin N → Bool) : (∑ i, sv a i)^2 = ∑ i, ∑ j, sv a i * sv a j := by
    calc
      (∑ i, sv a i)^2 = (∑ i, sv a i) * (∑ j, sv a j) := by ring
      _ = ∑ i, sv a i * (∑ j, sv a j) := by rw [Finset.sum_mul]
      _ = ∑ i, ∑ j, sv a i * sv a j := by simp only [Finset.mul_sum]
  have hterm (i j : Fin N) :
      (∑ a : Fin N → Bool, sv a i * sv a j) =
        if i = j then (Fintype.card (Fin N → Bool) : ℝ) else 0 := by
    by_cases hij : i = j
    · subst j
      have hsq (a : Fin N → Bool) : sv a i * sv a i = 1 := by
        nlinarith [AronowAudit.P018.Wave1.TailB_rare_sign_square (a i)]
      calc
        _ = ∑ a : Fin N → Bool, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro a ha
          exact hsq a
        _ = _ := by simp
    · have hflip : (∑ a : Fin N → Bool, sv (flipAt i a) i * sv (flipAt i a) j) =
          ∑ a : Fin N → Bool, sv a i * sv a j := by
        exact Equiv.sum_comp (flipAt i) (fun a => sv a i * sv a j)
      have hcancel (a : Fin N → Bool) :
          sv (flipAt i a) i * sv (flipAt i a) j = -(sv a i * sv a j) := by
        have hi : sv (flipAt i a) i = -sv a i := by
          simp [sv, flipAt, sign_flip]
        have hj : sv (flipAt i a) j = sv a j := by
          have hji : j ≠ i := Ne.symm hij
          simp [sv, flipAt, hji]
        rw [hi, hj]
        ring
      have hz : (∑ a : Fin N → Bool, sv a i * sv a j) =
          -(∑ a : Fin N → Bool, sv a i * sv a j) := by
        calc
          _ = ∑ a : Fin N → Bool, sv (flipAt i a) i * sv (flipAt i a) j := hflip.symm
          _ = ∑ a : Fin N → Bool, -(sv a i * sv a j) := by
            apply Finset.sum_congr rfl
            intro a ha
            exact hcancel a
          _ = _ := by simp
      have hzero : (∑ a : Fin N → Bool, sv a i * sv a j) = 0 := by linarith
      simp [hij, hzero]
  have hall : (∑ a : Fin N → Bool, (∑ i, sv a i)^2) =
      (N : ℝ) * (Fintype.card (Fin N → Bool) : ℝ) := by
    calc
      _ = ∑ a : Fin N → Bool, ∑ i, ∑ j, sv a i * sv a j := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hexp a
      _ = ∑ i : Fin N, ∑ a : Fin N → Bool, ∑ j : Fin N, sv a i * sv a j := by
        rw [Finset.sum_comm]
      _ = ∑ i : Fin N, ∑ j : Fin N, ∑ a : Fin N → Bool, sv a i * sv a j := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ i : Fin N, ∑ j : Fin N,
          (if i = j then (Fintype.card (Fin N → Bool) : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm i j
      _ = _ := by simp
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    _ = (∑ a : Fin N → Bool, (∑ i, sv a i)^2) / (N : ℝ)^2 := by
      simp_rw [div_pow]
      rw [← Finset.sum_div]
    _ = _ := by rw [hall]; field_simp [hNr]


lemma event_atom_real {N m : ℕ} {ω : Fin N → RUnit} (hω : ω ∈ rEvent N m) :
    (AronowAudit.P018.repeatedLaw rRepeated N).real {ω} =
      (AronowAudit.P018.Wave1.TailB_rare_p m)^N := by
  rw [measureReal_def, AronowAudit.P018.Wave1.TailB_rare_row_atom]
  simp_rw [hω.1]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (AronowAudit.P018.Wave1.TailB_rare_p_pos m).le]
  exact ENNReal.toReal_ofReal (pow_nonneg (AronowAudit.P018.Wave1.TailB_rare_p_pos m).le N)

lemma index_slope_sum {N m : ℕ} (hN : 0 < N) (δ : ℝ) (hδ : δ ≠ 0) :
    (∑ x : Index N m,
      (2 * ((∑ i : Fin N, AronowAudit.P018.signValue (x.2.1 i)) / (N : ℝ)) / δ)^2) =
      (Fintype.card (Index N m) : ℝ) * (4 / ((N : ℝ)*δ^2)) := by
  classical
  let g : (Fin N → Bool) → ℝ := fun a =>
    (2 * ((∑ i : Fin N, AronowAudit.P018.signValue (a i)) / (N : ℝ)) / δ)^2
  have hsumg : (∑ a : Fin N → Bool, g a) =
      (4 / δ^2) * ((Fintype.card (Fin N → Bool) : ℝ) / N) := by
    calc
      _ = ∑ a : Fin N → Bool, (4 / δ^2) *
          ((∑ i : Fin N, AronowAudit.P018.signValue (a i)) / (N : ℝ))^2 := by
        apply Finset.sum_congr rfl
        intro a ha
        dsimp [g]
        ring
      _ = (4 / δ^2) *
          (∑ a : Fin N → Bool, ((∑ i : Fin N, AronowAudit.P018.signValue (a i)) / (N : ℝ))^2) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [signMean_square_sum N hN]
  have hprod : (∑ x : Index N m, g x.2.1) =
      (Fintype.card (Labels N m) : ℝ) * (Fintype.card (Fin N → Bool) : ℝ) *
        (4 / δ^2) * ((Fintype.card (Fin N → Bool) : ℝ) / N) := by
    calc
      _ = ∑ c : Labels N m, ∑ a : Fin N → Bool, ∑ b : Fin N → Bool, g a := by
        simp only [Index, Fintype.sum_prod_type, Prod.fst, Prod.snd]
      _ = ∑ c : Labels N m, ∑ a : Fin N → Bool, (Fintype.card (Fin N → Bool) : ℝ) * g a := by
        apply Finset.sum_congr rfl
        intro c hc
        apply Finset.sum_congr rfl
        intro a ha
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ = ∑ c : Labels N m, (Fintype.card (Fin N → Bool) : ℝ) * ∑ a : Fin N → Bool, g a := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [Finset.mul_sum]
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [hsumg]
        ring
  have hcard : (Fintype.card (Index N m) : ℝ) =
      (Fintype.card (Labels N m) : ℝ) * (Fintype.card (Fin N → Bool) : ℝ) * (Fintype.card (Fin N → Bool) : ℝ) := by
    change (Fintype.card (Labels N m × ((Fin N → Bool) × (Fin N → Bool))) : ℝ) = _
    rw [Fintype.card_prod, Fintype.card_prod]
    push_cast
    ring
  calc
    _ = ∑ x : Index N m, g x.2.1 := by rfl
    _ = _ := hprod
    _ = _ := by rw [hcard]; field_simp [hδ, show (N : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hN)] <;> ring

lemma event_finite (N m : ℕ) : (rEvent N m).Finite := by
  classical
  letI : Fintype {ω : Fin N → RUnit // ω ∈ rEvent N m} :=
    Fintype.ofEquiv (Index N m) (eventEquiv N m)
  exact Set.finite_def.mpr ⟨inferInstance⟩

lemma source_event_integrable {N m : ℕ} (hN : 3 ≤ N) (hNm : N ≤ m+1) :
    Integrable (fun ω => (AronowAudit.P018.repeatedOLS rRepeated ω 1)^2)
      ((AronowAudit.P018.repeatedLaw rRepeated N).restrict (rEvent N m)) := by
  classical
  letI : IsProbabilityMeasure rLaw := AronowAudit.P018.Wave1.TailB_rare_probability
  let μ := AronowAudit.P018.repeatedLaw rRepeated N
  have hμ : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => rLaw))
    infer_instance
  letI : IsFiniteMeasure μ := by infer_instance
  have hs : (rEvent N m).Finite := event_finite N m
  exact IntegrableOn.of_finite hs

lemma index_nonempty {N m : ℕ} (hNm : N ≤ m+1) : Nonempty (Index N m) := by
  classical
  refine ⟨(⟨fun i => Fin.castLE hNm i, ?_⟩, fun _ => false, fun _ => false)⟩
  intro i j hij
  apply Fin.ext
  simpa using hij



lemma source_event_mass {N m : ℕ} (hNm : N ≤ m+1) :
    (AronowAudit.P018.repeatedLaw rRepeated N (rEvent N m)).toReal =
      (AronowAudit.P018.Wave1.TailB_rare_p m)^N * (Fintype.card (Index N m) : ℝ) := by
  classical
  letI : IsProbabilityMeasure rLaw := AronowAudit.P018.Wave1.TailB_rare_probability
  let μ := AronowAudit.P018.repeatedLaw rRepeated N
  have hμ : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => rLaw))
    infer_instance
  letI : IsFiniteMeasure μ := by infer_instance
  letI : Fintype {ω : Fin N → RUnit // ω ∈ rEvent N m} :=
    Fintype.ofEquiv (Index N m) (eventEquiv N m)
  have hs : (rEvent N m).Finite := event_finite N m
  have hconst : IntegrableOn (fun _ : Fin N → RUnit => (1 : ℝ)) (rEvent N m) μ :=
    IntegrableOn.of_finite hs
  have hset := MeasureTheory.setIntegral_countable
    (fun _ : Fin N → RUnit => (1 : ℝ)) hs.countable hconst
  have hEval : (∫ ω in rEvent N m, (1 : ℝ) ∂μ) = μ.real (rEvent N m) := by
    simp [measureReal_def, Measure.restrict_apply, hs.measurableSet]
  have hmass : μ.real (rEvent N m) =
      (Fintype.card (Index N m) : ℝ) *
        (AronowAudit.P018.Wave1.TailB_rare_p m)^N := by
    calc
      μ.real (rEvent N m) = ∑' ω : {ω : Fin N → RUnit // ω ∈ rEvent N m},
          μ.real {ω.1} := by
        rw [← hEval]
        simpa using hset
      _ = ∑ x : Index N m, μ.real {(eventEquiv N m x).1} := by
        rw [tsum_fintype]
        exact ((eventEquiv N m).sum_comp (fun ω => μ.real {ω.1})).symm
      _ = ∑ x : Index N m, (AronowAudit.P018.Wave1.TailB_rare_p m)^N := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [event_atom_real (eventEquiv N m x).2]
      _ = _ := by simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa [measureReal_def, μ, Index, Fintype.card_prod, mul_comm, mul_left_comm, mul_assoc] using hmass

lemma slope_decode {N m : ℕ} (hN : 2 ≤ N) (x : Index N m) :
    AronowAudit.P018.repeatedOLS rRepeated (decode x) 1 =
      2 * ((∑ i : Fin N, AronowAudit.P018.signValue (x.2.1 i)) / (N : ℝ)) /
        AronowAudit.P018.rareDelta (m+1) := by
  have hs := AronowAudit.P018.Wave1.TailB_rare_event_slope hN
    (eventEquiv N m x).2
  have he : (eventEquiv N m x).1 = decode x := rfl
  rw [he] at hs
  have ha : AronowAudit.P018.Wave1.TailB_rare_Abar (decode x) =
      (∑ i : Fin N, AronowAudit.P018.signValue (x.2.1 i)) / (N : ℝ) := rfl
  rw [ha] at hs
  exact hs

lemma source_event_integral {N m : ℕ} (hN : 3 ≤ N) (hNm : N ≤ m+1) :
    (∫ ω, (AronowAudit.P018.repeatedOLS rRepeated ω 1)^2
      ∂ (AronowAudit.P018.repeatedLaw rRepeated N).restrict (rEvent N m)) =
      (AronowAudit.P018.Wave1.TailB_rare_p m)^N *
        ((Fintype.card (Index N m) : ℝ) *
          (4 / ((N : ℝ)*(AronowAudit.P018.rareDelta (m+1))^2))) := by
  classical
  letI : IsProbabilityMeasure rLaw := AronowAudit.P018.Wave1.TailB_rare_probability
  let μ := AronowAudit.P018.repeatedLaw rRepeated N
  have hμ : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (Measure.pi (fun _ : Fin N => rLaw))
    infer_instance
  letI : IsFiniteMeasure μ := by infer_instance
  letI : Fintype {ω : Fin N → RUnit // ω ∈ rEvent N m} :=
    Fintype.ofEquiv (Index N m) (eventEquiv N m)
  have hs : (rEvent N m).Finite := event_finite N m
  have hf : IntegrableOn
      (fun ω : Fin N → RUnit => (AronowAudit.P018.repeatedOLS rRepeated ω 1)^2)
      (rEvent N m) μ := source_event_integrable hN hNm
  have hset := MeasureTheory.setIntegral_countable
      (fun ω : Fin N → RUnit => (AronowAudit.P018.repeatedOLS rRepeated ω 1)^2)
      hs.countable hf
  have hsum : (∫ ω in rEvent N m,
      (AronowAudit.P018.repeatedOLS rRepeated ω 1)^2 ∂μ) =
      ∑ x : Index N m, (AronowAudit.P018.Wave1.TailB_rare_p m)^N *
        (AronowAudit.P018.repeatedOLS rRepeated (decode x) 1)^2 := by
    calc
      _ = ∑' ω : {ω : Fin N → RUnit // ω ∈ rEvent N m},
          μ.real {ω.1} * (AronowAudit.P018.repeatedOLS rRepeated ω.1 1)^2 := by
        simpa [smul_eq_mul] using hset
      _ = ∑ x : Index N m, μ.real {(eventEquiv N m x).1} *
          (AronowAudit.P018.repeatedOLS rRepeated (eventEquiv N m x).1 1)^2 := by
        rw [tsum_fintype]
        exact ((eventEquiv N m).sum_comp
          (fun ω => μ.real {ω.1} * (AronowAudit.P018.repeatedOLS rRepeated ω.1 1)^2)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [event_atom_real (eventEquiv N m x).2]
        rfl
  have hδ : AronowAudit.P018.rareDelta (m+1) ≠ 0 :=
    ne_of_gt (AronowAudit.P018.Wave1.TailB_rare_delta_pos (m+1) (by omega))
  have hslopes : (∑ x : Index N m,
      (AronowAudit.P018.repeatedOLS rRepeated (decode x) 1)^2) =
      ∑ x : Index N m,
        (2 * ((∑ i : Fin N, AronowAudit.P018.signValue (x.2.1 i)) / (N : ℝ)) /
          AronowAudit.P018.rareDelta (m+1))^2 := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [slope_decode (by omega)]
  calc
    _ = ∑ x : Index N m, (AronowAudit.P018.Wave1.TailB_rare_p m)^N *
        (AronowAudit.P018.repeatedOLS rRepeated (decode x) 1)^2 := hsum
    _ = (AronowAudit.P018.Wave1.TailB_rare_p m)^N *
        ∑ x : Index N m, (AronowAudit.P018.repeatedOLS rRepeated (decode x) 1)^2 := by
      rw [Finset.mul_sum]
    _ = (AronowAudit.P018.Wave1.TailB_rare_p m)^N *
        ((Fintype.card (Index N m) : ℝ) *
          (4 / ((N : ℝ)*(AronowAudit.P018.rareDelta (m+1))^2))) := by
      rw [hslopes]
      exact congrArg ((AronowAudit.P018.Wave1.TailB_rare_p m)^N * ·)
        (index_slope_sum (by omega) (AronowAudit.P018.rareDelta (m+1)) hδ)
    _ = _ := rfl

lemma source_event_ratio {N m : ℕ} (hN : 3 ≤ N) (hNm : N ≤ m+1) :
    (∫ ω, (AronowAudit.P018.repeatedOLS rRepeated ω 1)^2
      ∂ (AronowAudit.P018.repeatedLaw rRepeated N).restrict (rEvent N m)) /
      (AronowAudit.P018.repeatedLaw rRepeated N (rEvent N m)).toReal =
        4 / ((N : ℝ)*(AronowAudit.P018.rareDelta (m+1))^2) := by
  have hn : 0 < N := by omega
  have hmass := source_event_mass hNm
  have hint := source_event_integral hN hNm
  have hidx : 0 < (Fintype.card (Index N m) : ℝ) := by
    have hne : Nonempty (Index N m) := index_nonempty hNm
    exact_mod_cast (Fintype.card_pos_iff.mpr hne)
  have hp : 0 < (AronowAudit.P018.Wave1.TailB_rare_p m)^N :=
    pow_pos (AronowAudit.P018.Wave1.TailB_rare_p_pos m) N
  rw [hint, hmass]
  field_simp [ne_of_gt hp, ne_of_gt hidx] <;> ring

end SAP.P018b.WH.W1.P.T19_L4

theorem SAP.P018b.WH.W1.T19_L4_proof : SAP.P018b.WH.W1.T19_L4 := by
  intro N m hN hNm
  have hI := SAP.P018b.WH.W1.P.T19_L4.source_event_integrable hN hNm
  have hR := SAP.P018b.WH.W1.P.T19_L4.source_event_ratio hN hNm
  constructor
  · simpa [SAP.P018b.WH.W1.P.T19_L4.model_kernel_eq,
      SAP.P018b.WH.W1.P.T19_L4.model_event_eq,
      SAP.P018b.Bridge.repeatedLaw_eq,
      SAP.P018b.Bridge.repeatedOLS_eq] using hI
  · simpa [SAP.P018b.WH.W1.P.T19_L4.model_kernel_eq,
      SAP.P018b.WH.W1.P.T19_L4.model_event_eq,
      SAP.P018b.WH.W1.P.T19_L4.model_delta_eq,
      SAP.P018b.Bridge.repeatedLaw_eq,
      SAP.P018b.Bridge.repeatedOLS_eq] using hR

