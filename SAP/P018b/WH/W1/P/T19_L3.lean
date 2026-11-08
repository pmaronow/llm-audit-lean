import SAP.P018b.WH.W1.Leaves
import AronowAudit.P018.Wave1.Gap.TailBRareFinite
import Mathlib.Data.Fintype.CardEmbedding

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SAP.P018b.WH.W1.P.T19_L3

open Finset MeasureTheory
open scoped BigOperators ENNReal

abbrev RareUnit := AronowAudit.P018.RareUnit

/-- An event row assembled from its injective labels and two sign vectors. -/
def row {N m : ℕ} (q : (Fin N ↪ Fin (m + 1)) × (Fin N → Bool) × (Fin N → Bool)) :
    Fin N → RareUnit := fun i => ⟨m, q.1 i, q.2.1 i, q.2.2 i⟩

theorem row_injective {N m : ℕ} :
    Function.Injective (fun q : (Fin N ↪ Fin (m + 1)) × (Fin N → Bool) × (Fin N → Bool) => row q) := by
  intro q r h
  rcases q with ⟨e, a, b⟩
  rcases r with ⟨f, c, d⟩
  have he : e = f := by
    apply DFunLike.ext
    intro i
    have hi := congrFun h i
    apply Fin.ext
    exact congrArg (fun u : RareUnit => u.label.val) hi
  have ha : a = c := by
    funext i
    have hi := congrFun h i
    exact congrArg AronowAudit.P018.RareUnit.A hi
  have hb : b = d := by
    funext i
    have hi := congrFun h i
    exact congrArg AronowAudit.P018.RareUnit.B hi
  subst f
  subst c
  subst d
  rfl

theorem row_mem_event_iff {N m : ℕ} (ω : Fin N → RareUnit) :
    ω ∈ SAP.P018b.wholeRareEvent SAP.P018b.WH.W1.rareModel N m ↔
      ∃ q : (Fin N ↪ Fin (m + 1)) × (Fin N → Bool) × (Fin N → Bool), row q = ω := by
  constructor
  · intro hω
    rcases hω with ⟨hlevel, hinj⟩
    have hlevel' (i : Fin N) : (ω i).m = m := hlevel i
    let lab : Fin N → Fin (m + 1) := fun i =>
      ⟨(ω i).label.val, by rw [← hlevel' i]; exact (ω i).label.isLt⟩
    have hlab : Function.Injective lab := by
      intro i j hij
      apply hinj
      have hij' : (ω i).label.val = (ω j).label.val := by
        have := congrArg Fin.val hij
        simpa [lab] using this
      exact hij'
    let q : (Fin N ↪ Fin (m + 1)) × (Fin N → Bool) × (Fin N → Bool) :=
      ⟨⟨lab, hlab⟩, fun i => (ω i).A, fun i => (ω i).B⟩
    refine ⟨q, ?_⟩
    funext i
    cases hu : ω i with
    | mk n c a b =>
      have hn : n = m := by simpa [hu] using hlevel' i
      subst n
      change AronowAudit.P018.RareUnit.mk m (lab i) ((ω i).A) ((ω i).B) = AronowAudit.P018.RareUnit.mk m c a b
      simp only [AronowAudit.P018.RareUnit.mk.injEq]
      refine ⟨trivial, ?_, ?_, ?_⟩
      · have hc : lab i = c := by
          apply Fin.ext
          exact congrArg (fun u : RareUnit => u.label.val) hu
        exact heq_of_eq hc
      · simp [hu]
      · simp [hu]
  · rintro ⟨q, rfl⟩
    rcases q with ⟨e, a, b⟩
    change (∀ i, SAP.P018b.WH.W1.rareModel.level (row (e, a, b) i) = m) ∧
      Function.Injective (fun i => SAP.P018b.WH.W1.rareModel.label (row (e, a, b) i))
    constructor
    · intro i
      rfl
    · intro i j hij
      apply e.injective
      apply Fin.ext
      exact hij

theorem event_as_finset {N m : ℕ} :
    (↑(Finset.univ.image (row (N := N) (m := m))) : Set (Fin N → RareUnit)) =
      SAP.P018b.wholeRareEvent SAP.P018b.WH.W1.rareModel N m := by
  ext ω
  simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and]
  exact (row_mem_event_iff ω).symm

theorem card_rows {N m : ℕ} :
    (Finset.univ.image (row (N := N) (m := m))).card =
      (m + 1).descFactorial N * 2^N * 2^N := by
  classical
  rw [Finset.card_image_of_injective _ row_injective]
  simp [Fintype.card_embedding_eq, Nat.mul_assoc]

theorem real_probability_formula (N m : ℕ) :
    ((m + 1).descFactorial N : ℝ) * 2^N * 2^N *
        (AronowAudit.P018.Wave1.TailB_rare_p m)^N =
      (2 : ℝ)^(-((m + 1 : ℤ) * N)) *
        (Nat.descFactorial (m + 1) N : ℝ) / (m + 1 : ℝ)^N := by
  rw [AronowAudit.P018.Wave1.TailB_rare_p_eq]
  have hM : (m + 1 : ℝ) ≠ 0 := by positivity
  have hpow2 : (2 : ℝ)^N * 2^N = (2 : ℝ)^(2 * N) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow3 : (2 : ℝ)^(2 * N) * (2 : ℝ)^((m + 1) * N) =
      (2 : ℝ)^((m + 3) * N) := by
    rw [← pow_add]
    congr 1
    ring
  have hz : (2 : ℝ)^(-((m + 1 : ℤ) * N)) =
      1 / (2 : ℝ)^((m + 1) * N) := by
    rw [zpow_neg]
    rw [← show (((m + 1) * N : ℕ) : ℤ) = ((m + 1 : ℤ) * N) by norm_cast]
    rw [zpow_natCast]
    exact (one_div _).symm
  rw [show ((m + 1).descFactorial N : ℝ) * 2^N * 2^N =
      ((m + 1).descFactorial N : ℝ) * (2^N * 2^N) by ring, hpow2,
    one_div_pow, mul_pow, ← pow_mul, hz]
  field_simp [hM, pow_ne_zero]
  rw [show ((m + 1).descFactorial N : ℝ) * 2^(2 * N) * 2^((m + 1) * N) =
      ((m + 1).descFactorial N : ℝ) * (2^(2 * N) * 2^((m + 1) * N)) by ring, hpow3]

theorem row_atom {N m : ℕ}
    (q : (Fin N ↪ Fin (m + 1)) × (Fin N → Bool) × (Fin N → Bool)) :
    repeatedLaw (wholeRareKernel rareModel) N {row q} =
      (ENNReal.ofReal (AronowAudit.P018.Wave1.TailB_rare_p m))^N := by
  change AronowAudit.P018.repeatedLaw AronowAudit.P018.rareRepeated N {row q} = _
  rw [AronowAudit.P018.Wave1.TailB_rare_row_atom]
  simp [row]

theorem event_mass {N m : ℕ} :
    repeatedLaw (wholeRareKernel rareModel) N
        (SAP.P018b.wholeRareEvent rareModel N m) =
      ((Finset.univ.image (row (N := N) (m := m))).card : ℝ≥0∞) *
        (ENNReal.ofReal (AronowAudit.P018.Wave1.TailB_rare_p m))^N := by
  classical
  let s : Finset (Fin N → RareUnit) := Finset.univ.image (row (N := N) (m := m))
  calc
    _ = repeatedLaw (wholeRareKernel rareModel) N (↑s) := by
      rw [← event_as_finset]
    _ = ∑ ω ∈ s, repeatedLaw (wholeRareKernel rareModel) N {ω} :=
      (MeasureTheory.sum_measure_singleton).symm
    _ = ∑ ω ∈ s, (ENNReal.ofReal (AronowAudit.P018.Wave1.TailB_rare_p m))^N := by
      apply Finset.sum_congr rfl
      intro ω hω
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hω
      exact row_atom q
    _ = _ := by simp [s]

end SAP.P018b.WH.W1.P.T19_L3

theorem SAP.P018b.WH.W1.T19_L3_proof : SAP.P018b.WH.W1.T19_L3 := by
  intro N m hN hNM
  classical
  have hdf : 0 < (m + 1).descFactorial N := Nat.descFactorial_pos.mpr hNM
  refine ⟨?_, ?_⟩
  · rw [SAP.P018b.WH.W1.P.T19_L3.event_mass,
      SAP.P018b.WH.W1.P.T19_L3.card_rows]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (AronowAudit.P018.Wave1.TailB_rare_p_pos m).le,
      Nat.cast_mul, Nat.cast_pow]
    exact SAP.P018b.WH.W1.P.T19_L3.real_probability_formula N m
  · rw [SAP.P018b.WH.W1.P.T19_L3.event_mass]
    apply ENNReal.mul_pos
    · rw [SAP.P018b.WH.W1.P.T19_L3.card_rows]
      exact_mod_cast (Nat.ne_of_gt (by positivity :
        0 < (m + 1).descFactorial N * 2^N * 2^N))
    · exact ne_of_gt (ENNReal.pow_pos
        (ENNReal.ofReal_pos.mpr (AronowAudit.P018.Wave1.TailB_rare_p_pos m)) N)
