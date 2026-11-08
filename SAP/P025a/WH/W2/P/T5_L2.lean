import SAP.P025a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025a.WH.W2.P.T5_L2

open scoped BigOperators

private theorem infected_filter {N₁ N₀ : ℕ} (t₁ : Finset (Fin N₁))
    (t₀ : Finset (Fin N₀)) :
    (wholeBinarySample t₁ t₀).filter (fun i => wholeBinaryOutcome i = 1) =
      t₁.disjSum (∅ : Finset (Fin N₀)) := by
  classical
  ext x
  rw [Finset.mem_filter]
  cases x with
  | inl i => simp [wholeBinarySample, wholeBinaryOutcome, Finset.inl_mem_disjSum]
  | inr i => simp [wholeBinarySample, wholeBinaryOutcome, Finset.inr_mem_disjSum]

private theorem uninfected_filter {N₁ N₀ : ℕ} (t₁ : Finset (Fin N₁))
    (t₀ : Finset (Fin N₀)) :
    (wholeBinarySample t₁ t₀).filter (fun i => wholeBinaryOutcome i = 0) =
      (∅ : Finset (Fin N₁)).disjSum t₀ := by
  classical
  ext x
  rw [Finset.mem_filter]
  cases x with
  | inl i => simp [wholeBinarySample, wholeBinaryOutcome, Finset.inl_mem_disjSum]
  | inr i => simp [wholeBinarySample, wholeBinaryOutcome, Finset.inr_mem_disjSum]

end SAP.P025a.WH.W2.P.T5_L2

open SAP.P025a.WH.W2.P.T5_L2

theorem SAP.P025a.WH.W2.T5_L2_proof : SAP.P025a.WH.W2.T5_L2 := by
  classical
  intro N₁ N₀ s₁ s₀ hs₁ hs₀ hs₁N hs₀N t₁ t₀ ht₁ ht₀
  have hN₁ : 0 < N₁ := by omega
  have hN₀ : 0 < N₀ := by omega
  have hN₁R : 0 < (N₁ : ℝ) := by exact_mod_cast hN₁
  have hN₀R : 0 < (N₀ : ℝ) := by exact_mod_cast hN₀
  have hs₁R : 0 < (s₁ : ℝ) := by exact_mod_cast hs₁
  have hs₀R : 0 < (s₀ : ℝ) := by exact_mod_cast hs₀
  have hπ₁ : 0 < (s₁ : ℝ) / N₁ := div_pos hs₁R hN₁R
  have hπ₀ : 0 < (s₀ : ℝ) / N₀ := div_pos hs₀R hN₀R
  let s := wholeBinarySample t₁ t₀
  have hfilter₁ : (s.filter (fun i => wholeBinaryOutcome i = 1)).card = s₁ := by
    rw [infected_filter]
    simp [ht₁]
  have hfilter₀ : (s.filter (fun i => wholeBinaryOutcome i = 0)).card = s₀ := by
    rw [uninfected_filter]
    simp [ht₀]
  have hcard : s.card = s₁ + s₀ := by
    simp [s, wholeBinarySample, ht₁, ht₀]
  have hnum : (∑ i ∈ s, wholeBinaryOutcome i) = s₁ := by
    simp [s, wholeBinarySample, wholeBinaryOutcome, Finset.sum_disjSum, ht₁]
  have hden : wholeHajekDenominator (Sum.elim (fun _ => (s₁ : ℝ) / N₁)
      (fun _ => (s₀ : ℝ) / N₀)) s =
      (s₁ : ℝ) * (1 / ((s₁ : ℝ) / N₁)) +
        (s₀ : ℝ) * (1 / ((s₀ : ℝ) / N₀)) := by
    simp [wholeHajekDenominator, s, wholeBinarySample, Finset.sum_disjSum,
      Finset.sum_const, nsmul_eq_mul, ht₁, ht₀]
  have hweighted : (∑ i ∈ s,
      wholeBinaryOutcome i /
        Sum.elim (fun _ => (s₁ : ℝ) / N₁) (fun _ => (s₀ : ℝ) / N₀) i) =
      (s₁ : ℝ) * (1 / ((s₁ : ℝ) / N₁)) := by
    simp [s, wholeBinarySample, wholeBinaryOutcome, Finset.sum_disjSum,
      Finset.sum_const, nsmul_eq_mul, ht₁]
  have hpart₁ : (s₁ : ℝ) * (1 / ((s₁ : ℝ) / N₁)) = (N₁ : ℝ) := by
    field_simp
  have hpart₀ : (s₀ : ℝ) * (1 / ((s₀ : ℝ) / N₀)) = (N₀ : ℝ) := by
    field_simp
  have hdenval : wholeHajekDenominator
      (Sum.elim (fun _ => (s₁ : ℝ) / N₁) (fun _ => (s₀ : ℝ) / N₀)) s =
      (N₁ : ℝ) + N₀ := by
    rw [hden, hpart₁, hpart₀]
  have hdenpos : 0 < wholeHajekDenominator
      (Sum.elim (fun _ => (s₁ : ℝ) / N₁) (fun _ => (s₀ : ℝ) / N₀)) s := by
    rw [hdenval]
    exact add_pos hN₁R hN₀R
  have hratio : wholeBinaryHajek
      (Sum.elim (fun _ => (s₁ : ℝ) / N₁) (fun _ => (s₀ : ℝ) / N₀)) s =
      (N₁ : ℝ) / (N₁ + N₀) := by
    unfold wholeBinaryHajek
    rw [hweighted, hpart₁, hdenval]
  have hraw : wholeSampleFraction s = (s₁ : ℝ) / (s₁ + s₀) := by
    unfold wholeSampleFraction
    rw [hnum, hcard]
    simp only [Nat.cast_add]
  unfold wholeBinaryDrawFacts
  simpa [s, wholeSampleFraction] using
    (⟨hfilter₁, hfilter₀, hcard, hraw, hdenpos, hratio⟩ :
      (s.filter (fun i => wholeBinaryOutcome i = 1)).card = s₁ ∧
      (s.filter (fun i => wholeBinaryOutcome i = 0)).card = s₀ ∧
      s.card = s₁ + s₀ ∧
      wholeSampleFraction s = (s₁ : ℝ) / (s₁ + s₀) ∧
      0 < wholeHajekDenominator
        (Sum.elim (fun _ => (s₁ : ℝ) / N₁) (fun _ => (s₀ : ℝ) / N₀)) s ∧
      wholeBinaryHajek
        (Sum.elim (fun _ => (s₁ : ℝ) / N₁) (fun _ => (s₀ : ℝ) / N₀)) s =
          (N₁ : ℝ) / (N₁ + N₀))
