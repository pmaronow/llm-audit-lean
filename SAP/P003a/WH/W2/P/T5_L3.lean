import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2.P.T5_L3

open scoped BigOperators
open SAP.P003a
attribute [local instance 0] Classical.propDecidable

lemma candidate_interval (o : Counts) (m : ℕ)
    (hab : o.a + o.b = m) (hcd : o.c + o.d = m) :
    (candidateNumerators o).toFinset =
      Finset.Icc ((o.a : ℤ) - o.c - m) ((o.a : ℤ) - o.c + m) := by
  have habZ : ((o.a + o.b : ℕ) : ℤ) = (m : ℤ) := by exact_mod_cast hab
  have htotal : o.total = 2*m := by
    dsimp [Counts.total]
    omega
  ext x
  simp only [List.mem_toFinset, candidateNumerators, List.mem_map,
    List.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨k, hk, hx⟩
    rw [habZ] at hx
    have hk' : (k : ℤ) ≤ 2*m := by
      have : k ≤ 2*m := by omega
      exact_mod_cast this
    constructor <;> omega
  · rintro ⟨hlo, hhi⟩
    let k : ℕ := (x - ((o.a : ℤ) - o.c - m)).toNat
    have hkcast : (k : ℤ) = x - ((o.a : ℤ) - o.c - m) := by
      dsimp [k]
      exact Int.toNat_of_nonneg (by omega)
    have hk : k < o.total + 1 := by
      rw [htotal]
      have hk' : (k : ℤ) ≤ 2*m := by rw [hkcast]; omega
      have : k ≤ 2*m := by exact_mod_cast hk'
      omega
    refine ⟨k, hk, ?_⟩
    rw [habZ]
    dsimp [k]
    omega

lemma estimate_balanced (o : Counts) (m : ℕ) (hm : 0 < m)
    (hab : o.a + o.b = m) (hcd : o.c + o.d = m) :
    ((2*m : ℕ) : ℝ) * estimate o =
      ((2 * ((o.a : ℤ) - o.c) : ℤ) : ℝ) := by
  have habQ : ((o.a + o.b : ℕ) : ℚ) = (m : ℚ) := by exact_mod_cast hab
  have hcdQ : ((o.c + o.d : ℕ) : ℚ) = (m : ℚ) := by exact_mod_cast hcd
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  push_cast at habQ hcdQ
  have hq : estimateQ o = ((o.a : ℚ) - o.c) / m := by
    unfold estimateQ
    rw [habQ, hcdQ]
    field_simp [show (m : ℚ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hm)]
  unfold estimate
  rw [hq]
  push_cast
  field_simp [hmR]

lemma card_upper (m : ℕ) (Δ : ℤ) (hΔhi : Δ ≤ m) :
    (Finset.Icc (2*Δ) (Δ+m)).card = ((m : ℤ)-Δ).toNat+1 := by
  rw [Int.card_Icc]
  apply (Nat.cast_inj (R := ℤ)).mp
  have hn₁ : 0 ≤ Δ + (m : ℤ) + 1 - 2*Δ := by omega
  have hn₂ : 0 ≤ (m : ℤ)-Δ := by omega
  push_cast
  rw [Int.toNat_of_nonneg hn₁, Int.toNat_of_nonneg hn₂]
  omega

lemma card_lower (m : ℕ) (Δ : ℤ) (hΔlo : -(m : ℤ) ≤ Δ) :
    (Finset.Icc (Δ-m) (2*Δ)).card = ((m : ℤ)+Δ).toNat+1 := by
  rw [Int.card_Icc]
  apply (Nat.cast_inj (R := ℤ)).mp
  have hn₁ : 0 ≤ 2*Δ + 1 - (Δ-(m : ℤ)) := by omega
  have hn₂ : 0 ≤ (m : ℤ)+Δ := by omega
  push_cast
  rw [Int.toNat_of_nonneg hn₁, Int.toNat_of_nonneg hn₂]
  omega

end SAP.P003a.WH.W2.P.T5_L3

open SAP.P003a

theorem SAP.P003a.WH.W2.T5_L3_proof : SAP.P003a.WH.W2.T5_L3 := by
  intro o m hm hab hcd
  let Δ : ℤ := (o.a : ℤ) - o.c
  change
    o.total = 2*m ∧ -(m : ℤ) ≤ Δ ∧ Δ ≤ m ∧
      ((2*m : ℕ) : ℝ) * estimate o = ((2*Δ : ℤ) : ℝ) ∧
      (candidateNumerators o).toFinset = Finset.Icc (Δ-m) (Δ+m) ∧
      (Finset.Icc (2*Δ) (Δ+m)).card = ((m : ℤ)-Δ).toNat+1 ∧
      (Finset.Icc (Δ-m) (2*Δ)).card = ((m : ℤ)+Δ).toNat+1 ∧
      (Finset.Icc (2*Δ) (Δ+m)).card ≤ 2*m+1 ∧
      (Finset.Icc (Δ-m) (2*Δ)).card ≤ 2*m+1
  have htotal : o.total = 2*m := by
    dsimp [Counts.total]
    omega
  have hΔlo : -(m : ℤ) ≤ Δ := by
    dsimp [Δ]
    have ha : o.a ≤ m := by omega
    have hc : o.c ≤ m := by omega
    exact_mod_cast (show -(m : ℤ) ≤ (o.a : ℤ) - o.c by omega)
  have hΔhi : Δ ≤ m := by
    dsimp [Δ]
    have ha : o.a ≤ m := by omega
    have hc : o.c ≤ m := by omega
    exact_mod_cast (show (o.a : ℤ) - o.c ≤ (m : ℤ) by omega)
  have hcand := SAP.P003a.WH.W2.P.T5_L3.candidate_interval o m hab hcd
  have hest := SAP.P003a.WH.W2.P.T5_L3.estimate_balanced o m hm hab hcd
  have hcardU := SAP.P003a.WH.W2.P.T5_L3.card_upper m Δ hΔhi
  have hcardL := SAP.P003a.WH.W2.P.T5_L3.card_lower m Δ hΔlo
  have hboundU : (Finset.Icc (2*Δ) (Δ+m)).card ≤ 2*m+1 := by
    rw [hcardU]
    have hnat : ((m : ℤ)-Δ).toNat ≤ 2*m := by
      have hcast : ((((m : ℤ)-Δ).toNat : ℕ) : ℤ) = (m : ℤ)-Δ :=
        Int.toNat_of_nonneg (by omega)
      have hz : ((((m : ℤ)-Δ).toNat : ℕ) : ℤ) ≤ (2*m : ℤ) := by
        rw [hcast]
        omega
      exact_mod_cast hz
    omega
  have hboundL : (Finset.Icc (Δ-m) (2*Δ)).card ≤ 2*m+1 := by
    rw [hcardL]
    have hnat : ((m : ℤ)+Δ).toNat ≤ 2*m := by
      have hcast : ((((m : ℤ)+Δ).toNat : ℕ) : ℤ) = (m : ℤ)+Δ :=
        Int.toNat_of_nonneg (by omega)
      have hz : ((((m : ℤ)+Δ).toNat : ℕ) : ℤ) ≤ (2*m : ℤ) := by
        rw [hcast]
        omega
      exact_mod_cast hz
    omega
  exact ⟨htotal, hΔlo, hΔhi, hest, by simpa [Δ] using hcand,
    by simpa [Δ] using hcardU, by simpa [Δ] using hcardL,
    hboundU, hboundL⟩

