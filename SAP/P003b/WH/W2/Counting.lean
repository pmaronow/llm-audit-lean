import SAP.P003b.WH.W2.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003b.WH.W2
open scoped BigOperators
open SAP.P003b.Bridge
attribute [local instance 0] Classical.propDecidable
noncomputable section
set_option maxHeartbeats 1000000

theorem totalEight_card (n : ℕ) : (wholeTotalEight n).card = (n+7).choose 7 := by
  rw [wholeTotalEight, Finset.card_biUnion]
  · simp_rw [stratum_card]
    exact AronowAudit.P003.Wave1.corrected_stratum_count_eight_sum n
  · intro r _ s _ hrs
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    simp only [stratifiedCounts,Finset.product_eq_sprod,Finset.mem_product,allCounts_mem] at hv hv'
    exact hrs (hv.1.symm.trans hv'.1)

theorem unstratified_image (n : ℕ) : Finset.univ.image (tableCounts (n := n)) = allCounts n := by
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,allCounts_mem]
  constructor
  · rintro ⟨w,rfl⟩
    exact (countsOn_total Finset.univ w).trans (by simp)
  · intro ht
    subst n
    obtain ⟨w,hw⟩ := AronowAudit.P003.Wave1.neyman_exists_table (toCounts v)
    refine ⟨w,?_⟩
    change toCounts (tableCounts w) = toCounts v at hw
    exact (to_inj _ _).mp hw

theorem composition_bound (k a n : ℕ) (ha : a ≤ n) :
    ((a+k).choose k : ℝ) ≤ ((n : ℝ)+1)^k := by
  exact_mod_cast (Nat.choose_add_le_add_one_pow a k).trans
    (Nat.pow_le_pow_left (Nat.add_le_add_right ha 1) k)

theorem polynomial_order (f : ℕ → ℝ) (k : ℕ)
    (hpos : ∀ n, 0 ≤ f n) (hf : ∀ n, f n ≤ ((n : ℝ)+1)^k) :
    f =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^k) := by
  apply Asymptotics.IsBigO.of_bound ((2 : ℝ)^k)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, abs_of_nonneg (hpos n), Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)^k)]
  calc
    f n ≤ ((n : ℝ)+1)^k := hf n
    _ ≤ (2*(n : ℝ))^k := pow_le_pow_left₀ (by positivity) (by linarith) k
    _ = _ := mul_pow _ _ _

theorem stratum_order (N₀ N₁ : ℕ → ℕ) (hN : ∀ n, N₀ n+N₁ n = n) :
    (fun n => ((stratifiedCounts (N₀ n) (N₁ n)).card : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^6) ∧
    (fun n => ((stratifiedCounts (N₀ n) (N₁ n)).card : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^7) := by
  have hb (n : ℕ) : ((stratifiedCounts (N₀ n) (N₁ n)).card : ℝ) ≤ ((n : ℝ)+1)^6 := by
    rw [stratum_card, Nat.cast_mul]
    have h₀ := composition_bound 3 (N₀ n) n (by have := hN n; omega)
    have h₁ := composition_bound 3 (N₁ n) n (by have := hN n; omega)
    calc
      _ ≤ ((n : ℝ)+1)^3 * ((n : ℝ)+1)^3 :=
        mul_le_mul h₀ h₁ (by positivity) (by positivity)
      _ = _ := by ring
  refine ⟨polynomial_order _ 6 (fun _ => by positivity) hb,
    polynomial_order _ 7 (fun _ => by positivity) ?_⟩
  intro n
  calc
    _ ≤ ((n : ℝ)+1)^6 := hb n
    _ ≤ ((n : ℝ)+1)^7 := by
      have h := mul_nonneg (pow_nonneg (by positivity : (0 : ℝ) ≤ n+1) 6)
        (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
      nlinarith [show ((n : ℝ)+1)^7 = ((n : ℝ)+1)^6*((n : ℝ)+1) by ring]

theorem four_order : (fun n => ((allCounts n).card : ℝ))
    =O[Filter.atTop] (fun n : ℕ => (n : ℝ)^3) := by
  apply polynomial_order _ 3 (fun _ => by positivity)
  intro n
  rw [four_card]
  exact composition_bound 3 n n le_rfl

theorem tables_card (n : ℕ) : Fintype.card (PotentialTable n) = 4^n := by
  simp [PotentialTable, Fintype.card_prod]

end
end SAP.P003b.WH.W2
