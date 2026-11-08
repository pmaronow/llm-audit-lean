import SAP.P002b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P002b.WH.W1.P.T26_L5

noncomputable section
open SAP.P002b
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

private def iv_armCoefficients {k : ℕ} (θ : IVIndex k → ℝ) (a : Bool) :
    Option (Fin k) → ℝ
  | none => θ (.inl 1)
  | some s => θ (.inr (a, s))

private theorem iv_augmented_dot {n k : ℕ} (x : Fin n → Fin k → ℝ)
    (i : Fin n) (c : Option (Fin k) → ℝ) :
    dotProduct (augmented x i) c = c none + slopeDot (x i) c := by
  simp [dotProduct, Fintype.sum_option, augmented, slopeDot]

private theorem iv_row_dot {n k : ℕ} (P : CovPopulation n k) (D : Fin n → ℝ)
    (S : Finset (Fin n)) (i : Fin n) (θ : IVIndex k → ℝ) :
    dotProduct (ivRow P D S i) θ =
      D i * θ (.inl 0) + θ (.inl 1) +
        slopeDot (P.x i) (iv_armCoefficients θ (decide (i ∈ S))) := by
  by_cases hi : i ∈ S <;>
    simp [dotProduct, ivRow, Fintype.sum_sum_type, Fin.sum_univ_two,
      Fintype.sum_prod_type, Fintype.sum_bool, slopeDot, iv_armCoefficients, hi]

/-- The inverse formula gives zero residual moments after removing the factor 1/n. -/
private theorem iv_instrument_moments {n k : ℕ} (P : CovPopulation n k)
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

/-- Zero augmented residual scores identify a full-rank arm fit. -/
private theorem iv_identify_arm {n k : ℕ} (x : Fin n → Fin k → ℝ)
    (A : Finset (Fin n)) (q : Fin n → ℝ) (c : Option (Fin k) → ℝ)
    (hA : A.Nonempty) (hgram : (gram x A).det ≠ 0)
    (hmom : ∀ j, ∑ i ∈ A, augmented x i j *
      (q i - dotProduct (augmented x i) c) = 0) :
    ols x A q = c ∧
      groupMean A (fun i => q i - slopeDot (x i) c) = c none := by
  have hscore : score x A (fun i => q i - dotProduct (augmented x i) c) = 0 := by
    ext j
    simp only [score, groupMean, hmom j, zero_div, Pi.zero_apply]
  change AronowAudit.P002.score x A
    (fun i => q i - dotProduct (AronowAudit.P002.augmented x i) c) = 0 at hscore
  have hfit : ols x A q = c := by
    have H := AronowAudit.P002.ols_error x A q c hgram
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
  rw [he]
  change AronowAudit.P002.groupMean A
    (fun i => (q i - dotProduct (AronowAudit.P002.augmented x i) c) + c none) = _
  rw [AronowAudit.P002.groupMean_add_const A _ _ hA]
  change groupMean A (fun i => q i - dotProduct (augmented x i) c) + _ = _
  rw [hres, zero_add]

end
end SAP.P002b.WH.W1.P.T26_L5

open SAP.P002b
open SAP.P002b.WH.W1.P.T26_L5
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable

theorem SAP.P002b.WH.W1.T26_L5_proof : SAP.P002b.WH.W1.T26_L5 := by
  intro n k P Y D S hP hS hx h1 h0 hcross hinst
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
    change Y i - b * D i -
        (θ (.inl 1) + slopeDot (P.x i) (iv_armCoefficients θ a)) =
      Y i - (D i * θ (.inl 0) + θ (.inl 1) +
        slopeDot (P.x i) (iv_armCoefficients θ a))
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
    simp only [adjustedTau, adjustedWith, fitted, ite_true, ite_false,
      Bool.false_eq_true, ↓reduceIte]
    rw [ht.1, hf.1, ht.2, hf.2, sub_self]
  have hlinear := (AronowAudit.P002.corrected_I1_I2
    (SAP.P002b.Bridge.toCovPopulation P) S Y D b h1 h0).2.1
  have heq : adjustedTau P D S * b = adjustedTau P Y S := by
    change adjustedTau P R S = adjustedTau P Y S - b * adjustedTau P D S at hlinear
    rw [hzero] at hlinear
    nlinarith
  simpa [b, θ] using heq
