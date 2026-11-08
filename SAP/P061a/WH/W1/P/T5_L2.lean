import SAP.P061a.WH.W1.Leaves
import AronowAudit.P061.P061_Foundations

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a.WH.W1.P.T5_L2

open scoped BigOperators Topology Classical BoundedContinuousFunction ENNReal
open Filter MeasureTheory

open SAP.P061a
open SAP.P061a.WH.W1

private theorem uniform_tail_mass (n : ℕ) :
    (∑ _z : Fin n → Fin 2, (1/2 : ℝ)^n) = 1 := by
  rw [Finset.sum_const, Finset.card_univ]
  simp only [nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin]
  norm_num [← one_div, ← mul_pow]

private theorem pair_marginal (n : ℕ) (f : Fin 2 → Fin 2 → ℝ) :
    mean (boundaryDesignW1 n) (fun z => f (z 0) (z 1)) =
      ∑ a : Fin 2, ∑ b : Fin 2, (if a = b then (3/8 : ℝ) else 1/8) * f a b := by
  classical
  unfold mean
  rw [tsum_fintype]
  simp_rw [boundaryDesignW1]
  rw [AronowAudit.P061.sum_vector_succ (n+1)]
  change (∑ a : Fin 2, ∑ w : Fin (n+1) → Fin 2,
    (if a = w 0 then (3/8 : ℝ) else 1/8) * (1/2 : ℝ)^n * f a (w 0)) = _
  congr 1
  funext a
  rw [AronowAudit.P061.sum_vector_succ n
    (fun w : Fin (n+1) → Fin 2 =>
      (if a = w 0 then (3/8 : ℝ) else 1/8) * (1/2 : ℝ)^n * f a (w 0))]
  change (∑ b : Fin 2, ∑ v : Fin n → Fin 2,
    (if a = b then (3/8 : ℝ) else 1/8) * (1/2 : ℝ)^n * f a b) = _
  congr 1
  funext b
  have hs : (∑ v : Fin n → Fin 2,
      (if a = b then (3/8 : ℝ) else 1/8) * (1/2 : ℝ)^n * f a b) =
      (if a = b then (3/8 : ℝ) else 1/8) * f a b := by
    calc
      _ = ∑ v : Fin n → Fin 2,
          ((if a = b then (3/8 : ℝ) else 1/8) * f a b) * (1/2 : ℝ)^n := by
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = _ := by rw [← Finset.mul_sum, uniform_tail_mass n, mul_one]
  exact hs

private theorem mean_pair_from_mass (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n))
    (hmass : BoundaryMassW1 n D) (f : Fin 2 → Fin 2 → ℝ) :
    mean D (fun z => f (z 0) (z 1)) =
      ∑ a : Fin 2, ∑ b : Fin 2, (if a = b then (3/8 : ℝ) else 1/8) * f a b := by
  have heq : mean D (fun z => f (z 0) (z 1)) =
      mean (boundaryDesignW1 n) (fun z => f (z 0) (z 1)) := by
    unfold mean
    rw [tsum_fintype, tsum_fintype]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hmass z]
    rfl
  rw [heq]
  exact pair_marginal n f

private theorem bit2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  have hv : a.val = 0 ∨ a.val = 1 := by have h := a.isLt; omega
  rcases hv with h | h
  · left
    exact Fin.ext h
  · right
    exact Fin.ext h

private theorem raw_numerators (n : ℕ) (D : AtomicDesign (BoundarySpaceW1 n))
    (hmass : BoundaryMassW1 n D) :
    mean D (fun z => if boundaryExposureW1 n 0 z = 1 then boundaryResponsesW1 n 0 z else 0) =
        1/2 + (3/8 : ℝ)/(n+2 : ℝ) ∧
    mean D (fun z => if boundaryExposureW1 n 0 z = 0 then boundaryResponsesW1 n 0 z else 0) =
        1/2 + (1/8 : ℝ)/(n+2 : ℝ) ∧
    mean D (fun z => if boundaryExposureW1 n 1 z = 1 then boundaryResponsesW1 n 1 z else 0) =
        1/2 + (3/8 : ℝ)/(n+2 : ℝ) ∧
    mean D (fun z => if boundaryExposureW1 n 1 z = 0 then boundaryResponsesW1 n 1 z else 0) =
        1/2 + (1/8 : ℝ)/(n+2 : ℝ) := by
  have h01 : mean D (fun z => if boundaryExposureW1 n 0 z = 1 then
      boundaryResponsesW1 n 0 z else 0) = 1/2 + (3/8 : ℝ)/(n+2 : ℝ) := by
    let f : Fin 2 → Fin 2 → ℝ := fun a b =>
      if (a.val : ℝ) = 1 then 1 + (b.val : ℝ)/(n+2 : ℝ) else 0
    have hfun : (fun z => if boundaryExposureW1 n 0 z = 1 then
        boundaryResponsesW1 n 0 z else 0) = fun z => f (z 0) (z 1) := by
      funext z
      have ha := bit2_cases (z 0)
      have hb := bit2_cases (z 1)
      rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        simp [f, boundaryExposureW1, boundaryResponsesW1, ha, hb]
    calc
      _ = mean D (fun z => f (z 0) (z 1)) := by rw [hfun]
      _ = _ := by
        rw [mean_pair_from_mass n D hmass f]
        simp only [Fin.sum_univ_two]
        dsimp [f]
        norm_num
        ring
  have h00 : mean D (fun z => if boundaryExposureW1 n 0 z = 0 then
      boundaryResponsesW1 n 0 z else 0) = 1/2 + (1/8 : ℝ)/(n+2 : ℝ) := by
    let f : Fin 2 → Fin 2 → ℝ := fun a b =>
      if a = 0 then 1 + (b.val : ℝ)/(n+2 : ℝ) else 0
    have hfun : (fun z => if boundaryExposureW1 n 0 z = 0 then
        boundaryResponsesW1 n 0 z else 0) = fun z => f (z 0) (z 1) := by
      funext z
      have ha := bit2_cases (z 0)
      have hb := bit2_cases (z 1)
      rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        simp [f, boundaryExposureW1, boundaryResponsesW1, ha, hb]
    calc
      _ = mean D (fun z => f (z 0) (z 1)) := by rw [hfun]
      _ = _ := by
        rw [mean_pair_from_mass n D hmass f]
        simp only [Fin.sum_univ_two]
        dsimp [f]
        norm_num
        ring
  have h11 : mean D (fun z => if boundaryExposureW1 n 1 z = 1 then
      boundaryResponsesW1 n 1 z else 0) = 1/2 + (3/8 : ℝ)/(n+2 : ℝ) := by
    let f : Fin 2 → Fin 2 → ℝ := fun a b =>
      if (b.val : ℝ) = 1 then 1 + (a.val : ℝ)/(n+2 : ℝ) else 0
    have hfun : (fun z => if boundaryExposureW1 n 1 z = 1 then
        boundaryResponsesW1 n 1 z else 0) = fun z => f (z 0) (z 1) := by
      funext z
      have ha := bit2_cases (z 0)
      have hb := bit2_cases (z 1)
      rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        simp [f, boundaryExposureW1, boundaryResponsesW1, ha, hb]
    calc
      _ = mean D (fun z => f (z 0) (z 1)) := by rw [hfun]
      _ = _ := by
        rw [mean_pair_from_mass n D hmass f]
        simp only [Fin.sum_univ_two]
        dsimp [f]
        norm_num
        ring
  have h10 : mean D (fun z => if boundaryExposureW1 n 1 z = 0 then
      boundaryResponsesW1 n 1 z else 0) = 1/2 + (1/8 : ℝ)/(n+2 : ℝ) := by
    let f : Fin 2 → Fin 2 → ℝ := fun a b =>
      if b = 0 then 1 + (a.val : ℝ)/(n+2 : ℝ) else 0
    have hfun : (fun z => if boundaryExposureW1 n 1 z = 0 then
        boundaryResponsesW1 n 1 z else 0) = fun z => f (z 0) (z 1) := by
      funext z
      have ha := bit2_cases (z 0)
      have hb := bit2_cases (z 1)
      rcases ha with ha | ha <;> rcases hb with hb | hb <;>
        simp [f, boundaryExposureW1, boundaryResponsesW1, ha, hb]
    calc
      _ = mean D (fun z => f (z 0) (z 1)) := by rw [hfun]
      _ = _ := by
        rw [mean_pair_from_mass n D hmass f]
        simp only [Fin.sum_univ_two]
        dsimp [f]
        norm_num
        ring
  exact ⟨h01, h00, h11, h10⟩

private theorem mean_indicator_eq_probability {Ω : Type} [Fintype Ω]
    (D : AtomicDesign Ω) (A : Ω → Prop) :
    mean D (fun z => if A z then 1 else 0) = eventProbability D A := by
  classical
  unfold mean eventProbability
  rw [tsum_fintype, tsum_fintype]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases h : A z <;> simp [h]

private theorem sum_first_two (n : ℕ) (c : ℝ) :
    (∑ i : Fin (n+2), if i = 0 ∨ i = 1 then c else 0) = c+c := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have htail : ∑ i : Fin n,
      (if i.succ.succ = 0 ∨ i.succ.succ = 1 then c else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi0 : i.succ.succ ≠ (0 : Fin (n+2)) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_zero] at hv
      omega
    have hi1 : i.succ.succ ≠ (1 : Fin (n+2)) := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_one] at hv
      omega
    simp [hi0, hi1]
  rw [htail]
  have hs : Fin.succ (0 : Fin (n+1)) = (1 : Fin (n+2)) := by
    apply Fin.ext
    rfl
  simp [hs]

private theorem response_bounds (n : ℕ) (i : Fin (n+2)) (z : BoundarySpaceW1 n) :
    1 ≤ boundaryResponsesW1 n i z ∧ boundaryResponsesW1 n i z ≤ 3/2 := by
  have hN : 0 < (n+2 : ℝ) := by positivity
  have hN2 : 2 ≤ (n+2 : ℝ) := by exact_mod_cast (show 2 ≤ n+2 by omega)
  have hbit (j : Fin (n+2)) :
      0 ≤ ((z j).val : ℝ) ∧ ((z j).val : ℝ) ≤ 1 := by
    constructor
    · positivity
    · have hj : (z j).val ≤ 1 := by have h := (z j).isLt; omega
      exact_mod_cast hj
  by_cases hi0 : i = 0
  · subst i
    simp [boundaryResponsesW1]
    have hq := hbit 1
    have hfrac0 : 0 ≤ ((z 1).val : ℝ)/(n+2 : ℝ) := div_nonneg hq.1 (le_of_lt hN)
    have hfrac1 : ((z 1).val : ℝ)/(n+2 : ℝ) ≤ 1/2 := by
      apply (div_le_iff₀ hN).2
      nlinarith
    constructor <;> linarith
  · by_cases hi1 : i = 1
    · subst i
      simp [boundaryResponsesW1, hi0]
      have hq := hbit 0
      have hfrac0 : 0 ≤ ((z 0).val : ℝ)/(n+2 : ℝ) := div_nonneg hq.1 (le_of_lt hN)
      have hfrac1 : ((z 0).val : ℝ)/(n+2 : ℝ) ≤ 1/2 := by
        apply (div_le_iff₀ hN).2
        nlinarith
      constructor <;> linarith
    · norm_num [boundaryResponsesW1, hi0, hi1]

private theorem raw_own_zero (n : ℕ) (i : Fin (n+2)) (z : BoundarySpaceW1 n) :
    boundaryResponsesW1 n i (Function.update z i 1) -
      boundaryResponsesW1 n i (Function.update z i 0) = 0 := by
  by_cases hi0 : i = 0
  · subst i
    simp [boundaryResponsesW1, Function.update_of_ne]
  · by_cases hi1 : i = 1
    · subst i
      simp [boundaryResponsesW1, hi0, Function.update_of_ne]
    · simp [boundaryResponsesW1, hi0, hi1]

end SAP.P061a.WH.W1.P.T5_L2

theorem SAP.P061a.WH.W1.T5_L2_proof : SAP.P061a.WH.W1.T5_L2 := by
  intro n D hmass hmargins
  let N : ℝ := (n+2 : ℝ)
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hmarg := hmargins.2
  have hnums := SAP.P061a.WH.W1.P.T5_L2.raw_numerators n D hmass
  have hmeans : ∀ i : Fin (n+2),
      exposureMean D (boundaryExposureW1 n) (boundaryResponsesW1 n) i 1 =
        (if i = 0 ∨ i = 1 then 1 + (3/4 : ℝ)/N else 1) ∧
      exposureMean D (boundaryExposureW1 n) (boundaryResponsesW1 n) i 0 =
        (if i = 0 ∨ i = 1 then 1 + (1/4 : ℝ)/N else 1) := by
    intro i
    by_cases hi0 : i = 0
    · subst i
      constructor
      · have hcalc : exposureMean D (boundaryExposureW1 n) (boundaryResponsesW1 n) 0 1 =
            1 + (3/4 : ℝ)/N := by
          unfold exposureMean
          rw [hnums.1, (hmarg 0).1]
          dsimp [N]
          field_simp [hNne]
          <;> ring
        simpa using hcalc
      · have hcalc : exposureMean D (boundaryExposureW1 n) (boundaryResponsesW1 n) 0 0 =
            1 + (1/4 : ℝ)/N := by
          unfold exposureMean
          rw [hnums.2.1, (hmarg 0).2]
          dsimp [N]
          field_simp [hNne]
          <;> ring
        simpa using hcalc
    · by_cases hi1 : i = 1
      · subst i
        constructor
        · have hcalc : exposureMean D (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 1 =
              1 + (3/4 : ℝ)/N := by
            unfold exposureMean
            rw [hnums.2.2.1, (hmarg 1).1]
            dsimp [N]
            field_simp [hNne]
            <;> ring
          simpa using hcalc
        · have hcalc : exposureMean D (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0 =
              1 + (1/4 : ℝ)/N := by
            unfold exposureMean
            rw [hnums.2.2.2, (hmarg 1).2]
            dsimp [N]
            field_simp [hNne]
            <;> ring
          simpa using hcalc
      · constructor
        · have hconst : mean D (fun z =>
              if boundaryExposureW1 n i z = 1 then boundaryResponsesW1 n i z else 0) =
              exposureProbability D (boundaryExposureW1 n) i 1 := by
            calc
              _ = mean D (fun z => if boundaryExposureW1 n i z = 1 then 1 else 0) := by
                congr 1
                funext z
                simp [boundaryResponsesW1, hi0, hi1]
              _ = _ := SAP.P061a.WH.W1.P.T5_L2.mean_indicator_eq_probability D _
          unfold exposureMean
          rw [hconst, (hmarg i).1]
          simpa [hi0, hi1]
        · have hconst : mean D (fun z =>
              if boundaryExposureW1 n i z = 0 then boundaryResponsesW1 n i z else 0) =
              exposureProbability D (boundaryExposureW1 n) i 0 := by
            calc
              _ = mean D (fun z => if boundaryExposureW1 n i z = 0 then 1 else 0) := by
                congr 1
                funext z
                simp [boundaryResponsesW1, hi0, hi1]
              _ = _ := SAP.P061a.WH.W1.P.T5_L2.mean_indicator_eq_probability D _
          unfold exposureMean
          rw [hconst, (hmarg i).2]
          simpa [hi0, hi1]
  have hunit : ∀ i : Fin (n+2),
      unitContrast D (boundaryExposureW1 n) (boundaryResponsesW1 n) i 1 0 =
        (if i = 0 ∨ i = 1 then 1/(2*N) else 0) := by
    intro i
    rcases hmeans i with ⟨h1, h0⟩
    unfold unitContrast
    rw [h1, h0]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;>
      simp [hi0, hi1] <;> dsimp [N] <;> field_simp [hNne] <;> ring
  have hsum : (∑ i : Fin (n+2),
      unitContrast D (boundaryExposureW1 n) (boundaryResponsesW1 n) i 1 0) = 1/N := by
    calc
      _ = ∑ i : Fin (n+2), if i = 0 ∨ i = 1 then 1/(2*N) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hunit i
      _ = 1/N := by
        rw [SAP.P061a.WH.W1.P.T5_L2.sum_first_two]
        dsimp [N]
        field_simp [hNne]
        <;> ring
  have hcontrast :
      populationContrast D (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0 =
        boundaryTargetW1 n := by
    have hpop : populationContrast D (boundaryExposureW1 n) (boundaryResponsesW1 n) 1 0 =
        (n+2 : ℝ)⁻¹ * ∑ i,
          unitContrast D (boundaryExposureW1 n) (boundaryResponsesW1 n) i 1 0 := by
      unfold populationContrast populationExposureMean unitContrast
      simp only [Nat.cast_add, Nat.cast_ofNat, Finset.sum_sub_distrib, mul_sub]
    calc
      _ = (n+2 : ℝ)⁻¹ * (1/(n+2 : ℝ)) := by rw [hpop, hsum]
      _ = boundaryTargetW1 n := by
        unfold boundaryTargetW1
        field_simp
  have hdirect : boundaryDirectW1 n D = 0 := by
    have hz (i : Fin (n+2)) : mean D (fun z =>
        boundaryResponsesW1 n i (Function.update z i 1) -
          boundaryResponsesW1 n i (Function.update z i 0)) = 0 := by
      rw [show (fun z => boundaryResponsesW1 n i (Function.update z i 1) -
          boundaryResponsesW1 n i (Function.update z i 0)) = fun _ => 0 by
        funext z
        exact SAP.P061a.WH.W1.P.T5_L2.raw_own_zero n i z]
      simp [mean]
    simp [boundaryDirectW1, hz]
  refine ⟨?_, hmeans, ?_, hcontrast, hdirect⟩
  · intro i z
    exact SAP.P061a.WH.W1.P.T5_L2.response_bounds n i z
  · intro i z
    exact SAP.P061a.WH.W1.P.T5_L2.raw_own_zero n i z

