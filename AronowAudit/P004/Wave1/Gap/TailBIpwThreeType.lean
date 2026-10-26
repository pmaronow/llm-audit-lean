import AronowAudit.P004.P004_Spatial
import AronowAudit.P004.Wave1.LinePopulation.N3
import AronowAudit.P004.Wave1.LinePopulation.N4
import AronowAudit.P004.Wave1.LinePopulation.N5
import AronowAudit.P004.Wave1.LinePopulation.N6
import AronowAudit.P004.Wave1.LinePopulation.N7

/-! Cyclic counting and finite Bernoulli moments for P004-T1. -/

namespace AronowAudit.P004.Wave1

open scoped BigOperators Matrix Topology
open MeasureTheory Filter
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

local instance instTailBIpwDecidable (p : Prop) : Decidable p := Classical.propDecidable p

/-- Exact cyclic counting, including the number of complete three-node blocks. -/
theorem TailBIpw_sum_cycle (K : ℕ) (f : ℕ → ℝ) :
    (∑ i : Fin (3*K), f (i.val % 3)) = (K : ℝ)*(f 0+f 1+f 2) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i % 3)) (3*K)]
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    norm_num [Finset.sum_range_succ, Nat.add_mod, Nat.mul_mod]
    ring

/-- Nonnegative cyclic sums contain all complete blocks, at every sample size. -/
theorem TailBIpw_sum_cycle_lower (N : ℕ) (f : ℕ → ℝ) (hf : ∀ t, 0 ≤ f t) :
    (N/3 : ℕ)*(f 0+f 1+f 2) ≤ ∑ i : Fin N, f (i.val % 3) := by
  rw [← TailBIpw_sum_cycle]
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i % 3)) (3*(N/3)),
    Fin.sum_univ_eq_sum_range (fun i => f (i % 3)) N]
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (by omega : 3*(N/3) ≤ N))
  intro i _ _
  exact hf _

theorem TailBIpw_blocks_lower (N : ℕ) (hN : 6 ≤ N) :
    (N : ℝ)/6 ≤ (N/3 : ℕ) := by
  have hn : N ≤ 6*(N/3) := by omega
  have hc : (N : ℝ) ≤ 6*(N/3 : ℕ) := by exact_mod_cast hn
  linarith


theorem TailBIpw_circle (N : ℕ) :
    circleAverage (threeTypePopulation N) 0 = threeTypeTable N :=
  LinePopulation.n3_proof _

theorem TailBIpw_spatial : SpatialLocalConditions threeTypePopulation := by
  apply LinePopulation.spatialLocal_of LinePopulation.n5_proof
    LinePopulation.n6_proof LinePopulation.n7_proof threeTypeTable 2 0 (by norm_num) le_rfl
  · intro N i z
    unfold threeTypeTable
    split_ifs <;> norm_num
  · intro N j k z b _
    rfl

theorem TailBIpw_wellDefined (N : ℕ) : WellDefined (threeTypePopulation N) 0 :=
  LinePopulation.n4_proof _ _ le_rfl

theorem TailBIpw_local (N : ℕ) :
    LocalAt (circleAverage (threeTypePopulation N) 0)
      (nodeSeparation (threeTypePopulation N)) 0 := by
  simpa only [threeTypePopulation, mul_zero, add_zero] using
    LinePopulation.n7_proof (threeTypeTable N) 0 0 le_rfl le_rfl
      (fun _ _ _ _ _ => rfl)

/-- Factor an arbitrary coordinate function against a statistic unchanged by that coin. -/
theorem TailBIpw_factor_coordinate {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (i : Fin N) (g : Bool → ℝ)
    (F : Assignment N → ℝ) (hF : ∀ z b, F (Function.update z i b) = F z) :
    expect p (fun z => g (z i)*F z) =
      (p i*g true+(1-p i)*g false)*expect p F := by
  have he : (fun z : Assignment N => g (z i)*F z) = fun z =>
      g false*F z+(g true-g false)*((bit (z i))^1*F z) := by
    funext z
    cases h : z i <;> simp only [h, bit, Bool.false_eq_true, if_false, if_true] <;> ring
  rw [he, expect_add, expect_mul, expect_mul,
    bernoulli_positive_power p F i 1 (by omega) hp]
  simp_rw [hF]
  ring

theorem TailBIpw_coordinate_expect {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (i : Fin N) (g : Bool → ℝ) :
    expect p (fun z => g (z i)) = p i*g true+(1-p i)*g false := by
  simpa only [mul_one, expect_const] using
    TailBIpw_factor_coordinate p hp i g (fun _ => 1) (fun _ _ => rfl)

theorem TailBIpw_expect_finset {N : ℕ} (p : Fin N → ℝ)
    (s : Finset (Fin N)) (F : Fin N → Assignment N → ℝ) :
    expect p (fun z => ∑ i ∈ s, F i z) = ∑ i ∈ s, expect p (F i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem TailBIpw_centered_mean {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (a : Fin N → ℝ) (i : Fin N) :
    expect p (fun z => a i*(bit (z i)-p i)) = 0 := by
  rw [TailBIpw_coordinate_expect p hp i (fun b => a i*(bit b-p i))]
  norm_num [bit]
  ring

theorem TailBIpw_coordinate_moments {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (a : Fin N → ℝ) (i : Fin N) :
    expect p (fun z => (a i*(bit (z i)-p i))^2) = p i*(1-p i)*(a i)^2 ∧
      expect p (fun z => (a i*(bit (z i)-p i))^4) ≤ (a i)^4 := by
  constructor
  · rw [TailBIpw_coordinate_expect p hp i (fun b => (a i*(bit b-p i))^2)]
    norm_num [bit]
    ring
  · apply (expect_mono p hp _ (fun _ => (a i)^4) ?_).trans_eq (expect_const _ _)
    intro z
    have hb : |bit (z i)-p i| ≤ 1 := by
      have hi := hp i
      cases h : z i <;> simp only [h, bit, Bool.false_eq_true, if_false, if_true]
      · rw [zero_sub, abs_neg, abs_of_pos hi.1]
        exact hi.2.le
      · rw [abs_of_pos (sub_pos.mpr hi.2)]
        linarith
    have hab : |a i*(bit (z i)-p i)| ≤ |a i| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_one _)
    have hs := pow_le_pow_left₀ (abs_nonneg _) hab 4
    simpa only [show (4 : ℕ) = 2*2 from rfl, pow_abs_two_mul] using hs

/-- Exact second moment and a uniform fourth-moment bound for nonidentical
independent centered Bernoulli coordinates. No CLT or limiting law is assumed. -/
theorem TailBIpw_centered_moments {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 < p i ∧ p i < 1) (a : Fin N → ℝ) (s : Finset (Fin N)) :
    expect p (fun z => (∑ i ∈ s, a i*(bit (z i)-p i))^2) =
        ∑ i ∈ s, p i*(1-p i)*(a i)^2 ∧
      expect p (fun z => (∑ i ∈ s, a i*(bit (z i)-p i))^4) ≤
        3*(∑ i ∈ s, (a i)^2)^2 := by
  induction s using Finset.induction_on with
  | empty => norm_num [expect_const]
  | @insert i s hi ih =>
    let U : Assignment N → ℝ := fun z => ∑ j ∈ s, a j*(bit (z j)-p j)
    let X : Assignment N → ℝ := fun z => a i*(bit (z i)-p i)
    let Q : ℝ := ∑ j ∈ s, (a j)^2
    have hU (z : Assignment N) (b : Bool) : U (Function.update z i b) = U z := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
    have hUm : expect p U = 0 := by
      rw [show U = fun z => ∑ j ∈ s, a j*(bit (z j)-p j) from rfl,
        TailBIpw_expect_finset]
      simp only [TailBIpw_centered_mean p hp a, Finset.sum_const_zero]
    have hXm : expect p X = 0 := TailBIpw_centered_mean p hp a i
    have hfac (k l : ℕ) : expect p (fun z => (X z)^k*(U z)^l) =
        expect p (fun z => (X z)^k)*expect p (fun z => (U z)^l) := by
      rw [TailBIpw_factor_coordinate p hp i (fun b => (a i*(bit b-p i))^k)
        (fun z => (U z)^l) (fun z b => by rw [hU])]
      rw [TailBIpw_coordinate_expect p hp i (fun b => (a i*(bit b-p i))^k)]
    have hodd (l : ℕ) : expect p (fun z => X z*(U z)^l) = 0 := by
      simpa only [pow_one, hXm, zero_mul] using hfac 1 l
    have h31 : expect p (fun z => (X z)^3*U z) = 0 := by
      simpa only [pow_one, hUm, mul_zero] using hfac 3 1
    have hX2 : expect p (fun z => (X z)^2) = p i*(1-p i)*(a i)^2 :=
      (TailBIpw_coordinate_moments p hp a i).1
    have hX4 : expect p (fun z => (X z)^4) ≤ (a i)^4 :=
      (TailBIpw_coordinate_moments p hp a i).2
    have hU2 : expect p (fun z => (U z)^2) ≤ Q := by
      rw [show expect p (fun z => (U z)^2) =
        ∑ j ∈ s, p j*(1-p j)*(a j)^2 from ih.1]
      apply Finset.sum_le_sum
      intro j _
      have hw : p j*(1-p j) ≤ 1 := by nlinarith [sq_nonneg (p j-1/2)]
      exact (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans_eq (one_mul _)
    have hX2le : expect p (fun z => (X z)^2) ≤ (a i)^2 := by
      rw [hX2]
      have hw : p i*(1-p i) ≤ 1 := by nlinarith [sq_nonneg (p i-1/2)]
      exact (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans_eq (one_mul _)
    have hU20 : 0 ≤ expect p (fun z => (U z)^2) := by
      simpa only [expect_const] using expect_mono p hp (fun _ => 0) _ (fun z => sq_nonneg (U z))
    have hQ0 : 0 ≤ Q := Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hm : expect p (fun z => (X z)^2)*expect p (fun z => (U z)^2) ≤ (a i)^2*Q :=
      (mul_le_mul_of_nonneg_right hX2le hU20).trans
        (mul_le_mul_of_nonneg_left hU2 (sq_nonneg _))
    have he2 : expect p (fun z => (U z+X z)^2) =
        expect p (fun z => (U z)^2)+expect p (fun z => (X z)^2) := by
      have he : (fun z => (U z+X z)^2) =
          fun z => (U z)^2+2*(X z*(U z)^1)+(X z)^2 := by funext z; ring
      rw [he, expect_add, expect_add, expect_mul, hodd]
      ring
    have he4 : expect p (fun z => (U z+X z)^4) =
        expect p (fun z => (U z)^4)+
          6*(expect p (fun z => (X z)^2)*expect p (fun z => (U z)^2))+
          expect p (fun z => (X z)^4) := by
      have he : (fun z => (U z+X z)^4) = fun z =>
          (U z)^4+4*(X z*(U z)^3)+6*((X z)^2*(U z)^2)+
            4*((X z)^3*U z)+(X z)^4 := by funext z; ring
      rw [he, expect_add, expect_add, expect_add, expect_add,
        expect_mul, expect_mul, expect_mul, hodd, h31, hfac]
      ring
    have heq (z : Assignment N) :
        (∑ j ∈ insert i s, a j*(bit (z j)-p j)) = U z+X z := by
      rw [Finset.sum_insert hi]
      exact add_comm _ _
    simp only [heq, Finset.sum_insert hi]
    constructor
    · rw [he2, hX2, show expect p (fun z => (U z)^2) =
        ∑ j ∈ s, p j*(1-p j)*(a j)^2 from ih.1]
      ring
    · rw [he4]
      have hU4 : expect p (fun z => (U z)^4) ≤ 3*Q^2 := ih.2
      change _ ≤ 3*((a i)^2+Q)^2
      nlinarith only [hU4, hm, hX4, sq_nonneg ((a i)^2)]

/-- Balanced cyclic second/fourth moments. The probabilities here are explicitly indexed by natural types. -/
theorem TailBIpw_cyclic_moments (K : ℕ) (p a : ℕ → ℝ)
    (hp : ∀ t, 0 < p t ∧ p t < 1) :
    let π : Fin (3*K) → ℝ := fun i => p (i.val%3)
    let S : Assignment (3*K) → ℝ := fun z =>
      ∑ i, a (i.val%3)*(bit (z i)-π i)
    expect π (fun z => (S z)^2) =
      K*(p 0*(1-p 0)*(a 0)^2+p 1*(1-p 1)*(a 1)^2+p 2*(1-p 2)*(a 2)^2) ∧
    expect π (fun z => (S z)^4) ≤ 3*(K*((a 0)^2+(a 1)^2+(a 2)^2))^2 := by
  have hm := TailBIpw_centered_moments (fun i : Fin (3*K) => p (i.val%3))
    (fun i => hp _) (fun i => a (i.val%3)) Finset.univ
  rw [TailBIpw_sum_cycle K (fun t => p t*(1-p t)*(a t)^2),
    TailBIpw_sum_cycle K (fun t => (a t)^2)] at hm
  exact hm

end
end AronowAudit.P004.Wave1
