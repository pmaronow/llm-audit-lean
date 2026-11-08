import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.P004_HACCompletion
import AronowAudit.P004.Wave1.Gap.TailBNedHac

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T28_L1

open AronowAudit.P004
open AronowAudit.P004.Wave1
open SAP.P004b
open scoped BigOperators Matrix Classical

noncomputable section

lemma five_eq_full {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (p : ℝ) (hN : 0 < N)
    (hp : p ≠ 0) (hq : 1-p ≠ 0)
    (hQ : ∀ i j, Q i j = Q j i) (hdiag : ∀ i, Q i i = 1) :
    wholeHacFive z e Q ((N : ℝ)*p) ((N : ℝ)*(1-p)) =
      (∑ i, ∑ j, (bit (z i)*e i/p-(1-bit (z i))*e i/(1-p)) *
        (bit (z j)*e j/p-(1-bit (z j))*e j/(1-p))*Q i j)/(N : ℝ)^2 := by
  classical
  let a : Fin N → ℝ := fun i => bit (z i)*e i
  let c : Fin N → ℝ := fun i => (1-bit (z i))*e i
  let A : ℝ := (N : ℝ)*p
  let B : ℝ := (N : ℝ)*(1-p)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hA : A ≠ 0 := mul_ne_zero hN0 hp
  have hB : B ≠ 0 := mul_ne_zero hN0 hq
  have hswap : (∑ i, ∑ j, a i*c j*Q i j) =
      ∑ i, ∑ j, c i*a j*Q i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hQ j i]
    dsimp [a, c]
    ring
  have hpoint (i j : Fin N) :
      ((a i/p-c i/(1-p))*(a j/p-c j/(1-p))*Q i j)/(N : ℝ)^2 =
        (a i*a j*Q i j)/A^2 - (a i*c j*Q i j)/(A*B) -
        (c i*a j*Q i j)/(A*B) + (c i*c j*Q i j)/B^2 := by
    dsimp [A, B]
    field_simp [hN0, hp, hq]
    <;> ring
  have hfull :
      (∑ i, ∑ j, (a i/p-c i/(1-p))*(a j/p-c j/(1-p))*Q i j)/(N : ℝ)^2 =
        (∑ i, ∑ j, a i*a j*Q i j)/A^2 -
        (∑ i, ∑ j, a i*c j*Q i j)/(A*B) -
        (∑ i, ∑ j, c i*a j*Q i j)/(A*B) +
        (∑ i, ∑ j, c i*c j*Q i j)/B^2 := by
    rw [Finset.sum_div]
    calc
      (∑ i, (∑ j, (a i/p-c i/(1-p))*(a j/p-c j/(1-p))*Q i j)/(N : ℝ)^2) =
          ∑ i, ∑ j, ((a i/p-c i/(1-p))*(a j/p-c j/(1-p))*Q i j)/(N : ℝ)^2 := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.sum_div]
      _ =
          ∑ i, ∑ j, ((a i*a j*Q i j)/A^2 - (a i*c j*Q i j)/(A*B) -
            (c i*a j*Q i j)/(A*B) + (c i*c j*Q i j)/B^2) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              exact hpoint i j
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp_rw [← Finset.sum_div]
  have haa : (∑ i, ∑ j, a i*a j*Q i j) =
      (∑ i, a i^2) + ∑ i, ∑ j ∈ Finset.univ.erase i, a i*a j*Q i j := by
    rw [AronowAudit.P004.HACCompletion.split_diagonal]
    simp only [hdiag, mul_one, pow_two]
  have hcc : (∑ i, ∑ j, c i*c j*Q i j) =
      (∑ i, c i^2) + ∑ i, ∑ j ∈ Finset.univ.erase i, c i*c j*Q i j := by
    rw [AronowAudit.P004.HACCompletion.split_diagonal]
    simp only [hdiag, mul_one, pow_two]
  have hac : (∑ i, ∑ j, a i*c j*Q i j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, a i*c j*Q i j := by
    rw [AronowAudit.P004.HACCompletion.split_diagonal]
    have hz (i : Fin N) : a i*c i*Q i i = 0 := by
      dsimp [a, c]
      rw [hdiag]
      cases z i <;> simp [bit]
    simp_rw [hz]
    simp
  have hca : (∑ i, ∑ j, c i*a j*Q i j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, c i*a j*Q i j := by
    rw [AronowAudit.P004.HACCompletion.split_diagonal]
    have hz (i : Fin N) : c i*a i*Q i i = 0 := by
      dsimp [a, c]
      rw [hdiag]
      cases z i <;> simp [bit]
    simp_rw [hz]
    simp
  have hswapOff : (∑ i, ∑ j ∈ Finset.univ.erase i, a i*c j*Q i j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, c i*a j*Q i j := by
    rw [← hac, ← hca, hswap]
  have haSq (i : Fin N) : a i^2 = bit (z i)*e i^2 := by
    dsimp [a]
    cases z i <;> simp [bit]
  have hcSq (i : Fin N) : c i^2 = (1-bit (z i))*e i^2 := by
    dsimp [c]
    cases z i <;> simp [bit]
  have haOff : (∑ i, ∑ j ∈ Finset.univ.erase i, a i*a j*Q i j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, bit (z i)*bit (z j)*e i*e j*Q i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [a]
    ring
  have hcOff : (∑ i, ∑ j ∈ Finset.univ.erase i, c i*c j*Q i j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, (1-bit (z i))*(1-bit (z j))*e i*e j*Q i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [c]
    ring
  have hmixOff : (∑ i, ∑ j ∈ Finset.univ.erase i,
      (1-bit (z i))*bit (z j)*e i*e j*Q i j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, c i*a j*Q i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [c, a]
    ring
  unfold wholeHacFive
  rw [hfull, haa, hcc, hac, hca, hswapOff]
  simp_rw [haSq, hcSq, haOff, hcOff, ← hmixOff]
  rw [add_div, add_div]
  ring

end
end SAP.P004b.WH.W3.P.T28_L1

theorem SAP.P004b.WH.W3.T28_L1_proof : SAP.P004b.WH.W3.T28_L1 := by
  intro N p R D K b hp hb hK hD hdiag
  funext z
  classical
  by_cases hN : N = 0
  · subst N
    simp [SAP.P004b.wholeV1Five, SAP.P004b.wholeHacFive,
      SAP.P004b.nedV1, SAP.P004b.nedVRow, SAP.P004b.nedEpsilon]
  · have hNp : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    have hp0 : p ≠ 0 := ne_of_gt hp.1
    have hq : 1-p ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hp.2))
    rw [SAP.P004b.wholeV1Five, SAP.P004b.wholeHacFive]
    change SAP.P004b.wholeHacFive z (residual R z) (distanceKernel D K b)
      ((N : ℝ)*p) ((N : ℝ)*(1-p)) =
      ∑ i, AronowAudit.P004.nedVRow p R D K b
        (armMean R z true) (armMean R z false) i z
    rw [AronowAudit.P004.Wave1.TailB_Ned_rows_form]
    unfold AronowAudit.P004.Wave1.TailB_Ned_form
    rw [← AronowAudit.P004.Wave1.TailB_Ned_kernel_support D K b hb hK.2.1]
    rw [SAP.P004b.WH.W3.P.T28_L1.five_eq_full z (residual R z)
      (distanceKernel D K b) p (Nat.pos_of_ne_zero hN) hp0 hq
      (fun i j => by simp [distanceKernel, hD i j])
      (fun i => by simp [distanceKernel, hdiag i, hK.1])]
    have hcontrast (i : Fin N) :
        AronowAudit.P004.residualContrast (fun _ => p) R
          (fun _ a => if a then armMean R z true else armMean R z false) i z =
        bit (z i)*residual R z i/p-(1-bit (z i))*residual R z i/(1-p) := by
      cases hi : z i <;>
        simp [AronowAudit.P004.residualContrast, AronowAudit.P004.bit, SAP.P004b.bit,
          residual, hi]
    apply congrArg (fun x : ℝ => x/(N : ℝ)^2)
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← hcontrast i, ← hcontrast j]
    rfl
