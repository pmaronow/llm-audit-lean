import SAP.P004a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1.P.T1_L1

open SAP.P004a.WH.W1
open AronowAudit.P004
open scoped BigOperators

set_option maxHeartbeats 1000000

private def indexEquiv (K : ℕ) : (Fin K × Fin 3) ≃ Fin (3*K) :=
  (finProdFinEquiv : Fin K × Fin 3 ≃ Fin (K*3)).trans
    (finCongr (Nat.mul_comm K 3))

private lemma indexEquiv_apply (K : ℕ) (j : Fin K) (t : Fin 3) :
    indexEquiv K (j,t) = w1ThreeBlockIndex j t := by
  apply Fin.ext
  simp [indexEquiv, w1ThreeBlockIndex, finProdFinEquiv]
  omega

private def encodeBlocks (K : ℕ) (z : Assignment (3*K)) : Fin K → Assignment 3 :=
  fun j t => z (indexEquiv K (j,t))

private def decodeBlocks (K : ℕ) (b : Fin K → Assignment 3) : Assignment (3*K) :=
  fun i => b ((indexEquiv K).symm i).1 ((indexEquiv K).symm i).2

private def blockAssignments (K : ℕ) : Assignment (3*K) ≃ (Fin K → Assignment 3) where
  toFun := encodeBlocks K
  invFun := decodeBlocks K
  left_inv := by
    intro z
    funext i
    simp [encodeBlocks, decodeBlocks]
  right_inv := by
    intro b
    funext j
    funext t
    simp [encodeBlocks, decodeBlocks]

private lemma threeP_block (K : ℕ) (j : Fin K) (t : Fin 3) :
    w1ThreeP (3*K) (w1ThreeBlockIndex j t) = w1ThreeP 3 t := by
  have hN : w1ThreeP (3*K) = fun i =>
      AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) :=
    AronowAudit.P004.Wave1.DecideP004T1_propensities (3*K)
  have h3 : w1ThreeP 3 = fun i =>
      AronowAudit.P004.Wave1.DecideP004T1_p (i.val % 3) :=
    AronowAudit.P004.Wave1.DecideP004T1_propensities 3
  rw [hN, h3]
  apply congrArg AronowAudit.P004.Wave1.DecideP004T1_p
  simp only [w1ThreeBlockIndex]
  have ht := t.isLt
  omega

private lemma block_weight (K : ℕ) (b : Fin K → Assignment 3) :
    designWeight (w1ThreeP (3*K)) (decodeBlocks K b) =
      ∏ j : Fin K, designWeight (w1ThreeP 3) (b j) := by
  classical
  unfold designWeight decodeBlocks
  rw [← (indexEquiv K).prod_comp
    (fun i => coin (w1ThreeP (3*K) i)
      (b ((indexEquiv K).symm i).1 ((indexEquiv K).symm i).2))]
  simp_rw [Equiv.symm_apply_apply]
  rw [Fintype.prod_prod_type]
  simp_rw [indexEquiv_apply, threeP_block]

private lemma block_value (K : ℕ) (z : Assignment (3*K)) :
    w1ThreeBlock z = fun j => w1OneBlock (encodeBlocks K z j) := by
  funext j
  unfold w1ThreeBlock w1OneBlock encodeBlocks
  apply Finset.sum_congr rfl
  intro t ht
  rw [indexEquiv_apply]

private lemma decoded_block_value (K : ℕ) (b : Fin K → Assignment 3) :
    w1ThreeBlock (decodeBlocks K b) = fun j => w1OneBlock (b j) := by
  calc
    w1ThreeBlock (decodeBlocks K b) =
        fun j => w1OneBlock (encodeBlocks K (decodeBlocks K b) j) :=
      block_value K (decodeBlocks K b)
    _ = fun j => w1OneBlock (b j) := by
      have hb : encodeBlocks K (decodeBlocks K b) = b := by
        funext j t
        simp [encodeBlocks, decodeBlocks]
      rw [hb]

private lemma blockAssignments_symm (K : ℕ) (b : Fin K → Assignment 3) :
    (blockAssignments K).symm b = decodeBlocks K b := rfl

end SAP.P004a.WH.W1.P.T1_L1

open SAP.P004a.WH.W1
open SAP.P004a.WH.W1.P.T1_L1

theorem SAP.P004a.WH.W1.T1_L1_proof : SAP.P004a.WH.W1.T1_L1 := by
  intro K F
  classical
  unfold expect
  rw [← (blockAssignments K).symm.sum_comp
    (fun z => designWeight (w1ThreeP (3*K)) z * F (w1ThreeBlock z))]
  apply Finset.sum_congr rfl
  intro b hb
  rw [blockAssignments_symm, block_weight K b, decoded_block_value K b]
