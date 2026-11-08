import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace SAP.P018a.WH.W2.P.T2_L2

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
open SAP.P018a

lemma endpoints_lt {N : ℕ} (d : Dyad N) : firstUnit d < secondUnit d := by
  exact Finset.min'_lt_max'_of_card (members d) (by rw [members_card]; omega)

lemma members_endpoints {N : ℕ} (d : Dyad N) :
    members d = {firstUnit d, secondUnit d} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.min'_mem _ _
    · exact Finset.max'_mem _ _
  · rw [members_card]
    simp [ne_of_lt (endpoints_lt d)]

def pairScore (i j : Fin 4) : Vec 1 :=
  if i.val = 0 ∧ j.val = 1 then ![1] else if i.val = 2 ∧ j.val = 3 then ![-1] else 0

def mkPair {N : ℕ} (i j : Fin N) (hij : i ≠ j) : Dyad N :=
  ⟨{i, j}, by simp [dyads, Finset.mem_powersetCard, hij]⟩

lemma mkPair_endpoints {N : ℕ} (i j : Fin N) (hij : i < j) :
    firstUnit (mkPair i j hij.ne) = i ∧ secondUnit (mkPair i j hij.ne) = j := by
  simp [firstUnit, secondUnit, members, mkPair, min_eq_left hij.le, max_eq_right hij.le]

lemma upper_sum {N : ℕ} (F : Fin N → Fin N → ℝ) :
    (∑ d : Dyad N, F (firstUnit d) (secondUnit d)) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then F i j else 0 := by
  classical
  let P := (univ ×ˢ univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)
  have h : (∑ d : Dyad N, F (firstUnit d) (secondUnit d)) =
      ∑ p ∈ P, F p.1 p.2 := by
    apply Finset.sum_bij (fun d _ => (firstUnit d, secondUnit d))
    · intro d hd
      simp [P, endpoints_lt]
    · intro d hd e he hde
      apply Subtype.ext
      change members d = members e
      rw [members_endpoints d, members_endpoints e]
      rw [Prod.mk.injEq] at hde
      rw [hde.1, hde.2]
    · intro p hp
      have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      refine ⟨mkPair p.1 p.2 hp'.ne, mem_univ _, ?_⟩
      obtain ⟨h₁, h₂⟩ := mkPair_endpoints p.1 p.2 hp'
      exact Prod.ext h₁ h₂
    · intro d hd
      rfl
  rw [h]
  simp only [P, Finset.sum_filter, Finset.sum_product]

lemma pairScore_sum :
    (∑ i : Fin 4, ∑ j : Fin 4, if i < j then (pairScore i j) 0 else 0) = 0 := by
  norm_num [Fin.sum_univ_succ, pairScore]

lemma sum_fin_cast {n m : ℕ} {M : Type} [AddCommMonoid M]
    (h : n = m) (f : Fin n → M) :
    (∑ t : Fin n, f t) = ∑ t : Fin m, f ((finCongr h).symm t) := by
  exact Fintype.sum_equiv (finCongr h) f (fun t => f ((finCongr h).symm t)) (by intro; rfl)

def responseValue {n : ℕ} (t : Fin n) : ℝ :=
  if t.val = 0 then 0 else if t.val = 1 then 1 else -2

lemma block_raw (ω : Fin 4 → Unit) (d : Dyad 4) :
    (∑ t, score (repeatedX wholeRepairWitness ω d t)
      (repeatedY wholeRepairWitness ω d t)) =
      pairScore (firstUnit d) (secondUnit d) := by
  classical
  by_cases h01 : firstUnit d = 0 ∧ secondUnit d = 1
  · have h01v : (firstUnit d).val = 0 ∧ (secondUnit d).val = 1 :=
      ⟨congrArg Fin.val h01.1, congrArg Fin.val h01.2⟩
    have hT : wholeRepairWitness.T 4 d = 2 := by
      dsimp [wholeRepairWitness]
      simp [h01v]
    have hv : (∑ t, score (repeatedX wholeRepairWitness ω d t)
        (repeatedY wholeRepairWitness ω d t)) =
        ![(∑ t : Fin (wholeRepairWitness.T 4 d), responseValue t)] := by
      ext a
      fin_cases a
      simp only [Fintype.sum_apply]
      simp [responseValue, repeatedX, repeatedY, wholeRepairWitness, score]
    have hs : (∑ t : Fin (wholeRepairWitness.T 4 d), responseValue t) = 1 := by
      rw [sum_fin_cast hT responseValue]
      norm_num [responseValue, Fin.sum_univ_succ]
    rw [hv, hs]
    simp [pairScore, h01]
  · by_cases h23 : firstUnit d = 2 ∧ secondUnit d = 3
    · have h23v : (firstUnit d).val = 2 ∧ (secondUnit d).val = 3 :=
        ⟨congrArg Fin.val h23.1, congrArg Fin.val h23.2⟩
      have h01v : ¬((firstUnit d).val = 0 ∧ (secondUnit d).val = 1) := by
        intro h
        exact h01 ⟨Fin.ext h.1, Fin.ext h.2⟩
      have hT : wholeRepairWitness.T 4 d = 3 := by
        dsimp [wholeRepairWitness]
        simp [h23v]
      have hv : (∑ t, score (repeatedX wholeRepairWitness ω d t)
          (repeatedY wholeRepairWitness ω d t)) =
          ![(∑ t : Fin (wholeRepairWitness.T 4 d), responseValue t)] := by
        ext a
        fin_cases a
        simp only [Fintype.sum_apply]
        simp [responseValue, repeatedX, repeatedY, wholeRepairWitness, score]
      have hs : (∑ t : Fin (wholeRepairWitness.T 4 d), responseValue t) = -1 := by
        rw [sum_fin_cast hT responseValue]
        norm_num [responseValue, Fin.sum_univ_succ]
      rw [hv, hs]
      simp [pairScore, h23]
    · have h01v : ¬((firstUnit d).val = 0 ∧ (secondUnit d).val = 1) := by
        intro h
        exact h01 ⟨Fin.ext h.1, Fin.ext h.2⟩
      have h23v : ¬((firstUnit d).val = 2 ∧ (secondUnit d).val = 3) := by
        intro h
        exact h23 ⟨Fin.ext h.1, Fin.ext h.2⟩
      have h01mixed : ¬(firstUnit d = 0 ∧ (secondUnit d).val = 1) := by
        intro h
        exact h01 ⟨h.1, Fin.ext h.2⟩
      have h23mixed : ¬(firstUnit d = 2 ∧ (secondUnit d).val = 3) := by
        intro h
        exact h23 ⟨h.1, Fin.ext h.2⟩
      have hT : wholeRepairWitness.T 4 d = 1 := by
        dsimp [wholeRepairWitness]
        simp only [ite_eq_right h01v, ite_eq_right h23v]
      have hv : (∑ t, score (repeatedX wholeRepairWitness ω d t)
          (repeatedY wholeRepairWitness ω d t)) =
          ![(∑ t : Fin (wholeRepairWitness.T 4 d), responseValue t)] := by
        ext a
        fin_cases a
        simp only [Fintype.sum_apply]
        simp [responseValue, repeatedX, repeatedY, wholeRepairWitness, score]
      have hs : (∑ t : Fin (wholeRepairWitness.T 4 d), responseValue t) = 0 := by
        rw [sum_fin_cast hT responseValue]
        norm_num [responseValue, Fin.sum_univ_succ]
      rw [hv, hs]
      simp [pairScore, h01mixed, h23v]

lemma rawScore_total (ω : Fin 4 → Unit) :
    (∑ d : Dyad 4, ∑ t,
      score (repeatedX wholeRepairWitness ω d t) (repeatedY wholeRepairWitness ω d t)) = 0 := by
  classical
  have hterm (d : Dyad 4) :
      (∑ t, score (repeatedX wholeRepairWitness ω d t)
        (repeatedY wholeRepairWitness ω d t)) =
      pairScore (firstUnit d) (secondUnit d) := by
    exact block_raw ω d
  have hterm0 (d : Dyad 4) :
      (∑ t, (score (repeatedX wholeRepairWitness ω d t)
        (repeatedY wholeRepairWitness ω d t)) 0) =
      (pairScore (firstUnit d) (secondUnit d)) 0 := by
    have := congrArg (fun v : Vec 1 => v 0) (hterm d)
    simpa using this
  ext a
  fin_cases a
  change (∑ d : Dyad 4, ∑ t, (score (repeatedX wholeRepairWitness ω d t)
    (repeatedY wholeRepairWitness ω d t)) 0) = 0
  calc
    (∑ d : Dyad 4, ∑ t, (score (repeatedX wholeRepairWitness ω d t)
        (repeatedY wholeRepairWitness ω d t)) 0)
        = ∑ d : Dyad 4, (pairScore (firstUnit d) (secondUnit d)) 0 := by
            exact Finset.sum_congr rfl (fun d _ => hterm0 d)
    _ = ∑ i : Fin 4, ∑ j : Fin 4, if i < j then (pairScore i j) 0 else 0 :=
          upper_sum (fun i j => (pairScore i j) 0)
    _ = 0 := pairScore_sum

lemma meanGram_eq
    (hgram : ∀ ω : Fin 4 → Unit, repeatedGram wholeRepairWitness ω = !![9]) :
    meanMat (repeatedLaw wholeRepairWitness 4) (repeatedGram wholeRepairWitness) = !![9] := by
  ext a b
  simp only [meanMat]
  have hfun : (fun ω : Fin 4 → Unit => repeatedGram wholeRepairWitness ω a b) =
      fun _ => (!![9] : Mat 1) a b := by
    funext ω
    rw [hgram ω]
  rw [hfun]
  simp [repeatedLaw, wholeRepairWitness]

lemma meanRaw_eq :
    meanVec (repeatedLaw wholeRepairWitness 4) (fun ω =>
      ∑ d : Dyad 4, ∑ t,
        score (repeatedX wholeRepairWitness ω d t) (repeatedY wholeRepairWitness ω d t)) = 0 := by
  ext a
  simp only [meanVec]
  have hfun : (fun ω : Fin 4 → Unit =>
      (∑ d : Dyad 4, ∑ t,
        score (repeatedX wholeRepairWitness ω d t) (repeatedY wholeRepairWitness ω d t)) a) =
      fun _ => 0 := by
    funext ω
    rw [rawScore_total ω]
    rfl
  rw [hfun]
  simp [repeatedLaw, wholeRepairWitness]

lemma beta_zero
    (hgram : ∀ ω : Fin 4 → Unit, repeatedGram wholeRepairWitness ω = !![9]) :
    repeatedBeta wholeRepairWitness 4 = 0 := by
  unfold repeatedBeta
  rw [meanGram_eq hgram, meanRaw_eq]
  simp

end SAP.P018a.WH.W2.P.T2_L2

open SAP.P018a.WH.W2.P.T2_L2

theorem SAP.P018a.WH.W2.T2_L2_proof : SAP.P018a.WH.W2.T2_L2 := by
  intro hInput
  rcases hInput with ⟨_, _, _, _, hgram, _⟩
  have hβ : repeatedBeta wholeRepairWitness 4 = 0 := beta_zero hgram
  refine ⟨hβ, ?_, ?_⟩
  · intro ω d
    rw [hβ]
    simpa [repeatedBlockScore, dot, pairScore] using block_raw ω d
  · intro ω
    simpa [repeatedBlockScore, dot, hβ] using rawScore_total ω
