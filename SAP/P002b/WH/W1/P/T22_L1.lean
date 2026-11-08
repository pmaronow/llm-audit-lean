import SAP.P002b.WH.W1.Leaves
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Finset.Card
import AronowAudit.P002.Wave1.AlgorithmSupport.N14

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P002b.WH.W1.P.T22_L1

noncomputable section
open SAP.P002b
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

def PolicyTail {M : ℕ} (J : List ℝ)
    (choose : List (RecordedPiece M) → ℝ → Fin M)
    (history pieces : List (RecordedPiece M)) : Prop :=
  ∀ i : Fin pieces.length,
    (pieces.get i).index = choose (history ++ pieces.take i.val)
      (if history.length + i.val = 0 then J.head! - 1
       else nextAlgorithm2Sample J (pieces.get i).left)

theorem policyTail_cons {M : ℕ} (J : List ℝ)
    (choose : List (RecordedPiece M) → ℝ → Fin M)
    (history : List (RecordedPiece M)) (p : RecordedPiece M)
    (rest : List (RecordedPiece M))
    (hfirst : p.index = choose history
      (if history.length = 0 then J.head! - 1
       else nextAlgorithm2Sample J p.left))
    (hrest : PolicyTail J choose (history ++ [p]) rest) :
    PolicyTail J choose history (p :: rest) := by
  change (∀ i : Fin (rest.length + 1),
      ((p :: rest).get i).index =
        choose (history ++ (p :: rest).take i.val)
          (if history.length + i.val = 0 then J.head! - 1
           else nextAlgorithm2Sample J ((p :: rest).get i).left))
  rw [Fin.forall_fin_succ]
  constructor
  · simpa using hfirst
  · intro i
    have hi := hrest i
    simpa [List.take_succ_cons, List.get_cons_succ, List.length_append,
      List.length_singleton, List.append_assoc, Nat.add_assoc] using hi

theorem policy_run_exists {M : ℕ} (g : Fin M → ℝ → ℝ) (α : ℝ)
    (J : List ℝ) (hJ : IntersectionList g J) (hJne : J ≠ [])
    (choose : List (RecordedPiece M) → ℝ → Fin M)
    (hadm : AdmissibleIndexPolicy g α choose) :
    ∃ pieces, PolicyAlgorithm2Run g α J choose pieces := by
  let remaining : EReal → Finset ℝ :=
    fun l => J.toFinset.filter (fun β => l < (β : EReal))
  have hbuild : ∀ n : ℕ, ∀ (history : List (RecordedPiece M))
      (l : EReal) (m : Fin M),
      (remaining l).card = n →
      m = choose history
        (if history.length = 0 then J.head! - 1 else nextAlgorithm2Sample J l) →
      ∃ pieces : List (RecordedPiece M),
        (∃ r, pieces.head? = some ⟨l, r, m⟩) ∧
        (∀ i : Fin pieces.length,
          Algorithm2Step g α J (pieces.get i) (pieces[i.val + 1]?)) ∧
        PolicyTail J choose history pieces := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k ih history l m hk hm
    let C : Set ℝ :=
      {β | l < (β : EReal) ∧ ∃ s, g s ≠ g m ∧ g s β = g m β}
    have hCsub : C ⊆ {β : ℝ | β ∈ J} := by
      intro β hβ
      obtain ⟨s, hs, hsm⟩ := hβ.2
      exact (hJ.2 β).mpr ⟨s, m, hs, hsm⟩
    have hCfin : C.Finite := J.finite_toSet.subset hCsub
    by_cases hC : C.Nonempty
    · obtain ⟨e, he, hmin⟩ :=
        Set.exists_min_image C (fun β : ℝ => β) hCfin hC
      have hleast : IsLeast C e := ⟨he, hmin⟩
      have hle : l < (e : EReal) := he.1
      have heJ : e ∈ J := hCsub he

      have hsub : remaining (e : EReal) ⊆ remaining l := by
        intro β hβ
        have hβ' : β ∈ J.toFinset ∧ (e : EReal) < (β : EReal) :=
          Finset.mem_filter.mp hβ
        exact Finset.mem_filter.mpr ⟨hβ'.1, lt_trans hle hβ'.2⟩
      have heOld : e ∈ remaining l :=
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr heJ, hle⟩
      have heNew : e ∉ remaining (e : EReal) := by
        intro hem
        have hee : (e : EReal) < (e : EReal) := (Finset.mem_filter.mp hem).2
        exact (lt_irrefl (e : EReal)) hee
      have hstrict : remaining (e : EReal) ⊂ remaining l := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hsub, ?_⟩
        intro heq
        apply heNew
        rw [heq]
        exact heOld
      have hdecrease : (remaining (e : EReal)).card < k := by
        calc
          (remaining (e : EReal)).card < (remaining l).card :=
            Finset.card_lt_card hstrict
          _ = k := hk

      let p : RecordedPiece M := ⟨l, (e : EReal), m⟩
      let mNext : Fin M := choose (history ++ [p])
        (nextAlgorithm2Sample J (e : EReal))
      have hmNext : mNext ∈ mcIndices g α (nextAlgorithm2Sample J (e : EReal)) := by
        exact hadm (history ++ [p]) (nextAlgorithm2Sample J (e : EReal))
      have hmNextPolicy : mNext = choose (history ++ [p])
          (if (history ++ [p]).length = 0 then J.head! - 1
           else nextAlgorithm2Sample J (e : EReal)) := by
        simp [mNext]
      obtain ⟨rest, ⟨r, hhead⟩, hsteps, htail⟩ :=
        ih (remaining (e : EReal)).card hdecrease (history ++ [p])
          (e : EReal) mNext rfl hmNextPolicy
      have hpStep : Algorithm2Step g α J p rest.head? := by
        change
          (if C.Nonempty then
            ∃ e' : ℝ, IsLeast C e' ∧ (e : EReal) = (e' : EReal)
          else (e : EReal) = ⊤) ∧
          (match rest.head? with
          | none => (e : EReal) = ⊤
          | some q => (e : EReal) ≠ ⊤ ∧ q.left = (e : EReal) ∧
              q.index ∈ mcIndices g α (nextAlgorithm2Sample J (e : EReal)))
        constructor
        · rw [if_pos hC]
          exact ⟨e, hleast, rfl⟩
        · rw [hhead]
          exact ⟨EReal.coe_ne_top e, rfl, hmNext⟩
      have hpolicy : PolicyTail J choose history (p :: rest) := by
        apply policyTail_cons
        · simpa [p] using hm
        · exact htail
      refine ⟨p :: rest, ⟨(e : EReal), rfl⟩, ?_, hpolicy⟩
      exact (AronowAudit.P002.Wave1.AlgorithmSupport.n14_proof
        (Algorithm2Step g α J) p rest).mpr ⟨hpStep, hsteps⟩
    · let p : RecordedPiece M := ⟨l, ⊤, m⟩
      have hpStep : Algorithm2Step g α J p none := by
        change
          (if C.Nonempty then
            ∃ e : ℝ, IsLeast C e ∧ (⊤ : EReal) = (e : EReal)
          else (⊤ : EReal) = ⊤) ∧ (⊤ : EReal) = ⊤
        rw [if_neg hC]
        exact ⟨rfl, rfl⟩
      have hpolicy : PolicyTail J choose history [p] := by
        apply policyTail_cons
        · simpa [p] using hm
        · intro i
          exact Fin.elim0 i
      refine ⟨[p], ⟨⊤, rfl⟩, ?_, hpolicy⟩
      apply (AronowAudit.P002.Wave1.AlgorithmSupport.n14_proof
        (Algorithm2Step g α J) p []).mpr
      constructor
      · exact hpStep
      · intro i
        exact Fin.elim0 i

  let m₀ : Fin M := choose [] (J.head! - 1)
  have hm₀ : m₀ ∈ mcIndices g α (J.head! - 1) := hadm [] (J.head! - 1)
  have hm₀policy : m₀ = choose [] (if ([] : List (RecordedPiece M)).length = 0 then
      J.head! - 1 else nextAlgorithm2Sample J ⊥) := by
    simp [m₀]
  obtain ⟨pieces, ⟨r, hhead⟩, hsteps, htail⟩ :=
    hbuild (remaining ⊥).card [] ⊥ m₀ rfl hm₀policy
  have hrun : Algorithm2Run g α J pieces := by
    refine ⟨hJ, hJne, ?_, ?_, hsteps⟩
    · intro hnil
      simp [hnil] at hhead
    · intro p hp
      have hpEq : p = ⟨⊥, r, m₀⟩ := Option.some.inj (hp.symm.trans hhead)
      rw [hpEq]
      exact ⟨rfl, hm₀⟩
  refine ⟨pieces, hrun, ?_⟩
  intro i
  have hi := htail i
  simpa [PolicyTail] using hi

end
end SAP.P002b.WH.W1.P.T22_L1

theorem SAP.P002b.WH.W1.T22_L1_proof : SAP.P002b.WH.W1.T22_L1 := by
  intro M g α J hJ hJne choose hadm
  exact SAP.P002b.WH.W1.P.T22_L1.policy_run_exists g α J hJ hJne choose hadm
