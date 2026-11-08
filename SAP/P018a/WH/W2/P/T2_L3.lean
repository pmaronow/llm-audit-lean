import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.P018_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018a.WH.W2.P.T2_L3

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

def witnessScore (d : Dyad 4) : Vec 1 :=
  if (firstUnit d).val = 0 ∧ (secondUnit d).val = 1 then ![1]
  else if (firstUnit d).val = 2 ∧ (secondUnit d).val = 3 then ![-1] else 0

def endpointScore (i j : Fin 4) : ℝ :=
  if i.val = 0 ∧ j.val = 1 then 1
  else if i.val = 2 ∧ j.val = 3 then -1 else 0

def endpointPair (i j k l : Fin 4) : ℝ :=
  if (({i, j} : Finset (Fin 4)) ∩ {k, l}).Nonempty then
    endpointScore i j * endpointScore k l else 0

def endpointOuter (i j : Fin 4) : ℝ :=
  ∑ f : Dyad 4,
    if (({i, j} : Finset (Fin 4)) ∩ {firstUnit f, secondUnit f}).Nonempty then
      endpointScore i j * endpointScore (firstUnit f) (secondUnit f) else 0

theorem members_pair {N : ℕ} (d : Dyad N) :
    members d = {firstUnit d, secondUnit d} := by
  exact AronowAudit.P018.Wave1.printed_members_endpoints d

theorem endpoints_lt {N : ℕ} (d : Dyad N) : firstUnit d < secondUnit d := by
  exact Finset.min'_lt_max'_of_card (members d) (by rw [members_card]; omega)

def mkDyad {N : ℕ} (i j : Fin N) (hij : i ≠ j) : Dyad N :=
  ⟨{i, j}, by simp [dyads, Finset.mem_powersetCard, hij]⟩

theorem mkDyad_endpoints {N : ℕ} (i j : Fin N) (hij : i < j) :
    firstUnit (mkDyad i j hij.ne) = i ∧ secondUnit (mkDyad i j hij.ne) = j := by
  simp [firstUnit, secondUnit, members, mkDyad, Finset.min'_pair, Finset.max'_pair,
    min_eq_left hij.le, max_eq_right hij.le]

theorem upper_sum {N : ℕ} (F : Fin N → Fin N → ℝ) :
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
      rw [members_pair, members_pair]
      rw [Prod.mk.injEq] at hde
      rw [hde.1, hde.2]
    · intro p hp
      have hp' : p.1 < p.2 := (Finset.mem_filter.mp hp).2
      refine ⟨mkDyad p.1 p.2 hp'.ne, mem_univ _, ?_⟩
      obtain ⟨h₁, h₂⟩ := mkDyad_endpoints p.1 p.2 hp'
      exact Prod.ext h₁ h₂
    · intro d hd
      rfl
  rw [h]
  simp only [P, Finset.sum_filter, Finset.sum_product]

theorem endpoint_inner_sum (i j : Fin 4) :
    (∑ f : Dyad 4,
      if (({i, j} : Finset (Fin 4)) ∩ {firstUnit f, secondUnit f}).Nonempty then
        endpointScore i j * endpointScore (firstUnit f) (secondUnit f) else 0) =
      ∑ k : Fin 4, ∑ l : Fin 4, if k < l then endpointPair i j k l else 0 := by
  let F : Fin 4 → Fin 4 → ℝ := fun k l => endpointPair i j k l
  change (∑ f : Dyad 4, F (firstUnit f) (secondUnit f)) = _
  rw [upper_sum]

end SAP.P018a.WH.W2.P.T2_L3

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators
open SAP.P018a.WH.W2.P.T2_L3

theorem SAP.P018a.WH.W2.T2_L3_proof : SAP.P018a.WH.W2.T2_L3 := by
  intro hproj
  rcases hproj with ⟨_, hscore, hsum⟩
  classical
  let P := repeatedLaw wholeRepairWitness 4
  haveI : IsProbabilityMeasure P := by
    dsimp [P, repeatedLaw, wholeRepairWitness]
    infer_instance
  have hq (ω : Fin 4 → Unit) (d : Dyad 4) :
      repeatedBlockScore wholeRepairWitness (repeatedBeta wholeRepairWitness 4) ω d =
        witnessScore d := by
    simpa [witnessScore] using hscore ω d
  have htotal (ω : Fin 4 → Unit) :
      (∑ d : Dyad 4, repeatedBlockScore wholeRepairWitness
        (repeatedBeta wholeRepairWitness 4) ω d) = 0 := hsum ω
  have hqfun (ω : Fin 4 → Unit) :
      (fun d : Dyad 4 => repeatedBlockScore wholeRepairWitness
        (repeatedBeta wholeRepairWitness 4) ω d) = witnessScore := by
    funext d
    exact hq ω d
  have hmeat : ∀ ω : Fin 4 → Unit,
      meat members (fun d : Dyad 4 => repeatedBlockScore wholeRepairWitness
        (repeatedBeta wholeRepairWitness 4) ω d) = !![2] := by
    intro ω
    rw [hqfun]
    ext a b
    fin_cases a
    fin_cases b
    change (∑ d : Dyad 4, ∑ f : Dyad 4,
      if (members d ∩ members f).Nonempty then
        witnessScore d 0 * witnessScore f 0 else 0) =
        2
    simp_rw [members_pair]
    change (∑ d : Dyad 4, ∑ f : Dyad 4,
      if (({firstUnit d, secondUnit d} : Finset (Fin 4)) ∩
          {firstUnit f, secondUnit f}).Nonempty then
        endpointScore (firstUnit d) (secondUnit d) *
          endpointScore (firstUnit f) (secondUnit f) else 0) = 2
    change (∑ d : Dyad 4, endpointOuter (firstUnit d) (secondUnit d)) = 2
    rw [upper_sum]
    simp_rw [endpointOuter, endpoint_inner_sum]
    norm_num [endpointPair, endpointScore, Fin.sum_univ_succ]
  have htotfun : (fun ω : Fin 4 → Unit =>
      ∑ d : Dyad 4, repeatedBlockScore wholeRepairWitness
        (repeatedBeta wholeRepairWitness 4) ω d) = fun _ => 0 := by
    funext ω
    exact htotal ω
  have hvar : varMat P (fun ω => ∑ d : Dyad 4,
      repeatedBlockScore wholeRepairWitness (repeatedBeta wholeRepairWitness 4) ω d) = 0 := by
    ext i j
    rw [htotfun]
    simp [varMat, covMat, ProbabilityTheory.covariance]
  have hmean : meanMat P (fun ω => meat members (fun d : Dyad 4 =>
      repeatedBlockScore wholeRepairWitness (repeatedBeta wholeRepairWitness 4) ω d)) = !![2] := by
    ext i j
    rw [show (fun ω => meat members (fun d : Dyad 4 =>
        repeatedBlockScore wholeRepairWitness (repeatedBeta wholeRepairWitness 4) ω d)) =
        (fun _ : Fin 4 → Unit => (!![2] : Mat 1)) from by
          funext ω
          exact hmeat ω]
    simp [meanMat]
  refine ⟨hvar, hmean, ?_⟩
  rw [hvar, hmean]
  intro h
  have h00 := congrArg (fun M : Mat 1 => M 0 0) h
  norm_num at h00
