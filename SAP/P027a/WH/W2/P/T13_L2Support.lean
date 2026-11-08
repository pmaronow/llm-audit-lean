import SAP.P027a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P027a.WH.W2.P.T13_L2

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {α : Type*} [MeasurableSpace α]

def firstHit (F : Set α) (n : ℕ) : Set (ℕ → α) :=
  {w | (∀ i < n, w i ∉ F) ∧ w n ∈ F}

def firstExact (F : Set α) (n : ℕ) (x : α) : Set (ℕ → α) :=
  {w | (∀ i < n, w i ∉ F) ∧ w n ∈ F ∧ w n = x}

def noHit (F : Set α) : Set (ℕ → α) :=
  {w | ¬ ∃ n, w n ∈ F}

def firstHitCylinder (F : Set α) (n : ℕ) : Set (ℕ → α) :=
  Set.pi (Finset.range (n + 1)) (fun i => if i = n then F else Fᶜ)

def firstExactCylinder (F : Set α) (n : ℕ) (x : α) : Set (ℕ → α) :=
  Set.pi (Finset.range (n + 1))
    (fun i => if i = n then F ∩ {x} else Fᶜ)

lemma firstHit_eq_cylinder (F : Set α) (n : ℕ) :
    firstHit F n = firstHitCylinder F n := by
  ext w
  simp only [firstHit, firstHitCylinder, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · rintro ⟨hprior, hn⟩ i hi
    by_cases h : i = n
    · simpa [h] using hn
    · have hin : i < n := by omega
      simpa [h] using hprior i hin
  · intro h
    refine ⟨?_, ?_⟩
    · intro i hi
      have hir : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hmem := h i (by simpa using hir)
      have hne : i ≠ n := by omega
      simpa [hne] using hmem
    · have hmem := h n (by simp)
      simpa using hmem

lemma firstExact_eq_cylinder (F : Set α) (n : ℕ) (x : α) :
    firstExact F n x = firstExactCylinder F n x := by
  ext w
  simp only [firstExact, firstExactCylinder, Set.mem_pi, Finset.mem_coe, Finset.mem_range]
  constructor
  · rintro ⟨hprior, hnF, hnx⟩ i hi
    by_cases h : i = n
    · simpa [h, hnx] using hnF
    · have hin : i < n := by omega
      simpa [h] using hprior i hin
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hir : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hmem := h i (by simpa using hir)
      have hne : i ≠ n := by omega
      simpa [hne] using hmem
    · have hmem := h n (by simp)
      simp only [if_pos rfl] at hmem
      exact hmem.1
    · have hmem := h n (by simp)
      simp only [if_pos rfl] at hmem
      exact hmem.2

lemma firstHit_measurable (F : Set α) (n : ℕ) (hF : MeasurableSet F) :
    MeasurableSet (firstHit F n) := by
  rw [firstHit_eq_cylinder]
  exact MeasurableSet.pi (Finset.countable_toSet _) (by
    intro i hi
    split_ifs <;> simp [hF])

lemma firstExact_measurable (F : Set α) (n : ℕ) (x : α)
    [MeasurableSingletonClass α] (hF : MeasurableSet F) :
    MeasurableSet (firstExact F n x) := by
  rw [firstExact_eq_cylinder]
  exact MeasurableSet.pi (Finset.countable_toSet _) (by
    intro i hi
    split_ifs <;> simp [hF])

lemma firstHit_measure (μ : Measure α) [IsProbabilityMeasure μ] (F : Set α) (n : ℕ)
    (hF : MeasurableSet F) :
    Measure.infinitePi (fun _ : ℕ => μ) (firstHit F n) =
      (μ Fᶜ) ^ n * μ F := by
  rw [firstHit_eq_cylinder, firstHitCylinder]
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => μ) (mt := by
    intro i hi
    by_cases h : i = n
    · simp [h, hF]
    · simp [h, hF.compl])]
  rw [Finset.prod_range_succ]
  have hprod :
      (∏ i ∈ Finset.range n, μ (if i = n then F else Fᶜ)) = (μ Fᶜ) ^ n := by
    calc
      (∏ i ∈ Finset.range n, μ (if i = n then F else Fᶜ)) =
          ∏ i ∈ Finset.range n, μ Fᶜ := by
            apply Finset.prod_congr rfl
            intro i hi
            have hne : i ≠ n := by simp only [Finset.mem_range] at hi; omega
            simp [hne]
      _ = (μ Fᶜ) ^ n := by simp
  rw [hprod]
  simp

lemma firstExact_measure (μ : Measure α) [IsProbabilityMeasure μ] (F : Set α) (n : ℕ) (x : α)
    [MeasurableSingletonClass α]
    (hF : MeasurableSet F) :
    Measure.infinitePi (fun _ : ℕ => μ) (firstExact F n x) =
      (μ Fᶜ) ^ n * μ ({x} ∩ F) := by
  rw [firstExact_eq_cylinder, firstExactCylinder]
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => μ) (mt := by
    intro i hi
    by_cases h : i = n
    · simp [h, hF, measurableSet_singleton]
    · simp [h, hF.compl])]
  rw [Finset.prod_range_succ]
  have hprod :
      (∏ i ∈ Finset.range n, μ (if i = n then F ∩ {x} else Fᶜ)) =
        (μ Fᶜ) ^ n := by
    calc
      (∏ i ∈ Finset.range n, μ (if i = n then F ∩ {x} else Fᶜ)) =
          ∏ i ∈ Finset.range n, μ Fᶜ := by
            apply Finset.prod_congr rfl
            intro i hi
            have hne : i ≠ n := by simp only [Finset.mem_range] at hi; omega
            simp [hne]
      _ = (μ Fᶜ) ^ n := by simp
  rw [hprod]
  simp [Set.inter_comm]

lemma firstHit_pairwise (F : Set α) : Pairwise (Disjoint on firstHit F) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro w hi hj
  rcases hi with ⟨hiPrior, hiHit⟩
  rcases hj with ⟨hjPrior, hjHit⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (hjPrior i hlt) hiHit
  · exact (hiPrior j hgt) hjHit

lemma firstExact_pairwise (F : Set α) (x : α) :
    Pairwise (Disjoint on fun n => firstExact F n x) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro w hi hj
  rcases hi with ⟨hiPrior, hiHit, _⟩
  rcases hj with ⟨hjPrior, hjHit, _⟩
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (hjPrior i hlt) hiHit
  · exact (hiPrior j hgt) hjHit

lemma output_preimage (F : Set α) (x z : α) :
    {w : ℕ → α | (if h : ∃ n, w n ∈ F then w (Nat.find h) else z) = x} =
      (⋃ n, firstExact F n x) ∪ (if x = z then noHit F else ∅) := by
  classical
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion]
  change (if h : ∃ n, w n ∈ F then w (Nat.find h) else z) = x ↔
    (∃ n, w ∈ firstExact F n x) ∨ w ∈ (if x = z then noHit F else ∅)
  by_cases he : ∃ n, w n ∈ F
  · have hfind : w (Nat.find he) ∈ F := Nat.find_spec he
    have hD : w ∉ (if x = z then noHit F else ∅) := by
      by_cases hx : x = z <;> simp [hx, noHit, he]
    simp only [dif_pos he, hD, or_false]
    simp only [firstExact]
    constructor
    · intro hout
      refine ⟨Nat.find he, ?_⟩
      refine ⟨?_, hfind, hout⟩
      intro i hi hmem
      have hle := Nat.find_min' he hmem
      omega
    · rintro ⟨n, hprior, hhit, hnx⟩
      have hfindle : Nat.find he ≤ n := Nat.find_min' he hhit
      have hnle : n ≤ Nat.find he := by
        by_contra hnot
        have hlt : Nat.find he < n := by omega
        exact hprior (Nat.find he) hlt hfind
      have hEq : n = Nat.find he := by omega
      simpa [hEq] using hnx
  · have hzero : ¬ ∃ n, w n ∈ F := he
    have hU : ¬ ∃ n, w ∈ firstExact F n x := by
      rintro ⟨n, hn⟩
      rcases hn with ⟨_, hhit, _⟩
      exact hzero ⟨n, hhit⟩
    have hnot : w ∈ noHit F := by simpa [noHit] using hzero
    have hD : w ∈ (if x = z then noHit F else ∅) ↔ x = z := by
      by_cases hx : x = z <;> simp [hx, hnot]
    simp [he, hU, hD, eq_comm]

end
end SAP.P027a.WH.W2.P.T13_L2
