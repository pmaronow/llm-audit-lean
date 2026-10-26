import AronowAudit.P037.P037_Sample
import AronowAudit.P037.P037_Design
import AronowAudit.P037.P037_FiniteDesign
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.BigOperators

namespace AronowAudit.P037.Wave1
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma blockedExposure_avoidance_count (n t : ℕ) (peers : Finset (Fin n)) :
    Fintype.card {s : {s : Finset (Fin n) // s.card=t} //
      Disjoint s.val peers} = Nat.choose (n-peers.card) t := by
  classical
  let e : {s : {s : Finset (Fin n) // s.card=t} // Disjoint s.val peers} ≃
      {s // s ∈ (seedChoices n t).filter (fun s => Disjoint s peers)} :=
    { toFun := fun s => ⟨s.val.val, by simp [seedChoices, s.val.property, s.property]⟩
      invFun := fun s => ⟨⟨s.val, (Finset.mem_powersetCard.mp
        (Finset.mem_filter.mp s.property).1).2⟩, (Finset.mem_filter.mp s.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, count_avoiding_seeds]

lemma blockedExposure_local_sum (n t : ℕ) (peers : Finset (Fin n)) :
    (∑ s : {s : Finset (Fin n) // s.card=t},
      (1:ℝ)/(Nat.choose n t:ℝ) * (if Disjoint s.val peers then 1 else 0)) =
      (Nat.choose (n-peers.card) t:ℝ)/(Nat.choose n t:ℝ) := by
  classical
  rw [← Finset.mul_sum, Finset.sum_boole]
  have hc := blockedExposure_avoidance_count n t peers
  rw [← Fintype.card_subtype] 
  rw [hc]
  ring

theorem blocked_school_exposure_formula_proof {b : ℕ} (n t : Fin b → ℕ)
    (peers : (h : Fin b) → Finset (Fin (n h))) (ht : ∀ h, t h≤n h) :
    let Ω := (h : Fin b) → {s : Finset (Fin (n h)) // s.card=t h}
    (1/2)*(∑ z : Ω,
      (∏ h, (1:ℝ)/(Nat.choose (n h) (t h):ℝ)) *
        (if ∀ h, Disjoint (z h).val (peers h) then (1:ℝ) else 0))=
      blockedSchoolExposure n t (fun h => (peers h).card) := by
  classical
  dsimp only
  unfold blockedSchoolExposure
  congr 1
  calc
    _ = ∑ z : (h : Fin b) → {s : Finset (Fin (n h)) // s.card=t h},
        ∏ h, ((1:ℝ)/(Nat.choose (n h) (t h):ℝ) *
          (if Disjoint (z h).val (peers h) then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.prod_mul_distrib, Fintype.prod_boole]
      split_ifs <;> rfl
    _ = ∏ h, ∑ s : {s : Finset (Fin (n h)) // s.card=t h},
        (1:ℝ)/(Nat.choose (n h) (t h):ℝ) *
          (if Disjoint s.val (peers h) then 1 else 0) :=
      finite_product_factorization (I := Fin b)
        (Ω := fun h => {s : Finset (Fin (n h)) // s.card=t h})
        (fun h s => (1:ℝ)/(Nat.choose (n h) (t h):ℝ) *
          (if Disjoint s.val (peers h) then 1 else 0))
    _ = _ := by simp_rw [blockedExposure_local_sum]

lemma monteCarlo_chebyshev_ge {Ω : Type*} [Fintype Ω]
    (d : FiniteDesign Ω) (X : Ω → ℝ) (ε : ℝ) (hε : 0<ε) :
    designProbability d (fun z => ε ≤ |X z-designMean d X|) ≤
      designVariance d X / ε^2 := by
  classical
  rw [le_div_iff₀ (sq_pos_of_pos hε), designVariance_centered]
  unfold designProbability designMean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro z _
  change (d.weight z * if ε ≤ |X z-designMean d X| then 1 else 0)*ε^2 ≤
    d.weight z*(X z-designMean d X)^2
  by_cases hz : ε ≤ |X z-designMean d X|
  · simp only [if_pos hz, mul_one]
    apply mul_le_mul_of_nonneg_left _ (d.nonneg z)
    nlinarith [sq_abs (X z-designMean d X)]
  · simp only [if_neg hz, mul_zero, zero_mul]
    exact mul_nonneg (d.nonneg z) (sq_nonneg _)

lemma monteCarlo_single {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (J : ℕ) (hJ : 0<J)
    (E : Ω → Prop) (ε : ℝ) (hε : 0<ε) :
    (∑ z : Fin J → Ω, (∏ j, P.mass (z j)) *
      (if |((Finset.univ.filter (fun j => E (z j))).card:ℝ)/J-
        sampleProb P E|≥ε then (1:ℝ) else 0)) ≤ 1/(4*J*ε^2) := by
  classical
  let d : FiniteDesign Ω := ⟨P.mass, fun z => (P.positive z).le, P.total⟩
  let D := productDesign (fun _ : Fin J => d)
  let X := fun j : Fin J => fun z : Fin J → Ω => if E (z j) then (1:ℝ) else 0
  have hmean : ∀ j, designMean D (X j)=sampleProb P E := by
    intro j
    convert product_design_coordinate_mean (fun _ : Fin J => d) j
      (fun z => if E z then (1:ℝ) else 0) using 1 <;>
      simp [D, X, designMean, sampleProb, d, productDesign] <;> congr!
  have hpair : ∀ j k, j≠k →
      designMean D (fun z => X j z*X k z)=(sampleProb P E)^2 := by
    intro j k hjk
    convert product_design_coordinate_pair (fun _ : Fin J => d) j k hjk
      (fun z => if E z then (1:ℝ) else 0) (fun z => if E z then (1:ℝ) else 0) using 1 <;>
      simp [D, X, designMean, sampleProb, d, productDesign, pow_two] <;> congr!
  have hbinary : ∀ j z, X j z=0 ∨ X j z=1 := by
    intro j z
    dsimp [X]
    split_ifs <;> simp
  obtain ⟨hm, _, hv, _⟩ :=
    monte_carlo_frequency_moments D J hJ X (sampleProb P E) hbinary hmean hpair
  have ht := monteCarlo_chebyshev_ge D (fun z => (∑ j, X j z)/J) ε hε
  rw [hm] at ht
  have hcount : ∀ z : Fin J → Ω,
      (∑ j, X j z)=((Finset.univ.filter (fun j => E (z j))).card:ℝ) := by
    intro z
    exact Finset.sum_boole _ _
  simp_rw [hcount] at ht hv
  calc
    _ ≤ designVariance D (fun z => ((Finset.univ.filter (fun j => E (z j))).card:ℝ)/J)/ε^2 := ht
    _ ≤ (1/(4*J))/ε^2 := div_le_div_of_nonneg_right hv (sq_nonneg ε)
    _ = _ := by ring

theorem monte_carlo_simultaneous_bound_proof {Ω : Type*} [Fintype Ω]
    (P : SupportedDesign Ω) (m J : ℕ) (hJ : 0<J)
    (E : Fin m → Ω → Prop) (ε : ℝ) (hε : 0<ε) :
    (∑ z : Fin J → Ω, (∏ j, P.mass (z j)) *
      (if ∃ k, |((Finset.univ.filter (fun j => E k (z j))).card:ℝ)/J-
        sampleProb P (E k)|≥ε then (1:ℝ) else 0))≤(m:ℝ)/(4*J*ε^2) := by
  classical
  let d : FiniteDesign Ω := ⟨P.mass, fun z => (P.positive z).le, P.total⟩
  let D := productDesign (fun _ : Fin J => d)
  let A := fun k : Fin m => fun z : Fin J → Ω =>
    ε ≤ |((Finset.univ.filter (fun j => E k (z j))).card:ℝ)/J-sampleProb P (E k)|
  calc
    _ = designProbability D (fun z => ∃ k, A k z) := by
      simp [D, d, A, designProbability, designMean, productDesign]
    _ ≤ ∑ k, designProbability D (A k) :=
      WitnessCompletion.probability_exists_le_sum D A
    _ ≤ ∑ _k : Fin m, 1/(4*J*ε^2) := by
      apply Finset.sum_le_sum
      intro k _
      exact monteCarlo_single P J hJ (E k) ε hε
    _ = (m:ℝ)/(4*J*ε^2) := by simp [div_eq_mul_inv]

lemma schoolSampler_subset_card (n t : ℕ) :
    Fintype.card {s : Finset (Fin n) // s.card=t} = Nat.choose n t := by
  classical
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter (fun s : Finset (Fin n) => s.card=t)) =
      Finset.univ.powersetCard t := by ext s; simp
  rw [he, Finset.card_powersetCard]
  simp

noncomputable def schoolSampler_section {B : ℕ}
    (s : Finset (Fin B × Fin 4)) (b : Fin B) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => (b,i)∈s)

lemma schoolSampler_section_card {B : ℕ} (s : Finset (Fin B × Fin 4)) (b : Fin B) :
    (schoolSampler_section s b).card = (s.filter (fun i => i.1=b)).card := by
  classical
  apply Finset.card_bij (fun i _ => (b,i))
  · intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, rfl⟩
  · intro i _ j _ h
    exact congrArg Prod.snd h
  · intro j hj
    refine ⟨j.2, ?_, ?_⟩
    · have h := Finset.mem_filter.mp hj
      simp [schoolSampler_section, ← h.2, h.1]
    · exact Prod.ext (Finset.mem_filter.mp hj).2.symm rfl

noncomputable def schoolSampler_assemble {B : ℕ}
    (z : Fin B → {s : Finset (Fin 4) // s.card=2}) : Finset (Fin B × Fin 4) :=
  Finset.univ.filter (fun i => i.2∈(z i.1).val)

lemma schoolSampler_section_assemble {B : ℕ}
    (z : Fin B → {s : Finset (Fin 4) // s.card=2}) (b : Fin B) :
    schoolSampler_section (schoolSampler_assemble z) b = (z b).val := by
  classical
  ext i
  simp [schoolSampler_section, schoolSampler_assemble]

noncomputable def schoolSampler_equiv (B : ℕ) :
    {s // s∈blockedSchoolSupport B} ≃
      (Fin B → {s : Finset (Fin 4) // s.card=2}) where
  toFun s b := ⟨schoolSampler_section s.val b, by
    rw [schoolSampler_section_card]
    exact (Finset.mem_filter.mp s.property).2 b⟩
  invFun z := ⟨schoolSampler_assemble z, by
    classical
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
    intro b
    rw [← schoolSampler_section_card, schoolSampler_section_assemble]
    exact (z b).property⟩
  left_inv s := by
    classical
    apply Subtype.ext
    ext i
    simp [schoolSampler_assemble, schoolSampler_section]
  right_inv z := by
    funext b
    apply Subtype.ext
    exact schoolSampler_section_assemble z b

lemma schoolSampler_blocked_card (B : ℕ) :
    (blockedSchoolSupport B).card=6^B := by
  rw [← Fintype.card_coe, Fintype.card_congr (schoolSampler_equiv B)]
  simp [schoolSampler_subset_card, Nat.choose]

lemma schoolSampler_pair56 :
    uniformSchoolProbability 56 28 (fun s => (0 : Fin 56)∈s ∧ 1∈s)=27/110 := by
  classical
  calc
    _ = (((Finset.univ.powersetCard 28).filter
        (fun s : Finset (Fin 56) => {0,1} ⊆ s)).card:ℝ)/(Nat.choose 56 28:ℝ) := by
      unfold uniformSchoolProbability
      apply congrArg (fun s : Finset (Finset (Fin 56)) => (s.card:ℝ)/(Nat.choose 56 28:ℝ))
      ext s
      simp [unblockedSchoolSupport, Finset.insert_subset_iff]
    _ = _ := by
      rw [Finset.card_filter_powersetCard_subset]
      · norm_num only [Finset.card_univ, Fintype.card_fin, Finset.card_insert_of_notMem
          (by simp : (0 : Fin 56) ∉ ({1} : Finset (Fin 56))), Finset.card_singleton]
        have h54 : Nat.choose 54 26=1877405874732108 := by
          rw [Nat.choose_eq_factorial_div_factorial (by omega)]
          norm_num [Nat.factorial]
        rw [h54, school_support_count_arithmetic.2.1]
        norm_num
      · exact Finset.subset_univ _
      · norm_num

lemma schoolSampler_pair4 :
    uniformSchoolProbability 4 2 (fun s => (0 : Fin 4)∈s ∧ 1∈s)=1/6 := by
  classical
  calc
    _ = (((Finset.univ.powersetCard 2).filter
        (fun s : Finset (Fin 4) => {0,1} ⊆ s)).card:ℝ)/(Nat.choose 4 2:ℝ) := by
      unfold uniformSchoolProbability
      apply congrArg (fun s : Finset (Finset (Fin 4)) => (s.card:ℝ)/(Nat.choose 4 2:ℝ))
      ext s
      simp [unblockedSchoolSupport, Finset.insert_subset_iff]
    _ = _ := by
      rw [Finset.card_filter_powersetCard_subset]
      · norm_num [Nat.choose]
      · exact Finset.subset_univ _
      · norm_num

section SmallSupportCertificates
attribute [-instance] Classical.propDecidable

def schoolSampler_unblocked8_states : Finset (Finset (Fin 8)) :=
    {{0,1,2,3},
    {0,1,2,4},
    {0,1,2,5},
    {0,1,2,6},
    {0,1,2,7},
    {0,1,3,4},
    {0,1,3,5},
    {0,1,3,6},
    {0,1,3,7},
    {0,1,4,5},
    {0,1,4,6},
    {0,1,4,7},
    {0,1,5,6},
    {0,1,5,7},
    {0,1,6,7},
    {0,2,3,4},
    {0,2,3,5},
    {0,2,3,6},
    {0,2,3,7},
    {0,2,4,5},
    {0,2,4,6},
    {0,2,4,7},
    {0,2,5,6},
    {0,2,5,7},
    {0,2,6,7},
    {0,3,4,5},
    {0,3,4,6},
    {0,3,4,7},
    {0,3,5,6},
    {0,3,5,7},
    {0,3,6,7},
    {0,4,5,6},
    {0,4,5,7},
    {0,4,6,7},
    {0,5,6,7},
    {1,2,3,4},
    {1,2,3,5},
    {1,2,3,6},
    {1,2,3,7},
    {1,2,4,5},
    {1,2,4,6},
    {1,2,4,7},
    {1,2,5,6},
    {1,2,5,7},
    {1,2,6,7},
    {1,3,4,5},
    {1,3,4,6},
    {1,3,4,7},
    {1,3,5,6},
    {1,3,5,7},
    {1,3,6,7},
    {1,4,5,6},
    {1,4,5,7},
    {1,4,6,7},
    {1,5,6,7},
    {2,3,4,5},
    {2,3,4,6},
    {2,3,4,7},
    {2,3,5,6},
    {2,3,5,7},
    {2,3,6,7},
    {2,4,5,6},
    {2,4,5,7},
    {2,4,6,7},
    {2,5,6,7},
    {3,4,5,6},
    {3,4,5,7},
    {3,4,6,7},
    {3,5,6,7},
    {4,5,6,7}}

lemma schoolSampler_unblocked8_explicit :
    unblockedSchoolSupport 8 4 = schoolSampler_unblocked8_states := by
  apply Finset.ext
  intro s
  simp only [unblockedSchoolSupport, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  revert s
  decide

def schoolSampler_blocked2_states : Finset (Finset (Fin 2 × Fin 4)) :=
    {{(0,0),(0,1),(1,0),(1,1)},
    {(0,0),(0,1),(1,0),(1,2)},
    {(0,0),(0,1),(1,0),(1,3)},
    {(0,0),(0,1),(1,1),(1,2)},
    {(0,0),(0,1),(1,1),(1,3)},
    {(0,0),(0,1),(1,2),(1,3)},
    {(0,0),(0,2),(1,0),(1,1)},
    {(0,0),(0,2),(1,0),(1,2)},
    {(0,0),(0,2),(1,0),(1,3)},
    {(0,0),(0,2),(1,1),(1,2)},
    {(0,0),(0,2),(1,1),(1,3)},
    {(0,0),(0,2),(1,2),(1,3)},
    {(0,0),(0,3),(1,0),(1,1)},
    {(0,0),(0,3),(1,0),(1,2)},
    {(0,0),(0,3),(1,0),(1,3)},
    {(0,0),(0,3),(1,1),(1,2)},
    {(0,0),(0,3),(1,1),(1,3)},
    {(0,0),(0,3),(1,2),(1,3)},
    {(0,1),(0,2),(1,0),(1,1)},
    {(0,1),(0,2),(1,0),(1,2)},
    {(0,1),(0,2),(1,0),(1,3)},
    {(0,1),(0,2),(1,1),(1,2)},
    {(0,1),(0,2),(1,1),(1,3)},
    {(0,1),(0,2),(1,2),(1,3)},
    {(0,1),(0,3),(1,0),(1,1)},
    {(0,1),(0,3),(1,0),(1,2)},
    {(0,1),(0,3),(1,0),(1,3)},
    {(0,1),(0,3),(1,1),(1,2)},
    {(0,1),(0,3),(1,1),(1,3)},
    {(0,1),(0,3),(1,2),(1,3)},
    {(0,2),(0,3),(1,0),(1,1)},
    {(0,2),(0,3),(1,0),(1,2)},
    {(0,2),(0,3),(1,0),(1,3)},
    {(0,2),(0,3),(1,1),(1,2)},
    {(0,2),(0,3),(1,1),(1,3)},
    {(0,2),(0,3),(1,2),(1,3)}}

lemma schoolSampler_blocked2_explicit :
    blockedSchoolSupport 2 = schoolSampler_blocked2_states := by
  apply Finset.ext
  intro s
  simp only [blockedSchoolSupport, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]
  revert s
  decide

lemma schoolSampler_variances_rat :
    (let varianceU := fun y : Fin 8 → ℚ =>
      (∑ s ∈ schoolSampler_unblocked8_states,
        ((∑ i, (if i∈s then (1:ℚ) else -1)*y i)/4)^2)/70
     let varianceB := fun y : (Fin 2 × Fin 4) → ℚ =>
      (∑ s ∈ schoolSampler_blocked2_states,
        ((∑ i, (if i∈s then (1:ℚ) else -1)*y i)/4)^2)/36
     varianceU ![1,1,1,1,0,0,0,0]=1/7 ∧
     varianceB (fun i => if i.1=0 then 1 else 0)=0 ∧
     varianceU ![2,0,1,1,1,1,1,1]=1/7 ∧
     varianceB (fun i => if i=(0,0) then 2 else if i=(0,1) then 0 else 1)=1/6) := by
  decide +kernel

end SmallSupportCertificates
attribute [local instance] Classical.propDecidable

theorem school_sampler_counterexample_proof :
    (blockedSchoolSupport 14).card=78364164096 ∧
    (unblockedSchoolSupport 56 28).card=7648690600760440 ∧
    (unblockedSchoolSupport 8 4).card=70 ∧ (blockedSchoolSupport 2).card=36 ∧
    ({0,1,2,3} : Finset (Fin 8))∈unblockedSchoolSupport 8 4 ∧
    ({(0,0),(0,1),(0,2),(0,3)} : Finset (Fin 2 × Fin 4))∉blockedSchoolSupport 2 ∧
    uniformSchoolProbability 56 28 (fun s => (0 : Fin 56)∈s ∧ 1∈s)=27/110 ∧
    uniformSchoolProbability 4 2 (fun s => (0 : Fin 4)∈s ∧ 1∈s)=1/6 ∧
    (let varianceU := fun y : Fin 8 → ℝ =>
      (∑ s ∈ unblockedSchoolSupport 8 4,
        ((∑ i, (if i∈s then (1:ℝ) else -1)*y i)/4)^2)/70
     let varianceB := fun y : (Fin 2 × Fin 4) → ℝ =>
      (∑ s ∈ blockedSchoolSupport 2,
        ((∑ i, (if i∈s then (1:ℝ) else -1)*y i)/4)^2)/36
     varianceU ![1,1,1,1,0,0,0,0]=1/7 ∧
     varianceB (fun i => if i.1=0 then 1 else 0)=0 ∧
     varianceU ![2,0,1,1,1,1,1,1]=1/7 ∧
     varianceB (fun i => if i=(0,0) then 2 else if i=(0,1) then 0 else 1)=1/6) := by
  classical
  have hu : (Finset.univ : Finset (Fin 8))={0,1,2,3,4,5,6,7} := by
    ext i; fin_cases i <;> simp
  have hb : (Finset.univ : Finset (Fin 2 × Fin 4))=
      {(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)} := by
    ext ⟨b,i⟩; fin_cases b <;> fin_cases i <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, schoolSampler_pair56, schoolSampler_pair4, ?_⟩
  · rw [schoolSampler_blocked_card]
    exact school_support_count_arithmetic.1
  · simpa [unblockedSchoolSupport] using school_support_count_arithmetic.2.1
  · norm_num [unblockedSchoolSupport, Nat.choose]
  · rw [schoolSampler_blocked_card]
    norm_num
  · simp [unblockedSchoolSupport]
  · intro h
    have h0 := (Finset.mem_filter.mp h).2 (0 : Fin 2)
    norm_num [Finset.filter_insert, Finset.filter_singleton] at h0
  · dsimp only
    simp only [schoolSampler_unblocked8_explicit, schoolSampler_blocked2_explicit]
    have h := schoolSampler_variances_rat
    dsimp only at h
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hc := congrArg (fun q : ℚ => (q:ℝ)) h.1
      norm_num [Rat.cast_sum, Fin.sum_univ_succ, Fintype.sum_prod_type,
        apply_ite (fun q : ℚ => (q:ℝ))] at hc ⊢ <;> exact hc
    · have hc := congrArg (fun q : ℚ => (q:ℝ)) h.2.1
      norm_num [Rat.cast_sum, Fin.sum_univ_succ, Fintype.sum_prod_type,
        apply_ite (fun q : ℚ => (q:ℝ))] at hc ⊢ <;> exact hc
    · have hc := congrArg (fun q : ℚ => (q:ℝ)) h.2.2.1
      norm_num [Rat.cast_sum, Fin.sum_univ_succ, Fintype.sum_prod_type,
        apply_ite (fun q : ℚ => (q:ℝ))] at hc ⊢ <;> exact hc
    · have hc := congrArg (fun q : ℚ => (q:ℝ)) h.2.2.2
      norm_num [Rat.cast_sum, Fin.sum_univ_succ, Fintype.sum_prod_type,
        apply_ite (fun q : ℚ => (q:ℝ))] at hc ⊢ <;> exact hc


lemma schoolVariance_signed_mean {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (htotal : ∑ z, p z=1)
    (S : Ω → Bool) (half : (∑ z, p z*(if S z then 1 else 0))=1/2) :
    (∑ z, p z*(if S z then (1:ℝ) else -1))=0 := by
  have he : ∀ z, p z*(if S z then (1:ℝ) else -1) =
      2*(p z*(if S z then 1 else 0))-p z := by
    intro z
    cases S z <;> simp <;> ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, half, htotal]
  norm_num

lemma schoolVariance_signed_pair {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : Ω → ℝ) (htotal : ∑ z, p z=1)
    (S : Ω → Fin n → Bool) (half : ∀ i, (∑ z, p z*(if S z i then 1 else 0))=1/2)
    (i j : Fin n) :
    (∑ z, p z*((if S z i then (1:ℝ) else -1)*(if S z j then (1:ℝ) else -1)))=
      (if i=j then 1 else 4*(∑ z, p z*(if S z i=true ∧ S z j=true then 1 else 0))-1) := by
  by_cases hij : i=j
  · subst j
    simp only [ite_true, eq_self]
    convert htotal using 1
    apply Finset.sum_congr rfl
    intro z _
    cases S z i <;> simp
  · rw [if_neg hij]
    have he : ∀ z,
        p z*((if S z i then (1:ℝ) else -1)*(if S z j then (1:ℝ) else -1)) =
        4*(p z*(if S z i=true ∧ S z j=true then 1 else 0))-
          2*(p z*(if S z i then 1 else 0))-
          2*(p z*(if S z j then 1 else 0))+p z := by
      intro z
      cases S z i <;> cases S z j <;> simp <;> ring
    simp_rw [he]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum, half, htotal]
    ring

theorem school_statistic_variance_proof {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : Ω → ℝ) (hp : ∀ z, 0≤p z) (htotal : ∑ z, p z=1)
    (S : Ω → Fin n → Bool) (half : ∀ i, (∑ z, p z*(if S z i then 1 else 0))=1/2)
    (y : Fin n → ℝ) (m : ℕ) (hm : 0<m) :
    let T := fun z => (∑ i, ((if S z i then (1:ℝ) else -1)*y i))/(m:ℝ)
    (∑ z, p z*T z)=0 ∧
    (∑ z, p z*(T z)^2)=
      (∑ i, ∑ j, y i*y j*(if i=j then 1 else
        4*(∑ z, p z*(if S z i=true ∧ S z j=true then 1 else 0))-1))/(m:ℝ)^2 := by
  dsimp only
  constructor
  · simp_rw [← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
    rw [Finset.sum_comm]
    have he : ∀ i, (∑ z, p z*((if S z i then (1:ℝ) else -1)*y i))=0 := by
      intro i
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul, schoolVariance_signed_mean p htotal (fun z => S z i) (half i)]
      ring
    simp_rw [he]
    simp
  · simp_rw [div_pow, ← mul_div_assoc, ← Finset.sum_div]
    congr 1
    calc
      _ = ∑ z, ∑ i, ∑ j,
          y i*y j*(p z*((if S z i then (1:ℝ) else -1)*(if S z j then (1:ℝ) else -1))) := by
        apply Finset.sum_congr rfl
        intro z _
        simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = ∑ i, ∑ j, y i*y j*(∑ z,
          p z*((if S z i then (1:ℝ) else -1)*(if S z j then (1:ℝ) else -1))) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum]
      _ = _ := by simp_rw [schoolVariance_signed_pair p htotal S half]

end AronowAudit.P037.Wave1
