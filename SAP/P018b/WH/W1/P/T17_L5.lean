import SAP.P018b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018b.WH.W1.P.T17_L5

open Finset Matrix
open scoped BigOperators Matrix.Norms.Elementwise

lemma endpoints_lt {N : ℕ} (d : SAP.P018b.Dyad N) :
    SAP.P018b.firstUnit d < SAP.P018b.secondUnit d := by
  exact Finset.min'_lt_max'_of_card (SAP.P018b.members d)
    (by rw [SAP.P018b.members_card]; omega)

lemma members_endpoints {N : ℕ} (d : SAP.P018b.Dyad N) :
    SAP.P018b.members d = {SAP.P018b.firstUnit d, SAP.P018b.secondUnit d} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact Finset.min'_mem _ _
    · exact Finset.max'_mem _ _
  · rw [SAP.P018b.members_card]
    simp [ne_of_lt (endpoints_lt d)]

def mkDyad {N : ℕ} (i j : Fin N) (hij : i ≠ j) : SAP.P018b.Dyad N :=
  ⟨{i, j}, by simp [SAP.P018b.dyads, Finset.mem_powersetCard, hij]⟩

lemma mkDyad_endpoints {N : ℕ} (i j : Fin N) (hij : i < j) :
    SAP.P018b.firstUnit (mkDyad i j hij.ne) = i ∧
    SAP.P018b.secondUnit (mkDyad i j hij.ne) = j := by
  simp [SAP.P018b.firstUnit, SAP.P018b.secondUnit, SAP.P018b.members,
    mkDyad, Finset.min'_pair, Finset.max'_pair,
    min_eq_left hij.le, max_eq_right hij.le]

lemma upper_sum {N : ℕ} (F : Fin N → Fin N → ℝ) :
    (∑ d : SAP.P018b.Dyad N,
      F (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) =
      ∑ i : Fin N, ∑ j : Fin N, if i < j then F i j else 0 := by
  classical
  let P := (univ ×ˢ univ : Finset (Fin N × Fin N)).filter (fun p => p.1 < p.2)
  have h : (∑ d : SAP.P018b.Dyad N,
      F (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) =
      ∑ p ∈ P, F p.1 p.2 := by
    apply Finset.sum_bij (fun d _ => (SAP.P018b.firstUnit d, SAP.P018b.secondUnit d))
    · intro d hd
      simp [P, endpoints_lt]
    · intro d hd e he hde
      apply Subtype.ext
      change SAP.P018b.members d = SAP.P018b.members e
      rw [members_endpoints d, members_endpoints e]
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

def point (i : Fin 20) : ℝ :=
  if i.val = 0 then 1 else if i.val = 1 then 2 else if i.val = 2 then 3 else
  if i.val = 3 then 4 else 5 / 2

def z (i j : Fin 20) : ℝ := |point i - point j|

def p (i j : Fin 20) : ℝ :=
  if i.val = 0 ∧ j.val = 1 then 1 else
  if i.val = 0 ∧ j.val = 2 then -1 else
  if i.val = 1 ∧ j.val = 3 then -1 else
  if i.val = 2 ∧ j.val = 3 then 1 else 0

def residualPair (i j : Fin 20) : ℝ := p i j - 37 / 3381 + 95 / 3381 * z i j

def influence (i j : Fin 20) : ℝ := residualPair i j * (95 * z i j - 37) / 6762

lemma padded_eq (d : SAP.P018b.Dyad 20) :
    SAP.P018b.wholePaddedY d =
      p (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) := by
  rfl

lemma simX_eq (i : Fin 20) :
    SAP.P018b.simulationX SAP.P018b.wholeTwentyPoint i = point i := by
  simp [SAP.P018b.simulationX, SAP.P018b.wholeTwentyPoint, point]

lemma design_entries (d : SAP.P018b.Dyad 20) :
    SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint d =
      ![1, z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)] := by
  simp [SAP.P018b.wholeSimulationDesign, z, point, SAP.P018b.simulationX,
    SAP.P018b.wholeTwentyPoint]

lemma response_entries (d : SAP.P018b.Dyad 20) :
    SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint d =
      z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) +
        p (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) := by
  rw [SAP.P018b.wholeSimulationResponse, simX_eq, simX_eq]
  simp [SAP.P018b.simulationError, z, point, SAP.P018b.wholeTwentyPoint, padded_eq]

lemma z_sum : (∑ d : SAP.P018b.Dyad 20,
    z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) = 74 := by
  rw [upper_sum]
  norm_num [z, point, Fin.sum_univ_succ]

lemma z_sq_sum : (∑ d : SAP.P018b.Dyad 20,
    (z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) ^ 2) = 100 := by
  rw [upper_sum (fun i j => (z i j)^2)]
  norm_num [z, point, Fin.sum_univ_succ]

lemma p_sum : (∑ d : SAP.P018b.Dyad 20,
    p (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) = 0 := by
  rw [upper_sum]
  norm_num [p, Fin.sum_univ_succ]

lemma zp_sum : (∑ d : SAP.P018b.Dyad 20,
    z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) *
      p (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) = -2 := by
  rw [upper_sum (fun i j => z i j * p i j)]
  norm_num [z, p, point, Fin.sum_univ_succ]

lemma dyad_count : (∑ d : SAP.P018b.Dyad 20, (1 : ℝ)) = 190 := by
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_univ,
    Fintype.card_coe]
  norm_num [SAP.P018b.dyads, Finset.card_powersetCard, Nat.choose_two_right]

lemma gram_eq :
    SAP.P018b.sampleGram (SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint) =
      !![(190 : ℝ), 74; 74, 100] := by
  ext i j
  fin_cases i <;> fin_cases j
  · simp only [SAP.P018b.sampleGram, Matrix.sum_apply, SAP.P018b.outer,
      design_entries, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.reduceFinMk]
    simpa using dyad_count
  · simp only [SAP.P018b.sampleGram, Matrix.sum_apply, SAP.P018b.outer,
      design_entries, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.reduceFinMk]
    simpa using z_sum
  · simp only [SAP.P018b.sampleGram, Matrix.sum_apply, SAP.P018b.outer,
      design_entries, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.reduceFinMk]
    simpa [mul_comm] using z_sum
  · simp only [SAP.P018b.sampleGram, Matrix.sum_apply, SAP.P018b.outer,
      design_entries, Matrix.cons_val_zero', Matrix.cons_val_succ',
      Matrix.cons_val_fin_one, Matrix.of_apply, Fin.reduceFinMk]
    simpa [pow_two] using z_sq_sum

lemma response_sums :
    (∑ d : SAP.P018b.Dyad 20,
      SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint d) = 74 ∧
    (∑ d : SAP.P018b.Dyad 20,
      (z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) *
        SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint d) = 98 := by
  constructor
  · simp_rw [response_entries]
    rw [Finset.sum_add_distrib, z_sum, p_sum]
    norm_num
  · simp_rw [response_entries]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hzz : (∑ d : SAP.P018b.Dyad 20,
        z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) *
          z (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d)) = 100 := by
      simpa [pow_two] using z_sq_sum
    rw [hzz, zp_sum]
    norm_num

lemma score_sum :
    (∑ d : SAP.P018b.Dyad 20,
      SAP.P018b.score
        (SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint d)
        (SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint d)) = ![74, 98] := by
  ext i
  fin_cases i
  · have h := response_sums.1
    simpa [SAP.P018b.score, design_entries, mul_comm] using h
  · have h := response_sums.2
    simpa [SAP.P018b.score, design_entries, mul_comm] using h

lemma inverse_eq :
    (SAP.P018b.sampleGram
      (SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint))⁻¹ =
      !![(100 / 13524 : ℝ), -74 / 13524; -74 / 13524, 190 / 13524] := by
  rw [gram_eq]
  let G : SAP.P018b.Mat 2 := !![(190 : ℝ), 74; 74, 100]
  let B : SAP.P018b.Mat 2 := !![100 / 13524, -74 / 13524; -74 / 13524, 190 / 13524]
  have hB : B * G = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [B, G, Matrix.mul_apply, Fin.sum_univ_succ]
  have hi : G⁻¹ = B := Matrix.inv_eq_left_inv hB
  simpa [G, B] using hi

lemma ols_eq : SAP.P018b.sampleOLS
    (SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint)
    (SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint) = ![37 / 3381, 3286 / 3381] := by
  rw [SAP.P018b.sampleOLS, inverse_eq, score_sum]
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_succ]

lemma residual_eq (d : SAP.P018b.Dyad 20) :
    SAP.P018b.fittedResidual
      (SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint)
      (SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint) d =
      residualPair (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) := by
  rw [SAP.P018b.fittedResidual, ols_eq, design_entries, response_entries]
  simp [SAP.P018b.dot, residualPair, z, p]
  ring

def bread : SAP.P018b.Mat 2 :=
  !![(100 / 13524 : ℝ), -74 / 13524; -74 / 13524, 190 / 13524]

def b10 : ℝ := bread (1 : Fin 2) (0 : Fin 2)
def b11 : ℝ := bread (1 : Fin 2) (1 : Fin 2)

lemma bread_symm : bread.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [bread]

def q (d : SAP.P018b.Dyad 20) : SAP.P018b.Vec 2 :=
  SAP.P018b.score (SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint d)
    (SAP.P018b.fittedResidual
      (SAP.P018b.wholeSimulationDesign SAP.P018b.wholeTwentyPoint)
      (SAP.P018b.wholeSimulationResponse SAP.P018b.wholeTwentyPoint) d)

lemma influence_eq (d : SAP.P018b.Dyad 20) :
    b10 * q d 0 + b11 * q d 1 =
      influence (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) := by
  rw [q, SAP.P018b.score, residual_eq, design_entries]
  simp [bread, b10, b11, influence, residualPair, z]
  norm_num <;> ring_nf

def nodeScore (i : Fin 20) : ℝ :=
  ∑ d : SAP.P018b.Dyad 20,
    if i ∈ SAP.P018b.members d then
      influence (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) else 0

lemma nodeScore_pair (i : Fin 20) : nodeScore i =
    ∑ a : Fin 20, ∑ b : Fin 20,
      if a < b ∧ (i = a ∨ i = b) then influence a b else 0 := by
  rw [nodeScore]
  have hm (d : SAP.P018b.Dyad 20) :
      (if i ∈ SAP.P018b.members d then
        influence (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) else 0) =
      (if i ∈ ({SAP.P018b.firstUnit d, SAP.P018b.secondUnit d} : Finset (Fin 20)) then
        influence (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d) else 0) := by
    rw [members_endpoints]
  simp_rw [hm]
  rw [upper_sum (fun a b =>
    if i ∈ ({a, b} : Finset (Fin 20)) then influence a b else 0)]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  by_cases hab : a < b <;> simp [hab, and_comm]

lemma node_sum_sq : (∑ i : Fin 20, (nodeScore i)^2) =
    2416685620 / 6222449609901 := by
  simp_rw [nodeScore_pair]
  norm_num [influence, residualPair, z, p, point, Fin.sum_univ_succ]

lemma dyad_sum_sq :
    (∑ d : SAP.P018b.Dyad 20,
      (influence (SAP.P018b.firstUnit d) (SAP.P018b.secondUnit d))^2) =
      2084770201 / 1893789011709 := by
  rw [upper_sum (fun i j => (influence i j)^2)]
  norm_num [influence, residualPair, z, p, point, Fin.sum_univ_succ]

lemma nodeScore_eq_unit (i : Fin 20) :
    b10 * SAP.P018b.unitScore SAP.P018b.members q i 0 +
      b11 * SAP.P018b.unitScore SAP.P018b.members q i 1 = nodeScore i := by
  simp only [nodeScore, SAP.P018b.unitScore, Finset.sum_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hi : i ∈ SAP.P018b.members d
  · simp [hi, influence_eq]
  · simp [hi]

lemma intersection_count (d f : SAP.P018b.Dyad 20) :
    ((SAP.P018b.members d ∩ SAP.P018b.members f).card : ℝ) =
      (if (SAP.P018b.members d ∩ SAP.P018b.members f).Nonempty then 1 else 0) +
        (if d = f then 1 else 0) := by
  classical
  by_cases hdf : d = f
  · subst f
    have hi : SAP.P018b.firstUnit d ∈ SAP.P018b.members d := Finset.min'_mem _ _
    have hne : (SAP.P018b.members d ∩ SAP.P018b.members d).Nonempty := by
      exact ⟨SAP.P018b.firstUnit d, Finset.mem_inter.mpr ⟨hi, hi⟩⟩
    rw [Finset.inter_self] at hne ⊢
    norm_num [SAP.P018b.members_card, hne]
  · have hc : (SAP.P018b.members d ∩ SAP.P018b.members f).card ≤ 2 := by
      calc
        _ ≤ (SAP.P018b.members d).card := Finset.card_le_card inter_subset_left
        _ = 2 := SAP.P018b.members_card d
    have hn : (SAP.P018b.members d ∩ SAP.P018b.members f).card ≠ 2 := by
      intro h
      have h1 : SAP.P018b.members d ∩ SAP.P018b.members f = SAP.P018b.members d :=
        Finset.eq_of_subset_of_card_le inter_subset_left (by rw [SAP.P018b.members_card, h])
      have h2 : SAP.P018b.members d ∩ SAP.P018b.members f = SAP.P018b.members f :=
        Finset.eq_of_subset_of_card_le inter_subset_right
          (by rw [SAP.P018b.members_card, h])
      exact hdf (Subtype.ext (h1.symm.trans h2))
    by_cases he : (SAP.P018b.members d ∩ SAP.P018b.members f).Nonempty
    · have hcard : (SAP.P018b.members d ∩ SAP.P018b.members f).card = 1 := by
        have hp := Finset.card_pos.mpr he
        omega
      simp [he, hdf, hcard]
    · simp [he, hdf, Finset.not_nonempty_iff_eq_empty.mp he]

lemma overlap_identity (q : SAP.P018b.Dyad 20 → SAP.P018b.Vec 2) :
    SAP.P018b.meat SAP.P018b.members q =
      (∑ i : Fin 20, SAP.P018b.outer
        (SAP.P018b.unitScore SAP.P018b.members q i)
        (SAP.P018b.unitScore SAP.P018b.members q i)) - SAP.P018b.dyadMeat q := by
  classical
  ext a b
  simp only [SAP.P018b.meat, SAP.P018b.unitScore, SAP.P018b.outer,
    Matrix.of_apply, SAP.P018b.dyadMeat, Matrix.sub_apply, Pi.sub_apply,
    Matrix.sum_apply, Finset.sum_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  have hswap : (∑ i : Fin 20, ∑ d : SAP.P018b.Dyad 20, ∑ f : SAP.P018b.Dyad 20,
      (if i ∈ SAP.P018b.members d then q d else 0) a *
        (if i ∈ SAP.P018b.members f then q f else 0) b) =
      ∑ d : SAP.P018b.Dyad 20, ∑ f : SAP.P018b.Dyad 20, ∑ i : Fin 20,
        (if i ∈ SAP.P018b.members d then q d else 0) a *
          (if i ∈ SAP.P018b.members f then q f else 0) b := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_comm]
  rw [hswap]
  have hterm (d f : SAP.P018b.Dyad 20) :
      (∑ i : Fin 20,
        (if i ∈ SAP.P018b.members d then q d else 0) a *
          (if i ∈ SAP.P018b.members f then q f else 0) b) =
        (if (SAP.P018b.members d ∩ SAP.P018b.members f).Nonempty then
          q d a * q f b else 0) + (if d = f then q d a * q f b else 0) := by
    have ht : (∑ i : Fin 20,
        (if i ∈ SAP.P018b.members d then q d else 0) a *
          (if i ∈ SAP.P018b.members f then q f else 0) b) =
        ((SAP.P018b.members d ∩ SAP.P018b.members f).card : ℝ) * (q d a * q f b) := by
      simp_rw [ite_apply, Pi.zero_apply]
      simp only [ite_mul, zero_mul, mul_ite, mul_zero]
      simp_rw [← ite_and]
      simp [← Finset.mem_inter, ← Finset.sum_filter, Finset.inter_comm]
    rw [ht, intersection_count d f, add_mul]
    split_ifs <;> ring
  simp_rw [hterm, Finset.sum_add_distrib]
  simp only [AronowAudit.P018.matrix_ite_apply, Matrix.zero_apply, SAP.P018b.outer,
    Matrix.of_apply, Finset.sum_ite_eq, mem_univ, if_true]
  ring

lemma slope_overlap (P : SAP.P018b.Mat 2) (hP : P.IsSymm)
    (q : SAP.P018b.Dyad 20 → SAP.P018b.Vec 2) :
    SAP.P018b.sandwich P (SAP.P018b.meat SAP.P018b.members q) 1 1 =
      (∑ i : Fin 20,
        (P 1 0 * SAP.P018b.unitScore SAP.P018b.members q i 0 +
          P 1 1 * SAP.P018b.unitScore SAP.P018b.members q i 1)^2) -
      ∑ d : SAP.P018b.Dyad 20,
        (P 1 0 * q d 0 + P 1 1 * q d 1)^2 := by
  have ho (v : SAP.P018b.Vec 2) :
      (P * SAP.P018b.outer v v * P) 1 1 =
        (P 1 0 * v 0 + P 1 1 * v 1)^2 := by
    simp only [Matrix.mul_apply, Fin.sum_univ_two, SAP.P018b.outer, Matrix.of_apply]
    rw [← hP.apply 0 1]
    ring
  rw [overlap_identity q]
  simp only [SAP.P018b.sandwich, SAP.P018b.dyadMeat, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.sub_apply,
    Matrix.sum_apply, ho]

end SAP.P018b.WH.W1.P.T17_L5

theorem SAP.P018b.WH.W1.T17_L5_proof : SAP.P018b.WH.W1.T17_L5 := by
  change SAP.P018b.wholeSimulationSlope SAP.P018b.wholeTwentyPoint =
    -31032915283 / 43557147269307
  rw [SAP.P018b.wholeSimulationSlope, SAP.P018b.sampleVariance,
    SAP.P018b.WH.W1.P.T17_L5.inverse_eq]
  change SAP.P018b.sandwich SAP.P018b.WH.W1.P.T17_L5.bread
      (SAP.P018b.meat SAP.P018b.members SAP.P018b.WH.W1.P.T17_L5.q) 1 1 =
    -31032915283 / 43557147269307
  rw [SAP.P018b.WH.W1.P.T17_L5.slope_overlap
    SAP.P018b.WH.W1.P.T17_L5.bread SAP.P018b.WH.W1.P.T17_L5.bread_symm
    SAP.P018b.WH.W1.P.T17_L5.q]
  have h10 : SAP.P018b.WH.W1.P.T17_L5.bread (1 : Fin 2) (0 : Fin 2) =
      SAP.P018b.WH.W1.P.T17_L5.b10 := by
    rfl
  have h11 : SAP.P018b.WH.W1.P.T17_L5.bread (1 : Fin 2) (1 : Fin 2) =
      SAP.P018b.WH.W1.P.T17_L5.b11 := by
    rfl
  simp_rw [h10, h11, SAP.P018b.WH.W1.P.T17_L5.nodeScore_eq_unit,
    SAP.P018b.WH.W1.P.T17_L5.influence_eq]
  rw [SAP.P018b.WH.W1.P.T17_L5.node_sum_sq,
    SAP.P018b.WH.W1.P.T17_L5.dyad_sum_sq]
  norm_num
