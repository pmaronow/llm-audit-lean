import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace SAP.P019a.WH.W1.P.T3_L2

open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section
open Classical

private def label (ω : Fin 16) : Fin 3 :=
  if finiteSampleWitness.Y ω then 2 else if finiteSampleWitness.Z ω then 0 else 1

private def countLabel (l : Fin 4 → Fin 3) (z : Fin 3) : ℕ :=
  ∑ i, if l i = z then 1 else 0

private def occupiedLabels (l : Fin 4 → Fin 3) : Prop :=
  0 < countLabel l 0 ∧ 0 < countLabel l 1

private def labelA (l : Fin 4 → Fin 3) : ℝ :=
  1 - (countLabel l 2 : ℝ) / 4

private def labelProb (z : Fin 3) : ℝ := if z = 2 then 1/4 else 3/8

private theorem mean_sum_local {Ω : Type*} [Fintype Ω] (P : SAP.P019a.FiniteLaw Ω)
    {ι : Type*} [Fintype ι] (f : ι → Ω → ℝ) :
    P.mean (fun ω => ∑ i, f i ω) = ∑ i, P.mean (f i) := by
  simp only [SAP.P019a.FiniteLaw.mean, Finset.mul_sum]
  rw [Finset.sum_comm]

private theorem mean_const_mul_local {Ω : Type*} [Fintype Ω] (P : SAP.P019a.FiniteLaw Ω)
    (c : ℝ) (f : Ω → ℝ) : P.mean (fun ω => c * f ω) = c * P.mean f := by
  unfold SAP.P019a.FiniteLaw.mean
  calc
    (∑ ω, P.mass ω * (c * f ω)) = ∑ ω, c * (P.mass ω * f ω) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = c * ∑ ω, P.mass ω * f ω := by rw [Finset.mul_sum]

private theorem iid_mean_prod_local {Ω : Type*} [Fintype Ω] (P : SAP.P019a.FiniteLaw Ω)
    (f : Fin 4 → Ω → ℝ) :
    (P.iid 4).mean (fun s => ∏ i, f i (s i)) = ∏ i, P.mean (f i) := by
  unfold SAP.P019a.FiniteLaw.mean SAP.P019a.FiniteLaw.iid
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i ω => P.mass ω * f i ω)).symm

private theorem label_prob (z : Fin 3) : finiteSampleWitness.law.prob
    (fun ω => label ω = z) = labelProb z := by
  fin_cases z <;>
    norm_num [label, labelProb, finiteSampleWitness, uniformFin, fairBit,
      FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]

private theorem sum_cons {α : Type*} [Fintype α] (n : ℕ)
    (f : (Fin (n+1) → α) → ℝ) :
    (∑ s, f s) = ∑ a, ∑ t : Fin n → α, f (Fin.cons a t) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
    ((Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp f).symm

private theorem label_table :
    (∑ l : Fin 4 → Fin 3, (∏ i, labelProb (l i)) *
      if occupiedLabels l then (1 : ℝ) else 0) = 1431/2048 ∧
    (∑ l : Fin 4 → Fin 3, (∏ i, labelProb (l i)) *
      if occupiedLabels l then labelA l else 0) = 1161/2048 ∧
    (∑ l : Fin 4 → Fin 3, (∏ i, labelProb (l i)) *
      if occupiedLabels l then (labelA l)^2 else 0) = 1971/4096 := by
  simp only [sum_cons, Fintype.sum_unique]
  simp (config := {maxSteps := 1000000}) only
    [occupiedLabels, labelA, countLabel, labelProb,
      Fin.sum_univ_succ, Fin.prod_univ_succ]
  norm_num [Fin.cons]

private theorem label_statistics (s : Fin 4 → Fin 16) :
    (finiteSampleWitness.occupied s ↔ occupiedLabels (fun i => label (s i))) ∧
    finiteSampleWitness.sampleA s = labelA (fun i => label (s i)) := by
  have hcell (i : Fin 4) :
      (finiteSampleWitness.cell true false (s i) ↔ label (s i) = 0) ∧
      (finiteSampleWitness.cell false false (s i) ↔ label (s i) = 1) := by
    dsimp [label, Study.cell]
    by_cases hy : finiteSampleWitness.Y (s i) = true <;>
      by_cases hz : finiteSampleWitness.Z (s i) = true <;> simp [hy, hz]
  have hc1 : finiteSampleWitness.cellCount s true false =
      countLabel (fun i => label (s i)) 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [(hcell i).1]
  have hc0 : finiteSampleWitness.cellCount s false false =
      countLabel (fun i => label (s i)) 1 := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [(hcell i).2]
  constructor
  · simp only [Study.occupied, occupiedLabels, hc1, hc0]
  · unfold Study.sampleA Study.ybar labelA countLabel
    congr 2
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [label, bitVal]
    by_cases hy : finiteSampleWitness.Y (s i) = true <;>
      by_cases hz : finiteSampleWitness.Z (s i) = true <;> simp [hy, hz]

private theorem iid_label_push (F : (Fin 4 → Fin 3) → ℝ) :
    (finiteSampleWitness.law.iid 4).mean
      (fun s => F (fun i => label (s i))) =
      ∑ l : Fin 4 → Fin 3, (∏ i, labelProb (l i)) * F l := by
  have he : (fun s : Fin 4 → Fin 16 => F (fun i => label (s i))) =
      (fun s => ∑ l : Fin 4 → Fin 3,
        F l * ∏ i, if label (s i) = l i then (1 : ℝ) else 0) := by
    funext s
    symm
    rw [Finset.sum_eq_single (fun i => label (s i))]
    · simp
    · intro l _ hl
      have hx : ∃ i, label (s i) ≠ l i := by
        by_contra hn
        apply hl
        funext i
        exact (not_ne_iff.mp (not_exists.mp hn i)).symm
      obtain ⟨i, hi⟩ := hx
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
    · simp
  rw [he, mean_sum_local]
  apply Finset.sum_congr rfl
  intro l _
  rw [mean_const_mul_local]
  have hprod := iid_mean_prod_local finiteSampleWitness.law
    (fun i ω => if label ω = l i then (1 : ℝ) else 0)
  rw [hprod]
  have hm (z : Fin 3) : finiteSampleWitness.law.mean
      (fun ω => if label ω = z then (1 : ℝ) else 0) = labelProb z := by
    simpa [SAP.P019a.FiniteLaw.prob, labelProb] using label_prob z
  simp_rw [hm]
  ring

theorem label_numeric_moments :
    let S := finiteSampleWitness
    let P := S.law.iid 4
    let A := @Study.sampleA (Fin 16) _ S 4
    P.prob S.occupied = 1431/2048 ∧
    P.ce A S.occupied = 43/53 ∧
    P.ce (fun s => (A s)^2) S.occupied = 73/106 := by
  dsimp only
  let S := finiteSampleWitness
  let P := S.law.iid 4
  let A := @Study.sampleA (Fin 16) _ S 4
  have hpush := iid_label_push
  have hD : P.prob S.occupied = 1431/2048 := by
    unfold FiniteLaw.prob
    have he : (fun s : Fin 4 → Fin 16 => if S.occupied s then (1 : ℝ) else 0) =
        (fun s => if occupiedLabels (fun i => label (s i)) then 1 else 0) := by
      funext s
      simp only [S, (label_statistics s).1]
    rw [he, hpush (fun l => if occupiedLabels l then 1 else 0), label_table.1]
  refine ⟨hD, ?_, ?_⟩
  · unfold FiniteLaw.ce
    rw [hD]
    have he : (fun s : Fin 4 → Fin 16 =>
        if S.occupied s then A s else 0) =
        (fun s => if occupiedLabels (fun i => label (s i)) then
          labelA (fun i => label (s i)) else 0) := by
      funext s
      simp only [S, A, (label_statistics s).1, (label_statistics s).2]
    rw [he, hpush (fun l => if occupiedLabels l then labelA l else 0), label_table.2.1]
    norm_num
  · unfold FiniteLaw.ce
    rw [hD]
    have he : (fun s : Fin 4 → Fin 16 =>
        if S.occupied s then (A s)^2 else 0) =
        (fun s => if occupiedLabels (fun i => label (s i)) then
          (labelA (fun i => label (s i)))^2 else 0) := by
      funext s
      simp only [S, A, (label_statistics s).1, (label_statistics s).2]
    rw [he, hpush (fun l => if occupiedLabels l then (labelA l)^2 else 0), label_table.2.2]
    norm_num

private theorem atom_le {Ω : Type*} [Fintype Ω] (P : AronowAudit.P019.FiniteLaw Ω)
    (D : Ω → Prop) [DecidablePred D] (s : Ω) (hs : D s) : P.mass s ≤ P.prob D := by
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset Ω))
    (f := fun t => P.mass t * if D t then (1 : ℝ) else 0)
    (fun t _ => mul_nonneg (P.nonneg t) (by split_ifs <;> norm_num))
    (Finset.mem_univ s)
  simpa only [AronowAudit.P019.FiniteLaw.prob, AronowAudit.P019.FiniteLaw.mean,
    if_pos hs, mul_one] using h

private theorem null_mean {Ω : Type*} [Fintype Ω] (P : AronowAudit.P019.FiniteLaw Ω)
    (D : Ω → Prop) [DecidablePred D]
    (hD : P.prob D = 0) (f : Ω → ℝ) :
    P.mean (fun s => if D s then f s else 0) = 0 := by
  unfold AronowAudit.P019.FiniteLaw.mean
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : D s
  · have hmass : P.mass s = 0 := by
      have h := atom_le P D s hs
      rw [hD] at h
      exact le_antisymm h (P.nonneg s)
    simp [hs, hmass]
  · simp [hs]

private theorem partition_mean {Ω : Type*} [Fintype Ω]
    (P : AronowAudit.P019.FiniteLaw Ω)
    {Λ : Type*} [Fintype Λ] (L : Ω → Λ) (f : Ω → ℝ) :
    P.mean f = ∑ l, P.mean (fun s => if L s = l then f s else 0) := by
  rw [← AronowAudit.P019.mean_sum]
  congr 1
  funext s
  simp

private theorem transfer {Ω : Type*} [Fintype Ω] (P : AronowAudit.P019.FiniteLaw Ω)
    {Λ : Type*} [Fintype Λ] (L : Ω → Λ)
    (D : Ω → Prop) [DecidablePred D] (f g : Ω → ℝ)
    (hD : ∀ s t, L t = L s → (D t ↔ D s))
    (hfg : ∀ s, D s → P.prob (fun t => L t = L s) ≠ 0 →
      P.ce f (fun t => L t = L s) = P.ce g (fun t => L t = L s)) :
    P.ce f D = P.ce g D := by
  unfold AronowAudit.P019.FiniteLaw.ce
  congr 1
  rw [partition_mean P L (fun s => if D s then f s else 0),
    partition_mean P L (fun s => if D s then g s else 0)]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hex : ∃ s, L s = l ∧ D s
  · obtain ⟨s, hsl, hds⟩ := hex
    have hf (u : Ω → ℝ) :
        (fun t => if L t = l then (if D t then u t else 0) else 0) =
        (fun t => if L t = L s then u t else 0) := by
      funext t
      by_cases ht : L t = l
      · have hdt := (hD s t (ht.trans hsl.symm)).2 hds
        simp [ht, hsl, hdt]
      · simp [ht, hsl]
    rw [hf f, hf g]
    by_cases hp : P.prob (fun t => L t = L s) = 0
    · rw [null_mean P _ hp f, null_mean P _ hp g]
    · have h := hfg s hds hp
      unfold AronowAudit.P019.FiniteLaw.ce at h
      exact (div_left_inj' hp).mp h
  · have hn (t : Ω) (ht : L t = l) : ¬ D t := by
      intro hd
      exact hex ⟨t, ht, hd⟩
    have hz (u : Ω → ℝ) :
        (fun t => if L t = l then (if D t then u t else 0) else 0) = fun _ => 0 := by
      funext t
      by_cases ht : L t = l <;> simp [ht, hn t]
    rw [hz f, hz g]

private theorem ce_event_eq {Ω : Type*} [Fintype Ω] (P : AronowAudit.P019.FiniteLaw Ω)
    (f : Ω → ℝ) (D E : Ω → Prop) [DecidablePred D] [DecidablePred E]
    (h : ∀ x, D x ↔ E x) : P.ce f D = P.ce f E := by
  unfold AronowAudit.P019.FiniteLaw.ce
  have hn : (fun x => if D x then f x else 0) = fun x => if E x then f x else 0 := by
    funext x
    by_cases hd : D x
    · simp [hd, (h x).mp hd]
    · have he : ¬ E x := fun he => hd ((h x).mpr he)
      simp [hd, he]
  have hp : (fun x => if D x then (1 : ℝ) else 0) = fun x => if E x then 1 else 0 := by
    funext x
    by_cases hd : D x
    · simp [hd, (h x).mp hd]
    · have he : ¬ E x := fun he => hd ((h x).mpr he)
      simp [hd, he]
  unfold AronowAudit.P019.FiniteLaw.prob
  rw [hn, hp]

private def pairLabel (S : AronowAudit.P019.Study (Fin 16))
    (s : Fin 4 → Fin 16) : Fin 4 → Bool × Bool :=
  fun i => (S.Y (s i), S.Z (s i))

private theorem pairLabel_fibre (S : AronowAudit.P019.Study (Fin 16))
    (s t : Fin 4 → Fin 16) :
    pairLabel S t = pairLabel S s ↔ S.patternFibre s t := by
  simp only [pairLabel, funext_iff, Prod.mk.injEq, AronowAudit.P019.Study.patternFibre]

private theorem occupied_fibre (S : AronowAudit.P019.Study (Fin 16))
    (s t : Fin 4 → Fin 16) (h : S.patternFibre s t) : (S.occupied t ↔ S.occupied s) := by
  have hc (z y : Bool) : S.cellCount t z y = S.cellCount s z y := by
    unfold AronowAudit.P019.Study.cellCount
    apply Finset.sum_congr rfl
    intro i _
    change (if S.cell z y (t i) then (1 : ℕ) else 0) =
      (if S.cell z y (s i) then 1 else 0)
    unfold AronowAudit.P019.Study.cell
    rw [(h i).2, (h i).1]
  simp only [AronowAudit.P019.Study.occupied, hc]

theorem mean_B :
    (AronowAudit.P019.finiteSampleWitness.law.iid 4).ce
      (fun s : Fin 4 → Fin 16 => AronowAudit.P019.finiteSampleWitness.sampleB s 0 0)
      AronowAudit.P019.finiteSampleWitness.occupied = -2/3 := by
  let S := AronowAudit.P019.finiteSampleWitness
  let P := S.law.iid 4
  let B := fun s : Fin 4 → Fin 16 => S.sampleB s 0 0
  change P.ce B S.occupied = -2/3
  have hs : S.standing := AronowAudit.P019.finite_sample_witness_valid
  have hp : P.prob S.occupied ≠ 0 := by
    have h := AronowAudit.P019.Wave1.finite_product_counterexample_proof.2.1
    change P.prob S.occupied = 1431/2048 at h
    rw [h]
    norm_num
  have hb := AronowAudit.P019.Wave1.corrected_conditional_means_proof S hs 4
    (by norm_num) 0 0
  have hB : P.ce B S.occupied =
      S.listMean true false - S.listMean false false - 1 := by
    calc
      P.ce B S.occupied = P.ce (fun _ =>
          S.listMean true false - S.listMean false false - 1) S.occupied := by
        apply transfer P (pairLabel S) S.occupied B (fun _ =>
          S.listMean true false - S.listMean false false - 1)
        · intro s t h
          exact occupied_fibre S s t ((pairLabel_fibre S s t).1 h)
        · intro s hd hf
          letI : DecidablePred (fun t => pairLabel S t = pairLabel S s) :=
            fun t => Classical.propDecidable _
          have he : (fun t => pairLabel S t = pairLabel S s) = S.patternFibre s := by
            funext t
            exact propext (pairLabel_fibre S s t)
          have hf' : P.prob (S.patternFibre s) ≠ 0 := by simpa only [he] using hf
          calc
            P.ce B (fun t => pairLabel S t = pairLabel S s) =
                P.ce B (S.patternFibre s) :=
              @ce_event_eq (Fin 4 → Fin 16) _ P B
                (fun t => pairLabel S t = pairLabel S s) (S.patternFibre s)
                (fun t => Classical.propDecidable _) (fun t => Classical.propDecidable _)
                (fun t => pairLabel_fibre S s t)
            _ = S.listMean true false - S.listMean false false - 1 :=
                (hb.2.1 s hd hf').1
            _ = P.ce (fun _ => S.listMean true false - S.listMean false false - 1)
                (S.patternFibre s) := (AronowAudit.P019.ce_const P _ _ hf').symm
            _ = P.ce (fun _ => S.listMean true false - S.listMean false false - 1)
                (fun t => pairLabel S t = pairLabel S s) :=
              (@ce_event_eq (Fin 4 → Fin 16) _ P _
                (fun t => pairLabel S t = pairLabel S s) (S.patternFibre s)
                (fun t => Classical.propDecidable _) (fun t => Classical.propDecidable _)
                (fun t => pairLabel_fibre S s t)).symm
      _ = S.listMean true false - S.listMean false false - 1 := by
        exact AronowAudit.P019.ce_const P _ _ hp
  have hm1 : S.listMean true false = 5/6 := by
    norm_num [S, AronowAudit.P019.Study.listMean, AronowAudit.P019.Study.cell,
      AronowAudit.P019.finiteSampleWitness,
      AronowAudit.P019.FiniteLaw.ce, AronowAudit.P019.FiniteLaw.prob,
      AronowAudit.P019.FiniteLaw.mean, AronowAudit.P019.uniformFin,
      AronowAudit.P019.fairBit, Fin.sum_univ_succ]
  have hm0 : S.listMean false false = 1/2 := by
    norm_num [S, AronowAudit.P019.Study.listMean, AronowAudit.P019.Study.cell,
      AronowAudit.P019.finiteSampleWitness,
      AronowAudit.P019.FiniteLaw.ce, AronowAudit.P019.FiniteLaw.prob,
      AronowAudit.P019.FiniteLaw.mean, AronowAudit.P019.uniformFin,
      AronowAudit.P019.fairBit, Fin.sum_univ_succ]
  rw [hm1, hm0] at hB
  change P.ce B S.occupied = -2/3
  rw [hB]
  ring

end
end SAP.P019a.WH.W1.P.T3_L2

open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators
open Classical

theorem SAP.P019a.WH.W1.T3_L2_proof : SAP.P019a.WH.W1.T3_L2 := by
  change wholeT3Moments
  dsimp only [wholeT3Moments]
  let S := finiteSampleWitness
  let P := S.law.iid 4
  let A := @Study.sampleA (Fin 16) _ S 4
  let B := fun s : Fin 4 → Fin 16 => S.sampleB s 0 0
  obtain ⟨hD, hA, hA2⟩ := SAP.P019a.WH.W1.P.T3_L2.label_numeric_moments
  obtain ⟨_, _, hcovSrc, _, hmuSrc, hformulaSrc, _, _⟩ :=
    AronowAudit.P019.Wave1.finite_product_counterexample_proof
  have hA' : P.ce A S.occupied = 43/53 := hA
  have hA2' : P.ce (fun s => A s^2) S.occupied = 73/106 := hA2
  have hprob : P.prob S.occupied = 1431/2048 := hD
  have hB' : P.ce B S.occupied = -2/3 := by
    have h := SAP.P019a.WH.W1.P.T3_L2.mean_B
    rw [← Bridge.finiteSampleWitness_eq] at h
    change ((Bridge.toLaw S.law).iid 4).ce B S.occupied = -2/3 at h
    rw [Bridge.iid_eq S.law 4] at h
    rw [Bridge.ce_eq P B S.occupied] at h
    exact h
  have hcov : P.ccov A B S.occupied = 0 := by
    have h := hcovSrc
    rw [← Bridge.finiteSampleWitness_eq] at h
    change ((Bridge.toLaw S.law).iid 4).ccov A B S.occupied = 0 at h
    rw [Bridge.iid_eq S.law 4] at h
    unfold AronowAudit.P019.FiniteLaw.ccov at h
    rw [Bridge.ce_eq P (fun s => A s * B s) S.occupied,
      Bridge.ce_eq P A S.occupied, Bridge.ce_eq P B S.occupied] at h
    change P.ce (fun s => A s * B s) S.occupied -
      P.ce A S.occupied * P.ce B S.occupied = 0 at h
    exact h
  have hAB : P.ce (fun s => A s * B s) S.occupied = -86/159 := by
    unfold FiniteLaw.ccov at hcov
    have hab : P.ce (fun s => A s * B s) S.occupied =
        P.ce A S.occupied * P.ce B S.occupied := by linarith [hcov]
    rw [hab, hA', hB']
    norm_num
  have hcvA : P.cv A S.occupied = 171/5618 := by
    unfold FiniteLaw.cv
    rw [hA', hA2']
    norm_num
  have hformula : (P.ce A S.occupied)^2 * P.cv B S.occupied +
      P.cv A S.occupied * (P.ce B S.occupied)^2 +
      P.cv A S.occupied * P.cv B S.occupied = 75809/202248 := by
    have h := hformulaSrc
    rw [← Bridge.finiteSampleWitness_eq] at h
    change ((Bridge.toLaw S.law).iid 4).ce A S.occupied ^ 2 *
        ((Bridge.toLaw S.law).iid 4).cv B S.occupied +
        ((Bridge.toLaw S.law).iid 4).cv A S.occupied *
          (((Bridge.toLaw S.law).iid 4).ce B S.occupied)^2 +
        ((Bridge.toLaw S.law).iid 4).cv A S.occupied *
          ((Bridge.toLaw S.law).iid 4).cv B S.occupied = 75809/202248 at h
    rw [Bridge.iid_eq S.law 4] at h
    unfold AronowAudit.P019.FiniteLaw.cv at h
    rw [Bridge.ce_eq P A S.occupied,
      Bridge.ce_eq P (fun s => A s^2) S.occupied,
      Bridge.ce_eq P B S.occupied,
      Bridge.ce_eq P (fun s => B s^2) S.occupied] at h
    simpa only [SAP.P019a.FiniteLaw.cv] using h
  have hcvB : P.cv B S.occupied = 1001/1908 := by
    rw [hA', hB', hcvA] at hformula
    nlinarith [hformula]
  have hB2 : P.ce (fun s => B s^2) S.occupied = 1849/1908 := by
    unfold FiniteLaw.cv at hcvB
    rw [hB'] at hcvB
    nlinarith [hcvB]
  have hcvAB : P.cv (fun s => A s * B s) S.occupied = 141205/404496 := by
    have hmu : (fun s : Fin 4 → Fin 16 => S.muHat s 0 0) =
        (fun s => A s * B s + 1) := by
      funext s
      dsimp [A, B, Study.muHat, Study.sampleA, Study.sampleB]
      ring
    have hmu' : P.cv (fun s => S.muHat s 0 0) S.occupied = 141205/404496 := by
      have h := hmuSrc
      rw [← Bridge.finiteSampleWitness_eq] at h
      change ((Bridge.toLaw S.law).iid 4).cv (fun s => S.muHat s 0 0)
        S.occupied = 141205/404496 at h
      rw [Bridge.iid_eq S.law 4] at h
      unfold AronowAudit.P019.FiniteLaw.cv at h
      rw [Bridge.ce_eq P (fun s => S.muHat s 0 0) S.occupied,
        Bridge.ce_eq P (fun s => S.muHat s 0 0 ^ 2) S.occupied] at h
      simpa only [SAP.P019a.FiniteLaw.cv] using h
    have hpos : 0 < (Bridge.toLaw P).prob S.occupied := by
      rw [Bridge.prob_eq, hprob]
      norm_num
    have hshiftD := AronowAudit.P019.conditional_variance_shift
      (Bridge.toLaw P) (fun s => A s * B s) S.occupied
      (ne_of_gt hpos) (1 : ℝ)
    unfold AronowAudit.P019.FiniteLaw.cv at hshiftD
    rw [Bridge.ce_eq P (fun s => A s * B s) S.occupied,
      Bridge.ce_eq P (fun s => A s * B s + 1) S.occupied,
      Bridge.ce_eq P (fun s => (A s * B s)^2) S.occupied,
      Bridge.ce_eq P (fun s => (A s * B s + 1)^2) S.occupied] at hshiftD
    have hshift : P.cv (fun s => A s * B s + 1) S.occupied =
        P.cv (fun s => A s * B s) S.occupied := by
      simpa only [SAP.P019a.FiniteLaw.cv] using hshiftD
    rw [hmu, hshift] at hmu'
    exact hmu'
  have hA2B2 : P.ce (fun s => A s^2 * B s^2) S.occupied = 4897/7632 := by
    unfold FiniteLaw.cv at hcvAB
    have hsq : (fun s : Fin 4 → Fin 16 => (A s * B s)^2) =
        (fun s => A s^2 * B s^2) := by
      funext s
      ring
    rw [hsq] at hcvAB
    rw [hAB] at hcvAB
    nlinarith [hcvAB]
  exact ⟨hA', hA2', hB', hB2, hAB, hA2B2⟩
