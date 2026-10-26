import AronowAudit.P019.P019_Audit
import AronowAudit.P019.Wave1.Gap.GP019B2b
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum

/-!
Corrected finite-cell results and covariance order.
-/

namespace AronowAudit.P019.Wave1

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

variable {Ω : Type*} [Fintype Ω]


private theorem ccl_ce_sum {ι : Type*} [Fintype ι] (P : FiniteLaw Ω)
    (f : ι → Ω → ℝ) (D : Ω → Prop) [DecidablePred D] :
    P.ce (fun s => ∑ i, f i s) D = ∑ i, P.ce (f i) D := by
  unfold FiniteLaw.ce
  have he : (fun s => if D s then ∑ i, f i s else 0) =
      (fun s => ∑ i, if D s then f i s else 0) := by
    funext s; by_cases hd : D s <;> simp [hd]
  rw [he, mean_sum, Finset.sum_div]

private theorem ccl_ce_div (P : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ)
    (D : Ω → Prop) [DecidablePred D] :
    P.ce (fun s => f s/c) D = P.ce f D/c := by
  simpa only [div_eq_mul_inv] using ce_mul_const P f c⁻¹ D

private theorem ccl_ce_left (P : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ)
    (D : Ω → Prop) [DecidablePred D] :
    P.ce (fun s => c*f s) D = c*P.ce f D := by
  simpa only [mul_comm c] using ce_mul_const P f c D

private theorem ccl_atom_le (P : FiniteLaw Ω) (D : Ω → Prop)
    [DecidablePred D] (s : Ω) (hs : D s) : P.mass s ≤ P.prob D := by
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset Ω)) (f := fun t => P.mass t * if D t then (1 : ℝ) else 0)
    (fun t _ => mul_nonneg (P.nonneg t) (by split_ifs <;> norm_num))
    (Finset.mem_univ s)
  simpa only [FiniteLaw.prob, FiniteLaw.mean, if_pos hs, mul_one] using h

private theorem ccl_null_mean (P : FiniteLaw Ω) (D : Ω → Prop)
    [DecidablePred D] (hD : P.prob D = 0) (f : Ω → ℝ) :
    P.mean (fun s => if D s then f s else 0) = 0 := by
  rw [mean_congr_support P _ (fun _ => 0) ?_, mean_const]
  intro s hp
  have hn : ¬ D s := by
    intro hs; have h := ccl_atom_le P D s hs; rw [hD] at h; linarith
  simp only [if_neg hn]

private theorem ccl_partition {Λ : Type*} [Fintype Λ] (P : FiniteLaw Ω)
    (L : Ω → Λ) (f : Ω → ℝ) :
    P.mean f = ∑ l, P.mean (fun s => if L s=l then f s else 0) := by
  rw [← mean_sum]
  congr 1
  funext s
  simp

/-- Finite tower, expressed as transfer of two conditional means.
The label type indexes distinct fibres rather than sample representatives. -/
private theorem ccl_transfer {Λ : Type*} [Fintype Λ] (P : FiniteLaw Ω)
    (L : Ω → Λ) (D : Ω → Prop) [DecidablePred D] (f g : Ω → ℝ)
    (hD : ∀ s t, L t=L s → (D t ↔ D s))
    (hfg : ∀ s, D s → P.prob (fun t => L t=L s) ≠ 0 →
      P.ce f (fun t => L t=L s) = P.ce g (fun t => L t=L s)) :
    P.ce f D = P.ce g D := by
  unfold FiniteLaw.ce
  congr 1
  rw [ccl_partition P L (fun s => if D s then f s else 0),
    ccl_partition P L (fun s => if D s then g s else 0)]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hex : ∃ s, L s=l ∧ D s
  · obtain ⟨s, hsl, hds⟩ := hex
    have hf (u : Ω → ℝ) :
        (fun t => if L t=l then (if D t then u t else 0) else 0) =
        (fun t => if L t=L s then u t else 0) := by
      funext t
      by_cases ht : L t=l
      · have hdt := (hD s t (ht.trans hsl.symm)).2 hds
        simp [ht, hsl, hdt]
      · simp [ht, hsl]
    rw [hf f, hf g]
    by_cases hp : P.prob (fun t => L t=L s)=0
    · rw [ccl_null_mean P _ hp f, ccl_null_mean P _ hp g]
    · have h := hfg s hds hp
      unfold FiniteLaw.ce at h
      exact (div_left_inj' hp).mp h
  · have hn (t : Ω) (ht : L t=l) : ¬ D t := by
      intro hd; exact hex ⟨t, ht, hd⟩
    have hz (u : Ω → ℝ) :
        (fun t => if L t=l then (if D t then u t else 0) else 0) =
        (fun _ => 0) := by
      funext t; by_cases ht : L t=l <;> simp [ht, hn t]
    rw [hz f, hz g]

private def ccl_label (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : Fin n → Bool × Bool :=
  fun i => (S.Y (s i), S.Z (s i))

private theorem ccl_fibre (S : Study Ω) {n : ℕ} (s t : Fin n → Ω) :
    ccl_label S t = ccl_label S s ↔ S.patternFibre s t := by
  simp only [ccl_label, funext_iff, Prod.mk.injEq, Study.patternFibre]

private theorem ccl_invariants (S : Study Ω) {n : ℕ} (s t : Fin n → Ω)
    (hst : S.patternFibre s t) :
    (∀ z y, S.cellCount t z y=S.cellCount s z y) ∧
    S.sampleA t=S.sampleA s ∧ S.sampleH t=S.sampleH s ∧
    (S.occupied t ↔ S.occupied s) := by
  have hc : ∀ z y, S.cellCount t z y=S.cellCount s z y := by
    intro z y
    apply Finset.sum_congr rfl
    intro i _
    simp only [Study.cell, (hst i).1, (hst i).2] <;> congr 1 <;> congr 1
  have ha : S.sampleA t=S.sampleA s := by
    unfold Study.sampleA Study.ybar
    congr 2
    apply Finset.sum_congr rfl
    intro i _; rw [(hst i).1]
  refine ⟨hc, ha, ?_, ?_⟩
  · simp only [Study.sampleH, hc]
  · simp only [Study.occupied, hc]

private theorem ccl_pattern_transfer (S : Study Ω) (n : ℕ)
    (D : (Fin n → Ω) → Prop) [DecidablePred D]
    (f g : (Fin n → Ω) → ℝ)
    (hD : ∀ s t, S.patternFibre s t → (D t ↔ D s))
    (hfg : ∀ s, D s → (S.law.iid n).prob (S.patternFibre s) ≠ 0 →
      (S.law.iid n).ce f (S.patternFibre s) =
        (S.law.iid n).ce g (S.patternFibre s)) :
    (S.law.iid n).ce f D = (S.law.iid n).ce g D := by
  apply ccl_transfer (S.law.iid n) (ccl_label S) D f g
  · intro s t h; exact hD s t ((ccl_fibre S s t).1 h)
  · intro s hd hp
    simpa only [ccl_fibre] using hfg s hd (by simpa only [ccl_fibre] using hp)

private theorem ccl_coordinate (S : Study Ω) (hs : S.standing) (n : ℕ)
    (s : Fin n → Ω) (hF : (S.law.iid n).prob (S.patternFibre s) ≠ 0)
    (i : Fin n) (f : ℕ → ℝ) :
    (S.law.iid n).ce (fun t => f (S.V (t i))) (S.patternFibre s) =
      S.law.ce (fun ω => f (S.V ω)) (S.cell (S.Z (s i)) (S.Y (s i))) := by
  have hc (z y : Bool) : S.law.prob (S.cell z y) ≠ 0 :=
    ne_of_gt (hs.2.2.2.1 z y).1
  have h := conditional_sample_factorization S n s
    (fun j v => if j=i then f v else 1) hF
  have he : (fun t : Fin n → Ω => ∏ j, if j=i then f (S.V (t j)) else 1) =
      (fun t => f (S.V (t i))) := by
    funext t; exact Fintype.prod_ite_eq' i (fun j => f (S.V (t j)))
  rw [he] at h
  have hm (j : Fin n) :
      S.law.ce (fun ω => if j=i then f (S.V ω) else 1)
        (S.cell (S.Z (s j)) (S.Y (s j))) =
      if j=i then S.law.ce (fun ω => f (S.V ω))
        (S.cell (S.Z (s j)) (S.Y (s j))) else 1 := by
    by_cases hj : j=i <;> simp [hj, ce_const, hc]
  simpa only [hm, Fintype.prod_ite_eq'] using h

private theorem ccl_pair (S : Study Ω) (hs : S.standing) (n : ℕ)
    (s : Fin n → Ω) (hF : (S.law.iid n).prob (S.patternFibre s) ≠ 0)
    (i j : Fin n) (hij : i ≠ j) (f g : ℕ → ℝ) :
    (S.law.iid n).ce (fun t => f (S.V (t i))*g (S.V (t j))) (S.patternFibre s) =
      S.law.ce (fun ω => f (S.V ω)) (S.cell (S.Z (s i)) (S.Y (s i))) *
      S.law.ce (fun ω => g (S.V ω)) (S.cell (S.Z (s j)) (S.Y (s j))) := by
  have hc (z y : Bool) : S.law.prob (S.cell z y) ≠ 0 :=
    ne_of_gt (hs.2.2.2.1 z y).1
  have h := conditional_sample_factorization S n s
    (fun k v => (if k=i then f v else 1)*(if k=j then g v else 1)) hF
  have he : (fun t : Fin n → Ω => ∏ k,
      (if k=i then f (S.V (t k)) else 1)*(if k=j then g (S.V (t k)) else 1)) =
      (fun t => f (S.V (t i))*g (S.V (t j))) := by
    funext t
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', Fintype.prod_ite_eq']
  rw [he] at h
  have hm (k : Fin n) :
      S.law.ce (fun ω => (if k=i then f (S.V ω) else 1)*
        (if k=j then g (S.V ω) else 1)) (S.cell (S.Z (s k)) (S.Y (s k))) =
      (if k=i then S.law.ce (fun ω => f (S.V ω))
        (S.cell (S.Z (s k)) (S.Y (s k))) else 1)*
      (if k=j then S.law.ce (fun ω => g (S.V ω))
        (S.cell (S.Z (s k)) (S.Y (s k))) else 1) := by
    by_cases hi : k=i
    · subst k; simp [hij]
    · by_cases hj : k=j
      · subst k; simp [hi]
      · simp [hi, hj, ce_const, hc]
  simpa only [hm, Finset.prod_mul_distrib, Fintype.prod_ite_eq'] using h

private theorem ccl_cell_representation (S : Study Ω) {n : ℕ}
    (s t : Fin n → Ω) (hst : S.patternFibre s t) (z : Bool)
    (hz : 0 < S.cellCount s z false) (c : ℝ) :
    S.cellMean t z false c =
      (∑ i, if S.cell z false (s i) then (S.V (t i) : ℝ) else 0)/
        (S.cellCount s z false : ℝ) := by
  have hc := (ccl_invariants S s t hst).1 z false
  unfold Study.cellMean
  rw [hc, if_neg (Nat.ne_of_gt hz)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Study.cell, (hst i).1, (hst i).2] <;> congr 1

private theorem ccl_count_real (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) :
    (∑ i, if S.cell z false (s i) then (1 : ℝ) else 0) =
      (S.cellCount s z false : ℝ) := by
  simp only [Study.cellCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private theorem ccl_pattern_cell_mean (S : Study Ω) (hs : S.standing) (n : ℕ)
    (s : Fin n → Ω) (hF : (S.law.iid n).prob (S.patternFibre s) ≠ 0)
    (z : Bool) (hz : 0 < S.cellCount s z false) (c : ℝ) :
    (S.law.iid n).ce (fun t => S.cellMean t z false c) (S.patternFibre s) =
      S.listMean z false := by
  have hN : (S.cellCount s z false : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hz
  rw [ce_congr_support (S.law.iid n) _ _ (S.patternFibre s)
    (by intro t _ ht; exact ccl_cell_representation S s t ht z hz c)]
  rw [ccl_ce_div, ccl_ce_sum]
  have hm (i : Fin n) :
      (S.law.iid n).ce (fun t => if S.cell z false (s i) then (S.V (t i) : ℝ) else 0)
        (S.patternFibre s) =
      (if S.cell z false (s i) then (1 : ℝ) else 0)*S.listMean z false := by
    by_cases hi : S.cell z false (s i)
    · rw [if_pos hi]
      have h := ccl_coordinate S hs n s hF i (fun v => (v : ℝ))
      simpa only [hi.1, hi.2, Study.listMean, one_mul, if_pos hi] using h
    · simp [hi, ce_const, hF]
  simp_rw [hm]
  rw [← Finset.sum_mul, ccl_count_real]
  field_simp [hN]

private theorem ccl_pattern_cell_product (S : Study Ω) (hs : S.standing) (n : ℕ)
    (s : Fin n → Ω) (hF : (S.law.iid n).prob (S.patternFibre s) ≠ 0)
    (z w : Bool) (hz : 0 < S.cellCount s z false) (hw : 0 < S.cellCount s w false)
    (cz cw : ℝ) :
    (S.law.iid n).ce (fun t => S.cellMean t z false cz*S.cellMean t w false cw)
      (S.patternFibre s) = S.listMean z false*S.listMean w false +
        if z=w then S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z false)/
          (S.cellCount s z false : ℝ) else 0 := by
  let N := (S.cellCount s z false : ℝ)
  let M := (S.cellCount s w false : ℝ)
  let mz := S.listMean z false
  let mw := S.listMean w false
  let vz := S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z false)
  have hN : N ≠ 0 := by dsimp [N]; exact_mod_cast Nat.ne_of_gt hz
  have hM : M ≠ 0 := by dsimp [M]; exact_mod_cast Nat.ne_of_gt hw
  let U := fun (i : Fin n) (t : Fin n → Ω) =>
    if S.cell z false (s i) then (S.V (t i) : ℝ) else 0
  let V := fun (j : Fin n) (t : Fin n → Ω) =>
    if S.cell w false (s j) then (S.V (t j) : ℝ) else 0
  let az := fun i : Fin n => if S.cell z false (s i) then (1 : ℝ) else 0
  let aw := fun i : Fin n => if S.cell w false (s i) then (1 : ℝ) else 0
  have hp (i j : Fin n) :
      (S.law.iid n).ce (fun t => U i t*V j t) (S.patternFibre s) =
      az i*aw j*(mz*mw) + if i=j ∧ z=w then az i*vz else 0 := by
    by_cases hi : S.cell z false (s i)
    · by_cases hj : S.cell w false (s j)
      · by_cases hij : i=j
        · subst j
          have hzw : z=w := hi.1.symm.trans hj.1
          subst w
          have hcoord := ccl_coordinate S hs n s hF i (fun v => (v : ℝ)^2)
          have hsecond : S.law.ce (fun ω => (S.V ω : ℝ)^2) (S.cell z false) =
              vz+mz^2 := by dsimp [vz, mz, Study.listMean, FiniteLaw.cv]; ring
          have hc2 : (S.law.iid n).ce (fun t => (S.V (t i) : ℝ)^2)
              (S.patternFibre s) = vz+mz^2 := by
            simpa only [hi.1, hi.2, hsecond] using hcoord
          simpa [U, V, az, aw, hi, pow_two, mz, mw, add_comm] using hc2
        · have hpair := ccl_pair S hs n s hF i j hij (fun v => (v : ℝ)) (fun v => (v : ℝ))
          simpa [U, V, az, aw, hi, hj, hij, hi.1, hi.2, hj.1, hj.2,
            mz, mw, Study.listMean] using hpair
      · have hdis : ¬ (i=j ∧ z=w) := by
          rintro ⟨hij, hzw⟩; subst j; subst w; exact hj hi
        simp [U, V, az, aw, hj, hi, hdis, ce_const, hF]
    · simp [U, V, az, aw, hi, ce_const, hF]
  have hrep : (S.law.iid n).ce
      (fun t => S.cellMean t z false cz*S.cellMean t w false cw) (S.patternFibre s) =
      (∑ i, ∑ j, (S.law.iid n).ce (fun t => U i t*V j t) (S.patternFibre s))/(N*M) := by
    calc
      _ = (S.law.iid n).ce (fun t => (∑ i, ∑ j, U i t*V j t)/(N*M))
          (S.patternFibre s) := by
        apply ce_congr_support
        intro t _ ht
        rw [ccl_cell_representation S s t ht z hz cz,
          ccl_cell_representation S s t ht w hw cw]
        change (∑ i, U i t)/N*((∑ j, V j t)/M) =
          (∑ i, ∑ j, U i t*V j t)/(N*M)
        rw [← Finset.sum_mul_sum]
        <;> ring
      _ = _ := by
        rw [ccl_ce_div, ccl_ce_sum]
        simp_rw [ccl_ce_sum]
  rw [hrep]
  simp_rw [hp, Finset.sum_add_distrib]
  have haz : ∑ i, az i=N := ccl_count_real S s z
  have haw : ∑ i, aw i=M := ccl_count_real S s w
  have hmain : (∑ i, ∑ j, az i*aw j*(mz*mw)) = N*M*(mz*mw) := by
    calc
      (∑ i, ∑ j, az i*aw j*(mz*mw)) =
          (∑ i, ∑ j, az i*aw j)*(mz*mw) := by simp only [Finset.sum_mul]
      _ = (∑ i, az i)*(∑ j, aw j)*(mz*mw) := by rw [Fintype.sum_mul_sum]
      _ = N*M*(mz*mw) := by rw [haz, haw]
  rw [hmain]
  by_cases hzw : z=w
  · subst w
    have hdiag : (∑ i, ∑ j, if i=j ∧ z=z then az i*vz else 0) = N*vz := by
      simp only [eq_self_iff_true, and_true, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [← Finset.sum_mul, haz]
    rw [hdiag, if_pos rfl]
    change (N*N*(mz*mz)+N*vz)/(N*N)=mz*mz+vz/N
    field_simp [hN] <;> ring
  · simp only [hzw, and_false, if_false, Finset.sum_const_zero, add_zero]
    change N*M*(mz*mw)/(N*M)=mz*mw
    field_simp [hN, hM]

private theorem ccl_positive_atom (P : FiniteLaw Ω) (D : Ω → Prop)
    [DecidablePred D] (hp : 0 < P.prob D) : ∃ s, 0 < P.mass s ∧ D s := by
  by_contra hn
  have hz : P.prob D=0 := by
    unfold FiniteLaw.prob
    rw [mean_congr_support P _ (fun _ => 0) ?_, mean_const]
    intro s hs
    have hd : ¬ D s := by intro hd; exact hn ⟨s, hs, hd⟩
    simp [hd]
  linarith

private theorem ccl_occupied_positive (S : Study Ω) (hs : S.standing)
    (n : ℕ) (hn : 2 ≤ n) : 0 < (S.law.iid n).prob S.occupied := by
  obtain ⟨u, hu, huc⟩ := ccl_positive_atom S.law (S.cell true false)
    (hs.2.2.2.1 true false).1
  obtain ⟨v, hv, hvc⟩ := ccl_positive_atom S.law (S.cell false false)
    (hs.2.2.2.1 false false).1
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let s : Fin n → Ω := fun i => if i=i0 then u else v
  have hne : i1 ≠ i0 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
  have h0 : S.cell true false (s i0) := by simpa [s] using huc
  have h1 : S.cell false false (s i1) := by simpa [s, hne] using hvc
  have hd : S.occupied s := by
    constructor
    · apply Nat.pos_of_ne_zero
      intro hz
      have hall : ∀ i, ¬ S.cell true false (s i) := by
        simpa [Study.cellCount] using hz
      exact hall i0 h0
    · apply Nat.pos_of_ne_zero
      intro hz
      have hall : ∀ i, ¬ S.cell false false (s i) := by
        simpa [Study.cellCount] using hz
      exact hall i1 h1
  have hp : 0 < (S.law.iid n).mass s := by
    change 0 < ∏ i, S.law.mass (s i)
    apply Finset.prod_pos
    intro i _
    dsimp [s]; split_ifs <;> assumption
  exact lt_of_lt_of_le hp (ccl_atom_le (S.law.iid n) S.occupied s hd)

private theorem ccl_occupied_cell_mean (S : Study Ω) (hs : S.standing)
    (n : ℕ) (hn : 2 ≤ n) (z : Bool) (c : ℝ) :
    (S.law.iid n).ce (fun t => S.cellMean t z false c) S.occupied =
      S.listMean z false := by
  let P := S.law.iid n
  have hp := ne_of_gt (ccl_occupied_positive S hs n hn)
  rw [← ce_const P (S.listMean z false) S.occupied hp]
  apply ccl_pattern_transfer S n S.occupied
  · intro s t h; exact (ccl_invariants S s t h).2.2.2
  · intro s hd hF
    have hz : 0 < S.cellCount s z false := by cases z <;> [exact hd.2; exact hd.1]
    rw [ccl_pattern_cell_mean S hs n s hF z hz c, ce_const P _ _ hF]

private theorem ccl_cross_covariance (S : Study Ω) (hs : S.standing)
    (n : ℕ) (hn : 2 ≤ n) (c1 c0 : ℝ) :
    (S.law.iid n).ccov (fun t => S.cellMean t true false c1)
      (fun t => S.cellMean t false false c0) S.occupied = 0 := by
  let P := S.law.iid n
  have hp := ne_of_gt (ccl_occupied_positive S hs n hn)
  have hm : P.ce (fun t => S.cellMean t true false c1*S.cellMean t false false c0)
      S.occupied = S.listMean true false*S.listMean false false := by
    rw [← ce_const P (S.listMean true false*S.listMean false false) S.occupied hp]
    apply ccl_pattern_transfer S n S.occupied
    · intro s t h; exact (ccl_invariants S s t h).2.2.2
    · intro s hd hF
      rw [ccl_pattern_cell_product S hs n s hF true false hd.1 hd.2 c1 c0,
        ce_const P _ _ hF]
      simp
  unfold FiniteLaw.ccov
  rw [hm, ccl_occupied_cell_mean S hs n hn true c1,
    ccl_occupied_cell_mean S hs n hn false c0]
  ring

private theorem ccl_iid_labels {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (P : FiniteLaw Ω)
    (n : ℕ) (L : Ω → Λ) (F : (Fin n → Λ) → ℝ) (v : Fin n → Ω → ℝ) :
    (P.iid n).mean (fun s => F (fun i => L (s i))*∏ i, v i (s i)) =
      ∑ l : Fin n → Λ, F l*∏ i, P.mean (fun ω => if L ω=l i then v i ω else 0) := by
  have he : (fun s : Fin n → Ω => F (fun i => L (s i))*∏ i, v i (s i)) =
      (fun s => ∑ l : Fin n → Λ,
        F l*∏ i, if L (s i)=l i then v i (s i) else 0) := by
    funext s
    symm
    rw [Finset.sum_eq_single (fun i => L (s i))]
    · simp
    · intro l _ hl
      have hex : ∃ i, L (s i) ≠ l i := by
        by_contra hn
        apply hl
        funext i; exact (not_ne_iff.mp (not_exists.mp hn i)).symm
      obtain ⟨i, hi⟩ := hex
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
    · simp
  rw [he, mean_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [mean_const_mul, iid_mean_prod P n (fun i ω => if L ω=l i then v i ω else 0)]


/- Nested-subset enumeration. -/
private def ccl_lower {n : ℕ} (c : Fin n → Fin 3) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i ≠ 2)
private def ccl_success {n : ℕ} (c : Fin n → Fin 3) : Finset (Fin n) :=
  Finset.univ.filter (fun i => c i = 0)
private def ccl_pattern {n : ℕ} (T A : Finset (Fin n)) (i : Fin n) : Fin 3 :=
  if i ∈ T then if i ∈ A then 0 else 1 else 2

private theorem ccl_pattern_lower {n : ℕ} (T A : Finset (Fin n)) :
    ccl_lower (ccl_pattern T A) = T := by
  ext i
  by_cases ht : i ∈ T <;> by_cases ha : i ∈ A <;> simp [ccl_lower, ccl_pattern, ht, ha]

private theorem ccl_pattern_success {n : ℕ} (T A : Finset (Fin n)) (hAT : A ⊆ T) :
    ccl_success (ccl_pattern T A) = A := by
  ext i
  simp only [ccl_success, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hA : i ∈ A
  · simp [ccl_pattern, hA, hAT hA]
  · by_cases ht : i ∈ T <;> simp [ccl_pattern, hA, ht]

private theorem ccl_restore {n : ℕ} (c : Fin n → Fin 3) :
    ccl_pattern (ccl_lower c) (ccl_success c) = c := by
  funext i
  have hi : c i = 0 ∨ c i = 1 ∨ c i = 2 := by omega
  rcases hi with h | h | h <;> simp [ccl_pattern, ccl_lower, ccl_success, h]

private theorem ccl_sum_patterns {n : ℕ} (F : (Fin n → Fin 3) → ℝ) :
    (∑ c, F c) = ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
      ∑ A ∈ T.powerset, F (ccl_pattern T A) := by
  classical
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun c _ => ⟨ccl_lower c, ccl_success c⟩)
  · intro c _
    simp only [Finset.mem_sigma, Finset.mem_powerset, Finset.subset_univ, true_and]
    intro i hi
    simp only [ccl_success, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [ccl_lower, hi]
  · intro c _ d _ h
    have ht : ccl_lower c = ccl_lower d := congrArg Sigma.fst h
    have ha : ccl_success c = ccl_success d := by simpa using congrArg (fun z => z.2) h
    rw [← ccl_restore c, ← ccl_restore d, ht, ha]
  · intro b hb
    rcases b with ⟨T,A⟩
    simp only [Finset.mem_sigma, Finset.mem_powerset] at hb
    exact ⟨ccl_pattern T A, Finset.mem_univ _, by
      simp [ccl_pattern_lower, ccl_pattern_success T A hb.2]⟩
  · intro c _
    rw [ccl_restore]

private theorem ccl_prod_pattern {n : ℕ} (T A : Finset (Fin n)) (hAT : A ⊆ T)
    (a b d : ℝ) :
    (∏ i : Fin n, if ccl_pattern T A i = 0 then a else if ccl_pattern T A i = 1 then b else d) =
      a^A.card * b^(T.card-A.card) * d^(n-T.card) := by
  classical
  have hf : (fun i : Fin n => if ccl_pattern T A i = 0 then a else
      if ccl_pattern T A i = 1 then b else d) =
      (fun i => if i ∈ T then if i ∈ A then a else b else d) := by
    funext i
    by_cases ht : i ∈ T <;> by_cases ha : i ∈ A <;> simp [ccl_pattern, ht, ha]
  rw [hf, Finset.prod_ite, Finset.prod_ite]
  have hT : Finset.univ.filter (fun i : Fin n => i ∈ T) = T := by ext i; simp
  have hTA : T.filter (fun i => i ∈ A) = A := by
    ext i; simp only [Finset.mem_filter]; exact ⟨And.right, fun h => ⟨hAT h,h⟩⟩
  have hTnA : T.filter (fun i => i ∉ A) = T \ A := by ext i; simp
  have hnT : (Finset.univ.filter (fun i : Fin n => i ∉ T)).card = n-T.card := by
    rw [show Finset.univ.filter (fun i : Fin n => i ∉ T) = Finset.univ \ T by ext i; simp,
      Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp
  rw [hT, hTA, hTnA]
  simp only [Finset.prod_const, Finset.card_sdiff_of_subset hAT, hnT]

/-- Enumerate category vectors by a lower-bin subset and its success subset. -/
private theorem ccl_multinomial {n : ℕ} (F : ℕ → ℕ → ℝ) (a b d : ℝ) :
    (∑ c : Fin n → Fin 3, F (ccl_lower c).card (ccl_success c).card *
      ∏ i, if c i = 0 then a else if c i = 1 then b else d) =
    ∑ k ∈ Finset.range (n+1), ∑ s ∈ Finset.range (k+1),
      (n.choose k : ℝ) * (k.choose s : ℝ) * F k s * a^s * b^(k-s) * d^(n-k) := by
  classical
  rw [ccl_sum_patterns, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro k hk
  have hinner (T : Finset (Fin n)) (hT : T ∈ Finset.univ.powersetCard k) :
      (∑ A ∈ T.powerset,
        F (ccl_lower (ccl_pattern T A)).card (ccl_success (ccl_pattern T A)).card *
          ∏ i, if ccl_pattern T A i = 0 then a else if ccl_pattern T A i = 1 then b else d) =
      ∑ s ∈ Finset.range (k+1), (k.choose s : ℝ) * F k s * a^s * b^(k-s) * d^(n-k) := by
    have hcard : T.card = k := (Finset.mem_powersetCard.mp hT).2
    simp_rw [ccl_pattern_lower]
    calc
      _ = ∑ A ∈ T.powerset, F k A.card * (a^A.card * b^(k-A.card) * d^(n-k)) := by
        apply Finset.sum_congr rfl
        intro A hA
        have hs := Finset.mem_powerset.mp hA
        rw [ccl_pattern_success T A hs, ccl_prod_pattern T A hs, hcard]
      _ = _ := by
        rw [Finset.sum_powerset, hcard]
        apply Finset.sum_congr rfl
        intro s hs
        rw [Finset.sum_powersetCard s T (fun r => F k r * (a^r * b^(k-r) * d^(n-k)))]
        simp only [hcard, nsmul_eq_mul]
        ring
  calc
    _ = ∑ _T ∈ Finset.univ.powersetCard k,
        ∑ s ∈ Finset.range (k+1), (k.choose s : ℝ) * F k s * a^s * b^(k-s) * d^(n-k) :=
      Finset.sum_congr rfl hinner
    _ = _ := by
      rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring


private theorem ccl_prob_nonneg (P : FiniteLaw Ω) (D : Ω → Prop)
    [DecidablePred D] : 0 ≤ P.prob D := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (P.nonneg ω)
    (by dsimp only; split_ifs <;> norm_num))

private theorem ccl_prob_le_one (P : FiniteLaw Ω) (D : Ω → Prop)
    [DecidablePred D] : P.prob D ≤ 1 := by
  rw [← mean_const P 1]
  apply Finset.sum_le_sum
  intro ω _
  apply mul_le_mul_of_nonneg_left _ (P.nonneg ω)
  dsimp only
  split_ifs <;> norm_num

private def ccl_category (S : Study Ω) (ω : Ω) : Fin 3 :=
  if S.Y ω = false then if S.Z ω = true then 0 else 1 else 2

private theorem ccl_category_prob (S : Study Ω) (hs : S.standing) (j : Fin 3) :
    S.law.prob (fun ω => ccl_category S ω = j) =
      if j = 0 then S.law.prob (fun ω => S.Y ω = false)*S.gamma
      else if j = 1 then S.law.prob (fun ω => S.Y ω = false)*(1-S.gamma)
      else S.law.prob (fun ω => S.Y ω = true) := by
  have h0 : (fun ω => ccl_category S ω = 0) = S.cell true false := by
    funext ω
    cases hy : S.Y ω <;> cases hz : S.Z ω <;> simp [ccl_category, Study.cell, hy, hz]
  have h1 : (fun ω => ccl_category S ω = 1) = S.cell false false := by
    funext ω
    cases hy : S.Y ω <;> cases hz : S.Z ω <;> simp [ccl_category, Study.cell, hy, hz]
  have h2 : (fun ω => ccl_category S ω = 2) = (fun ω => S.Y ω = true) := by
    funext ω
    cases hy : S.Y ω <;> cases hz : S.Z ω <;> simp [ccl_category, hy, hz]
  have hp (j : Fin 3) (D : Ω → Prop) [DecidablePred D]
      (hD : (fun ω => ccl_category S ω=j)=D) :
      S.law.prob (fun ω => ccl_category S ω=j)=S.law.prob D := by
    unfold FiniteLaw.prob
    congr 1
    funext ω
    simp only [congrFun hD ω]
  fin_cases j
  · change S.law.prob (fun ω => ccl_category S ω = (0 : Fin 3)) =
      S.law.prob (fun ω => S.Y ω=false)*S.gamma
    rw [hp 0 _ h0, cell_probability S hs.2.2.1]
    exact mul_comm _ _
  · change S.law.prob (fun ω => ccl_category S ω = (1 : Fin 3)) =
      S.law.prob (fun ω => S.Y ω=false)*(1-S.gamma)
    rw [hp 1 _ h1, cell_probability S hs.2.2.1, prob_false]
    exact mul_comm _ _
  · change S.law.prob (fun ω => ccl_category S ω = (2 : Fin 3)) =
      S.law.prob (fun ω => S.Y ω=true)
    exact hp 2 _ h2

private theorem ccl_count_statistics (S : Study Ω) {n : ℕ} (s : Fin n → Ω) :
    (ccl_lower (fun i => ccl_category S (s i))).card = S.negativeCount s ∧
    (ccl_success (fun i => ccl_category S (s i))).card = S.cellCount s true false := by
  constructor
  · unfold ccl_lower Study.negativeCount Study.cellCount
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases hy : S.Y (s i) <;> cases hz : S.Z (s i) <;>
      simp [ccl_category, Study.cell, hy, hz]
  · unfold ccl_success Study.cellCount
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i _
    cases hy : S.Y (s i) <;> cases hz : S.Z (s i) <;>
      simp [ccl_category, Study.cell, hy, hz]

private theorem ccl_counts_sum (S : Study Ω) (hs : S.standing) (n : ℕ)
    (F : ℕ → ℕ → ℝ) :
    (S.law.iid n).mean (fun s => F (S.negativeCount s) (S.cellCount s true false)) =
    ∑ k ∈ Finset.range (n+1), ∑ i ∈ Finset.range (k+1),
      (n.choose k : ℝ)*(k.choose i : ℝ)*F k i *
        (S.law.prob (fun ω => S.Y ω = false)*S.gamma)^i *
        (S.law.prob (fun ω => S.Y ω = false)*(1-S.gamma))^(k-i) *
        (S.law.prob (fun ω => S.Y ω = true))^(n-k) := by
  have h := ccl_iid_labels S.law n (ccl_category S)
    (fun l => F (ccl_lower l).card (ccl_success l).card) (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one, ccl_count_statistics] at h
  rw [h]
  change (∑ l : Fin n → Fin 3, F (ccl_lower l).card (ccl_success l).card *
    ∏ i, S.law.prob (fun ω => ccl_category S ω=l i)) = _
  simp_rw [ccl_category_prob S hs]
  exact ccl_multinomial F _ _ _

private theorem ccl_joint_mass (S : Study Ω) (hs : S.standing) (n k i : ℕ)
    (hk : k ≤ n) (hi : i ≤ k) :
    (S.law.iid n).mean (fun s => if S.negativeCount s=k then
      (if S.cellCount s true false=i then (1 : ℝ) else 0) else 0) =
      (n.choose k : ℝ)*(k.choose i : ℝ)*
        (S.law.prob (fun ω => S.Y ω = false)*S.gamma)^i *
        (S.law.prob (fun ω => S.Y ω = false)*(1-S.gamma))^(k-i) *
        (S.law.prob (fun ω => S.Y ω = true))^(n-k) := by
  have h := ccl_counts_sum S hs n (fun a b => if a=k then if b=i then 1 else 0 else 0)
  simpa [Finset.mem_range, Nat.lt_succ_iff, hk, hi, mul_ite] using h

private theorem ccl_negative_mass (S : Study Ω) (hs : S.standing) (n k : ℕ)
    (hk : k ≤ n) :
    (S.law.iid n).prob (fun s => S.negativeCount s=k) =
      (n.choose k : ℝ)*(S.law.prob (fun ω => S.Y ω = false))^k *
        (S.law.prob (fun ω => S.Y ω = true))^(n-k) := by
  let q := S.law.prob (fun ω => S.Y ω = false)
  let r := S.law.prob (fun ω => S.Y ω = true)
  have h := ccl_counts_sum S hs n (fun a _ => if a=k then 1 else 0)
  change (S.law.iid n).mean (fun s => if S.negativeCount s=k then (1 : ℝ) else 0) = _
  rw [h]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.lt_succ_iff, hk, ↓reduceIte]
  change (∑ i ∈ Finset.range (k+1),
    (n.choose k : ℝ)*(k.choose i : ℝ)*(q*S.gamma)^i*(q*(1-S.gamma))^(k-i)*r^(n-k)) = _
  have he : (∑ i ∈ Finset.range (k+1),
      (n.choose k : ℝ)*(k.choose i : ℝ)*(q*S.gamma)^i*(q*(1-S.gamma))^(k-i)*r^(n-k)) =
      (n.choose k : ℝ)*((q*S.gamma+q*(1-S.gamma))^k)*r^(n-k) := by
    rw [add_pow]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  congr 2
  ring

private theorem ccl_conditional_count (S : Study Ω) (hs : S.standing) (n k i : ℕ)
    (hk : k ≤ n) (hK : (S.law.iid n).prob (fun s => S.negativeCount s=k) ≠ 0)
    (hi : i ≤ k) :
    (S.law.iid n).ce (fun s => if S.cellCount s true false=i then 1 else 0)
      (fun s => S.negativeCount s=k) =
        (Nat.choose k i : ℝ)*S.gamma^i*(1-S.gamma)^(k-i) := by
  unfold FiniteLaw.ce
  rw [ccl_joint_mass S hs n k i hk hi]
  apply (div_eq_iff hK).2
  rw [ccl_negative_mass S hs n k hk]
  simp only [mul_pow]
  rw [show (S.law.prob (fun ω => S.Y ω=false))^k =
    (S.law.prob (fun ω => S.Y ω=false))^i *
      (S.law.prob (fun ω => S.Y ω=false))^(k-i) by rw [← pow_add, Nat.add_sub_of_le hi]]
  ring

private theorem ccl_A_covariance (S : Study Ω) (hs : S.standing)
    (n : ℕ) (hn : 2 ≤ n) (z : Bool) (c : ℝ) :
    (S.law.iid n).ccov (fun t => S.cellMean t z false c) S.sampleA S.occupied = 0 := by
  let P := S.law.iid n
  have hm : P.ce (fun t => S.cellMean t z false c*S.sampleA t) S.occupied =
      S.listMean z false*P.ce S.sampleA S.occupied := by
    rw [← ccl_ce_left P (S.listMean z false) S.sampleA S.occupied]
    apply ccl_pattern_transfer S n S.occupied
    · intro s t h; exact (ccl_invariants S s t h).2.2.2
    · intro s hd hF
      have hz : 0 < S.cellCount s z false := by cases z <;> [exact hd.2; exact hd.1]
      have hl := ce_congr_support P
        (fun t => S.cellMean t z false c*S.sampleA t)
        (fun t => S.cellMean t z false c*S.sampleA s) (S.patternFibre s)
        (by intro t _ ht; rw [(ccl_invariants S s t ht).2.1])
      have hr := ce_congr_support P (fun t => S.listMean z false*S.sampleA t)
        (fun _ => S.listMean z false*S.sampleA s) (S.patternFibre s)
        (by intro t _ ht; rw [(ccl_invariants S s t ht).2.1])
      rw [hl, hr, ce_mul_const, ccl_pattern_cell_mean S hs n s hF z hz c,
        ce_const P _ _ hF]
  unfold FiniteLaw.ccov
  rw [hm, ccl_occupied_cell_mean S hs n hn z c]
  ring

theorem corrected_cell_lemmas_proof (S : Study Ω) (hs : S.standing) (n : ℕ) (hn : 2 ≤ n)
    (c1 c0 : ℝ) :
    let P := S.law.iid n
    0 < P.prob (S.occupied) ∧
    (∀ z : Bool,
      P.prob (fun s => S.cellCount s z false = 0) =
        (1 - S.law.prob (S.cell z false))^n ∧
      0 < P.prob (fun s => S.cellCount s z false = 0)) ∧
    (∀ k : ℕ, k ≤ n → P.prob (fun s => S.negativeCount s = k) ≠ 0 →
      ∀ i : ℕ, i ≤ k →
        P.ce (fun s => if S.cellCount s true false = i then 1 else 0)
          (fun s => S.negativeCount s = k) =
            (Nat.choose k i : ℝ) * S.gamma^i * (1-S.gamma)^(k-i)) ∧
    (∀ (s : Fin n → Ω), S.occupied s → P.prob (S.patternFibre s) ≠ 0 →
      (∀ z : Bool,
        P.ce (fun t => S.cellMean t z false (if z then c1 else c0)) (S.patternFibre s) =
          S.listMean z false ∧
        P.cv (fun t => S.cellMean t z false (if z then c1 else c0)) (S.patternFibre s) =
          S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell z false) / (S.cellCount s z false : ℝ)) ∧
      P.ccov (fun t => S.cellMean t true false c1) (fun t => S.cellMean t false false c0)
        (S.patternFibre s) = 0) ∧
    (∀ z : Bool,
      P.ccov (fun t => S.cellMean t z false (if z then c1 else c0)) S.sampleA S.occupied = 0) ∧
    P.ccov (fun t => S.cellMean t true false c1) (fun t => S.cellMean t false false c0)
      S.occupied = 0 := by
  dsimp only
  refine ⟨ccl_occupied_positive S hs n hn, ?_, ?_, ?_, ?_, ccl_cross_covariance S hs n hn c1 c0⟩
  · intro z
    refine ⟨empty_cell_probability S n z false, ?_⟩
    rw [empty_cell_probability]
    apply pow_pos
    have hcell : S.law.prob (S.cell z false) =
        S.law.prob (fun ω => S.Z ω=z)*S.law.prob (fun ω => S.Y ω=false) :=
      cell_probability S hs.2.2.1 z false
    have hzle := ccl_prob_le_one S.law (fun ω => S.Z ω=z)
    have hy := (regularity_probabilities S hs.2.2.2).2 true
    have hy0 := ccl_prob_nonneg S.law (fun ω => S.Y ω=false)
    have hylt : S.law.prob (fun ω => S.Y ω=false) < 1 := by
      rw [prob_false]; linarith
    rw [hcell]
    have := mul_le_mul_of_nonneg_right hzle hy0
    linarith
  · intro k hk hK i hi
    exact ccl_conditional_count S hs n k i hk hK hi
  · intro s hd hF
    refine ⟨?_, ?_⟩
    · intro z
      have hz : 0 < S.cellCount s z false := by cases z <;> [exact hd.2; exact hd.1]
      refine ⟨ccl_pattern_cell_mean S hs n s hF z hz _, ?_⟩
      have hprod := ccl_pattern_cell_product S hs n s hF z z hz hz
        (if z then c1 else c0) (if z then c1 else c0)
      simpa only [FiniteLaw.cv, pow_two, ccl_pattern_cell_mean S hs n s hF z hz,
        if_pos rfl, if_true, add_sub_cancel_left] using
        congrArg (fun x : ℝ => x-S.listMean z false*S.listMean z false) hprod
    · unfold FiniteLaw.ccov
      rw [ccl_pattern_cell_product S hs n s hF true false hd.1 hd.2 c1 c0,
        ccl_pattern_cell_mean S hs n s hF true hd.1 c1,
        ccl_pattern_cell_mean S hs n s hF false hd.2 c0]
      simp
  · intro z
    exact ccl_A_covariance S hs n hn z (if z then c1 else c0)

/- Covariance order: finite-product tails, L² reciprocal remainders,
   polarization, and exponentially small occupied-conditioning errors. -/

local notation "avg" => GP019B2b_t18_avg
local notation "MB" => GP019B2b_t18_MomentBound

private def cvo_indicator (D : Ω → Prop) : Ω → ℝ := fun ω => if D ω then 1 else 0
private def cvo_count (D : Ω → Prop) (n : ℕ) (s : Fin n → Ω) : ℕ :=
  ∑ i, if D (s i) then 1 else 0

private lemma cvo_count_cast (D : Ω → Prop) (n : ℕ) (s : Fin n → Ω) :
    (cvo_count D n s : ℝ) = ∑ i, cvo_indicator D (s i) := by
  simp only [cvo_count, cvo_indicator, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private lemma cvo_avg_bounds (D : Ω → Prop) (n : ℕ) (s : Fin n → Ω) :
    0 ≤ avg (cvo_indicator D) n s ∧ avg (cvo_indicator D) n s ≤ 1 := by
  have hs0 : 0 ≤ ∑ i, cvo_indicator D (s i) :=
    Finset.sum_nonneg (fun _ _ => by dsimp [cvo_indicator]; split_ifs <;> norm_num)
  have hs1 : (∑ i, cvo_indicator D (s i)) ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun _ _ => by
        dsimp [cvo_indicator]; split_ifs <;> norm_num)
      _ = _ := by simp
  constructor
  · exact div_nonneg hs0 (Nat.cast_nonneg _)
  · by_cases hn : n=0
    · subst n; simp [GP019B2b_t18_avg]
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).2 hs1

private lemma cvo_prob_bounds (P : FiniteLaw Ω) (D : Ω → Prop) :
    0 ≤ P.prob D ∧ P.prob D ≤ 1 := by
  constructor
  · exact GP019B2b_t18_mean_nonneg _ (fun _ => by split_ifs <;> norm_num)
  · rw [← mean_const P 1]
    exact GP019B2b_t18_mean_mono _ (fun _ => by split_ifs <;> norm_num)

/-- A direct finite-product Chernoff bound; no measure bridge is needed. -/
private lemma cvo_lower_tail (P : FiniteLaw Ω) (D : Ω → Prop) (n : ℕ) (hn : 0 < n) :
    (P.iid n).prob (fun s => avg (cvo_indicator D) n s < P.prob D/4) ≤
      Real.exp (-(P.prob D/4)*(n : ℝ)) := by
  let p := P.prob D
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h01 := cvo_prob_bounds P D
  have hexp : Real.exp (-1 : ℝ) ≤ 1/2 := by
    rw [Real.exp_neg]
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos 1)).2
    have hh := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hmgf : P.mean (fun ω => Real.exp (-cvo_indicator D ω)) ≤ Real.exp (-p/2) := by
    have he : (fun ω => Real.exp (-cvo_indicator D ω)) =
        (fun ω => 1-cvo_indicator D ω*(1-Real.exp (-1))) := by
      funext ω; dsimp [cvo_indicator]; split_ifs <;> simp
    rw [he, mean_sub, mean_const, mean_mul_const]
    change 1-p*(1-Real.exp (-1)) ≤ Real.exp (-p/2)
    have hh := Real.add_one_le_exp (-p/2)
    nlinarith [mul_le_mul_of_nonneg_left hexp h01.1]
  calc
    _ ≤ (P.iid n).mean (fun s => Real.exp ((p/4)*(n : ℝ)-∑ i, cvo_indicator D (s i))) := by
      apply GP019B2b_t18_mean_mono
      intro s
      change (if avg (cvo_indicator D) n s < p/4 then (1 : ℝ) else 0) ≤ _
      split_ifs with h
      · apply Real.one_le_exp_iff.2
        have hh := (div_lt_iff₀ hn0).1 h
        linarith
      · exact (Real.exp_pos _).le
    _ = Real.exp ((p/4)*(n : ℝ)) *
        (P.mean (fun ω => Real.exp (-cvo_indicator D ω)))^n := by
      have he : (fun s : Fin n → Ω => Real.exp ((p/4)*(n : ℝ)-∑ i, cvo_indicator D (s i))) =
          (fun s => Real.exp ((p/4)*(n : ℝ))*∏ i, Real.exp (-cvo_indicator D (s i))) := by
        funext s
        rw [← Real.exp_sum, Finset.sum_neg_distrib, sub_eq_add_neg, Real.exp_add]
      rw [he, mean_const_mul, iid_mean_prod P n (fun _ ω => Real.exp (-cvo_indicator D ω))]
      simp
    _ ≤ Real.exp ((p/4)*(n : ℝ)) * (Real.exp (-p/2))^n := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply pow_le_pow_left₀ _ hmgf
      exact GP019B2b_t18_mean_nonneg _ (fun _ => (Real.exp_pos _).le)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

private lemma cvo_exp_limit (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ)^k*Real.exp (-c*(n : ℝ))) atTop (nhds 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).comp
    tendsto_natCast_atTop_atTop
  simpa only [Function.comp_def, Real.rpow_natCast] using h

private lemma cvo_exp_bound (c : ℝ) (hc : 0 < c) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (n : ℝ)^k*Real.exp (-c*(n : ℝ)) ≤ C := by
  have h := Metric.isBounded_range_of_tendsto _ (cvo_exp_limit c hc k)
  obtain ⟨C, hC⟩ := h.bddAbove
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  exact (hC (Set.mem_range_self n)).trans (le_max_left _ _)

private lemma cvo_inv_bound (D : Ω → Prop) (n : ℕ) (hn : 0 < n) (s : Fin n → Ω) :
    0 ≤ (avg (cvo_indicator D) n s)⁻¹ ∧ (avg (cvo_indicator D) n s)⁻¹ ≤ n := by
  rw [GP019B2b_t18_avg, ← cvo_count_cast, inv_div]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  constructor
  · positivity
  · by_cases hz : cvo_count D n s=0
    · simp [hz]
    · apply (div_le_iff₀ (by exact_mod_cast Nat.pos_of_ne_zero hz)).2
      have hN : (1 : ℝ) ≤ cvo_count D n s := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz
      nlinarith

private lemma cvo_inv_remainder_point (p a : ℝ) (n : ℕ)
    (hp : 0 < p) (hp1 : p ≤ 1) (hn : 0 < n) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : a⁻¹ ≤ n) :
    (a⁻¹-1/p+(a-p)/p^2)^2 ≤
      (16/p^6)*(a-p)^4 + (3*(1+1/p^2+1/p^4))*(n : ℝ)^2*
        (if a < p/4 then 1 else 0) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hp0 : p ≠ 0 := ne_of_gt hp
  have had : (a-p)^2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-(a-p)) (by linarith : 0 ≤ 1+(a-p))]
  by_cases hgood : p/4 ≤ a
  · rw [if_neg (not_lt.mpr hgood), mul_zero, add_zero]
    have ha0 : 0 < a := by linarith
    have hid : a⁻¹-1/p+(a-p)/p^2 = (a-p)^2/(p^2*a) := by
      field_simp [hp0, ne_of_gt ha0]; ring
    rw [hid, div_pow]
    apply (div_le_iff₀ (by positivity : 0 < (p^2*a)^2)).2
    have hden : p^2 ≤ 16*a^2 := by nlinarith [sq_nonneg (4*a-p)]
    have h := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ (a-p)^4/p^2)
    field_simp [hp0] at h ⊢
    nlinarith only [h]
  · rw [if_pos (lt_of_not_ge hgood), mul_one]
    have hthree : (a⁻¹-1/p+(a-p)/p^2)^2 ≤ 3*((a⁻¹)^2+(1/p)^2+((a-p)/p^2)^2) := by
      nlinarith [sq_nonneg (a⁻¹+1/p), sq_nonneg (a⁻¹-(a-p)/p^2),
        sq_nonneg (1/p+(a-p)/p^2)]
    have ht2 : (a⁻¹)^2 ≤ (n : ℝ)^2 :=
      pow_le_pow_left₀ (inv_nonneg.mpr ha) ht 2
    have hd2 : ((a-p)/p^2)^2 ≤ 1/p^4 := by
      rw [div_pow, ← pow_mul]
      exact div_le_div_of_nonneg_right had (by positivity)
    have hp2 : 0 ≤ 1/p^2 := by positivity
    have hp4 : 0 ≤ 1/p^4 := by positivity
    have hn2 : (1 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
    have h1 := mul_le_mul_of_nonneg_left hn2 hp2
    have h2 := mul_le_mul_of_nonneg_left hn2 hp4
    have hb : 0 ≤ (16/p^6)*(a-p)^4 := by positivity
    rw [div_pow] at hthree
    nlinarith

private lemma cvo_inv_remainder (P : FiniteLaw Ω) (D : Ω → Prop)
    (hp : 0 < P.prob D) :
    MB P 2 (fun n s => (avg (cvo_indicator D) n s)⁻¹-1/P.prob D+
      avg (fun ω => cvo_indicator D ω-P.prob D) n s/(P.prob D)^2) := by
  let p := P.prob D
  let f := fun ω => cvo_indicator D ω-p
  have hf : P.mean f=0 := by dsimp [f,p,cvo_indicator]; rw [mean_sub, mean_const]; change P.prob D-P.prob D=0; ring
  obtain ⟨C,hC,hfour⟩ := GP019B2b_t18_fourth_average P f hf
  obtain ⟨B,hB,hBnd⟩ := cvo_exp_bound (p/4) (by dsimp [p]; linarith) 4
  let K := 3*(1+1/p^2+1/p^4)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨(16/p^6)*C+K*B, by positivity, ?_⟩
  intro n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnne := ne_of_gt hn0
  have hcenter (s : Fin n → Ω) : avg f n s = avg (cvo_indicator D) n s-p :=
    GP019B2b_t18_avg_center _ _ n hn s
  have hpoly (s : Fin n → Ω) := cvo_inv_remainder_point p
    (avg (cvo_indicator D) n s) n hp (cvo_prob_bounds P D).2 hn
    (cvo_avg_bounds D n s).1 (cvo_avg_bounds D n s).2 (cvo_inv_bound D n hn s).2
  have htail := cvo_lower_tail P D n hn
  have hbound : (n : ℝ)^2*Real.exp (-(p/4)*(n : ℝ)) ≤ B/(n : ℝ)^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hn0)).2
    convert hBnd n using 1 <;> ring
  calc
    _ ≤ (P.iid n).mean (fun s => (16/p^6)*(avg f n s)^4 + K*(n : ℝ)^2*
        (if avg (cvo_indicator D) n s < p/4 then 1 else 0)) := by
      apply GP019B2b_t18_mean_mono
      intro s
      simpa only [f, p, hcenter s] using hpoly s
    _ = (16/p^6)*(P.iid n).mean (fun s => (avg f n s)^4) +
        K*(n : ℝ)^2*(P.iid n).prob (fun s => avg (cvo_indicator D) n s < p/4) := by
      rw [mean_add, mean_const_mul, mean_const_mul]; rfl
    _ ≤ (16/p^6)*(C/(n : ℝ)^2)+K*((n : ℝ)^2*Real.exp (-(p/4)*(n : ℝ))) := by
      have h1 := mul_le_mul_of_nonneg_left (hfour n hn) (by positivity : 0 ≤ 16/p^6)
      have h2 := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ K*(n : ℝ)^2)
      nlinarith only [h1,h2]
    _ ≤ (16/p^6)*(C/(n : ℝ)^2)+K*(B/(n : ℝ)^2) := by
      gcongr
    _ = _ := by ring

private lemma cvo_cov_add (P : FiniteLaw Ω) (f g : Ω → ℝ) :
    P.variance (fun ω => f ω+g ω) = P.variance f+P.variance g+2*P.cov f g := by
  have he : (fun ω => (f ω+g ω)^2) =
      (fun ω => (f ω)^2+(g ω)^2+2*(f ω*g ω)) := by funext ω; ring
  simp only [FiniteLaw.variance, FiniteLaw.cov, he, mean_add, mean_const_mul]
  ring

private lemma cvo_cov_transfer (P : FiniteLaw Ω)
    (G F : (n : ℕ) → (Fin n → Ω) → ℝ) (a b : ℝ) (u v : Ω → ℝ)
    (hu : P.mean u=0) (hv : P.mean v=0)
    (hG : MB P 2 (fun n s => G n s-a-avg u n s))
    (hF : MB P 2 (fun n s => F n s-b-avg v n s)) :
    Tendsto (fun n : ℕ => (n : ℝ)*(P.iid n).cov (G n) (F n)) atTop (nhds (P.cov u v)) := by
  have hsum : MB P 2 (fun n s => G n s+F n s-(a+b)-avg (fun ω => u ω+v ω) n s) := by
    have hh := GP019B2b_t18_bound_add P 2 2 (by norm_num)
      GP019B2b_t18_square_add hG hF
    convert hh using 1
    funext n s
    rw [GP019B2b_t18_avg_add]
    ring
  have hsum0 : P.mean (fun ω => u ω+v ω)=0 := by rw [mean_add,hu,hv]; ring
  have h1 := GP019B2b_t18_variance_transfer P G a u (P.variance u) hu rfl hG
  have h2 := GP019B2b_t18_variance_transfer P F b v (P.variance v) hv rfl hF
  have h3 := GP019B2b_t18_variance_transfer P (fun n s => G n s+F n s) (a+b)
    (fun ω => u ω+v ω) (P.variance (fun ω => u ω+v ω)) hsum0 rfl hsum
  have h := ((h3.sub h1).sub h2).div_const 2
  rw [cvo_cov_add] at h
  have he : (P.variance u+P.variance v+2*P.cov u v-P.variance u-P.variance v)/2 =
      P.cov u v := by ring
  rw [he] at h
  convert h using 1
  funext n
  rw [cvo_cov_add]
  ring

private lemma cvo_abs_mean (P : FiniteLaw Ω) (f : Ω → ℝ) :
    |P.mean f| ≤ P.mean (fun ω => |f ω|) := by
  unfold FiniteLaw.mean
  calc
    _ ≤ ∑ ω, |P.mass ω*f ω| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp only [abs_mul, abs_of_nonneg (P.nonneg _)]

private lemma cvo_mean_bound (P : FiniteLaw Ω) (f : Ω → ℝ) (B : ℝ)
    (hf : ∀ ω, |f ω| ≤ B) : |P.mean f| ≤ B := by
  calc
    _ ≤ P.mean (fun ω => |f ω|) := cvo_abs_mean P f
    _ ≤ P.mean (fun _ => B) := GP019B2b_t18_mean_mono P hf
    _ = B := mean_const P B

private def cvo_condition (P : FiniteLaw Ω) (D : Ω → Prop) (hd : 0 < P.prob D) : FiniteLaw Ω where
  mass := fun ω => P.mass ω*(if D ω then 1 else 0)/P.prob D
  nonneg := fun ω => div_nonneg (mul_nonneg (P.nonneg ω) (by split_ifs <;> norm_num)) hd.le
  total := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hd)

private lemma cvo_condition_mean (P : FiniteLaw Ω) (D : Ω → Prop) (hd : 0 < P.prob D)
    (f : Ω → ℝ) : (cvo_condition P D hd).mean f=P.ce f D := by
  simp only [FiniteLaw.mean, cvo_condition, FiniteLaw.ce]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

private lemma cvo_ce_bound (P : FiniteLaw Ω) (D : Ω → Prop) (hd : 0 < P.prob D)
    (f : Ω → ℝ) (B : ℝ) (hf : ∀ ω, |f ω| ≤ B) : |P.ce f D| ≤ B := by
  rw [← cvo_condition_mean P D hd f]
  exact cvo_mean_bound _ f B hf

private lemma cvo_ce_error (P : FiniteLaw Ω) (D : Ω → Prop) (hd : 1/2 ≤ P.prob D)
    (f : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ ω, |f ω| ≤ B) :
    |P.ce f D-P.mean f| ≤ 4*B*(1-P.prob D) := by
  let d := P.prob D
  let e := 1-d
  have hd0 : 0 < d := by dsimp [d]; linarith
  have he0 : 0 ≤ e := sub_nonneg.mpr (cvo_prob_bounds P D).2
  let off := P.mean (fun ω => if ¬ D ω then f ω else 0)
  have hoff : |off| ≤ B*e := by
    calc
      _ ≤ P.mean (fun ω => |if ¬ D ω then f ω else 0|) := cvo_abs_mean _ _
      _ ≤ P.mean (fun ω => B*(if ¬ D ω then 1 else 0)) := by
        apply GP019B2b_t18_mean_mono
        intro ω
        by_cases hω : D ω <;> simp [hω, hf ω]
      _ = B*e := by rw [mean_const_mul]; change B*P.prob (fun ω => ¬ D ω)=B*e
                    rw [probability_complement]
  have hsplit : P.mean (fun ω => if D ω then f ω else 0)=P.mean f-off := by
    rw [← mean_sub]
    congr 1
    funext ω
    by_cases hω : D ω <;> simp [off, hω]
  have heq : P.ce f D-P.mean f=(e*P.mean f-off)/d := by
    rw [FiniteLaw.ce,hsplit]
    dsimp only [e]
    field_simp [ne_of_gt hd0]
    ring
  rw [heq,abs_div,abs_of_pos hd0]
  apply (div_le_iff₀ hd0).2
  have h1 : |e*P.mean f-off| ≤ e*B+B*e := by
    calc
      _ ≤ |e*P.mean f|+|off| := abs_sub _ _
      _ ≤ e*B+B*e := by
        rw [abs_mul,abs_of_nonneg he0]
        exact add_le_add (mul_le_mul_of_nonneg_left (cvo_mean_bound P f B hf) he0) hoff
  have hd' : 1/2 ≤ d := hd
  nlinarith [mul_nonneg hB he0]

private lemma cvo_ccov_error (P : FiniteLaw Ω) (D : Ω → Prop) (hd : 1/2 ≤ P.prob D)
    (f g : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ ω, |f ω| ≤ 1) (hg : ∀ ω, |g ω| ≤ B) :
    |P.ccov f g D-P.cov f g| ≤ 12*B*(1-P.prob D) := by
  have hd0 : 0 < P.prob D := by linarith
  have he0 : 0 ≤ 1-P.prob D := sub_nonneg.mpr (cvo_prob_bounds P D).2
  have hfg (ω : Ω) : |f ω*g ω| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (hf ω) (hg ω) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have h1 := cvo_ce_error P D hd (fun ω => f ω*g ω) B hB hfg
  have h2 := cvo_ce_error P D hd f 1 (by norm_num) hf
  have h3 := cvo_ce_error P D hd g B hB hg
  have hcf := cvo_ce_bound P D hd0 f 1 hf
  have hmg := cvo_mean_bound P g B hg
  have heq : P.ccov f g D-P.cov f g =
      (P.ce (fun ω => f ω*g ω) D-P.mean (fun ω => f ω*g ω))-
        (P.ce f D*(P.ce g D-P.mean g)+(P.ce f D-P.mean f)*P.mean g) := by
    unfold FiniteLaw.ccov FiniteLaw.cov
    ring
  rw [heq]
  calc
    _ ≤ |P.ce (fun ω => f ω*g ω) D-P.mean (fun ω => f ω*g ω)|+
        (|P.ce f D| *|P.ce g D-P.mean g|+|P.ce f D-P.mean f| *|P.mean g|) := by
      apply (abs_sub _ _).trans
      gcongr
      simpa only [abs_mul] using abs_add_le
        (P.ce f D*(P.ce g D-P.mean g)) ((P.ce f D-P.mean f)*P.mean g)
    _ ≤ 4*B*(1-P.prob D)+(1*(4*B*(1-P.prob D))+(4*1*(1-P.prob D))*B) := by
      gcongr
    _ = _ := by ring

private lemma cvo_condition_transfer (P : FiniteLaw Ω)
    (G F : (n : ℕ) → (Fin n → Ω) → ℝ) (D : (n : ℕ) → (Fin n → Ω) → Prop)
    (C L : ℝ) (hC : 0 ≤ C)
    (hG : ∀ n s, |G n s| ≤ 1) (hF : ∀ n, 0 < n → ∀ s, |F n s| ≤ C*(n : ℝ))
    (hD : Tendsto (fun n : ℕ => (n : ℝ)^2*(1-(P.iid n).prob (D n))) atTop (nhds 0))
    (hcov : Tendsto (fun n : ℕ => (n : ℝ)*(P.iid n).cov (G n) (F n)) atTop (nhds L)) :
    Tendsto (fun n : ℕ => (n : ℝ)*(P.iid n).ccov (G n) (F n) (D n)) atTop (nhds L) := by
  have he0 (n : ℕ) : 0 ≤ 1-(P.iid n).prob (D n) :=
    sub_nonneg.mpr (cvo_prob_bounds _ _).2
  have he : Tendsto (fun n : ℕ => 1-(P.iid n).prob (D n)) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall he0) _ hD
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn2 : (1 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hn2 (he0 n)]
  have hdlim : Tendsto (fun n : ℕ => (P.iid n).prob (D n)) atTop (nhds 1) := by
    simpa only [sub_zero, sub_sub_cancel] using (tendsto_const_nhds (x := (1 : ℝ))).sub he
  have hd : ∀ᶠ n : ℕ in atTop, 1/2 ≤ (P.iid n).prob (D n) :=
    ((tendsto_order.1 hdlim).1 (1/2) (by norm_num)).mono (fun _ h => h.le)
  have herr : Tendsto (fun n : ℕ => (n : ℝ)*
      ((P.iid n).ccov (G n) (F n) (D n)-(P.iid n).cov (G n) (F n))) atTop (nhds 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      (g := fun n : ℕ => (12*C)*((n : ℝ)^2*(1-(P.iid n).prob (D n))))
    · filter_upwards [hd,eventually_ge_atTop 1] with n hdn hn
      have hh := cvo_ccov_error (P.iid n) (D n) hdn (G n) (F n) (C*(n : ℝ))
        (by positivity) (hG n) (hF n (by omega))
      rw [abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
      have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg n)
      nlinarith only [hh']
    · simpa using hD.const_mul (12*C)
  have h := hcov.add herr
  simpa only [add_zero] using h.congr (fun n => by ring)

private lemma cvo_centered (P : FiniteLaw Ω) (D : Ω → Prop) :
    P.mean (fun ω => cvo_indicator D ω-P.prob D)=0 := by
  rw [mean_sub,mean_const]
  change P.prob D-P.prob D=0
  ring

private lemma cvo_nested_cov (P : FiniteLaw Ω) (D E : Ω → Prop)
    (hDE : ∀ ω, D ω → E ω) :
    P.mean (fun ω => (cvo_indicator E ω-P.prob E)*(cvo_indicator D ω-P.prob D)) =
      P.prob D*(1-P.prob E) := by
  have he : (fun ω => (cvo_indicator E ω-P.prob E)*(cvo_indicator D ω-P.prob D)) =
      (fun ω => cvo_indicator D ω*(1-P.prob E)-cvo_indicator E ω*P.prob D+
        P.prob E*P.prob D) := by
    funext ω
    by_cases hd : D ω
    · have he := hDE ω hd
      simp [cvo_indicator,hd,he]
      ring
    · by_cases he : E ω <;> simp [cvo_indicator,hd,he] <;> ring
  rw [he,mean_add,mean_sub,mean_mul_const,mean_mul_const,mean_const]
  change P.prob D*(1-P.prob E)-P.prob E*P.prob D+P.prob E*P.prob D = _
  ring

private lemma cvo_square_remainder (P : FiniteLaw Ω) (D : Ω → Prop) :
    MB P 2 (fun n s => (avg (cvo_indicator D) n s)^2-(P.prob D)^2-
      avg (fun ω => 2*P.prob D*(cvo_indicator D ω-P.prob D)) n s) := by
  obtain ⟨C,hC,hh⟩ := GP019B2b_t18_fourth_average P
    (fun ω => cvo_indicator D ω-P.prob D) (cvo_centered P D)
  refine ⟨C,hC,fun n hn => ?_⟩
  convert hh n hn using 1
  congr 1
  funext s
  dsimp only
  rw [GP019B2b_t18_avg_const_mul,GP019B2b_t18_avg_center _ _ n hn s]
  ring

private lemma cvo_reciprocal_sum_remainder (P : FiniteLaw Ω) (D E : Ω → Prop)
    (hD : 0 < P.prob D) (hE : 0 < P.prob E) (a b : ℝ) :
    MB P 2 (fun n s => a*(avg (cvo_indicator D) n s)⁻¹+b*(avg (cvo_indicator E) n s)⁻¹-
      (a/P.prob D+b/P.prob E)-avg
        (fun ω => (-a/(P.prob D)^2)*(cvo_indicator D ω-P.prob D)+
          (-b/(P.prob E)^2)*(cvo_indicator E ω-P.prob E)) n s) := by
  have h1 := GP019B2b_t18_bound_scale P 2 a (sq_nonneg a) (cvo_inv_remainder P D hD)
  have h2 := GP019B2b_t18_bound_scale P 2 b (sq_nonneg b) (cvo_inv_remainder P E hE)
  have hh := GP019B2b_t18_bound_add P 2 2 (by norm_num)
    GP019B2b_t18_square_add h1 h2
  convert hh using 1
  funext n s
  simp only [GP019B2b_t18_avg_add,GP019B2b_t18_avg_const_mul]
  ring

private lemma cvo_occupied_tail (S : Study Ω) (hs : S.standing) :
    Tendsto (fun n : ℕ => (n : ℝ)^2*(1-(S.law.iid n).prob S.occupied)) atTop (nhds 0) := by
  have hp (z : Bool) : 0 < S.law.prob (S.cell z false) := (hs.2.2.2.1 z false).1
  have ht (z : Bool) (n : ℕ) : (S.law.iid n).prob (fun s => S.cellCount s z false=0) ≤
      Real.exp (-S.law.prob (S.cell z false)*(n : ℝ)) := by
    rw [empty_cell_probability]
    have h0 : 0 ≤ 1-S.law.prob (S.cell z false) := sub_nonneg.mpr (cvo_prob_bounds _ _).2
    have h1 : 1-S.law.prob (S.cell z false) ≤ Real.exp (-S.law.prob (S.cell z false)) := by
      have hh := Real.add_one_le_exp (-S.law.prob (S.cell z false)); linarith
    have hh := pow_le_pow_left₀ h0 h1 n
    convert hh using 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hb (n : ℕ) : 1-(S.law.iid n).prob S.occupied ≤
      Real.exp (-S.law.prob (S.cell true false)*(n : ℝ))+
      Real.exp (-S.law.prob (S.cell false false)*(n : ℝ)) := by
    have hunion : (S.law.iid n).prob (fun s => ¬ S.occupied s) ≤
        (S.law.iid n).prob (fun s => S.cellCount s true false=0)+
        (S.law.iid n).prob (fun s => S.cellCount s false false=0) := by
      rw [FiniteLaw.prob,FiniteLaw.prob,FiniteLaw.prob,← mean_add]
      apply GP019B2b_t18_mean_mono
      intro s
      by_cases h1 : S.cellCount s true false=0 <;>
        by_cases h0 : S.cellCount s false false=0 <;>
        simp [Study.occupied,Nat.pos_iff_ne_zero,h1,h0]
    rw [probability_complement] at hunion
    exact hunion.trans (add_le_add (ht true n) (ht false n))
  apply squeeze_zero (fun n => mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (cvo_prob_bounds _ _).2))
    (fun n => mul_le_mul_of_nonneg_left (hb n) (sq_nonneg _))
  have h := (cvo_exp_limit _ (hp true) 2).add (cvo_exp_limit _ (hp false) 2)
  simpa only [add_zero, mul_add] using h

private lemma cvo_ccov_scale (P : FiniteLaw Ω) (f g : Ω → ℝ) (a : ℝ) (D : Ω → Prop) :
    P.ccov f (fun ω => g ω*a) D=P.ccov f g D*a := by
  have he : (fun ω => f ω*(g ω*a))=(fun ω => (f ω*g ω)*a) := by funext ω; ring
  simp only [FiniteLaw.ccov,he,ce_mul_const]
  ring

theorem corrected_covariance_order_proof (S : Study Ω) (hs : S.standing) :
    let R := fun n : ℕ => (S.law.iid n).ccov
      (fun s => (S.sampleA s)^2) (fun s => S.sampleH s) (fun s => S.occupied s)
    Asymptotics.IsBigO atTop R (fun n : ℕ => (1/(n : ℝ))^2) ∧
    Tendsto (fun n : ℕ => (n : ℝ)^2 * R n) atTop
      (nhds (-2 * (S.mu * S.truthRate) *
        (S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell true false) / S.gamma +
         S.law.cv (fun ω => (S.V ω : ℝ)) (S.cell false false) / (1-S.gamma)))) := by
  let D := S.cell true false
  let E := S.cell false false
  let N := fun ω => S.Y ω=false
  let α := S.law.prob D
  let β := S.law.prob E
  let q := S.law.mean (cvo_indicator N)
  let s1 := S.law.cv (fun ω => (S.V ω : ℝ)) D
  let s0 := S.law.cv (fun ω => (S.V ω : ℝ)) E
  let G := fun n s => (avg (cvo_indicator N) n s)^2
  let F := fun n s => s1*(avg (cvo_indicator D) n s)⁻¹+s0*(avg (cvo_indicator E) n s)⁻¹
  let u := fun ω => 2*q*(cvo_indicator N ω-q)
  let v := fun ω => (-s1/α^2)*(cvo_indicator D ω-α)+(-s0/β^2)*(cvo_indicator E ω-β)
  let R := fun n : ℕ => (S.law.iid n).ccov
    (fun s => (S.sampleA s)^2) (fun s => S.sampleH s) (fun s => S.occupied s)
  let L := -2*(S.mu*S.truthRate)*(s1/S.gamma+s0/(1-S.gamma))
  change Asymptotics.IsBigO atTop R (fun n : ℕ => (1/(n : ℝ))^2) ∧
    Tendsto (fun n : ℕ => (n : ℝ)^2*R n) atTop (nhds L)
  have hα : 0 < α := (hs.2.2.2.1 true false).1
  have hβ : 0 < β := (hs.2.2.2.1 false false).1
  have hs1 : 0 ≤ s1 := (hs.2.2.2.1 true false).2.le
  have hs0 : 0 ≤ s0 := (hs.2.2.2.1 false false).2.le
  have hqresp : q=S.law.prob (fun ω => S.Y ω=false) := by
    dsimp only [q]
    unfold FiniteLaw.prob
    congr 1
    funext ω
    by_cases h : S.Y ω=false <;> simp [cvo_indicator,N,h]
  have hq : 0 < q := by
    rw [hqresp]
    exact (regularity_probabilities S hs.2.2.2).2 false
  have hγ : S.gamma ≠ 0 := ne_of_gt ((regularity_probabilities S hs.2.2.2).1 true)
  have hγ0 : 1-S.gamma ≠ 0 := by
    have h := ne_of_gt ((regularity_probabilities S hs.2.2.2).1 false)
    rw [prob_false] at h
    exact h
  have ha : α=q*S.gamma := by
    change S.law.prob (S.cell true false)=q*S.gamma
    rw [cell_probability S hs.2.2.1,hqresp]
    exact mul_comm _ _
  have hb : β=q*(1-S.gamma) := by
    change S.law.prob (S.cell false false)=q*(1-S.gamma)
    rw [cell_probability S hs.2.2.1,prob_false,hqresp]
    exact mul_comm _ _
  have hu : S.law.mean u=0 := by
    dsimp only [u]
    rw [mean_const_mul,mean_sub,mean_const]
    change 2*q*(q-q)=0
    ring
  have hv : S.law.mean v=0 := by
    dsimp only [v]
    rw [mean_add,mean_const_mul,mean_const_mul,cvo_centered,cvo_centered]
    ring
  have hRG : MB S.law 2 (fun n s => G n s-q^2-avg u n s) := cvo_square_remainder S.law N
  have hRF : MB S.law 2 (fun n s => F n s-(s1/α+s0/β)-avg v n s) :=
    cvo_reciprocal_sum_remainder S.law D E hα hβ s1 s0
  have hcov := cvo_cov_transfer S.law G F (q^2) (s1/α+s0/β) u v hu hv hRG hRF
  have hG (n : ℕ) (s : Fin n → Ω) : |G n s| ≤ 1 := by
    dsimp only [G]
    rw [abs_of_nonneg (sq_nonneg _)]
    have hh := cvo_avg_bounds N n s
    nlinarith
  have hF (n : ℕ) (hn : 0 < n) (s : Fin n → Ω) : |F n s| ≤ (s1+s0)*(n : ℝ) := by
    have h1 := cvo_inv_bound D n hn s
    have h0 := cvo_inv_bound E n hn s
    have hnon : 0 ≤ F n s := add_nonneg (mul_nonneg hs1 h1.1) (mul_nonneg hs0 h0.1)
    rw [abs_of_nonneg hnon]
    dsimp only [F]
    nlinarith [mul_le_mul_of_nonneg_left h1.2 hs1,mul_le_mul_of_nonneg_left h0.2 hs0]
  have hc : S.law.cov u v=L := by
    have h1 := cvo_nested_cov S.law D N (fun _ h => h.2)
    have h0 := cvo_nested_cov S.law E N (fun _ h => h.2)
    change S.law.mean (fun ω => (cvo_indicator N ω-q)*(cvo_indicator D ω-α))=α*(1-q) at h1
    change S.law.mean (fun ω => (cvo_indicator N ω-q)*(cvo_indicator E ω-β))=β*(1-q) at h0
    have he : (fun ω => u ω*v ω) = (fun ω =>
        (2*q*(-s1/α^2))*((cvo_indicator N ω-q)*(cvo_indicator D ω-α))+
        (2*q*(-s0/β^2))*((cvo_indicator N ω-q)*(cvo_indicator E ω-β))) := by
      funext ω
      dsimp only [u,v]
      ring
    rw [FiniteLaw.cov,hu,hv,zero_mul,sub_zero,he,mean_add,mean_const_mul,mean_const_mul,h1,h0]
    have hr : 1-q=S.mu*S.truthRate := by
      rw [hqresp,prob_false]
      have h := direct_response_probability S hs.1 hs.2.2.2
      linarith
    change (2*q*(-s1/α^2))*(α*(1-q))+(2*q*(-s0/β^2))*(β*(1-q))=L
    dsimp only [L]
    rw [← hr,ha,hb]
    field_simp [ne_of_gt hq,hγ,hγ0]
    ring
  have hcond := cvo_condition_transfer S.law G F (fun _ s => S.occupied s)
    (s1+s0) (S.law.cov u v) (add_nonneg hs1 hs0) hG hF (cvo_occupied_tail S hs) hcov
  rw [hc] at hcond
  have hident : ∀ᶠ n : ℕ in atTop,
      (n : ℝ)*(S.law.iid n).ccov (G n) (F n) S.occupied = (n : ℝ)^2*R n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    have hGn : G n=(fun s => (S.sampleA s)^2) := by
      funext s
      have he : cvo_indicator N=(fun ω => 1-bitVal (S.Y ω)) := by
        funext ω
        cases hy : S.Y ω <;> simp [cvo_indicator,N,bitVal,hy]
      dsimp [G,Study.sampleA,Study.ybar,GP019B2b_t18_avg]
      rw [he,Finset.sum_sub_distrib]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
      field_simp [hn0]
    have hFn : F n=(fun s => S.sampleH s*(n : ℝ)) := by
      funext s
      have hcount (z : Bool) : avg (cvo_indicator (S.cell z false)) n s =
          (S.cellCount s z false : ℝ)/(n : ℝ) := by
        simp only [GP019B2b_t18_avg,cvo_indicator,Study.cellCount,Nat.cast_sum,Nat.cast_ite,
          Nat.cast_one,Nat.cast_zero]
      dsimp only [F,D,E]
      rw [hcount true,hcount false,inv_div,inv_div]
      dsimp only [Study.sampleH,s1,s0,D,E]
      ring
    rw [hGn,hFn,cvo_ccov_scale]
    dsimp only [R]
    ring
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)^2*R n) atTop (nhds L) :=
    hcond.congr' hident
  refine ⟨?_,hlim⟩
  have hbnd : ∀ᶠ n : ℕ in atTop, |(n : ℝ)^2*R n| < |L|+1 :=
    (tendsto_order.1 hlim.abs).2 (|L|+1) (by linarith)
  apply Asymptotics.IsBigO.of_bound (|L|+1)
  filter_upwards [hbnd,eventually_ge_atTop 1] with n hh hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  change |R n| ≤ (|L|+1)*|(1/(n : ℝ))^2|
  rw [abs_of_nonneg (by positivity : 0 ≤ (1/(n : ℝ))^2),div_pow,one_pow,mul_one_div]
  apply (le_div_iff₀ (sq_pos_of_pos hn0)).2
  rw [abs_mul,abs_of_nonneg (sq_nonneg (n : ℝ))] at hh
  nlinarith only [hh]


end
end AronowAudit.P019.Wave1
