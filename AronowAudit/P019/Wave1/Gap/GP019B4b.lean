import AronowAudit.P019.P019_Audit
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
Exact finite-product counterexample.
The finite partition arguments below retain null fibres.
-/

namespace AronowAudit.P019.Wave1

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open scoped BigOperators
open Filter MeasureTheory ProbabilityTheory
noncomputable section
open Classical

variable {Ω : Type*} [Fintype Ω]

/- Helpers for finite conditional means and product variances. -/

private theorem GP019B4b_ce_sub (P : FiniteLaw Ω) (f g : Ω → ℝ)
    (D : Ω → Prop) [DecidablePred D] :
    P.ce (fun s => f s - g s) D = P.ce f D - P.ce g D := by
  unfold FiniteLaw.ce
  have he : (fun s => if D s then f s-g s else 0) =
      (fun s => (if D s then f s else 0)-(if D s then g s else 0)) := by
    funext s; split_ifs <;> simp
  rw [he, mean_sub, sub_div]

private theorem GP019B4b_ce_sum {ι : Type*} [Fintype ι] (P : FiniteLaw Ω)
    (f : ι → Ω → ℝ) (D : Ω → Prop) [DecidablePred D] :
    P.ce (fun s => ∑ i, f i s) D = ∑ i, P.ce (f i) D := by
  unfold FiniteLaw.ce
  have he : (fun s => if D s then ∑ i, f i s else 0) =
      (fun s => ∑ i, if D s then f i s else 0) := by
    funext s; by_cases hd : D s <;> simp [hd]
  rw [he, mean_sum, Finset.sum_div]

private theorem GP019B4b_ce_div (P : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ)
    (D : Ω → Prop) [DecidablePred D] :
    P.ce (fun s => f s/c) D = P.ce f D/c := by
  simpa only [div_eq_mul_inv] using ce_mul_const P f c⁻¹ D

private theorem GP019B4b_ce_left (P : FiniteLaw Ω) (c : ℝ) (f : Ω → ℝ)
    (D : Ω → Prop) [DecidablePred D] :
    P.ce (fun s => c*f s) D = c*P.ce f D := by
  simpa only [mul_comm c] using ce_mul_const P f c D

private theorem GP019B4b_atom_le (P : FiniteLaw Ω) (D : Ω → Prop)
    [DecidablePred D] (s : Ω) (hs : D s) : P.mass s ≤ P.prob D := by
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset Ω)) (f := fun t => P.mass t * if D t then (1 : ℝ) else 0)
    (fun t _ => mul_nonneg (P.nonneg t) (by split_ifs <;> norm_num))
    (Finset.mem_univ s)
  simpa only [FiniteLaw.prob, FiniteLaw.mean, if_pos hs, mul_one] using h

private theorem GP019B4b_null_mean (P : FiniteLaw Ω) (D : Ω → Prop)
    [DecidablePred D] (hD : P.prob D = 0) (f : Ω → ℝ) :
    P.mean (fun s => if D s then f s else 0) = 0 := by
  rw [mean_congr_support P _ (fun _ => 0) ?_, mean_const]
  intro s hp
  have hn : ¬ D s := by
    intro hs; have h := GP019B4b_atom_le P D s hs; rw [hD] at h; linarith
  simp only [if_neg hn]

private theorem GP019B4b_partition {Λ : Type*} [Fintype Λ] (P : FiniteLaw Ω)
    (L : Ω → Λ) (f : Ω → ℝ) :
    P.mean f = ∑ l, P.mean (fun s => if L s=l then f s else 0) := by
  rw [← mean_sum]
  congr 1
  funext s
  simp

/-- Finite tower, expressed as transfer of two conditional means.
The label type indexes distinct fibres rather than sample representatives. -/
private theorem GP019B4b_transfer {Λ : Type*} [Fintype Λ] (P : FiniteLaw Ω)
    (L : Ω → Λ) (D : Ω → Prop) [DecidablePred D] (f g : Ω → ℝ)
    (hD : ∀ s t, L t=L s → (D t ↔ D s))
    (hfg : ∀ s, D s → P.prob (fun t => L t=L s) ≠ 0 →
      P.ce f (fun t => L t=L s) = P.ce g (fun t => L t=L s)) :
    P.ce f D = P.ce g D := by
  unfold FiniteLaw.ce
  congr 1
  rw [GP019B4b_partition P L (fun s => if D s then f s else 0),
    GP019B4b_partition P L (fun s => if D s then g s else 0)]
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
    · rw [GP019B4b_null_mean P _ hp f, GP019B4b_null_mean P _ hp g]
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

private def GP019B4b_label (S : Study Ω) {n : ℕ} (s : Fin n → Ω) : Fin n → Bool × Bool :=
  fun i => (S.Y (s i), S.Z (s i))

private theorem GP019B4b_fibre (S : Study Ω) {n : ℕ} (s t : Fin n → Ω) :
    GP019B4b_label S t = GP019B4b_label S s ↔ S.patternFibre s t := by
  simp only [GP019B4b_label, funext_iff, Prod.mk.injEq, Study.patternFibre]

private theorem GP019B4b_invariants (S : Study Ω) {n : ℕ} (s t : Fin n → Ω)
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

private theorem GP019B4b_pattern_transfer (S : Study Ω) (n : ℕ)
    (D : (Fin n → Ω) → Prop) [DecidablePred D]
    (f g : (Fin n → Ω) → ℝ)
    (hD : ∀ s t, S.patternFibre s t → (D t ↔ D s))
    (hfg : ∀ s, D s → (S.law.iid n).prob (S.patternFibre s) ≠ 0 →
      (S.law.iid n).ce f (S.patternFibre s) =
        (S.law.iid n).ce g (S.patternFibre s)) :
    (S.law.iid n).ce f D = (S.law.iid n).ce g D := by
  apply GP019B4b_transfer (S.law.iid n) (GP019B4b_label S) D f g
  · intro s t h; exact hD s t ((GP019B4b_fibre S s t).1 h)
  · intro s hd hp
    simpa only [GP019B4b_fibre] using hfg s hd (by simpa only [GP019B4b_fibre] using hp)

private theorem GP019B4b_coordinate (S : Study Ω) (hs : S.standing) (n : ℕ)
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

private theorem GP019B4b_pair (S : Study Ω) (hs : S.standing) (n : ℕ)
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

private theorem GP019B4b_cell_representation (S : Study Ω) {n : ℕ}
    (s t : Fin n → Ω) (hst : S.patternFibre s t) (z : Bool)
    (hz : 0 < S.cellCount s z false) (c : ℝ) :
    S.cellMean t z false c =
      (∑ i, if S.cell z false (s i) then (S.V (t i) : ℝ) else 0)/
        (S.cellCount s z false : ℝ) := by
  have hc := (GP019B4b_invariants S s t hst).1 z false
  unfold Study.cellMean
  rw [hc, if_neg (Nat.ne_of_gt hz)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Study.cell, (hst i).1, (hst i).2] <;> congr 1

private theorem GP019B4b_count_real (S : Study Ω) {n : ℕ} (s : Fin n → Ω) (z : Bool) :
    (∑ i, if S.cell z false (s i) then (1 : ℝ) else 0) =
      (S.cellCount s z false : ℝ) := by
  simp only [Study.cellCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private theorem GP019B4b_pattern_cell_mean (S : Study Ω) (hs : S.standing) (n : ℕ)
    (s : Fin n → Ω) (hF : (S.law.iid n).prob (S.patternFibre s) ≠ 0)
    (z : Bool) (hz : 0 < S.cellCount s z false) (c : ℝ) :
    (S.law.iid n).ce (fun t => S.cellMean t z false c) (S.patternFibre s) =
      S.listMean z false := by
  have hN : (S.cellCount s z false : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hz
  rw [ce_congr_support (S.law.iid n) _ _ (S.patternFibre s)
    (by intro t _ ht; exact GP019B4b_cell_representation S s t ht z hz c)]
  rw [GP019B4b_ce_div, GP019B4b_ce_sum]
  have hm (i : Fin n) :
      (S.law.iid n).ce (fun t => if S.cell z false (s i) then (S.V (t i) : ℝ) else 0)
        (S.patternFibre s) =
      (if S.cell z false (s i) then (1 : ℝ) else 0)*S.listMean z false := by
    by_cases hi : S.cell z false (s i)
    · rw [if_pos hi]
      have h := GP019B4b_coordinate S hs n s hF i (fun v => (v : ℝ))
      simpa only [hi.1, hi.2, Study.listMean, one_mul, if_pos hi] using h
    · simp [hi, ce_const, hF]
  simp_rw [hm]
  rw [← Finset.sum_mul, GP019B4b_count_real]
  field_simp [hN]

private theorem GP019B4b_pattern_cell_product (S : Study Ω) (hs : S.standing) (n : ℕ)
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
          have hcoord := GP019B4b_coordinate S hs n s hF i (fun v => (v : ℝ)^2)
          have hsecond : S.law.ce (fun ω => (S.V ω : ℝ)^2) (S.cell z false) =
              vz+mz^2 := by dsimp [vz, mz, Study.listMean, FiniteLaw.cv]; ring
          have hc2 : (S.law.iid n).ce (fun t => (S.V (t i) : ℝ)^2)
              (S.patternFibre s) = vz+mz^2 := by
            simpa only [hi.1, hi.2, hsecond] using hcoord
          simpa [U, V, az, aw, hi, pow_two, mz, mw, add_comm] using hc2
        · have hpair := GP019B4b_pair S hs n s hF i j hij (fun v => (v : ℝ)) (fun v => (v : ℝ))
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
        rw [GP019B4b_cell_representation S s t ht z hz cz,
          GP019B4b_cell_representation S s t ht w hw cw]
        change (∑ i, U i t)/N*((∑ j, V j t)/M) =
          (∑ i, ∑ j, U i t*V j t)/(N*M)
        rw [← Finset.sum_mul_sum]
        <;> ring
      _ = _ := by
        rw [GP019B4b_ce_div, GP019B4b_ce_sum]
        simp_rw [GP019B4b_ce_sum]
  rw [hrep]
  simp_rw [hp, Finset.sum_add_distrib]
  have haz : ∑ i, az i=N := GP019B4b_count_real S s z
  have haw : ∑ i, aw i=M := GP019B4b_count_real S s w
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

private theorem GP019B4b_pattern_contrast (S : Study Ω) (hs : S.standing) (n : ℕ)
    (s : Fin n → Ω) (hd : S.occupied s)
    (hF : (S.law.iid n).prob (S.patternFibre s) ≠ 0) (c1 c0 : ℝ) :
    (S.law.iid n).ce (fun t => S.sampleB t c1 c0) (S.patternFibre s) =
      S.listMean true false-S.listMean false false-1 ∧
    (S.law.iid n).ce (fun t => (S.sampleB t c1 c0)^2) (S.patternFibre s) =
      (S.listMean true false-S.listMean false false-1)^2+S.sampleH s := by
  let P := S.law.iid n
  let F := S.patternFibre s
  let M1 := fun t : Fin n → Ω => S.cellMean t true false c1
  let M0 := fun t : Fin n → Ω => S.cellMean t false false c0
  have hm1 : P.ce M1 F=S.listMean true false :=
    GP019B4b_pattern_cell_mean S hs n s hF true hd.1 c1
  have hm0 : P.ce M0 F=S.listMean false false :=
    GP019B4b_pattern_cell_mean S hs n s hF false hd.2 c0
  have h11 := GP019B4b_pattern_cell_product S hs n s hF true true hd.1 hd.1 c1 c1
  have h00 := GP019B4b_pattern_cell_product S hs n s hF false false hd.2 hd.2 c0 c0
  have h10 := GP019B4b_pattern_cell_product S hs n s hF true false hd.1 hd.2 c1 c0
  simp only [if_true, Bool.true_eq_false, if_false, add_zero] at h11 h00 h10
  have hmean : P.ce (fun t => S.sampleB t c1 c0) F =
      S.listMean true false-S.listMean false false-1 := by
    change P.ce (fun t => (M1 t-M0 t)-1) F = _
    rw [GP019B4b_ce_sub, GP019B4b_ce_sub, hm1, hm0, ce_const P 1 F hF]
  refine ⟨hmean, ?_⟩
  have he : (fun t => (S.sampleB t c1 c0)^2) =
      (fun t => M1 t*M1 t+M0 t*M0 t-(M1 t*M0 t)*2-M1 t*2+M0 t*2+1) := by
    funext t; dsimp [Study.sampleB, M1, M0]; ring
  rw [he]
  simp only [ce_add, GP019B4b_ce_sub, ce_mul_const]
  rw [hm1, hm0, ce_const P 1 F hF]
  change P.ce (fun t => M1 t*M1 t) F + P.ce (fun t => M0 t*M0 t) F -
    P.ce (fun t => M1 t*M0 t) F*2-S.listMean true false*2+S.listMean false false*2+1 = _
  rw [h11, h00, h10]
  dsimp [Study.sampleH]; ring

private theorem GP019B4b_positive_atom (P : FiniteLaw Ω) (D : Ω → Prop)
    [DecidablePred D] (hp : 0 < P.prob D) : ∃ s, 0 < P.mass s ∧ D s := by
  by_contra hn
  have hz : P.prob D=0 := by
    unfold FiniteLaw.prob
    rw [mean_congr_support P _ (fun _ => 0) ?_, mean_const]
    intro s hs
    have hd : ¬ D s := by intro hd; exact hn ⟨s, hs, hd⟩
    simp [hd]
  linarith

private theorem GP019B4b_occupied_positive (S : Study Ω) (hs : S.standing)
    (n : ℕ) (hn : 2 ≤ n) : 0 < (S.law.iid n).prob S.occupied := by
  obtain ⟨u, hu, huc⟩ := GP019B4b_positive_atom S.law (S.cell true false)
    (hs.2.2.2.1 true false).1
  obtain ⟨v, hv, hvc⟩ := GP019B4b_positive_atom S.law (S.cell false false)
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
  exact lt_of_lt_of_le hp (GP019B4b_atom_le (S.law.iid n) S.occupied s hd)

private theorem GP019B4b_weighted_contrast (S : Study Ω) (hs : S.standing) (n : ℕ)
    (c1 c0 : ℝ) (w : (Fin n → Ω) → ℝ)
    (hw : ∀ s t, S.patternFibre s t → w t=w s) :
    let P := S.law.iid n
    let b := S.listMean true false-S.listMean false false-1
    P.ce (fun t => w t*S.sampleB t c1 c0) S.occupied =
      P.ce w S.occupied*b ∧
    P.ce (fun t => w t*(S.sampleB t c1 c0)^2) S.occupied =
      P.ce w S.occupied*b^2+P.ce (fun t => w t*S.sampleH t) S.occupied := by
  dsimp only
  let P := S.law.iid n
  let b := S.listMean true false-S.listMean false false-1
  have hd : ∀ s t : Fin n → Ω, S.patternFibre s t → (S.occupied t ↔ S.occupied s) :=
    fun s t h => (GP019B4b_invariants S s t h).2.2.2
  constructor
  · calc
      P.ce (fun t => w t*S.sampleB t c1 c0) S.occupied =
          P.ce (fun t => w t*b) S.occupied := by
        apply GP019B4b_pattern_transfer S n S.occupied _ _ hd
        intro s hsD hF
        have hm := (GP019B4b_pattern_contrast S hs n s hsD hF c1 c0).1
        have hl := ce_congr_support P (fun t => w t*S.sampleB t c1 c0)
          (fun t => w s*S.sampleB t c1 c0) (S.patternFibre s)
          (by intro t _ ht; rw [hw s t ht])
        have hr := ce_congr_support P (fun t => w t*b) (fun _ => w s*b)
          (S.patternFibre s) (by intro t _ ht; rw [hw s t ht])
        rw [hl, hr, GP019B4b_ce_left, hm, ce_const P _ _ hF]
      _ = P.ce w S.occupied*b := ce_mul_const P w b S.occupied
  · calc
      P.ce (fun t => w t*(S.sampleB t c1 c0)^2) S.occupied =
          P.ce (fun t => w t*(b^2+S.sampleH t)) S.occupied := by
        apply GP019B4b_pattern_transfer S n S.occupied _ _ hd
        intro s hsD hF
        have hm := (GP019B4b_pattern_contrast S hs n s hsD hF c1 c0).2
        have hl := ce_congr_support P (fun t => w t*(S.sampleB t c1 c0)^2)
          (fun t => w s*(S.sampleB t c1 c0)^2) (S.patternFibre s)
          (by intro t _ ht; rw [hw s t ht])
        have hr := ce_congr_support P (fun t => w t*(b^2+S.sampleH t))
          (fun _ => w s*(b^2+S.sampleH s)) (S.patternFibre s)
          (by intro t _ ht; rw [hw s t ht, (GP019B4b_invariants S s t ht).2.2.1])
        rw [hl, hr, GP019B4b_ce_left, hm, ce_const P _ _ hF]
      _ = P.ce w S.occupied*b^2+P.ce (fun t => w t*S.sampleH t) S.occupied := by
        simp only [mul_add, ce_add, ce_mul_const]

private theorem GP019B4b_occupied_cell_mean (S : Study Ω) (hs : S.standing)
    (n : ℕ) (hn : 2 ≤ n) (z : Bool) (c : ℝ) :
    (S.law.iid n).ce (fun t => S.cellMean t z false c) S.occupied =
      S.listMean z false := by
  let P := S.law.iid n
  have hp := ne_of_gt (GP019B4b_occupied_positive S hs n hn)
  rw [← ce_const P (S.listMean z false) S.occupied hp]
  apply GP019B4b_pattern_transfer S n S.occupied
  · intro s t h; exact (GP019B4b_invariants S s t h).2.2.2
  · intro s hd hF
    have hz : 0 < S.cellCount s z false := by cases z <;> [exact hd.2; exact hd.1]
    rw [GP019B4b_pattern_cell_mean S hs n s hF z hz c, ce_const P _ _ hF]

private theorem GP019B4b_cross_covariance (S : Study Ω) (hs : S.standing)
    (n : ℕ) (hn : 2 ≤ n) (c1 c0 : ℝ) :
    (S.law.iid n).ccov (fun t => S.cellMean t true false c1)
      (fun t => S.cellMean t false false c0) S.occupied = 0 := by
  let P := S.law.iid n
  have hp := ne_of_gt (GP019B4b_occupied_positive S hs n hn)
  have hm : P.ce (fun t => S.cellMean t true false c1*S.cellMean t false false c0)
      S.occupied = S.listMean true false*S.listMean false false := by
    rw [← ce_const P (S.listMean true false*S.listMean false false) S.occupied hp]
    apply GP019B4b_pattern_transfer S n S.occupied
    · intro s t h; exact (GP019B4b_invariants S s t h).2.2.2
    · intro s hd hF
      rw [GP019B4b_pattern_cell_product S hs n s hF true false hd.1 hd.2 c1 c0,
        ce_const P _ _ hF]
      simp
  unfold FiniteLaw.ccov
  rw [hm, GP019B4b_occupied_cell_mean S hs n hn true c1,
    GP019B4b_occupied_cell_mean S hs n hn false c0]
  ring

private theorem GP019B4b_product_moments (S : Study Ω) (hs : S.standing)
    (n : ℕ) (hn : 2 ≤ n) (c1 c0 : ℝ) :
    let P := S.law.iid n
    let A := @Study.sampleA Ω _ S n
    let B := fun s : Fin n → Ω => S.sampleB s c1 c0
    let h := @Study.sampleH Ω _ S n
    let b := S.listMean true false-S.listMean false false-1
    P.ce B S.occupied=b ∧ P.cv B S.occupied=P.ce h S.occupied ∧
    P.ce (fun s => A s*B s) S.occupied=P.ce A S.occupied*b ∧
    P.ce (fun s => (A s*B s)^2) S.occupied=
      P.ce (fun s => A s^2) S.occupied*b^2+P.ce (fun s => A s^2*h s) S.occupied := by
  dsimp only
  let P := S.law.iid n
  let b := S.listMean true false-S.listMean false false-1
  have hp := ne_of_gt (GP019B4b_occupied_positive S hs n hn)
  have h1 := GP019B4b_weighted_contrast S hs n c1 c0 (fun _ => 1) (by intros; rfl)
  dsimp only at h1
  simp only [one_mul, ce_const (S.law.iid n) 1 S.occupied hp] at h1
  norm_num only [one_mul] at h1
  have hA := GP019B4b_weighted_contrast S hs n c1 c0 S.sampleA
    (fun s t ht => (GP019B4b_invariants S s t ht).2.1)
  have hA2 := GP019B4b_weighted_contrast S hs n c1 c0 (fun t => (S.sampleA t)^2)
    (by intro s t ht; rw [(GP019B4b_invariants S s t ht).2.1])
  refine ⟨h1.1, ?_, hA.1, ?_⟩
  · unfold FiniteLaw.cv
    rw [h1.1, h1.2]; ring
  · simpa only [mul_pow] using hA2.2

private theorem GP019B4b_product_formula (S : Study Ω) (hs : S.standing)
    (n : ℕ) (hn : 2 ≤ n) (c1 c0 : ℝ) :
    let P := S.law.iid n
    let A := @Study.sampleA Ω _ S n
    let B := fun s : Fin n → Ω => S.sampleB s c1 c0
    let h := @Study.sampleH Ω _ S n
    let b := S.listMean true false-S.listMean false false-1
    P.cv (fun s => S.muHat s c1 c0) S.occupied =
      b^2*P.cv A S.occupied+P.ce (fun s => A s^2*h s) S.occupied ∧
    P.cv (fun s => A s*B s) S.occupied =
      b^2*P.cv A S.occupied+P.ce (fun s => A s^2*h s) S.occupied ∧
    P.cv (fun s => A s*B s) S.occupied -
      ((P.ce A S.occupied)^2*P.cv B S.occupied+
        P.cv A S.occupied*(P.ce B S.occupied)^2+
        P.cv A S.occupied*P.cv B S.occupied) =
      P.ccov (fun s => A s^2) h S.occupied := by
  dsimp only
  let P := S.law.iid n
  let A := @Study.sampleA Ω _ S n
  let B := fun s : Fin n → Ω => S.sampleB s c1 c0
  let h := @Study.sampleH Ω _ S n
  let b := S.listMean true false-S.listMean false false-1
  have hp := ne_of_gt (GP019B4b_occupied_positive S hs n hn)
  obtain ⟨hB, hvB, hAB, hAB2⟩ := GP019B4b_product_moments S hs n hn c1 c0
  have hv : P.cv (fun s => A s*B s) S.occupied =
      b^2*P.cv A S.occupied+P.ce (fun s => A s^2*h s) S.occupied := by
    unfold FiniteLaw.cv
    rw [hAB, hAB2]; ring
  have hmu : (fun s => S.muHat s c1 c0) = (fun s => A s*B s+1) := by
    funext s
    rw [estimator_product_identity]
    dsimp [A, B, Study.sampleA, Study.sampleB]; ring
  refine ⟨?_, hv, ?_⟩
  · rw [hmu, conditional_variance_shift P (fun s => A s*B s) S.occupied hp 1]
    exact hv
  · rw [hv, hB, hvB]
    unfold FiniteLaw.ccov FiniteLaw.cv
    ring

/-- Label transport for exact IID means, with an optional coordinate weight. -/
private theorem GP019B4b_iid_labels {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (P : FiniteLaw Ω)
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

private theorem GP019B4b_sum_cons {α : Type*} [Fintype α] (n : ℕ)
    (f : (Fin (n+1) → α) → ℝ) :
    (∑ s, f s) = ∑ a, ∑ t : Fin n → α, f (Fin.cons a t) := by
  simpa only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk] using
    ((Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp f).symm

private def GP019B4b_three (ω : Fin 16) : Fin 3 :=
  if finiteSampleWitness.Y ω then 2 else if finiteSampleWitness.Z ω then 0 else 1

private def GP019B4b_N (l : Fin 4 → Fin 3) (z : Fin 3) : ℕ :=
  ∑ i, if l i=z then 1 else 0

private def GP019B4b_D (l : Fin 4 → Fin 3) : Prop := 0 < GP019B4b_N l 0 ∧ 0 < GP019B4b_N l 1

private def GP019B4b_A (l : Fin 4 → Fin 3) : ℝ :=
  1-(GP019B4b_N l 2 : ℝ)/4

private def GP019B4b_H (l : Fin 4 → Fin 3) : ℝ :=
  (17/36 : ℝ)/(GP019B4b_N l 0 : ℝ)+(1/4 : ℝ)/(GP019B4b_N l 1 : ℝ)

private def GP019B4b_p (z : Fin 3) : ℝ := if z=2 then 1/4 else 3/8

private theorem GP019B4b_three_prob (z : Fin 3) :
    finiteSampleWitness.law.prob (fun ω => GP019B4b_three ω=z)=GP019B4b_p z := by
  fin_cases z <;>
    norm_num [GP019B4b_three, GP019B4b_p, finiteSampleWitness, uniformFin, fairBit,
      FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]

private theorem GP019B4b_witness_cells :
    finiteSampleWitness.listMean true false=5/6 ∧
    finiteSampleWitness.listMean false false=1/2 ∧
    finiteSampleWitness.law.cv (fun ω => (finiteSampleWitness.V ω : ℝ))
      (finiteSampleWitness.cell true false)=17/36 ∧
    finiteSampleWitness.law.cv (fun ω => (finiteSampleWitness.V ω : ℝ))
      (finiteSampleWitness.cell false false)=1/4 := by
  norm_num [finiteSampleWitness, uniformFin, fairBit, Study.listMean, Study.cell,
    FiniteLaw.cv, FiniteLaw.ce, FiniteLaw.prob, FiniteLaw.mean, Fin.sum_univ_succ]

private theorem GP019B4b_three_statistics (s : Fin 4 → Fin 16) :
    let l := fun i => GP019B4b_three (s i)
    (finiteSampleWitness.occupied s ↔ GP019B4b_D l) ∧
    finiteSampleWitness.sampleA s=GP019B4b_A l ∧
    finiteSampleWitness.sampleH s=GP019B4b_H l := by
  dsimp only
  have hcell (i : Fin 4) :
      (finiteSampleWitness.cell true false (s i) ↔ GP019B4b_three (s i)=0) ∧
      (finiteSampleWitness.cell false false (s i) ↔ GP019B4b_three (s i)=1) := by
    dsimp [GP019B4b_three, Study.cell]
    by_cases hy : finiteSampleWitness.Y (s i) = true <;>
      by_cases hz : finiteSampleWitness.Z (s i) = true <;> simp [hy, hz]
  have hc1 : finiteSampleWitness.cellCount s true false=GP019B4b_N (fun i => GP019B4b_three (s i)) 0 := by
    apply Finset.sum_congr rfl
    intro i _; simp only [(hcell i).1]
  have hc0 : finiteSampleWitness.cellCount s false false=GP019B4b_N (fun i => GP019B4b_three (s i)) 1 := by
    apply Finset.sum_congr rfl
    intro i _; simp only [(hcell i).2]
  refine ⟨by simp only [Study.occupied, GP019B4b_D, hc1, hc0], ?_, ?_⟩
  · unfold Study.sampleA Study.ybar GP019B4b_A GP019B4b_N
    congr 2
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [GP019B4b_three, bitVal]
    by_cases hy : finiteSampleWitness.Y (s i) = true <;>
      by_cases hz : finiteSampleWitness.Z (s i) = true <;> simp [hy, hz]
  · simp only [Study.sampleH, hc1, hc0, GP019B4b_witness_cells.2.2.1,
      GP019B4b_witness_cells.2.2.2, GP019B4b_H]

private theorem GP019B4b_table :
    (∑ l : Fin 4 → Fin 3, (∏ i, GP019B4b_p (l i))*if GP019B4b_D l then (1 : ℝ) else 0)=1431/2048 ∧
    (∑ l : Fin 4 → Fin 3, (∏ i, GP019B4b_p (l i))*if GP019B4b_D l then GP019B4b_A l else 0)=1161/2048 ∧
    (∑ l : Fin 4 → Fin 3, (∏ i, GP019B4b_p (l i))*if GP019B4b_D l then (GP019B4b_A l)^2 else 0)=1971/4096 ∧
    (∑ l : Fin 4 → Fin 3, (∏ i, GP019B4b_p (l i))*if GP019B4b_D l then GP019B4b_H l else 0)=
      (1001/1908)*(1431/2048) ∧
    (∑ l : Fin 4 → Fin 3, (∏ i, GP019B4b_p (l i))*if GP019B4b_D l then (GP019B4b_A l)^2*GP019B4b_H l else 0)=
      (2561/7632)*(1431/2048) := by
  -- Only 3^4 label patterns are expanded here.
  simp only [GP019B4b_sum_cons, Fintype.sum_unique]
  simp (config := {maxSteps := 1000000}) only
    [GP019B4b_D, GP019B4b_A, GP019B4b_H, GP019B4b_N, GP019B4b_p,
    Fin.sum_univ_succ, Fin.prod_univ_succ]
  norm_num [Fin.cons]

private theorem GP019B4b_witness_moments :
    let S := finiteSampleWitness
    let P := S.law.iid 4
    P.prob S.occupied=1431/2048 ∧
    P.ce S.sampleA S.occupied=43/53 ∧
    P.ce (fun s => (S.sampleA s)^2) S.occupied=73/106 ∧
    P.ce S.sampleH S.occupied=1001/1908 ∧
    P.ce (fun s => (S.sampleA s)^2*S.sampleH s) S.occupied=2561/7632 := by
  dsimp only
  let S := finiteSampleWitness
  let P := S.law.iid 4
  have hpush (F : (Fin 4 → Fin 3) → ℝ) :
      P.mean (fun s => F (fun i => GP019B4b_three (s i))) =
        ∑ l : Fin 4 → Fin 3, (∏ i, GP019B4b_p (l i))*F l := by
    have h := GP019B4b_iid_labels S.law 4 GP019B4b_three F (fun _ _ => 1)
    have hm (z : Fin 3) : S.law.mean
        (fun ω => if GP019B4b_three ω=z then (1 : ℝ) else 0)=GP019B4b_p z :=
      GP019B4b_three_prob z
    simpa only [Finset.prod_const_one, mul_one, one_mul, hm, mul_comm] using h
  have hD : P.prob S.occupied=1431/2048 := by
    unfold FiniteLaw.prob
    have he : (fun s : Fin 4 → Fin 16 => if S.occupied s then (1 : ℝ) else 0) =
        (fun s => if GP019B4b_D (fun i => GP019B4b_three (s i)) then 1 else 0) := by
      funext s; simp only [S, (GP019B4b_three_statistics s).1]
    rw [he, hpush (fun l => if GP019B4b_D l then 1 else 0)]; exact GP019B4b_table.1
  refine ⟨hD, ?_, ?_, ?_, ?_⟩
  all_goals
    unfold FiniteLaw.ce
    rw [hD]
  · have he : (fun s : Fin 4 → Fin 16 => if S.occupied s then S.sampleA s else 0) =
        (fun s => if GP019B4b_D (fun i => GP019B4b_three (s i)) then GP019B4b_A (fun i => GP019B4b_three (s i)) else 0) := by
      funext s; simp only [S, (GP019B4b_three_statistics s).1, (GP019B4b_three_statistics s).2.1]
    rw [he, hpush (fun l => if GP019B4b_D l then GP019B4b_A l else 0), GP019B4b_table.2.1]; norm_num
  · have he : (fun s : Fin 4 → Fin 16 => if S.occupied s then (S.sampleA s)^2 else 0) =
        (fun s => if GP019B4b_D (fun i => GP019B4b_three (s i)) then (GP019B4b_A (fun i => GP019B4b_three (s i)))^2 else 0) := by
      funext s; simp only [S, (GP019B4b_three_statistics s).1, (GP019B4b_three_statistics s).2.1]
    rw [he, hpush (fun l => if GP019B4b_D l then (GP019B4b_A l)^2 else 0), GP019B4b_table.2.2.1]; norm_num
  · have he : (fun s : Fin 4 → Fin 16 => if S.occupied s then S.sampleH s else 0) =
        (fun s => if GP019B4b_D (fun i => GP019B4b_three (s i)) then GP019B4b_H (fun i => GP019B4b_three (s i)) else 0) := by
      funext s; simp only [S, (GP019B4b_three_statistics s).1, (GP019B4b_three_statistics s).2.2]
    rw [he, hpush (fun l => if GP019B4b_D l then GP019B4b_H l else 0), GP019B4b_table.2.2.2.1]; norm_num
  · have he : (fun s : Fin 4 → Fin 16 => if S.occupied s then (S.sampleA s)^2*S.sampleH s else 0) =
        (fun s => if GP019B4b_D (fun i => GP019B4b_three (s i)) then
          (GP019B4b_A (fun i => GP019B4b_three (s i)))^2*GP019B4b_H (fun i => GP019B4b_three (s i)) else 0) := by
      funext s
      simp only [S, (GP019B4b_three_statistics s).1, (GP019B4b_three_statistics s).2.1,
        (GP019B4b_three_statistics s).2.2]
    rw [he, hpush (fun l => if GP019B4b_D l then (GP019B4b_A l)^2*GP019B4b_H l else 0), GP019B4b_table.2.2.2.2]; norm_num

private theorem GP019B4b_treated_two :
    (finiteSampleWitness.law.iid 4).prob
      (fun s => finiteSampleWitness.armCount s true=2)=3/8 := by
  have hz (z : Bool) : finiteSampleWitness.law.prob
      (fun ω => finiteSampleWitness.Z ω=z)=1/2 := by
    cases z <;> norm_num [FiniteLaw.prob, FiniteLaw.mean, finiteSampleWitness,
      uniformFin, fairBit, Fin.sum_univ_succ]
  have he : (fun s : Fin 4 → Fin 16 => if finiteSampleWitness.armCount s true=2 then (1 : ℝ) else 0) =
      (fun s => (if (∑ i, if finiteSampleWitness.Z (s i)=true then (1 : ℕ) else 0)=2
        then (1 : ℝ) else 0)*(∏ _ : Fin 4, (1 : ℝ))) := by
    simp only [Study.armCount, Finset.prod_const_one, mul_one]
    funext s
    congr 1
  rw [FiniteLaw.prob, he, GP019B4b_iid_labels finiteSampleWitness.law 4
    finiteSampleWitness.Z
    (fun l => if (∑ i, if l i=true then (1 : ℕ) else 0)=2 then (1 : ℝ) else 0)
    (fun _ _ => 1)]
  have hm (z : Bool) : finiteSampleWitness.law.mean
      (fun ω => if finiteSampleWitness.Z ω=z then (1 : ℝ) else 0)=1/2 := hz z
  simp only [hm]
  simp only [GP019B4b_sum_cons, Fintype.sum_unique]
  simp only [Fin.sum_univ_succ, Fintype.sum_bool, Fin.prod_univ_succ]
  norm_num [Fin.cons]

theorem finite_product_counterexample_proof :
    let S := finiteSampleWitness
    let P := S.law.iid 4
    let A := @Study.sampleA (Fin 16) _ S 4
    let B := fun s : Fin 4 → Fin 16 => S.sampleB s 0 0
    S.standing ∧ P.prob S.occupied = 1431/2048 ∧
    P.ccov A B S.occupied = 0 ∧
    P.ccov (fun s => S.cellMean s true false 0) (fun s => S.cellMean s false false 0)
      S.occupied = 0 ∧
    P.cv (fun s => S.muHat s 0 0) S.occupied = 141205/404496 ∧
    (P.ce A S.occupied)^2 * P.cv B S.occupied +
      P.cv A S.occupied * (P.ce B S.occupied)^2 +
      P.cv A S.occupied * P.cv B S.occupied = 75809/202248 ∧
    P.prob (fun s => S.armCount s true = 2) = 3/8 ∧
    P.prob (fun s => S.armCount s true = 0) = 1/16 := by
  dsimp only
  let S := finiteSampleWitness
  let P := S.law.iid 4
  let A := @Study.sampleA (Fin 16) _ S 4
  let B := fun s : Fin 4 → Fin 16 => S.sampleB s 0 0
  have hs : S.standing := finite_sample_witness_valid
  obtain ⟨hp, hA, hA2, hh, hA2h⟩ := GP019B4b_witness_moments
  obtain ⟨hB, hvB, hAB, hAB2⟩ := GP019B4b_product_moments S hs 4 (by norm_num) 0 0
  have hb : S.listMean true false-S.listMean false false-1=(-2/3 : ℝ) := by
    rw [GP019B4b_witness_cells.1, GP019B4b_witness_cells.2.1]; norm_num
  have hvarA : P.cv A S.occupied=171/5618 := by
    unfold FiniteLaw.cv
    rw [hA, hA2]; norm_num
  refine ⟨hs, hp, ?_, GP019B4b_cross_covariance S hs 4 (by norm_num) 0 0, ?_, ?_,
    GP019B4b_treated_two, realized_count_counterexample.2.2⟩
  · unfold FiniteLaw.ccov
    rw [hAB, hB]; ring
  · have hv := (GP019B4b_product_formula S hs 4 (by norm_num) 0 0).1
    rw [hb, hvarA, hA2h] at hv
    norm_num at hv
    exact hv
  · rw [hvB, hB, hb, hh, hA, hvarA]
    norm_num

end
end AronowAudit.P019.Wave1
