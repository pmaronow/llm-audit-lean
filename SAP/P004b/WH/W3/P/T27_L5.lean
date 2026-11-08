import SAP.P004b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T27_L5

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology

lemma fair_weight_nonneg {N : ℕ} (z : SAP.P004b.Assignment N) :
    0 ≤ SAP.P004b.designWeight (fun _ : Fin N => (1/2 : ℝ)) z := by
  unfold SAP.P004b.designWeight
  apply Finset.prod_nonneg
  intro i hi
  cases z i <;> simp [SAP.P004b.coin] <;> norm_num

lemma fair_expect_mono {N : ℕ} (X Y : SAP.P004b.Assignment N → ℝ)
    (hXY : ∀ z, X z ≤ Y z) :
    SAP.P004b.expect (fun _ : Fin N => (1/2 : ℝ)) X ≤
      SAP.P004b.expect (fun _ : Fin N => (1/2 : ℝ)) Y := by
  unfold SAP.P004b.expect
  apply Finset.sum_le_sum
  intro z hz
  exact mul_le_mul_of_nonneg_left (hXY z) (fair_weight_nonneg z)

lemma fair_prob_nonneg {N : ℕ} (E : SAP.P004b.Assignment N → Prop) :
    0 ≤ SAP.P004b.prob (fun _ : Fin N => (1/2 : ℝ)) E := by
  unfold SAP.P004b.prob SAP.P004b.expect
  apply Finset.sum_nonneg
  intro z hz
  exact mul_nonneg (fair_weight_nonneg z) (by
    dsimp
    split_ifs <;> norm_num)

lemma expect_div_fixed {N : ℕ} (p : Fin N → ℝ)
    (X : SAP.P004b.Assignment N → ℝ) (c : ℝ) :
    SAP.P004b.expect p (fun z => X z/c) = SAP.P004b.expect p X/c := by
  simp only [SAP.P004b.expect, ← mul_div_assoc, Finset.sum_div]

lemma conditional_chebyshev_bound (hLaw : SAP.P004b.WholeSparseCountLaw)
    (a : Bool) (ε : ℝ) (hε : 0 < ε) {N : ℕ} (hN : 3 ≤ N)
    (hsmall : 1 / (N : ℝ) < ε) :
    SAP.P004b.wholeSparseCond N a
      (fun z => ε < |SAP.P004b.wholeSparseQ z / N - 1/2|) ≤
        1 / ((N : ℝ) * ε^2) := by
  classical
  let p : Fin N → ℝ := fun _ => 1/2
  let U : SAP.P004b.Assignment N → ℝ := fun z =>
    SAP.P004b.wholeSparseQ z / N - (1/2 + 1/(2*(N : ℝ)))
  let V : SAP.P004b.Assignment N → ℝ := fun z =>
    if SAP.P004b.wholeFirst z = a then U z ^ 2 else 0
  let E : SAP.P004b.Assignment N → Prop := fun z =>
    SAP.P004b.wholeFirst z = a ∧
      ε < |SAP.P004b.wholeSparseQ z / N - 1/2|
  have hNreal : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hmul : 1 < ε * (N : ℝ) := (div_lt_iff₀ hNreal).mp hsmall
  have hshift : (1 : ℝ) / (2*(N : ℝ)) ≤ ε/2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2*(N : ℝ))).2
    nlinarith [hmul]
  have ht : 0 < ε/2 := by positivity
  have ht2 : 0 < (ε/2)^2 := sq_pos_of_pos ht
  have hpoint : ∀ z : SAP.P004b.Assignment N,
      (@ite ℝ (E z) (Classical.propDecidable (E z)) (1 : ℝ) 0) ≤
        (if SAP.P004b.wholeFirst z = a then U z ^ 2 / (ε/2)^2 else 0) := by
    intro z
    by_cases ha : SAP.P004b.wholeFirst z = a
    · by_cases he : ε < |SAP.P004b.wholeSparseQ z / N - 1/2|
      · have htriangle :
            |SAP.P004b.wholeSparseQ z / N - 1/2| ≤ |U z| + ε/2 := by
          have hshiftAbs : |(1 : ℝ)/(2*(N : ℝ))| ≤ ε/2 := by
            rw [abs_of_pos (by positivity : (0 : ℝ) < 1/(2*(N : ℝ)))]
            exact hshift
          calc
            |SAP.P004b.wholeSparseQ z / N - 1/2| =
                |(SAP.P004b.wholeSparseQ z / N - (1/2 + 1/(2*(N : ℝ)))) +
                    1/(2*(N : ℝ))| := by congr 1 <;> ring
            _ ≤ |SAP.P004b.wholeSparseQ z / N - (1/2 + 1/(2*(N : ℝ)))| +
                  |1/(2*(N : ℝ))| := abs_add_le _ _
            _ = |U z| + |1/(2*(N : ℝ))| := by simp [U]
            _ ≤ |U z| + ε/2 := by nlinarith [hshiftAbs]
        have hU : ε/2 < |U z| := by linarith
        have hEz : E z := ⟨ha, he⟩
        simp only [if_pos hEz, if_pos ha]
        change 1 ≤ U z ^ 2 / (ε/2)^2
        apply (le_div_iff₀ ht2).2
        have hsq : (ε/2)^2 ≤ U z ^ 2 := by
          nlinarith [sq_abs (U z)]
        simpa using hsq
      · have hEz : ¬ E z := by
          rintro ⟨_, hh⟩
          exact he hh
        simp only [if_neg hEz, if_pos ha]
        exact div_nonneg (sq_nonneg (U z)) ht2.le
    · have hEz : ¬ E z := by
        rintro ⟨hh, _⟩
        exact ha hh
      simp only [if_neg hEz, if_neg ha]
      norm_num
  have hmono : SAP.P004b.expect p
      (fun z => @ite ℝ (E z) (Classical.propDecidable (E z)) (1 : ℝ) 0) ≤
      SAP.P004b.expect p
        (fun z => if SAP.P004b.wholeFirst z = a then U z^2/(ε/2)^2 else 0) := by
    simpa [p] using fair_expect_mono _ _ hpoint
  have hfun :
      (fun z : SAP.P004b.Assignment N =>
        if SAP.P004b.wholeFirst z = a then U z ^ 2 / (ε/2)^2 else 0) =
      (fun z => V z / (ε/2)^2) := by
    funext z
    by_cases ha : SAP.P004b.wholeFirst z = a <;> simp [V, ha]
  have hprob :
      SAP.P004b.prob p E ≤
      SAP.P004b.expect p V / (ε/2)^2 := by
    unfold SAP.P004b.prob
    calc
      _ ≤ SAP.P004b.expect p
          (fun z => if SAP.P004b.wholeFirst z = a then U z^2/(ε/2)^2 else 0) := hmono
      _ = SAP.P004b.expect p V / (ε/2)^2 := by rw [hfun, expect_div_fixed]
  rcases hLaw N hN with ⟨_, _, hmom⟩
  have hsecond := (hmom a).2
  have hmoment : 2 * SAP.P004b.expect p V = ((N : ℝ)-1)/(4*(N : ℝ)^2) := by
    simpa [p, V, U] using hsecond
  have hraw :
      SAP.P004b.wholeSparseCond N a
        (fun z => ε < |SAP.P004b.wholeSparseQ z / N - 1/2|) ≤
        (((N : ℝ)-1)/(4*(N : ℝ)^2)) / (ε/2)^2 := by
    change 2 * SAP.P004b.prob p E ≤ _
    calc
      _ ≤ 2 * (SAP.P004b.expect p V / (ε/2)^2) :=
        mul_le_mul_of_nonneg_left hprob (by norm_num)
      _ = (2 * SAP.P004b.expect p V) / (ε/2)^2 := by ring
      _ = (((N : ℝ)-1)/(4*(N : ℝ)^2)) / (ε/2)^2 := by rw [hmoment]
  have hnum : (N : ℝ)-1 ≤ (N : ℝ) := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    linarith
  have hfactor :
      (((N : ℝ)-1)/(4*(N : ℝ)^2)) / (ε/2)^2 =
        ((N : ℝ)-1)/((N : ℝ)^2*ε^2) := by
    field_simp [ne_of_gt hNreal, ne_of_gt hε]
    <;> ring
  have htarget :
      1/((N : ℝ)*ε^2) = (N : ℝ)/((N : ℝ)^2*ε^2) := by
    field_simp [ne_of_gt hNreal, ne_of_gt hε]
    <;> ring
  have hfinal : ((N : ℝ)-1)/((N : ℝ)^2*ε^2) ≤
      1/((N : ℝ)*ε^2) := by
    rw [htarget]
    exact div_le_div_of_nonneg_right hnum (by positivity)
  rw [hfactor] at hraw
  exact hraw.trans hfinal

end SAP.P004b.WH.W3.P.T27_L5

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Classical Topology

theorem SAP.P004b.WH.W3.T27_L5_proof : SAP.P004b.WH.W3.T27_L5 := by
  intro hLaw a ε hε
  have hinv : Tendsto (fun N : ℕ => (1 : ℝ)/(N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ N : ℕ in atTop, (1 : ℝ)/(N : ℝ) < ε := by
    have h := hinv.eventually (Iio_mem_nhds hε)
    simpa using h
  have hupper : ∀ᶠ N : ℕ in atTop,
      SAP.P004b.wholeSparseCond N a
        (fun z => ε < |SAP.P004b.wholeSparseQ z / N - 1/2|) ≤
          (1/ε^2)/(N : ℝ) := by
    filter_upwards [eventually_ge_atTop 3, hsmall] with N hN hs
    have hb := SAP.P004b.WH.W3.P.T27_L5.conditional_chebyshev_bound
      hLaw a ε hε hN hs
    have heq : 1/((N : ℝ)*ε^2) = (1/ε^2)/(N : ℝ) := by
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
      field_simp [hn, ne_of_gt hε]
      <;> ring
    rw [heq] at hb
    exact hb
  have hlim : Tendsto (fun N : ℕ => (1/ε^2)/(N : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hnonneg : ∀ N : ℕ, 0 ≤ SAP.P004b.wholeSparseCond N a
      (fun z => ε < |SAP.P004b.wholeSparseQ z / N - 1/2|) := by
    intro N
    unfold SAP.P004b.wholeSparseCond
    apply mul_nonneg (by norm_num)
    exact SAP.P004b.WH.W3.P.T27_L5.fair_prob_nonneg _
  exact squeeze_zero' (Eventually.of_forall hnonneg) hupper hlim
