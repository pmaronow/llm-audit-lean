import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.Wave1.Gap.GLP0042B2
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
namespace SAP.P004b.WH.W3.P.T27_L10
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section
open SAP.P004b
lemma expect_coord {N : ℕ} (i : Fin N) (x y : ℝ) :
    expect (fun _ : Fin N => (1/2 : ℝ)) (fun z => if z i then x else y) = (x+y)/2 := by
  have hi : AronowAudit.P004.expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => if z i then (1 : ℝ) else 0) = 1/2 := by
    simpa only [AronowAudit.P004.expect_const, mul_one] using
      AronowAudit.P004.Wave1.T27_selected_update (N := N) (fun _ => (1 : ℝ)) i true
  have he : (fun z : Assignment N => if z i then x else y) =
      fun z => (x-y) * (if z i then (1 : ℝ) else 0) + y := by
    funext z; cases z i <;> norm_num
  change AronowAudit.P004.expect _ _ = _
  rw [he, AronowAudit.P004.expect_add, AronowAudit.P004.expect_mul,
    AronowAudit.P004.expect_const, hi]; ring
lemma five_diagonal {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hN : (N : ℝ) ≠ 0)
    (hQ : ∀ i j, Q i j = if i = j then 1 else 0) :
    wholeHacFive z e Q ((N : ℝ)/2) ((N : ℝ)/2) =
      (4/(N : ℝ)^2) * ∑ i, e i ^ 2 := by
  have hz (i : Fin N) : (∑ j ∈ Finset.univ.erase i,
      bit (z i)*bit (z j)*e i*e j*Q i j) = 0 := by
    apply Finset.sum_eq_zero; intro j hj; rw [hQ i j]; simp [Ne.symm (Finset.mem_erase.mp hj).1]
  have h01 (i : Fin N) : (∑ j ∈ Finset.univ.erase i,
      (1-bit (z i))*bit (z j)*e i*e j*Q i j) = 0 := by
    apply Finset.sum_eq_zero; intro j hj; rw [hQ i j]; simp [Ne.symm (Finset.mem_erase.mp hj).1]
  have h00 (i : Fin N) : (∑ j ∈ Finset.univ.erase i,
      (1-bit (z i))*(1-bit (z j))*e i*e j*Q i j) = 0 := by
    apply Finset.sum_eq_zero; intro j hj; rw [hQ i j]; simp [Ne.symm (Finset.mem_erase.mp hj).1]
  unfold wholeHacFive
  simp_rw [hz, h01, h00]
  simp only [Finset.sum_const_zero, zero_div, sub_zero, add_zero]
  have hcombine : (∑ i, bit (z i)*e i^2) + (∑ i, (1-bit (z i))*e i^2) = ∑ i, e i^2 := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro i hi; ring
  rw [← add_div, hcombine]
  field_simp [hN]
  <;> ring
lemma sparse_residual_squares {N : ℕ} (hN : 1 ≤ N) (z : Assignment N) :
    ∑ i : Fin N, residual (sparseTable N) z i ^ 2 =
      (1/4+3/4*bit (z ⟨0, by omega⟩))^2 *
        (1-1/armCount z (z ⟨0, by omega⟩)) := by
  let o : Fin N := ⟨0, by omega⟩
  let y : ℝ := 1/4+3/4*bit (z o)
  let q : ℝ := armCount z (z o)
  have hq1 : 1 ≤ q := by
    dsimp [q, armCount]
    have hsingle := Finset.single_le_sum (f := fun i : Fin N => if z i = z o then (1 : ℝ) else 0)
      (s := Finset.univ) (a := o) (fun i hi => by split_ifs <;> positivity) (Finset.mem_univ o)
    simpa using hsingle
  have hq : 0 < q := lt_of_lt_of_le (by norm_num) hq1
  have htable : sparseTable N = AronowAudit.P004.sparseTable N := by rfl
  have hmean (i : Fin N) : armMean (sparseTable N) z (z i) =
      if z i = z o then y/q else 0 := by
    have hnum (a : Bool) :
        (∑ j : Fin N, if z j = a then sparseTable N j z else 0) =
          if z o = a then y else 0 := by
      rw [Finset.sum_eq_single o]
      · simp [sparseTable, o, y]
      · intro j hj hjo
        have hjv : j.val ≠ 0 := by intro hv; apply hjo; exact Fin.ext hv
        simp [sparseTable, hjv]
      · simp
    unfold armMean
    rw [hnum (z i)]
    by_cases hi : z i = z o
    · have hcount : armCount z (z i) = q := by dsimp [q]; rw [hi]
      rw [if_pos hi.symm, hcount, if_pos hi]
    · have hrev : z o ≠ z i := fun hh => hi hh.symm
      simp only [if_neg hrev, if_neg hi]; simp
  have hterm (i : Fin N) : residual (sparseTable N) z i ^ 2 =
      (if i = o then y^2-2*y^2/q else 0) +
        (if z i = z o then y^2/q^2 else 0) := by
    rw [residual, hmean i]
    by_cases hi : i = o
    · subst i
      cases hz : z o <;>
        simp [sparseTable, o, y, q, hz] <;>
        field_simp [hq.ne'] <;> ring
    · have hiv : i.val ≠ 0 := by intro hv; apply hi; exact Fin.ext hv
      have hR : sparseTable N i z = 0 := by simp [sparseTable, hiv]
      rw [hR]
      by_cases hz : z i = z o
      · simp [hi, hz, y, q]; field_simp [hq.ne']
      · simp [hi, hz, y, q]
  rw [Finset.sum_congr rfl (fun i hi => hterm i), Finset.sum_add_distrib]
  have hone : (∑ i : Fin N, if i = o then y^2-2*y^2/q else 0) = y^2-2*y^2/q := by
    simp
  have htwo : (∑ i : Fin N, if z i = z o then y^2/q^2 else 0) = q*y^2/q^2 := by
    calc
      _ = (∑ i : Fin N, (if z i = z o then (1 : ℝ) else 0) * (y^2/q^2)) := by
        apply Finset.sum_congr rfl; intro i hi; split_ifs <;> ring
      _ = (∑ i : Fin N, if z i = z o then (1 : ℝ) else 0) * (y^2/q^2) := by
        rw [Finset.sum_mul]
      _ = q*y^2/q^2 := by simp [q, armCount] <;> ring
  rw [hone, htwo]
  dsimp [q]
  field_simp [hq.ne']; ring
lemma v1_formula {N : ℕ} (hN : 2 ≤ N) (z : Assignment N) :
    wholeSparseV1 N z = (4/(N : ℝ)^2) *
      ∑ i : Fin N, residual (sparseTable N) z i ^ 2 := by
  have hNpos : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hQ (i j : Fin N) : wholeSparseQmat N i j = if i=j then 1 else 0 := by
    exact AronowAudit.P004.Wave1.T27_kernel_eq hN i j
  have hc : circleAverage (sparsePopulation N) 1 = sparseTable N := AronowAudit.P004.Wave1.T27_circle N
  have hf := five_diagonal z (residual (sparseTable N) z) (wholeSparseQmat N) hNpos hQ
  unfold wholeSparseV1 wholeV1Five wholeSparseR; rw [hc]
  rw [show (N:ℝ)*(1/2:ℝ)=N/2 by ring, show (N:ℝ)*(1-(1/2:ℝ))=N/2 by ring]
  change wholeHacFive z (residual (sparseTable N) z) (wholeSparseQmat N) (N/2) (N/2) = _
  exact hf
lemma v2_diagonal {N : ℕ} (hN : 2 ≤ N) (z : Assignment N) :
    wholeSparseV2 N z = ∑ i : Fin N, (nedEpsilon (1/2) (sparseTable N)
      (1/(N : ℝ)) (1/(4*(N : ℝ))) i z)^2 := by
  have hb := AronowAudit.P004.Wave1.T27_bandwidth_bounds hN
  have hself (i : Fin N) : nodeSeparation (sparsePopulation N) i i = 0 := by
    change AronowAudit.P004.nodeSeparation (AronowAudit.P004.sparsePopulation N) i i = 0
    exact AronowAudit.P004.Wave1.T27_separation_self i
  have hbw : 0 ≤ sparseBandwidth N := by
    unfold sparseBandwidth; exact_mod_cast (Nat.zero_le (Nat.floor ((N : ℝ)^(1/12 : ℝ))))
  have hmem (i : Fin N) : i ∈ ball (nodeSeparation (sparsePopulation N)) i (sparseBandwidth N) := by
    simpa [ball, hself] using hbw
  have htable : sparseTable N = AronowAudit.P004.sparseTable N := by rfl
  have hbar1 : barMu (fun _ : Fin N => (1/2 : ℝ)) (sparseTable N) true = 1/(N : ℝ) := by
    change AronowAudit.P004.barMu _ (sparseTable N) true = _; rw [htable, AronowAudit.P004.Wave1.T27_barMu (show 0 < N by omega) true]; norm_num [AronowAudit.P004.bit]
  have hbar0 : barMu (fun _ : Fin N => (1/2 : ℝ)) (sparseTable N) false = 1/(4*(N : ℝ)) := by
    change AronowAudit.P004.barMu _ (sparseTable N) false = _; rw [htable, AronowAudit.P004.Wave1.T27_barMu (show 0 < N by omega) false]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp [hn]; norm_num [AronowAudit.P004.bit]
  have hkernel (i j : Fin N) : uniformKernel (nodeSeparation (sparsePopulation N) i j / sparseBandwidth N) = if i=j then 1 else 0 := AronowAudit.P004.Wave1.T27_kernel_eq hN i j
  have hrow (i : Fin N) : nedVRow (1/2) (sparseTable N) (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N) (1/(N : ℝ)) (1/(4*(N : ℝ))) i z = (nedEpsilon (1/2) (sparseTable N) (1/(N : ℝ)) (1/(4*(N : ℝ))) i z)^2 := by
    unfold nedVRow; rw [Finset.sum_eq_single i]
    · rw [hkernel i i]; simp; ring
    · intro j hj hji; rw [hkernel i j]; simp [Ne.symm hji]
    · intro hi; exact (hi (hmem i)).elim
  have hcircle : circleAverage (sparsePopulation N) 1 = sparseTable N := AronowAudit.P004.Wave1.T27_circle N
  change nedV2 (1/2) (wholeSparseR N) (nodeSeparation (sparsePopulation N)) uniformKernel (sparseBandwidth N) z = _
  rw [show wholeSparseR N = sparseTable N from hcircle]; unfold nedV2; rw [hbar1, hbar0]; simp_rw [hrow]
lemma v2_epsilon_values {N : ℕ} (hN : 3 ≤ N) : let o : Fin N := ⟨0, by omega⟩; ∀ i z,
    nedEpsilon (1/2) (sparseTable N) (1/(N : ℝ)) (1/(4*(N : ℝ))) i z =
      if i=o then if z o then 2*((N : ℝ)-1)/(N : ℝ)^2 else -((N : ℝ)-1)/(2*(N : ℝ)^2)
      else if z i then -2/(N : ℝ)^2 else 1/(2*(N : ℝ)^2) := by
  dsimp only; intro i z; let o : Fin N := ⟨0, by omega⟩
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  by_cases hi : i=o
  · subst i; cases hz : z o <;> simp [nedEpsilon, residualContrast, sparseTable, bit, o, hz] <;> field_simp [hn] <;> ring
  · have hiv : i.val ≠ 0 := by intro hv; apply hi; exact Fin.ext hv
    cases hz : z i <;> simp [nedEpsilon, residualContrast, sparseTable, bit, o, hi, hiv, hz] <;> field_simp [hn] <;> ring
lemma sum_if_single {N : ℕ} (o : Fin N) (a b : ℝ) : (∑ i : Fin N, if i=o then a else b) = a+((N : ℝ)-1)*b := by
  have he : (fun i : Fin N => if i=o then a else b) = fun i => (if i=o then a-b else 0)+b := by funext i; split_ifs <;> ring
  rw [he, Finset.sum_add_distrib]; have hs : (∑ i : Fin N, if i=o then a-b else 0) = a-b := by simp
  rw [hs]; simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
lemma v2_termized {N : ℕ} (hN : 3 ≤ N) (z : Assignment N) : wholeSparseV2 N z =
    ∑ i : Fin N, if i = (⟨0, by omega⟩ : Fin N) then
      if z ⟨0, by omega⟩ then (2*((N : ℝ)-1)/(N : ℝ)^2)^2 else (((N : ℝ)-1)/(2*(N : ℝ)^2))^2
    else if z i then (2/(N : ℝ)^2)^2 else (1/(2*(N : ℝ)^2))^2 := by
  rw [v2_diagonal (by omega)]
  have he := v2_epsilon_values hN
  dsimp only at he
  rw [show (fun i : Fin N => (nedEpsilon (1/2) (sparseTable N) (1/(N : ℝ)) (1/(4*(N : ℝ))) i z)^2) =
      (fun i => if i = (⟨0, by omega⟩ : Fin N) then
        if z ⟨0, by omega⟩ then (2*((N : ℝ)-1)/(N : ℝ)^2)^2 else (((N : ℝ)-1)/(2*(N : ℝ)^2))^2
      else if z i then (2/(N : ℝ)^2)^2 else (1/(2*(N : ℝ)^2))^2) by
      funext i; rw [he i z]; split_ifs <;> ring]
lemma v2_term_bounds {N : ℕ} (hN : 3 ≤ N)
    (z : Assignment N) (i : Fin N) :
    0 ≤ (if i = (⟨0, by omega⟩ : Fin N) then
        if z ⟨0, by omega⟩ then
          (2*((N : ℝ)-1)/(N : ℝ)^2)^2
        else (((N : ℝ)-1)/(2*(N : ℝ)^2))^2
      else if z i then (2/(N : ℝ)^2)^2 else (1/(2*(N : ℝ)^2))^2) ∧
      (if i = (⟨0, by omega⟩ : Fin N) then
        if z ⟨0, by omega⟩ then
          (2*((N : ℝ)-1)/(N : ℝ)^2)^2
        else (((N : ℝ)-1)/(2*(N : ℝ)^2))^2
      else if z i then (2/(N : ℝ)^2)^2 else (1/(2*(N : ℝ)^2))^2) ≤
        if i = (⟨0, by omega⟩ : Fin N) then 4/(N : ℝ)^2 else 4/(N : ℝ)^4 := by
  let n : ℝ := N
  have hn : 3 ≤ n := by dsimp [n]; exact_mod_cast hN
  have hnn : 0 < n := by linarith
  have hn1 : 0 ≤ n-1 ∧ n-1 ≤ n := by constructor <;> linarith
  have hnonneg : 0 ≤ (if i = (⟨0, by omega⟩ : Fin N) then
      if z ⟨0, by omega⟩ then (2*((N : ℝ)-1)/(N : ℝ)^2)^2
      else (((N : ℝ)-1)/(2*(N : ℝ)^2))^2
    else if z i then (2/(N : ℝ)^2)^2 else (1/(2*(N : ℝ)^2))^2) := by
    split_ifs <;> positivity
  constructor
  · exact hnonneg
  · by_cases hi : i = (⟨0, by omega⟩ : Fin N)
    · subst i; cases hz : z ⟨0, by omega⟩ <;> simp [hz] <;>
        field_simp [ne_of_gt hnn] <;> nlinarith [sq_nonneg (n-1), hn1.2]
    · cases hz : z i <;> simp [hi, hz] <;> field_simp [ne_of_gt hnn] <;> norm_num
lemma v2_expected {N : ℕ} (hN : 3 ≤ N) : expect (fun _ : Fin N => (1/2 : ℝ)) (wholeSparseV2 N) =
    17*((N : ℝ)-1)/(8*(N : ℝ)^3) := by
  let o : Fin N := ⟨0, by omega⟩
  let n : ℝ := N
  have hNcast : n ≠ 0 := by dsimp [n]; exact_mod_cast (show N ≠ 0 by omega)
  have hspike :
      expect (fun _ : Fin N => (1/2 : ℝ)) (fun z =>
        if z o then (2*(n-1)/n^2)^2 else ((n-1)/(2*n^2))^2) =
          17*(n-1)^2/(8*n^4) := by
    rw [expect_coord o ((2*(n-1)/n^2)^2) (((n-1)/(2*n^2))^2)]; field_simp [hNcast]; ring
  have hother (i : Fin N) :
      expect (fun _ : Fin N => (1/2 : ℝ)) (fun z =>
        if z i then (2/n^2)^2 else (1/(2*n^2))^2) = 17/(8*n^4) := by
    rw [expect_coord i ((2/n^2)^2) ((1/(2*n^2))^2)]; field_simp [hNcast]; ring
  change AronowAudit.P004.expect (fun _ : Fin N => (1/2 : ℝ)) (wholeSparseV2 N) = _
  rw [show wholeSparseV2 N = fun z =>
      ∑ i : Fin N, if i=o then if z o then (2*(n-1)/n^2)^2 else ((n-1)/(2*n^2))^2
        else if z i then (2/n^2)^2 else (1/(2*n^2))^2 from by funext z; rw [v2_termized hN z]]
  rw [AronowAudit.P004.expect_sum]
  have hmoment (i : Fin N) :
      AronowAudit.P004.expect (fun _ : Fin N => (1/2 : ℝ)) (fun z => if i=o then
        if z o then (2*(n-1)/n^2)^2 else ((n-1)/(2*n^2))^2
      else if z i then (2/n^2)^2 else (1/(2*n^2))^2) =
        if i=o then 17*(n-1)^2/(8*n^4) else 17/(8*n^4) := by
    change expect (fun _ : Fin N => (1/2 : ℝ)) (fun z => if i=o then
      if z o then (2*(n-1)/n^2)^2 else ((n-1)/(2*n^2))^2
      else if z i then (2/n^2)^2 else (1/(2*n^2))^2) = _
    by_cases hi : i=o
    · subst i; simpa using hspike
    · simpa [hi] using hother i
  have hsum : (∑ i : Fin N, if i=o then 17*(n-1)^2/(8*n^4) else 17/(8*n^4)) =
      17*(n-1)^2/(8*n^4)+((N : ℝ)-1)*(17/(8*n^4)) := sum_if_single o _ _
  calc
    _ = ∑ i : Fin N, if i=o then 17*(n-1)^2/(8*n^4) else 17/(8*n^4) := by
      apply Finset.sum_congr rfl; intro i hi; exact hmoment i
    _ = _ := hsum
  field_simp [hNcast]
  <;> ring
lemma sparse_residual_square_le_one {N : ℕ} (hN : 1 ≤ N)
    (z : Assignment N) :
    ∑ i : Fin N, residual (sparseTable N) z i ^ 2 ≤ 1 := by
  rw [sparse_residual_squares hN z]
  let o : Fin N := ⟨0, by omega⟩
  let q : ℝ := armCount z (z o)
  let y : ℝ := 1/4+3/4*bit (z o)
  have hq1 : 1 ≤ q := by
    dsimp [q, armCount]
    have hs := Finset.single_le_sum
      (f := fun i : Fin N => if z i = z o then (1 : ℝ) else 0)
      (s := Finset.univ) (a := o) (fun i hi => by split_ifs <;> positivity)
      (Finset.mem_univ o)
    simpa using hs
  have hq : 0 < q := by linarith
  have hy : 0 ≤ y ∧ y ≤ 1 := by
    cases hz : z o <;> simp [y, bit, hz] <;> norm_num
  have hrecip : 1/q ≤ 1 := (div_le_iff₀ hq).2 (by nlinarith [hq1])
  have hf : 0 ≤ 1-1/q ∧ 1-1/q ≤ 1 := by
    constructor
    · linarith
    · have : 0 ≤ (1:ℝ)/q := by positivity
      linarith
  have hy2 : y^2 ≤ 1 := by nlinarith [sq_nonneg y, sq_nonneg (y-1)]
  calc
    y^2*(1-1/q) ≤ 1*(1-1/q) := mul_le_mul_of_nonneg_right hy2 hf.1
    _ ≤ 1*1 := mul_le_mul_of_nonneg_left hf.2 (by norm_num)
    _ = 1 := by ring
lemma v2_point_bounds {N : ℕ} (hN : 3 ≤ N) (z : Assignment N) :
    0 ≤ wholeSparseV2 N z ∧ wholeSparseV2 N z ≤ 16/(N : ℝ)^2 := by
  let o : Fin N := ⟨0, by omega⟩
  have hn : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  rw [v2_termized hN z]
  constructor
  · exact Finset.sum_nonneg (fun i hi => (v2_term_bounds hN z i).1)
  · calc
      (∑ i : Fin N, if i=o then
        if z o then (2*((N : ℝ)-1)/(N : ℝ)^2)^2 else (((N : ℝ)-1)/(2*(N : ℝ)^2))^2
      else if z i then (2/(N : ℝ)^2)^2 else (1/(2*(N : ℝ)^2))^2) ≤
        ∑ i : Fin N, if i=o then 4/(N : ℝ)^2 else 4/(N : ℝ)^4 :=
          Finset.sum_le_sum (fun i hi => v2_term_bounds hN z i |>.2)
      _ = 4/(N : ℝ)^2+((N : ℝ)-1)*(4/(N : ℝ)^4) := sum_if_single o _ _
      _ ≤ 16/(N : ℝ)^2 := by
        field_simp [ne_of_gt hn]
        nlinarith [show (3:ℝ) ≤ (N:ℝ) by exact_mod_cast hN]
end
end SAP.P004b.WH.W3.P.T27_L10
theorem SAP.P004b.WH.W3.T27_L10_proof : SAP.P004b.WH.W3.T27_L10 := by
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  refine ⟨?_, ?_, SAP.P004b.WH.W3.P.T27_L10.v2_expected hN⟩
  · intro z
    have hsq0 : 0 ≤ ∑ i : Fin N, residual (sparseTable N) z i ^ 2 :=
      Finset.sum_nonneg (fun i hi => sq_nonneg _)
    have hsq1 := SAP.P004b.WH.W3.P.T27_L10.sparse_residual_square_le_one hN1 z
    rw [SAP.P004b.WH.W3.P.T27_L10.v1_formula hN2 z]
    constructor
    · exact mul_nonneg (by positivity) hsq0
    · calc
        (4/(N : ℝ)^2) * ∑ i : Fin N, residual (sparseTable N) z i ^ 2 ≤
            (4/(N : ℝ)^2) * 1 := mul_le_mul_of_nonneg_left hsq1 (by positivity)
        _ = 4/(N : ℝ)^2 := by ring
  · intro z
    exact SAP.P004b.WH.W3.P.T27_L10.v2_point_bounds hN z
