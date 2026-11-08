import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.Wave1.Gap.GLP0042B2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T27_L3

open SAP.P004b
open AronowAudit.P004
open scoped BigOperators Classical

private lemma first_mean {N : ℕ} (hN : 0 < N) :
    AronowAudit.P004.expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => bit (z ⟨0, hN⟩)) = 1/2 := by
  let o : Fin N := ⟨0, hN⟩
  have he : (fun z : Assignment N => bit (z o)) =
      (fun z => if z o = true then (1 : ℝ) else 0) := by
    funext z
    cases z o <;> simp [bit]
  rw [he]
  change AronowAudit.P004.expect (fun _ : Fin N => (1/2 : ℝ))
    (fun z => if z o = true then (1 : ℝ) else 0) = 1/2
  simpa only [AronowAudit.P004.expect_const, mul_one] using
    (AronowAudit.P004.Wave1.T27_selected_update
      (N := N) (fun _ : Assignment N => (1 : ℝ)) o true)

private lemma count_first_cov {N : ℕ} (hN : 0 < N) :
    AronowAudit.P004.cov (fun _ : Fin N => (1/2 : ℝ))
      (fun z => bit (z ⟨0, hN⟩)) (fun z => armCount z true) = 1/4 := by
  let o : Fin N := ⟨0, hN⟩
  let p : Fin N → ℝ := fun _ => 1/2
  let X : Assignment N → ℝ := fun z => bit (z o)
  have hX : AronowAudit.P004.expect p X = 1/2 := by
    change AronowAudit.P004.expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => bit (z ⟨0,hN⟩)) = 1/2
    exact first_mean hN
  have hq := AronowAudit.P004.Wave1.T27_count_moments (N := N) true
  have hqmean : AronowAudit.P004.expect p (fun z => armCount z true) = (N : ℝ)/2 := by
    change AronowAudit.P004.expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => AronowAudit.P004.armCount z true) = (N : ℝ)/2
    exact hq.1
  have hsplit (z : Assignment N) :
      armCount z true = (if z o = true then (1 : ℝ) else 0) +
        ∑ i ∈ Finset.univ.erase o, (if z i = true then (1 : ℝ) else 0) := by
    unfold armCount
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o)]
    ring
  have hsplitUpdate (z : Assignment N) :
      armCount (Function.update z o true) true =
        1 + ∑ i ∈ Finset.univ.erase o, (if z i = true then (1 : ℝ) else 0) := by
    unfold armCount
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ o)]
    have hrest : (∑ i ∈ Finset.univ.erase o,
        (if Function.update z o true i = true then (1 : ℝ) else 0)) =
        ∑ i ∈ Finset.univ.erase o, (if z i = true then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_erase] at hi
      rw [Function.update_of_ne hi.1]
    rw [hrest]
    simp
    ring
  have hqUpdate (z : Assignment N) :
      armCount (Function.update z o true) true = armCount z true + 1 - X z := by
    rw [hsplitUpdate z, hsplit z]
    simp [X, bit]
    ring
  have hqUpdateMean :
      AronowAudit.P004.expect p
        (fun z => armCount (Function.update z o true) true) =
        (N : ℝ)/2 + 1 - 1/2 := by
    calc
      _ = AronowAudit.P004.expect p (fun z => armCount z true + 1 - X z) := by
        apply congrArg (AronowAudit.P004.expect p)
        funext z
        exact hqUpdate z
      _ = _ := by rw [AronowAudit.P004.expect_sub, AronowAudit.P004.expect_add,
        AronowAudit.P004.expect_const, hqmean, hX]
  have hprod : AronowAudit.P004.expect p (fun z => X z * armCount z true) =
      (N : ℝ)/4 + 1/4 := by
    have he : (fun z => X z * armCount z true) =
        (fun z => if z o = true then armCount z true else 0) := by
      funext z
      cases hz : z o <;> simp [X, bit, hz]
    rw [he]
    change AronowAudit.P004.expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => if z o = true then armCount z true else 0) = _
    rw [AronowAudit.P004.Wave1.T27_selected_update, hqUpdateMean]
    ring
  change AronowAudit.P004.cov p X (fun z => armCount z true) = _
  unfold AronowAudit.P004.cov
  rw [hprod, hX, hqmean]
  ring

private lemma first_variance {N : ℕ} (hN : 0 < N) :
    AronowAudit.P004.variance (fun _ : Fin N => (1/2 : ℝ))
      (fun z => bit (z ⟨0, hN⟩)) = 1/4 := by
  let p : Fin N → ℝ := fun _ => 1/2
  let X : Assignment N → ℝ := fun z => bit (z ⟨0, hN⟩)
  have hX : AronowAudit.P004.expect p X = 1/2 := by
    change AronowAudit.P004.expect (fun _ : Fin N => (1/2 : ℝ))
      (fun z => bit (z ⟨0,hN⟩)) = 1/2
    exact first_mean hN
  have hXX : (fun z => X z * X z) = X := by
    funext z
    simp [X, bit]
  change AronowAudit.P004.variance p X = _
  unfold AronowAudit.P004.variance AronowAudit.P004.cov
  rw [hXX, hX]
  norm_num

private lemma variance_linear {N : ℕ} (p : Fin N → ℝ)
    (X Y : Assignment N → ℝ) (a b : ℝ) :
    AronowAudit.P004.variance p (fun z => a * X z + b * Y z) =
      a^2 * AronowAudit.P004.variance p X + b^2 * AronowAudit.P004.variance p Y +
        2*a*b*AronowAudit.P004.cov p X Y := by
  have hsq : (fun z => (a * X z + b * Y z) * (a * X z + b * Y z)) =
      (fun z => a^2 * (X z * X z) + b^2 * (Y z * Y z) +
        (2*a*b) * (X z * Y z)) := by
    funext z
    ring
  unfold AronowAudit.P004.variance AronowAudit.P004.cov
  rw [hsq]
  simp only [AronowAudit.P004.expect_add, AronowAudit.P004.expect_mul]
  ring

private lemma ht_sparse_formula {N : ℕ} (hN : 0 < N) (z : Assignment N) :
    AronowAudit.P004.ht (fun _ => (1/2 : ℝ)) (AronowAudit.P004.sparseTable N) z =
      (5/(2*(N : ℝ))) * AronowAudit.P004.bit (z ⟨0,hN⟩) -
        1/(2*(N : ℝ)) := by
  let o : Fin N := ⟨0, hN⟩
  have hsum :
      (∑ i : Fin N,
        (AronowAudit.P004.bit (z i) * AronowAudit.P004.sparseTable N i z / (1/2) -
          (1-AronowAudit.P004.bit (z i))*AronowAudit.P004.sparseTable N i z/(1-1/2))) =
       AronowAudit.P004.bit (z o) * AronowAudit.P004.sparseTable N o z/(1/2) -
          (1-AronowAudit.P004.bit (z o))*AronowAudit.P004.sparseTable N o z/(1-1/2) := by
    apply Finset.sum_eq_single o
    · intro i hi hio
      have hne : i.val ≠ 0 := by
        intro hv
        apply hio
        exact Fin.ext hv
      simp [AronowAudit.P004.sparseTable, hne]
    · simp
  change (∑ i : Fin N,
        (AronowAudit.P004.bit (z i) * AronowAudit.P004.sparseTable N i z / (1/2) -
          (1-AronowAudit.P004.bit (z i))*AronowAudit.P004.sparseTable N i z/(1-1/2))) /
      (N : ℝ) = _
  rw [hsum]
  cases hz : z o <;> norm_num [AronowAudit.P004.sparseTable, o, AronowAudit.P004.bit, hz]
  · field_simp
    <;> ring
  · field_simp
    <;> ring

private lemma sparse_linear_formula {N : ℕ} (hN : 0 < N) :
    SAP.P004b.linearHajek (fun _ => (1/2 : ℝ))
        (SAP.P004b.wholeSparseR N) =
      (fun z => (5/(2*(N : ℝ))) * bit (z ⟨0,hN⟩) -
        (5/(2*(N : ℝ)^2)) * armCount z true + 3/(4*(N : ℝ))) := by
  have hR : SAP.P004b.wholeSparseR N = AronowAudit.P004.sparseTable N := by
    have hP : SAP.P004b.Bridge.population (SAP.P004b.sparsePopulation N) =
        AronowAudit.P004.sparsePopulation N := by
      simpa [SAP.P004b.Bridge.sequence] using
        congrFun SAP.P004b.Bridge.sparsePopulation_eq N
    unfold SAP.P004b.wholeSparseR
    calc
      _ = AronowAudit.P004.circleAverage
          (SAP.P004b.Bridge.population (SAP.P004b.sparsePopulation N)) 1 :=
            SAP.P004b.Bridge.circleAverage_eq (SAP.P004b.sparsePopulation N) 1
      _ = AronowAudit.P004.circleAverage (AronowAudit.P004.sparsePopulation N) 1 := by
            rw [hP]
      _ = AronowAudit.P004.sparseTable N := AronowAudit.P004.Wave1.T27_circle N
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  funext z
  rw [hR]
  change AronowAudit.P004.linearHajek (fun _ => (1/2 : ℝ))
      (AronowAudit.P004.sparseTable N) z =
      (5/(2*(N : ℝ))) * AronowAudit.P004.bit (z ⟨0,hN⟩) -
        (5/(2*(N : ℝ)^2)) * AronowAudit.P004.armCount z true + 3/(4*(N : ℝ))
  rw [AronowAudit.P004.Wave1.T27_linear_identity hN z,
    ht_sparse_formula hN z]
  field_simp [hn]
  <;> ring

end SAP.P004b.WH.W3.P.T27_L3

open SAP.P004b
open SAP.P004b.WH.W3.P.T27_L3
open AronowAudit.P004
open scoped BigOperators Classical

theorem SAP.P004b.WH.W3.T27_L3_proof : SAP.P004b.WH.W3.T27_L3 := by
  intro N hN
  let o : Fin N := ⟨0, by omega⟩
  let p : Fin N → ℝ := fun _ => 1/2
  let X : Assignment N → ℝ := fun z => bit (z o)
  let Y : Assignment N → ℝ := fun z => armCount z true
  have hq := AronowAudit.P004.Wave1.T27_count_moments (N := N) true
  have hqvar : AronowAudit.P004.variance p Y = (N : ℝ)/4 := by
    change AronowAudit.P004.variance (fun _ : Fin N => (1/2 : ℝ))
      (fun z => AronowAudit.P004.armCount z true) = _
    exact hq.2
  have hXvar : AronowAudit.P004.variance p X = 1/4 := by
    change AronowAudit.P004.variance (fun _ : Fin N => (1/2 : ℝ))
      (fun z => bit (z ⟨0, by omega⟩)) = 1/4
    exact first_variance (by omega)
  have hcov : AronowAudit.P004.cov p X Y = 1/4 := by
    change AronowAudit.P004.cov (fun _ : Fin N => (1/2 : ℝ))
      (fun z => bit (z ⟨0, by omega⟩))
      (fun z => AronowAudit.P004.armCount z true) = 1/4
    exact count_first_cov (by omega)
  have hform := sparse_linear_formula (N := N) (by omega : 0 < N)
  have hlin : linearHajek (fun _ => (1/2 : ℝ)) (wholeSparseR N) =
      (fun z => (5/(2*(N : ℝ))) * X z -
        (5/(2*(N : ℝ)^2)) * Y z + 3/(4*(N : ℝ))) := by
    simpa [X, Y, o] using hform
  rw [hlin]
  change AronowAudit.P004.variance p
    (fun z => (5/(2*(N : ℝ))) * X z -
      (5/(2*(N : ℝ)^2)) * Y z + 3/(4*(N : ℝ))) = _
  rw [AronowAudit.P004.GraphCompletion.variance_add_const]
  have hlincomb : (fun z => (5/(2*(N : ℝ))) * X z -
      (5/(2*(N : ℝ)^2)) * Y z) =
      (fun z => (5/(2*(N : ℝ))) * X z +
        (-(5/(2*(N : ℝ)^2))) * Y z) := by
    funext z
    ring
  rw [hlincomb, variance_linear, hXvar, hqvar, hcov]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (by omega))
  field_simp [hn]
  <;> ring
