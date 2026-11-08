import SAP.P003a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W2.P.T12_L2

open SAP.P003a.Bridge
attribute [local instance 0] Classical.propDecidable

open scoped BigOperators

theorem labeled_tail_eq_pValue (n m : ℕ) (y : PotentialTable n)
    (hm : 0 < m) (hmn : m < n) (z : Assignment n m) :
    (pValue (tableCounts y) (unitObserved (unitOutcomes y z.val) z.val) : ℝ) =
      w2Tail m y (w2Deviation y z) := by
  let v : AronowAudit.P003.Counts := toAudit (tableCounts y)
  let o : Counts := unitObserved (unitOutcomes y z.val) z.val
  have hw : AronowAudit.P003.tableCounts y = v := by
    simp [v]
  have hcouple := AronowAudit.P003.Wave1.couplingB2_observed y z.val
  have htreated : AronowAudit.P003.Wave1.couplingB2_treated y z.val =
      AronowAudit.P003.Wave1.neyman_treated y z.val := rfl
  rw [htreated] at hcouple
  have houtcomes : AronowAudit.P003.unitOutcomes y z.val = unitOutcomes y z.val := rfl
  have hobs' : toAudit o = AronowAudit.P003.observed v
      (AronowAudit.P003.Wave1.neyman_treated y z.val) := by
    simpa only [v, o, houtcomes, to_unitObserved, to_tableCounts] using hcouple
  have hobs : AronowAudit.P003.observed v
      (AronowAudit.P003.Wave1.neyman_treated y z.val) = toAudit o := hobs'.symm
  have hqmem : AronowAudit.P003.Wave1.neyman_treated y z.val ∈
      AronowAudit.P003.randomStates v m :=
    AronowAudit.P003.Wave1.neyman_treated_mem y v hw m z
  have harms := AronowAudit.P003.Wave1.neyman_observed_arms v
    (AronowAudit.P003.Wave1.neyman_treated y z.val) m hqmem
  have ho : (toAudit o).total = v.total := by
    rw [← hobs]
    exact harms.1
  have hom : (toAudit o).a + (toAudit o).b = m := by
    rw [← hobs]
    exact harms.2
  have htau : AronowAudit.P003.tableTau y = AronowAudit.P003.tau v := by
    calc
      AronowAudit.P003.tableTau y = tableTau y := to_tableTau y
      _ = tau (tableCounts y) := table_effect n y (by omega)
      _ = AronowAudit.P003.tau v := by simp [v]
  let E : AronowAudit.P003.Counts → Prop := fun q =>
    (AronowAudit.P003.deviationNumerator v
      (AronowAudit.P003.observed v q) m).natAbs ≥
        (AronowAudit.P003.deviationNumerator v (toAudit o) m).natAbs
  have hpred (q : Assignment n m) :
      (|AronowAudit.P003.tableEstimator y q.val - AronowAudit.P003.tableTau y| ≥
        |AronowAudit.P003.tableEstimator y z.val - AronowAudit.P003.tableTau y|) ↔
        E (AronowAudit.P003.Wave1.neyman_treated y q.val) := by
    rw [htau,
      AronowAudit.P003.Wave1.neyman_estimator_eq y v hw m q,
      AronowAudit.P003.Wave1.neyman_estimator_eq y v hw m z,
      hobs]
    have hqmem := AronowAudit.P003.Wave1.neyman_treated_mem y v hw m q
    have hqarm := AronowAudit.P003.Wave1.neyman_observed_arms v
      (AronowAudit.P003.Wave1.neyman_treated y q.val) m hqmem
    exact AronowAudit.P003.Wave1.neyman_tail_iff v (toAudit o)
      (AronowAudit.P003.observed v (AronowAudit.P003.Wave1.neyman_treated y q.val))
      m ho hom hqarm.1 hqarm.2 ⟨hm, by
        have hvn : v.total = n := by
          rw [← hw]
          exact AronowAudit.P003.Wave1.neyman_table_total y
        rw [hvn]
        exact hmn⟩
  have hevent :
      (fun q : Assignment n m =>
        |AronowAudit.P003.tableEstimator y q.val - AronowAudit.P003.tableTau y| ≥
          |AronowAudit.P003.tableEstimator y z.val - AronowAudit.P003.tableTau y|) =
      (fun q => E (AronowAudit.P003.Wave1.neyman_treated y q.val)) := by
    funext q
    exact propext (hpred q)
  have hpush := AronowAudit.P003.Wave1.neyman_event_pushforward y v hw m E
  have hfinite : AronowAudit.P003.designProb v m E =
      (AronowAudit.P003.pValue v (toAudit o) : ℝ) := by
    unfold AronowAudit.P003.designProb AronowAudit.P003.pValue AronowAudit.P003.tailCount
    simp only [hom, AronowAudit.P003.binomial_eq_choose,
      Rat.cast_div, Rat.cast_natCast]
    congr 1
    rw [Nat.cast_list_sum]
    simp only [List.map_map, Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    by_cases he : E q
    · simp only [E, if_pos he]
    · simp only [E, if_neg he, Nat.cast_zero]
  have hprobA :
      AronowAudit.P003.uniformProb (fun q : Assignment n m =>
        |AronowAudit.P003.tableEstimator y q.val - AronowAudit.P003.tableTau y| ≥
          |AronowAudit.P003.tableEstimator y z.val - AronowAudit.P003.tableTau y|) =
        (AronowAudit.P003.pValue v (toAudit o) : ℝ) := by
    rw [hevent, hpush, hfinite]
  have hprob :
      uniformProb (fun q : Assignment n m =>
        |tableEstimator y q.val - tableTau y| ≥ |tableEstimator y z.val - tableTau y|) =
        (pValue (tableCounts y) o : ℝ) := by
    have hconv :
        AronowAudit.P003.uniformProb (fun q : Assignment n m =>
          |AronowAudit.P003.tableEstimator y q.val - AronowAudit.P003.tableTau y| ≥
            |AronowAudit.P003.tableEstimator y z.val - AronowAudit.P003.tableTau y|) =
        uniformProb (fun q : Assignment n m =>
          |tableEstimator y q.val - tableTau y| ≥ |tableEstimator y z.val - tableTau y|) := by
      simp only [AronowAudit.P003.uniformProb, SAP.P003a.uniformProb,
        to_tableEstimator, to_tableTau]
      rfl
    have hpval : AronowAudit.P003.pValue v (toAudit o) =
        pValue (tableCounts y) o := by
      simpa only [v] using to_pValue (tableCounts y) o
    calc
      _ = AronowAudit.P003.uniformProb (fun q : Assignment n m =>
          |AronowAudit.P003.tableEstimator y q.val - AronowAudit.P003.tableTau y| ≥
            |AronowAudit.P003.tableEstimator y z.val - AronowAudit.P003.tableTau y|) := hconv.symm
      _ = (AronowAudit.P003.pValue v (toAudit o) : ℝ) := hprobA
      _ = (pValue (tableCounts y) o : ℝ) := by rw [hpval]
  change (pValue (tableCounts y) o : ℝ) =
    uniformProb (fun q : Assignment n m => w2Deviation y z ≤ w2Deviation y q)
  have hactual :
      (fun q : Assignment n m =>
        |tableEstimator y q.val - tableTau y| ≥ |tableEstimator y z.val - tableTau y|) =
      (fun q => w2Deviation y z ≤ w2Deviation y q) := by
    funext q
    apply propext
    rfl
  rw [← hactual]
  exact hprob.symm

end SAP.P003a.WH.W2.P.T12_L2

theorem SAP.P003a.WH.W2.T12_L2_proof : SAP.P003a.WH.W2.T12_L2 := by
  intro n m y hm hmn z
  exact SAP.P003a.WH.W2.P.T12_L2.labeled_tail_eq_pValue n m y hm hmn z
