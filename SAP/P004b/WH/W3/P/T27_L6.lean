import SAP.P004b.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T27_L6

open scoped BigOperators Matrix Classical
open MeasureTheory ProbabilityTheory
noncomputable section

lemma sqrt_scale (q : ℝ) (hq : 0 < q) (hq1 : 1 < q) :
    Real.sqrt ((q-1)/q^3) * Real.sqrt (q/(q-1)) = 1/q := by
  have hqm : 0 < q-1 := by linarith
  have ha : 0 ≤ (q-1)/q^3 := by positivity
  have hprod : (q-1)/q^3 * (q/(q-1)) = (1/q)^2 := by
    field_simp [ne_of_gt hq, ne_of_gt hqm]
  calc
    Real.sqrt ((q-1)/q^3) * Real.sqrt (q/(q-1)) =
        Real.sqrt ((q-1)/q^3 * (q/(q-1)) ) := by rw [← Real.sqrt_mul ha]
    _ = Real.sqrt ((1/q)^2) := by rw [hprod]
    _ = 1/q := by rw [Real.sqrt_sq_eq_abs, abs_of_pos (one_div_pos.mpr hq)]

end
end SAP.P004b.WH.W3.P.T27_L6

open scoped BigOperators Matrix Classical
open MeasureTheory ProbabilityTheory

theorem SAP.P004b.WH.W3.T27_L6_proof : SAP.P004b.WH.W3.T27_L6 := by
  intro N hN z hq hqN
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnN : 0 < N := by omega
  let o : Fin N := ⟨0, by omega⟩
  have hfirst : SAP.P004b.wholeFirst z = z o := by
    simp [SAP.P004b.wholeFirst, hnN, o]
  have hqdef : SAP.P004b.wholeSparseQ z = armCount z (z o) := by
    simp [SAP.P004b.wholeSparseQ, hfirst]
  have hR : SAP.P004b.wholeSparseR N = sparseTable N :=
    AronowAudit.P004.Wave1.T27_circle N
  have hame0 : ame (fun _ => (1/2 : ℝ)) (sparseTable N) =
      (3/4 : ℝ)/(N : ℝ) := by
    exact AronowAudit.P004.Wave1.T27_ame (by omega)
  have hame : ame (fun _ => (1/2 : ℝ)) (SAP.P004b.wholeSparseR N) =
      3/(4*(N : ℝ)) := by
    rw [hR, hame0]
    ring
  have hcomp : armCount z true + armCount z false = (N : ℝ) := by
    simpa [SAP.P004b.armCount, AronowAudit.P004.armCount] using
      (AronowAudit.P004.Wave1.T27_count_complement z)
  cases ha : z o with
  | true =>
      have hfirstval : SAP.P004b.wholeFirst z = true := by rw [hfirst, ha]
      have hqbranch : SAP.P004b.wholeSparseQ z = armCount z true := by
        rw [hqdef, ha]
      have hcount : SAP.P004b.wholeSparseQ z + armCount z false = (N : ℝ) := by
        rw [hqbranch]
        exact hcomp
      have htrue : 0 < armCount z true := by
        rw [← hqbranch]
        linarith
      have hfalse : 0 < armCount z false := by
        linarith [hcount, hqN]
      have hmeanT0 := AronowAudit.P004.Wave1.T27_armMean (by omega) z true
      have hmeanT : armMean (sparseTable N) z true = 1/armCount z true := by
        have hmeanT0' : armMean (sparseTable N) z true =
            if z o = true then (1/4+3/4*bit (z o))/armCount z true else 0 := by
          simpa [SAP.P004b.armMean, SAP.P004b.armCount, SAP.P004b.bit,
            AronowAudit.P004.armMean, AronowAudit.P004.armCount,
            AronowAudit.P004.bit, SAP.P004b.sparseTable,
            AronowAudit.P004.sparseTable] using hmeanT0
        rw [hmeanT0']
        simp [ha, SAP.P004b.bit]
        norm_num
      have hmeanF0 := AronowAudit.P004.Wave1.T27_armMean (by omega) z false
      have hmeanF : armMean (sparseTable N) z false = 0 := by
        have hmeanF0' : armMean (sparseTable N) z false =
            if z o = false then (1/4+3/4*bit (z o))/armCount z false else 0 := by
          simpa [SAP.P004b.armMean, SAP.P004b.armCount, SAP.P004b.bit,
            AronowAudit.P004.armMean, AronowAudit.P004.armCount,
            AronowAudit.P004.bit, SAP.P004b.sparseTable,
            AronowAudit.P004.sparseTable] using hmeanF0
        rw [hmeanF0']
        simp [ha]
      have hHbranch : hajek (SAP.P004b.wholeSparseR N) z =
          1/SAP.P004b.wholeSparseQ z := by
        rw [hR, hajek, hmeanT, hmeanF, ← hqbranch]
        ring
      have hVspike : kernelVariance z (residual (sparseTable N) z)
          (distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel
            (sparseBandwidth N)) =
          (1/4+3/4*bit (z (⟨0, by omega⟩ : Fin N)))^2 *
            (armCount z (z (⟨0, by omega⟩ : Fin N))-1)/
              (armCount z (z (⟨0, by omega⟩ : Fin N)))^3 := by
        exact AronowAudit.P004.Wave1.T27_spike_variance (by omega) z htrue hfalse
      have hVbranch : SAP.P004b.wholeSparseHac N z =
          (SAP.P004b.wholeSparseQ z-1)/(SAP.P004b.wholeSparseQ z)^3 := by
        unfold SAP.P004b.wholeSparseHac
        rw [hR]
        change kernelVariance z (residual (sparseTable N) z)
          (distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel
            (sparseBandwidth N)) = _
        rw [hVspike, hqbranch]
        norm_num [o, ha, SAP.P004b.bit]
      have hqpos : 0 < SAP.P004b.wholeSparseQ z := by linarith
      have hqm : 0 < SAP.P004b.wholeSparseQ z - 1 := by linarith
      have hVpos : 0 < SAP.P004b.wholeSparseHac N z := by
        rw [hVbranch]
        exact div_pos hqm (by positivity)
      have hinterval : ValidInterval (SAP.P004b.wholeSparseR N)
          (SAP.P004b.wholeSparseQmat N) z := by
        exact ⟨⟨htrue, hfalse⟩, hVpos⟩
      have hscale := SAP.P004b.WH.W3.P.T27_L6.sqrt_scale (SAP.P004b.wholeSparseQ z) hqpos
        (by linarith : 1 < SAP.P004b.wholeSparseQ z)
      have hrootpos : 0 < Real.sqrt ((SAP.P004b.wholeSparseQ z-1)/
          (SAP.P004b.wholeSparseQ z)^3) :=
        Real.sqrt_pos.mpr (div_pos hqm (by positivity))
      have hstat : SAP.P004b.wholeSparseT N z =
          (1-3*SAP.P004b.wholeSparseQ z/(4*N))*
            Real.sqrt (SAP.P004b.wholeSparseQ z/
              (SAP.P004b.wholeSparseQ z-1)) := by
        unfold SAP.P004b.wholeSparseT
        rw [hHbranch, hame, hVbranch]
        apply (div_eq_iff hrootpos.ne').2
        calc
          1/SAP.P004b.wholeSparseQ z-3/(4*(N : ℝ)) =
              (1-3*SAP.P004b.wholeSparseQ z/(4*(N : ℝ))) /
                SAP.P004b.wholeSparseQ z := by
                  field_simp [ne_of_gt hqpos, ne_of_gt hn]
                  <;> ring
          _ = (1-3*SAP.P004b.wholeSparseQ z/(4*(N : ℝ))) *
              (Real.sqrt ((SAP.P004b.wholeSparseQ z-1)/
                (SAP.P004b.wholeSparseQ z)^3) *
                Real.sqrt (SAP.P004b.wholeSparseQ z/
                  (SAP.P004b.wholeSparseQ z-1))) := by rw [hscale]; ring
          _ = ((1-3*SAP.P004b.wholeSparseQ z/(4*(N : ℝ))) *
                Real.sqrt (SAP.P004b.wholeSparseQ z/
                  (SAP.P004b.wholeSparseQ z-1))) *
              Real.sqrt ((SAP.P004b.wholeSparseQ z-1)/
                (SAP.P004b.wholeSparseQ z)^3) := by
                  calc
                    _ = Real.sqrt ((SAP.P004b.wholeSparseQ z-1)/
                          (SAP.P004b.wholeSparseQ z)^3) *
                        ((1-3*SAP.P004b.wholeSparseQ z/(4*(N : ℝ))) *
                          Real.sqrt (SAP.P004b.wholeSparseQ z/
                            (SAP.P004b.wholeSparseQ z-1))) := by
                              exact mul_left_comm
                                (1-3*SAP.P004b.wholeSparseQ z/(4*(N : ℝ)))
                                (Real.sqrt ((SAP.P004b.wholeSparseQ z-1)/
                                  (SAP.P004b.wholeSparseQ z)^3))
                                (Real.sqrt (SAP.P004b.wholeSparseQ z/
                                  (SAP.P004b.wholeSparseQ z-1)))
                    _ = ((1-3*SAP.P004b.wholeSparseQ z/(4*(N : ℝ))) *
                          Real.sqrt (SAP.P004b.wholeSparseQ z/
                            (SAP.P004b.wholeSparseQ z-1))) *
                          Real.sqrt ((SAP.P004b.wholeSparseQ z-1)/
                            (SAP.P004b.wholeSparseQ z)^3) := by exact mul_comm _ _
      refine ⟨hinterval, ?_, ?_, ?_⟩
      · simpa [hfirstval] using hHbranch
      · simpa [hfirstval] using hVbranch
      · simpa [hfirstval] using hstat
  | false =>
      have hfirstval : SAP.P004b.wholeFirst z = false := by rw [hfirst, ha]
      have hqbranch : SAP.P004b.wholeSparseQ z = armCount z false := by
        rw [hqdef, ha]
      have hcount : armCount z true + SAP.P004b.wholeSparseQ z = (N : ℝ) := by
        rw [hqbranch]
        linarith [hcomp]
      have hfalse : 0 < armCount z false := by
        rw [← hqbranch]
        linarith
      have htrue : 0 < armCount z true := by
        linarith [hcount, hqN]
      have hmeanT0 := AronowAudit.P004.Wave1.T27_armMean (by omega) z true
      have hmeanT : armMean (sparseTable N) z true = 0 := by
        have hmeanT0' : armMean (sparseTable N) z true =
            if z o = true then (1/4+3/4*bit (z o))/armCount z true else 0 := by
          simpa [SAP.P004b.armMean, SAP.P004b.armCount, SAP.P004b.bit,
            AronowAudit.P004.armMean, AronowAudit.P004.armCount,
            AronowAudit.P004.bit, SAP.P004b.sparseTable,
            AronowAudit.P004.sparseTable] using hmeanT0
        rw [hmeanT0']
        simp [ha]
      have hmeanF0 := AronowAudit.P004.Wave1.T27_armMean (by omega) z false
      have hmeanF : armMean (sparseTable N) z false =
          (1/4)/armCount z false := by
        have hmeanF0' : armMean (sparseTable N) z false =
            if z o = false then (1/4+3/4*bit (z o))/armCount z false else 0 := by
          simpa [SAP.P004b.armMean, SAP.P004b.armCount, SAP.P004b.bit,
            AronowAudit.P004.armMean, AronowAudit.P004.armCount,
            AronowAudit.P004.bit, SAP.P004b.sparseTable,
            AronowAudit.P004.sparseTable] using hmeanF0
        rw [hmeanF0']
        simp [ha, bit]
      have hHbranch : hajek (SAP.P004b.wholeSparseR N) z =
          -1/(4*SAP.P004b.wholeSparseQ z) := by
        rw [hR, hajek, hmeanT, hmeanF, ← hqbranch]
        field_simp [ne_of_gt hfalse]
        <;> ring
      have hVspike : kernelVariance z (residual (sparseTable N) z)
          (distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel
            (sparseBandwidth N)) =
          (1/4+3/4*bit (z (⟨0, by omega⟩ : Fin N)))^2 *
            (armCount z (z (⟨0, by omega⟩ : Fin N))-1)/
              (armCount z (z (⟨0, by omega⟩ : Fin N)))^3 := by
        exact AronowAudit.P004.Wave1.T27_spike_variance (by omega) z htrue hfalse
      have hVbranch : SAP.P004b.wholeSparseHac N z =
          (SAP.P004b.wholeSparseQ z-1)/
            (16*(SAP.P004b.wholeSparseQ z)^3) := by
        unfold SAP.P004b.wholeSparseHac
        rw [hR]
        change kernelVariance z (residual (sparseTable N) z)
          (distanceKernel (nodeSeparation (sparsePopulation N)) uniformKernel
            (sparseBandwidth N)) = _
        rw [hVspike, hqbranch]
        norm_num [o, ha, SAP.P004b.bit]
        field_simp [ne_of_gt hfalse]
        <;> ring_nf
      have hqpos : 0 < SAP.P004b.wholeSparseQ z := by linarith
      have hqm : 0 < SAP.P004b.wholeSparseQ z - 1 := by linarith
      have hVpos : 0 < SAP.P004b.wholeSparseHac N z := by
        rw [hVbranch]
        exact div_pos hqm (by positivity)
      have hinterval : ValidInterval (SAP.P004b.wholeSparseR N)
          (SAP.P004b.wholeSparseQmat N) z := by
        exact ⟨⟨htrue, hfalse⟩, hVpos⟩
      let q := SAP.P004b.wholeSparseQ z
      have hqpos' : 0 < q := hqpos
      have hscale := SAP.P004b.WH.W3.P.T27_L6.sqrt_scale q hqpos (by linarith : 1 < q)
      have hApos : 0 ≤ (q-1)/q^3 := by positivity
      have hrootpos : 0 < Real.sqrt ((q-1)/q^3) :=
        Real.sqrt_pos.mpr (div_pos (by linarith) (by positivity))
      have hroot : Real.sqrt ((q-1)/(16*q^3)) =
          (1/4)*Real.sqrt ((q-1)/q^3) := by
        have heq : (q-1)/(16*q^3) = ((q-1)/q^3)/16 := by
          field_simp [ne_of_gt hqpos]
          <;> ring
        rw [heq, Real.sqrt_div hApos]
        norm_num
        <;> ring
      have hstat : SAP.P004b.wholeSparseT N z =
          -(1+3*q/N)*Real.sqrt (q/(q-1)) := by
        unfold SAP.P004b.wholeSparseT
        rw [hHbranch, hame, hVbranch]
        rw [hroot]
        apply (div_eq_iff (mul_pos (by norm_num) hrootpos).ne').2
        calc
          -1/(4*q)-3/(4*(N : ℝ)) = -(1+3*q/(N : ℝ))/(4*q) := by
            field_simp [ne_of_gt hqpos, ne_of_gt hn]
            <;> ring
          _ = -(1+3*q/(N : ℝ))*(1/q)/4 := by
            field_simp [ne_of_gt hqpos', ne_of_gt hn]
            <;> ring_nf
          _ = -(1+3*q/(N : ℝ)) *
              (Real.sqrt ((q-1)/q^3)*Real.sqrt (q/(q-1)))/4 := by rw [hscale]
          _ = (-(1+3*q/(N : ℝ))*Real.sqrt (q/(q-1))) *
              ((1/4 : ℝ)*Real.sqrt ((q-1)/q^3)) := by
                field_simp [ne_of_gt hqpos', ne_of_gt hn]
                <;> ring_nf
      refine ⟨hinterval, ?_, ?_, ?_⟩
      · simpa [hfirstval] using hHbranch
      · simpa [hfirstval] using hVbranch
      · simpa [hfirstval] using hstat

