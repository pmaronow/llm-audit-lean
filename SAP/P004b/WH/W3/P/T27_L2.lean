import SAP.P004b.WH.W3.Leaves
import AronowAudit.P004.Wave1.FiniteConditioning.FC4
import AronowAudit.P004.Wave1.FiniteConditioning.FC6
import AronowAudit.P004.Wave1.FiniteConditioning.FC7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004b.WH.W3.P.T27_L2

open SAP.P004b MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix Classical Topology
noncomputable section

lemma half_admissible {N : ℕ} :
    AronowAudit.P004.Wave1.FiniteConditioning.Admissible
      (fun _ : Fin N => (1/2 : ℝ)) := by
  intro i
  norm_num

lemma sparse_average_abs_le_one (hdisks : WholeSparseDisks)
    {N : ℕ} (hN : 0 < N) (d : ℝ) (hd : 0 ≤ d) (i : Fin N) :
    ∀ z, |circleAverage (sparsePopulation N) d i z| ≤ 1 := by
  have hformula := (hdisks N hN d hd).2 i
  have hself : nodeSeparation (sparsePopulation N) i i = 0 := by
    simp [nodeSeparation, sparsePopulation]
  have hi : i ∈ ball (nodeSeparation (sparsePopulation N)) i d := by
    simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hself]
    exact hd
  have hcardNat : 1 ≤ (ball (nodeSeparation (sparsePopulation N)) i d).card :=
    Finset.card_pos.mpr ⟨i, hi⟩
  have hcard : (1 : ℝ) ≤ ((ball (nodeSeparation (sparsePopulation N)) i d).card : ℝ) := by
    exact_mod_cast hcardNat
  intro z
  rw [hformula z]
  by_cases hnear : nodeSeparation (sparsePopulation N) i ⟨0, hN⟩ ≤ d
  · simp only [if_pos hnear]
    let num : ℝ := 1/4 + 3/4 * bit (wholeFirst z)
    let den : ℝ := ((ball (nodeSeparation (sparsePopulation N)) i d).card : ℝ)
    have hnum : 0 ≤ num ∧ num ≤ 1 := by
      dsimp [num]
      cases wholeFirst z <;> norm_num [bit]
    have hden : 0 < den := lt_of_lt_of_le (by norm_num) hcard
    have hquot0 : 0 ≤ num / den := div_nonneg hnum.1 hden.le
    have hquot1 : num / den ≤ 1 := (div_le_iff₀ hden).2 (by
      simpa only [one_mul] using (le_trans hnum.2 hcard))
    change |num / den| ≤ 1
    exact abs_le.mpr ⟨by linarith [hquot0], hquot1⟩
  · simp only [if_neg hnear]
    norm_num

lemma sparse_average_depends_if_far (hdisks : WholeSparseDisks)
    {N : ℕ} (hN : 0 < N) (d s : ℝ) (hd : 0 ≤ d) (hs : d < s)
    (i : Fin N) :
    ∀ z z', (∀ k ∈ ball (nodeSeparation (sparsePopulation N)) i s, z k = z' k) →
      circleAverage (sparsePopulation N) d i z = circleAverage (sparsePopulation N) d i z' := by
  have hformula := (hdisks N hN d hd).2 i
  let first : Fin N := ⟨0, hN⟩
  have hpick : ∀ z z', z first = z' first → wholeFirst z = wholeFirst z' := by
    intro z z' h
    simpa [wholeFirst, first, hN] using h
  intro z z' hagree
  by_cases hnear : nodeSeparation (sparsePopulation N) i first ≤ d
  · have hfirst : first ∈ ball (nodeSeparation (sparsePopulation N)) i s := by
      simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
      exact le_trans hnear (le_of_lt hs)
    have hcoin := hpick z z' (hagree first hfirst)
    rw [hformula z, hformula z', if_pos hnear, if_pos hnear]
    rw [hcoin]
  · rw [hformula z, hformula z', if_neg hnear, if_neg hnear]

lemma empty_conditionOn_eq_expect {N : ℕ} (p : Fin N → ℝ)
    (U : Assignment N → ℝ) :
    conditionOn p (∅ : Finset (Fin N)) U = fun _ => expect p U := by
  funext z
  simp [conditionOn, expect]

lemma l2_center_le {N : ℕ} (p : Fin N → ℝ) (U : Assignment N → ℝ) :
    AronowAudit.P004.l2Norm p (fun z => U z - AronowAudit.P004.expect p U) ≤
      AronowAudit.P004.l2Norm p U := by
  apply Real.sqrt_le_sqrt
  have he : AronowAudit.P004.expect p (fun z => (U z - AronowAudit.P004.expect p U)^2) =
      AronowAudit.P004.variance p U := by
    simpa only [AronowAudit.P004.variance, AronowAudit.P004.cov, pow_two] using
      (AronowAudit.P004.cov_centered p U U).symm
  rw [he]
  exact AronowAudit.P004.variance_le_second p U

lemma projection_error_le_norm {N : ℕ} (p : Fin N → ℝ)
    (hp : AronowAudit.P004.Wave1.FiniteConditioning.Admissible p)
    (J : Finset (Fin N)) (U : Assignment N → ℝ) :
    AronowAudit.P004.l2Norm p (fun z => U z - AronowAudit.P004.conditionOn p J U z) ≤
      AronowAudit.P004.l2Norm p U := by
  have hproj := (AronowAudit.P004.Wave1.FiniteConditioning.fc6_proof p hp J U).2
    (∅ : Finset (Fin N)) (Finset.empty_subset J)
  have hempty : AronowAudit.P004.conditionOn p (∅ : Finset (Fin N)) U =
      fun _ => AronowAudit.P004.expect p U := by
    funext z
    simp [AronowAudit.P004.conditionOn, AronowAudit.P004.expect]
  rw [hempty] at hproj
  exact hproj.trans (l2_center_le p U)

lemma sparse_projection_error_bound (hdisks : WholeSparseDisks)
    {N : ℕ} (d : ℝ) (hd : 0 ≤ d) (i : Fin N) (s : ℝ) (hs : 0 ≤ s) :
    l2Norm (fun _ : Fin N => (1/2 : ℝ))
      (fun z => circleAverage (sparsePopulation N) d i z -
        conditionOn (fun _ => (1/2 : ℝ))
          (ball (nodeSeparation (sparsePopulation N)) i s)
          (circleAverage (sparsePopulation N) d i) z) ≤ if s ≤ d then 1 else 0 := by
  have hN : 0 < N := Nat.zero_lt_of_lt i.isLt
  have hp := half_admissible (N := N)
  let J := ball (nodeSeparation (sparsePopulation N)) i s
  by_cases hsd : s ≤ d
  · simp only [if_pos hsd]
    have hnorm : AronowAudit.P004.l2Norm (fun _ : Fin N => (1/2 : ℝ))
        (circleAverage (sparsePopulation N) d i) ≤ 1 := by
      exact (AronowAudit.P004.Wave1.FiniteConditioning.fc7_proof
        (fun _ : Fin N => (1/2 : ℝ)) hp).2.2.2.2.2.1 _ 1
        (sparse_average_abs_le_one hdisks hN d hd i)
    have hproj := projection_error_le_norm (fun _ : Fin N => (1/2 : ℝ)) hp J
      (circleAverage (sparsePopulation N) d i)
    change AronowAudit.P004.l2Norm (fun _ : Fin N => (1/2 : ℝ))
      (fun z => circleAverage (sparsePopulation N) d i z -
        AronowAudit.P004.conditionOn (fun _ => (1/2 : ℝ)) J
          (circleAverage (sparsePopulation N) d i) z) ≤ 1
    simpa [J] using hproj.trans hnorm
  · simp only [if_neg hsd]
    have hdep := sparse_average_depends_if_far hdisks hN d s hd
      (lt_of_not_ge hsd) i
    have hc : AronowAudit.P004.conditionOn (fun _ : Fin N => (1/2 : ℝ)) J
        (circleAverage (sparsePopulation N) d i) =
          circleAverage (sparsePopulation N) d i := by
      apply AronowAudit.P004.Wave1.FiniteConditioning.conditionOn_of_depends _ hp J _ hdep
    change AronowAudit.P004.l2Norm (fun _ : Fin N => (1/2 : ℝ))
      (fun z => circleAverage (sparsePopulation N) d i z -
        AronowAudit.P004.conditionOn (fun _ => (1/2 : ℝ)) J
          (circleAverage (sparsePopulation N) d i) z) ≤ 0
    have hz : (fun z : Assignment N => circleAverage (sparsePopulation N) d i z -
        AronowAudit.P004.conditionOn (fun _ : Fin N => (1/2 : ℝ)) J
          (circleAverage (sparsePopulation N) d i) z) = fun _ => 0 := by
      funext z
      rw [hc]
      ring
    rw [hz]
    simp [AronowAudit.P004.l2Norm, AronowAudit.P004.expect]

lemma disk_average_depends_zero_error_at_one (N : ℕ) (i : Fin N) (s : ℝ)
    (hs : 0 ≤ s) :
    l2Norm (fun _ : Fin N => (1/2 : ℝ))
      (fun z => circleAverage (sparsePopulation N) 1 i z -
        conditionOn (fun _ => (1/2 : ℝ))
          (ball (nodeSeparation (sparsePopulation N)) i s)
          (circleAverage (sparsePopulation N) 1 i) z) = 0 := by
  have hcircle : circleAverage (sparsePopulation N) 1 = sparseTable N := by
    have hsrc := AronowAudit.P004.Wave1.T27_circle N
    have hpop : SAP.P004b.Bridge.population (sparsePopulation N) =
        AronowAudit.P004.sparsePopulation N := rfl
    have htable : sparseTable N = AronowAudit.P004.sparseTable N := rfl
    rw [SAP.P004b.Bridge.circleAverage_eq, hpop, htable]
    exact hsrc
  rw [hcircle]
  have hc : conditionOn (fun _ : Fin N => (1/2 : ℝ))
      (ball (nodeSeparation (sparsePopulation N)) i s)
    (sparseTable N i) = sparseTable N i := by
    apply AronowAudit.P004.Wave1.FiniteConditioning.conditionOn_of_depends _ half_admissible
    intro z z' hzz'
    have hself : nodeSeparation (sparsePopulation N) i i = 0 := by
      simp [nodeSeparation, sparsePopulation]
    have hi : i ∈ ball (nodeSeparation (sparsePopulation N)) i s := by
      simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and, hself]
      exact hs
    simp only [sparseTable, hzz' i hi]
  have hcSource : AronowAudit.P004.conditionOn (fun _ : Fin N => (1/2 : ℝ))
      (ball (nodeSeparation (sparsePopulation N)) i s) (sparseTable N i) =
        sparseTable N i := by
    change conditionOn (fun _ : Fin N => (1/2 : ℝ))
      (ball (nodeSeparation (sparsePopulation N)) i s) (sparseTable N i) = _
    exact hc
  change AronowAudit.P004.l2Norm (fun _ : Fin N => (1/2 : ℝ))
    (fun z => sparseTable N i z -
      AronowAudit.P004.conditionOn (fun _ => (1/2 : ℝ))
        (ball (nodeSeparation (sparsePopulation N)) i s) (sparseTable N i) z) = 0
  rw [hcSource]
  simp [AronowAudit.P004.l2Norm, AronowAudit.P004.expect]

end

end SAP.P004b.WH.W3.P.T27_L2

theorem SAP.P004b.WH.W3.T27_L2_proof : SAP.P004b.WH.W3.T27_L2 := by
  intro hdisks
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    let ψ : ℝ → ℝ := fun s => if s ≤ d then 1 else 0
    refine ⟨ψ, (fun N : ℕ => fun _ : Fin N => (1 : ℝ)), 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      by_cases hsd : s ≤ d <;> simp [ψ, hsd]
    · intro x hx y hy hxy
      by_cases hxd : x ≤ d
      · simp [ψ, hxd]
        split_ifs <;> norm_num
      · have hyd : ¬ y ≤ d := fun hyd => hxd (le_trans hxy hyd)
        simp [ψ, hxd, hyd]
    · refine tendsto_const_nhds.congr' ?_
      have htail : ∀ᶠ s : ℝ in Filter.atTop, d < s :=
        Filter.eventually_atTop.2 ⟨d + 1, fun s hs => by linarith⟩
      filter_upwards [htail] with s hs
      simp [ψ, not_le_of_gt hs]
    · refine ⟨5, by norm_num, 1, d + 1, by linarith, ?_⟩
      intro s hs
      have hds : d < s := lt_of_lt_of_le (by linarith) hs
      have hspos : 0 < s := by linarith
      simp only [ψ, if_neg (not_le_of_gt hds)]
      positivity
    · intro N i
      norm_num
    · intro N i s hs
      let J := ball (nodeSeparation (sparsePopulation N)) i s
      have herr := SAP.P004b.WH.W3.P.T27_L2.sparse_projection_error_bound
        hdisks d hd i s hs
      simpa [ψ] using herr
  · intro d hd N i s hs
    exact SAP.P004b.WH.W3.P.T27_L2.sparse_projection_error_bound
      hdisks d hd i s hs
  · exact SAP.P004b.WH.W3.P.T27_L2.disk_average_depends_zero_error_at_one
