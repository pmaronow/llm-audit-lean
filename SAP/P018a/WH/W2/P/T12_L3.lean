import SAP.P018a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

noncomputable section

open SAP.P018a Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction ENNReal

theorem SAP.P018a.WH.W2.T12_L3_proof : SAP.P018a.WH.W2.T12_L3 := by
  classical
  intro hL1 U _ k N R hR w β
  let P := repeatedLaw R N
  let q := fun d : Dyad N => fun ω : Fin N → U =>
    recordWeightedBlockScore R w β ω d
  letI : IsProbabilityMeasure R.μ := hR.1
  letI : IsProbabilityMeasure P := by
    dsimp [P, repeatedLaw]
    infer_instance
  have hInf (d : Dyad N) (a : Fin k) :
      MemLp (fun ω => q d ω a) ∞ P := (hL1 R hR w).2.2 β d a
  have hLp (d : Dyad N) (a : Fin k) :
      MemLp (fun ω => q d ω a) 2 P :=
    (hInf d a).mono_exponent (by norm_num)
  have hpair (d : Dyad N) : Measurable
      (fun ω : Fin N → U => (ω (firstUnit d), ω (secondUnit d))) :=
    (measurable_pi_apply (firstUnit d)).prodMk
      (measurable_pi_apply (secondUnit d))
  have hX (d : Dyad N) (t : Fin (R.T N d)) (a : Fin k) :
      Measurable (fun ω => repeatedX R ω d t a) := by
    exact ((measurable_pi_apply a).comp
      ((hR.2.1 d t).1.comp (hpair d)))
  have hY (d : Dyad N) (t : Fin (R.T N d)) :
      Measurable (fun ω => repeatedY R ω d t) := by
    exact (hR.2.1 d t).2.comp (hpair d)
  have hmeas (d : Dyad N) (a : Fin k) :
      Measurable (fun ω => q d ω a) := by
    simp only [q, recordWeightedBlockScore, Finset.sum_apply, score,
      Pi.smul_apply, smul_eq_mul, dot]
    apply Finset.measurable_fun_sum
    intro t ht
    exact (measurable_const.mul ((hY d t).sub
      (Finset.measurable_fun_sum _ (fun b _ =>
        (hX d t b).mul measurable_const)))).mul (hX d t a)
  have hsupport (d : Dyad N) (ω ω' : Fin N → U)
      (h : ∀ i ∈ members d, ω i = ω' i) : q d ω = q d ω' := by
    have hfirst : firstUnit d ∈ members d := by
      dsimp [firstUnit]
      exact Finset.min'_mem _ _
    have hsecond : secondUnit d ∈ members d := by
      dsimp [secondUnit]
      exact Finset.max'_mem _ _
    simp only [q, recordWeightedBlockScore, repeatedX, repeatedY]
    rw [h _ hfirst, h _ hsecond]
  have hcov (d f : Dyad N) (hdf : ¬overlap d f) :
      covMat P (q d) (q f) = 0 := by
    ext a b
    exact AronowAudit.P018.Wave1.WeightedConsistency.g2_proof R.μ
      (members d) (members f) (fun ω => q d ω a) (fun ω => q f ω b)
      (Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hdf))
      (hmeas d a) (hmeas f b)
      (fun ω ω' h => congrFun (hsupport d ω ω' h) a)
      (fun ω ω' h => congrFun (hsupport f ω ω' h) b)
      (hLp d a) (hLp f b)
  have hsplit (d : Dyad N) :
      (∑ f : Dyad N, covMat P (q d) (q f)) =
        varMat P (q d) + ∑ f ∈ neighbors d, covMat P (q d) (q f) := by
    have hzero (f : Dyad N) (hdf : ¬overlap d f) := hcov d f hdf
    rw [← Finset.sum_erase_add (s := (Finset.univ : Finset (Dyad N)))
      (a := d) (f := fun f => covMat P (q d) (q f)) (Finset.mem_univ d)]
    have hsub : neighbors d ⊆ (Finset.univ : Finset (Dyad N)).erase d := by
      intro f hf
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      simp [hf.1]
    have hsum :
        (∑ f ∈ (Finset.univ : Finset (Dyad N)).erase d,
          covMat P (q d) (q f)) =
        ∑ f ∈ neighbors d, covMat P (q d) (q f) := by
      symm
      apply Finset.sum_subset hsub
      intro f hf hnot
      apply hzero f
      intro hov
      apply hnot
      simp only [neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simpa using (Finset.ne_of_mem_erase hf), hov⟩
    rw [hsum]
    simp only [varMat]
    exact add_comm _ _
  have hvariance :
      varMat P (fun ω => ∑ d : Dyad N, q d ω) =
        ∑ d : Dyad N, ∑ f : Dyad N, covMat P (q d) (q f) := by
    ext a b
    simp only [varMat, covMat, Matrix.sum_apply, Finset.sum_apply]
    exact ProbabilityTheory.covariance_fun_sum_fun_sum
      (fun d => hLp d a) (fun f => hLp f b)
  have hcentered (hz : ∀ d : Dyad N, meanVec P (q d) = 0) :
      (∀ d f : Dyad N, covMat P (q d) (q f) =
        meanMat P (fun ω => outer (q d ω) (q f ω))) ∧
      varMat P (fun ω => ∑ d : Dyad N, q d ω) =
        meanMat P (fun ω => meat members (fun d => q d ω)) := by
    have hsp : varMat P (fun ω => ∑ d : Dyad N, q d ω) =
        ∑ d : Dyad N, ∑ f : Dyad N,
          if (members d ∩ members f).Nonempty then
            meanMat P (fun ω => outer (q d ω) (q f ω)) else 0 := by
      rw [hvariance]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      by_cases hov : (members d ∩ members f).Nonempty
      · simp only [hov, ite_true]
        ext a b
        have hza := congrFun (hz d) a
        have hzb := congrFun (hz f) b
        simp only [meanVec, Pi.zero_apply] at hza hzb
        simp only [covMat, meanMat, outer]
        rw [ProbabilityTheory.covariance_eq_sub (hLp d a) (hLp f b), hza, hzb]
        simp
      · simp only [hov, ite_false]
        exact hcov d f (by change ¬overlap d f; exact hov)
    refine ⟨?_, ?_⟩
    · intro d f
      ext a b
      have hza := congrFun (hz d) a
      have hzb := congrFun (hz f) b
      simp only [meanVec, Pi.zero_apply] at hza hzb
      simp only [covMat, meanMat, outer]
      rw [ProbabilityTheory.covariance_eq_sub (hLp d a) (hLp f b), hza, hzb]
      simp
    · rw [hsp]
      symm
      ext a b
      simp only [meanMat, meat, Matrix.sum_apply,
        AronowAudit.P018.matrix_ite_apply, outer,
        Matrix.zero_apply]
      have hi (d f : Dyad N) : Integrable
          (fun ω => if (members d ∩ members f).Nonempty then
            q d ω a * q f ω b else 0) P := by
        by_cases hov : (members d ∩ members f).Nonempty
        · split_ifs
          exact (hLp d a).integrable_mul (hLp f b)
        · split_ifs
          exact integrable_const _
      rw [integral_finsetSum _ (fun d _ =>
        integrable_finsetSum _ (fun f _ => hi d f))]
      simp_rw [integral_finsetSum _ (fun f _ => hi _ f)]
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro f hf
      split_ifs <;> simp [meanMat, outer]
  dsimp only [SAP.P018a.WH.W2.T12_L3, wholeRecordSparse]
  refine ⟨hcov, ?_, ?_⟩
  · rw [hvariance]
    apply Finset.sum_congr rfl
    intro d hd
    exact hsplit d
  · intro hz
    exact hcentered hz

end
