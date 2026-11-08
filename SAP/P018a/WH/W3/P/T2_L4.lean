import SAP.P018a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a.WH.W3.P.T2_L4

open Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix.Norms.Elementwise

abbrev D4 := SAP.P018a.Dyad 4
abbrev I6 := Fin 6

def dyad6 (i : I6) : D4 :=
  ⟨SAP.P018a.sixMembers i, by
    fin_cases i <;> decide⟩

def dyadEquiv : I6 ≃ D4 :=
  Equiv.ofBijective dyad6 (by decide)

lemma index_left (i : I6) : dyadEquiv.symm (dyad6 i) = i := by
  exact Equiv.symm_apply_apply dyadEquiv i

def q6 : I6 → Vec 1 := fun i => ![(![1, 0, 0, 0, 0, -1] : I6 → ℝ) i]

def code {N : ℕ} (d : SAP.P018a.Dyad N) : ℕ :=
  (SAP.P018a.members d).sum Fin.val

abbrev R : SAP.P018a.RepeatedKernel Unit 1 :=
  ⟨Measure.dirac (), fun _ _ => 1, fun _ _ _ _ _ => 1,
    fun _ d _ _ _ => if code d = 1 then 1 else if code d = 5 then -1 else 0⟩

lemma hT (d : D4) : R.T 4 d = 1 := rfl

lemma sum_dyad_reindex {α : Type*} [AddCommMonoid α] (f : D4 → α) :
    (∑ d : D4, f d) = ∑ i : I6, f (dyad6 i) := by
  exact (Fintype.sum_equiv dyadEquiv (fun i => f (dyadEquiv i)) f
    (fun _ => rfl)).symm

lemma repeatedAt : SAP.P018a.RepeatedAtSize R 4 := by
  refine ⟨?_, ?_, ?_, 1, by norm_num, ?_⟩
  · dsimp [R]
    infer_instance
  · intro d
    norm_num [R]
  · intro d t
    exact ⟨measurable_const, measurable_const⟩
  · intro d t
    filter_upwards with uv
    change ‖(1 : Vec 1)‖ ≤ 1 ∧ |(if code d = 1 then 1 else if code d = 5 then -1 else 0 : ℝ)| ≤ 1
    constructor
    · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro a
      fin_cases a
      norm_num
    · split_ifs <;> norm_num

lemma hcard : (Fintype.card D4 : ℝ) = 6 := by
  norm_num [show Fintype.card D4 = 6 from by decide]

lemma gram (ω : Fin 4 → Unit) :
    SAP.P018a.repeatedGram R ω = !![(6 : ℝ)] := by
  ext a b
  fin_cases a
  fin_cases b
  simp only [SAP.P018a.repeatedGram, Matrix.sum_apply]
  simp only [SAP.P018a.repeatedX, R, SAP.P018a.outer, Fin.sum_univ_one]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
    Matrix.of_apply]
  norm_num [R, Finset.sum_const, show (SAP.P018a.dyads 4).card = 6 from by decide]

lemma hL : SAP.P018a.repeatedL R 4 = 6 := by
  simp only [SAP.P018a.repeatedL, R, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hcard, mul_one]
  norm_num

lemma hMeanGram :
    meanMat (SAP.P018a.repeatedLaw R 4) (SAP.P018a.repeatedGram R) = !![(6 : ℝ)] := by
  haveI : IsProbabilityMeasure R.μ := by dsimp [R]; infer_instance
  haveI : IsProbabilityMeasure (SAP.P018a.repeatedLaw R 4) := by
    dsimp [SAP.P018a.repeatedLaw]
    infer_instance
  ext a b
  fin_cases a
  fin_cases b
  simp [meanMat, gram]

lemma score6 (i : I6) (ω : Fin 4 → Unit) :
    SAP.P018a.repeatedBlockScore R (0 : Vec 1) ω (dyad6 i) = q6 i := by
  ext a
  fin_cases a
  fin_cases i <;>
    simp [SAP.P018a.repeatedBlockScore, SAP.P018a.repeatedX, SAP.P018a.repeatedY,
      SAP.P018a.score, SAP.P018a.dot, R, code, dyad6, SAP.P018a.sixMembers,
      SAP.P018a.members, q6, Fin.sum_univ_one]

lemma hBeta : SAP.P018a.repeatedBeta R 4 = 0 := by
  haveI : IsProbabilityMeasure R.μ := by dsimp [R]; infer_instance
  haveI : IsProbabilityMeasure (SAP.P018a.repeatedLaw R 4) := by
    dsimp [SAP.P018a.repeatedLaw]
    infer_instance
  have hxy (ω : Fin 4 → Unit) :
      (∑ d : D4, ∑ t : Fin (R.T 4 d),
        SAP.P018a.score (SAP.P018a.repeatedX R ω d t) (SAP.P018a.repeatedY R ω d t)) = 0 := by
    rw [sum_dyad_reindex]
    simp only [Fin.sum_univ_one, SAP.P018a.repeatedX, SAP.P018a.repeatedY]
    norm_num [SAP.P018a.score, code, dyad6, SAP.P018a.sixMembers,
      SAP.P018a.members, Fin.sum_univ_succ]
  have hnum : meanVec (SAP.P018a.repeatedLaw R 4) (fun ω =>
      ∑ d : D4, ∑ t : Fin (R.T 4 d),
        SAP.P018a.score (SAP.P018a.repeatedX R ω d t) (SAP.P018a.repeatedY R ω d t)) = 0 := by
    funext a
    fin_cases a
    have hp : (fun ω : Fin 4 → Unit =>
        (∑ d : D4, ∑ t : Fin (R.T 4 d),
          SAP.P018a.score (SAP.P018a.repeatedX R ω d t)
            (SAP.P018a.repeatedY R ω d t)) 0) = fun _ => 0 := by
      funext ω
      exact congrArg (fun v : Vec 1 => v 0) (hxy ω)
    change (∫ ω, (∑ d : D4, ∑ t : Fin (R.T 4 d),
      SAP.P018a.score (SAP.P018a.repeatedX R ω d t)
        (SAP.P018a.repeatedY R ω d t)) 0 ∂SAP.P018a.repeatedLaw R 4) = 0
    rw [hp]
    simp
  rw [SAP.P018a.repeatedBeta, hMeanGram, hnum]
  simp

lemma hH : SAP.P018a.repeatedH R 4 = !![(1 : ℝ)] := by
  rw [SAP.P018a.repeatedH, hL, hMeanGram]
  norm_num

lemma scoreDyad (ω : Fin 4 → Unit) (d : D4) :
    SAP.P018a.repeatedBlockScore R (SAP.P018a.repeatedBeta R 4) ω d =
      q6 (dyadEquiv.symm d) := by
  rw [hBeta]
  let i := dyadEquiv.symm d
  have hd : dyad6 i = d := dyadEquiv.apply_symm_apply d
  rw [← hd]
  rw [index_left]
  exact score6 i ω

lemma hsumq (ω : Fin 4 → Unit) :
    (∑ d : D4, SAP.P018a.repeatedBlockScore R (SAP.P018a.repeatedBeta R 4) ω d) = 0 := by
  rw [sum_dyad_reindex]
  simp_rw [scoreDyad]
  simp_rw [index_left]
  ext a
  fin_cases a
  norm_num [q6, Fin.sum_univ_succ]

lemma hmean :
    meanVec (SAP.P018a.repeatedLaw R 4)
      (fun ω => ∑ d : D4, SAP.P018a.repeatedBlockScore R (SAP.P018a.repeatedBeta R 4) ω d) = 0 := by
  haveI : IsProbabilityMeasure R.μ := by dsimp [R]; infer_instance
  haveI : IsProbabilityMeasure (SAP.P018a.repeatedLaw R 4) := by
    dsimp [SAP.P018a.repeatedLaw]
    infer_instance
  funext a
  fin_cases a
  have hs : (fun ω : Fin 4 → Unit =>
      (∑ d : D4, SAP.P018a.repeatedBlockScore R
        (SAP.P018a.repeatedBeta R 4) ω d) 0) = fun _ => 0 := by
    funext ω
    exact congrArg (fun v : Vec 1 => v 0) (hsumq ω)
  change (∫ ω, (∑ d : D4, SAP.P018a.repeatedBlockScore R
    (SAP.P018a.repeatedBeta R 4) ω d) 0 ∂SAP.P018a.repeatedLaw R 4) = 0
  rw [hs]
  simp

lemma hvar :
    varMat (SAP.P018a.repeatedLaw R 4)
      (fun ω => ∑ d : D4, SAP.P018a.repeatedBlockScore R (SAP.P018a.repeatedBeta R 4) ω d) = 0 := by
  haveI : IsProbabilityMeasure R.μ := by dsimp [R]; infer_instance
  haveI : IsProbabilityMeasure (SAP.P018a.repeatedLaw R 4) := by
    dsimp [SAP.P018a.repeatedLaw]
    infer_instance
  ext a b
  fin_cases a
  fin_cases b
  have hs : (fun ω : Fin 4 → Unit =>
      (∑ d : D4, SAP.P018a.repeatedBlockScore R
        (SAP.P018a.repeatedBeta R 4) ω d) (0 : Fin 1)) = fun _ => 0 := by
    funext ω
    exact congrArg (fun v : Vec 1 => v 0) (hsumq ω)
  change ProbabilityTheory.covariance
    (fun ω : Fin 4 → Unit =>
      (∑ d : D4, SAP.P018a.repeatedBlockScore R
        (SAP.P018a.repeatedBeta R 4) ω d) (0 : Fin 1))
    (fun ω : Fin 4 → Unit =>
      (∑ d : D4, SAP.P018a.repeatedBlockScore R
        (SAP.P018a.repeatedBeta R 4) ω d) (0 : Fin 1))
    (SAP.P018a.repeatedLaw R 4) = 0
  rw [hs]
  exact ProbabilityTheory.covariance_const_left 0

lemma sum_pair_reindex {α : Type*} [AddCommMonoid α] (g : D4 → D4 → α) :
    (∑ d : D4, ∑ f : D4, g d f) =
      ∑ i : I6, ∑ j : I6, g (dyad6 i) (dyad6 j) := by
  rw [sum_dyad_reindex]
  simp_rw [sum_dyad_reindex]

lemma sparseAlgebra :
    (∑ d : D4, ∑ f : D4, if SAP.P018a.overlap d f then
      SAP.P018a.outer (q6 (dyadEquiv.symm d)) (q6 (dyadEquiv.symm f)) else 0) =
      !![(2 : ℝ)] := by
  ext a b
  fin_cases a
  fin_cases b
  rw [sum_pair_reindex]
  simp_rw [index_left]
  norm_num [SAP.P018a.overlap, SAP.P018a.members, dyad6,
    SAP.P018a.sixMembers, q6, SAP.P018a.outer, Fin.sum_univ_succ]

lemma hraw :
    sparseRawW3 (SAP.P018a.repeatedLaw R 4)
      (SAP.P018a.repeatedBlockScore R (SAP.P018a.repeatedBeta R 4)) = !![(2 : ℝ)] := by
  haveI : IsProbabilityMeasure R.μ := by dsimp [R]; infer_instance
  haveI : IsProbabilityMeasure (SAP.P018a.repeatedLaw R 4) := by
    dsimp [SAP.P018a.repeatedLaw]
    infer_instance
  have hmoment (d f : D4) :
      meanMat (SAP.P018a.repeatedLaw R 4) (fun ω =>
        SAP.P018a.outer
          (SAP.P018a.repeatedBlockScore R (SAP.P018a.repeatedBeta R 4) ω d)
          (SAP.P018a.repeatedBlockScore R (SAP.P018a.repeatedBeta R 4) ω f)) =
        SAP.P018a.outer (q6 (dyadEquiv.symm d)) (q6 (dyadEquiv.symm f)) := by
    ext a b
    fin_cases a
    fin_cases b
    simp [meanMat, scoreDyad, Equiv.symm_apply_apply]
  simp only [sparseRawW3]
  simp_rw [hmoment]
  exact sparseAlgebra

lemma hmeans :
    sparseMeansW3 (SAP.P018a.repeatedLaw R 4)
      (SAP.P018a.repeatedBlockScore R (SAP.P018a.repeatedBeta R 4)) = !![(2 : ℝ)] := by
  haveI : IsProbabilityMeasure R.μ := by dsimp [R]; infer_instance
  haveI : IsProbabilityMeasure (SAP.P018a.repeatedLaw R 4) := by
    dsimp [SAP.P018a.repeatedLaw]
    infer_instance
  have hqmean (d : D4) :
      meanVec (SAP.P018a.repeatedLaw R 4)
        (fun ω => SAP.P018a.repeatedBlockScore R (SAP.P018a.repeatedBeta R 4) ω d) =
        q6 (dyadEquiv.symm d) := by
    funext a
    fin_cases a
    simp [meanVec, scoreDyad, Equiv.symm_apply_apply]
  simp only [sparseMeansW3]
  simp_rw [hqmean]
  exact sparseAlgebra

lemma proofCore : SAP.P018a.WH.W3.T2_L4 := by
  refine ⟨R, repeatedAt, ?_, hmean, hvar, hraw, hmeans⟩
  rw [hH]
  simp

end SAP.P018a.WH.W3.P.T2_L4

theorem SAP.P018a.WH.W3.T2_L4_proof : SAP.P018a.WH.W3.T2_L4 :=
  SAP.P018a.WH.W3.P.T2_L4.proofCore
