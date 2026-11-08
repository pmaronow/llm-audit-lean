import SAP.P011a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011a.WH.W2.P.T10_L1

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators Classical

noncomputable section

def mixtureSource (a b : ℝ) (n : ℕ) (u : (Fin n → Bool) × (Fin n → Bool)) :
    Fin n → ℝ := fun i => a * AronowAudit.P011.sign (u.1 i) +
      b * AronowAudit.P011.sign (u.2 i)

def fixedSource (a b : ℝ) (s : ℕ → Bool) (n : ℕ) (u : Fin n → Bool) :
    Fin n → ℝ := fun i => a * AronowAudit.P011.sign (s i.val) +
      b * AronowAudit.P011.sign (u i)

def mixtureSupport (a b : ℝ) (n : ℕ) : Finset (Fin n → ℝ) :=
  Finset.univ.image (mixtureSource a b n)

lemma measurableSet_finset_real {n : ℕ} (S : Finset (Fin n → ℝ)) :
    MeasurableSet {y : Fin n → ℝ | y ∈ S} := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
    simp only [Finset.mem_insert]
    rw [show {y : Fin n → ℝ | y = x ∨ y ∈ S} =
      ({x} : Set (Fin n → ℝ)) ∪ {y : Fin n → ℝ | y ∈ S} by
        ext y
        simp]
    exact (measurableSet_singleton x).union ih

lemma ae_uniform_mem_finset_image {α : Type} {n : ℕ} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (f : α → Fin n → ℝ) (S : Finset (Fin n → ℝ)) (hf : ∀ u, f u ∈ S) :
    ∀ᵐ y ∂AronowAudit.P011.uniformLaw f, y ∈ S := by
  have hS : MeasurableSet {y : Fin n → ℝ | y ∈ S} := measurableSet_finset_real S
  rw [AronowAudit.P011.uniformLaw,
    ← PMF.toMeasure_map f (PMF.uniformOfFintype α) (measurable_of_finite f)]
  apply (ae_map_iff (measurable_of_finite f).aemeasurable hS).mpr
  exact ae_of_all _ hf

def representative {n : ℕ} (a b : ℝ) (T : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ := fun y =>
      ∑ x ∈ mixtureSupport a b n, if y = x then T x else 0

lemma measurable_representative {n : ℕ} (a b : ℝ) (T : (Fin n → ℝ) → ℝ) :
    Measurable (representative a b T) := by
  classical
  unfold representative
  apply Finset.measurable_sum
  intro x hx
  exact Measurable.ite (measurableSet_singleton x) measurable_const measurable_const

lemma representative_eq_on_support {n : ℕ} (a b : ℝ) (T : (Fin n → ℝ) → ℝ)
    (y : Fin n → ℝ) (hy : y ∈ mixtureSupport a b n) :
    representative a b T y = T y := by
  classical
  unfold representative
  rw [Finset.sum_eq_single y]
  · simp
  · intro x hx hxy
    simp [hxy.symm]
  · intro hnot
    exact (hnot hy).elim

end

end SAP.P011a.WH.W2.P.T10_L1

theorem SAP.P011a.WH.W2.T10_L1_proof : SAP.P011a.WH.W2.T10_L1 := by
  classical
  intro a b n T
  let S := SAP.P011a.WH.W2.P.T10_L1.mixtureSupport a b n
  let Tm := SAP.P011a.WH.W2.P.T10_L1.representative a b T
  refine ⟨Tm, ?_, ?_, ?_⟩
  · exact SAP.P011a.WH.W2.P.T10_L1.measurable_representative a b T
  · intro s
    have hsource : ∀ u : Fin n → Bool,
        SAP.P011a.WH.W2.P.T10_L1.fixedSource a b s n u ∈ S := by
      intro u
      change SAP.P011a.WH.W2.P.T10_L1.fixedSource a b s n u ∈
        Finset.univ.image (SAP.P011a.WH.W2.P.T10_L1.mixtureSource a b n)
      apply Finset.mem_image.mpr
      refine ⟨(fun i : Fin n => s i.val, u), Finset.mem_univ _, ?_⟩
      funext i
      rfl
    have hsupp : ∀ᵐ y ∂(AronowAudit.P011.fixedMeanModel a b s n).law, y ∈ S := by
      change ∀ᵐ y ∂AronowAudit.P011.uniformLaw
        (SAP.P011a.WH.W2.P.T10_L1.fixedSource a b s n), y ∈ S
      exact SAP.P011a.WH.W2.P.T10_L1.ae_uniform_mem_finset_image
        (SAP.P011a.WH.W2.P.T10_L1.fixedSource a b s n) S hsource
    filter_upwards [hsupp] with y hy
    exact SAP.P011a.WH.W2.P.T10_L1.representative_eq_on_support a b T y hy
  · have hsource : ∀ u : (Fin n → Bool) × (Fin n → Bool),
        SAP.P011a.WH.W2.P.T10_L1.mixtureSource a b n u ∈ S := by
      intro u
      change SAP.P011a.WH.W2.P.T10_L1.mixtureSource a b n u ∈
        Finset.univ.image (SAP.P011a.WH.W2.P.T10_L1.mixtureSource a b n)
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    have hsupp : ∀ᵐ y ∂(AronowAudit.P011.mixtureModel a b n).law, y ∈ S := by
      change ∀ᵐ y ∂AronowAudit.P011.uniformLaw
        (SAP.P011a.WH.W2.P.T10_L1.mixtureSource a b n), y ∈ S
      exact SAP.P011a.WH.W2.P.T10_L1.ae_uniform_mem_finset_image
        (SAP.P011a.WH.W2.P.T10_L1.mixtureSource a b n) S hsource
    filter_upwards [hsupp] with y hy
    exact SAP.P011a.WH.W2.P.T10_L1.representative_eq_on_support a b T y hy
