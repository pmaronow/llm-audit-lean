import SAP.P019a.WH.W2.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open SAP.P019a

open Classical
universe u

theorem SAP.P019a.WH.W2.T11_L1_proof : SAP.P019a.WH.W2.T11_L1 := by
  intro Ω _ J S
  let Q : Measure (T11Observation J) := S.law.map S.observe
  have hmass (t : T11Observation J) :
      S.finiteStudy.law.mass t = Q.real {t} := by
    change (S.law (S.observe ⁻¹' {t})).toReal =
      ((S.law.map S.observe) {t}).toReal
    rw [Measure.map_apply S.measurable_observe (measurableSet_singleton t)]
  have hfinite (f : T11Observation J → ℝ) : Integrable f Q := Integrable.of_finite
  have hcomp (f : T11Observation J → ℝ) :
      Integrable (fun ω => f (S.observe ω)) S.law := by
    exact (integrable_map_measure (hfinite f).aestronglyMeasurable
      S.measurable_observe.aemeasurable).mp (hfinite f)
  have hmean (f : T11Observation J → ℝ) :
      S.mean f = S.finiteStudy.law.mean f := by
    change (∫ ω, f (S.observe ω) ∂S.law) = _
    calc
      (∫ ω, f (S.observe ω) ∂S.law) = ∫ t, f t ∂Q := by
        symm
        exact integral_map S.measurable_observe.aemeasurable
          (hfinite f).aestronglyMeasurable
      _ = ∑ t, S.finiteStudy.law.mass t * f t := by
        rw [integral_fintype (hfinite f)]
        simp [hmass, smul_eq_mul]
      _ = S.finiteStudy.law.mean f := by
        rfl
  have hprob (D : T11Observation J → Prop) :
      S.prob D = S.finiteStudy.law.prob D := by
    classical
    have hq : Q.real ↑(Finset.univ.filter D) =
        ∑ t, S.finiteStudy.law.mass t * (if D t then 1 else 0) := by
      calc
        Q.real ↑(Finset.univ.filter D) =
            ∑ t ∈ Finset.univ.filter D, Q.real {t} := by
          rw [← sum_measureReal_singleton (μ := Q) (Finset.univ.filter D)]
        _ = ∑ t, S.finiteStudy.law.mass t * (if D t then 1 else 0) := by
          simp [hmass, Finset.sum_filter]
    have hq' : Q.real {t | D t} =
        ∑ t, S.finiteStudy.law.mass t * (if D t then 1 else 0) := by
      have hset : ({t | D t} : Set (T11Observation J)) =
          (Finset.univ.filter D : Finset (T11Observation J)) := by
        ext t
        simp
      rw [hset]
      exact hq
    change (S.law (S.observe ⁻¹' {t | D t})).toReal = _
    rw [← Measure.map_apply S.measurable_observe (by measurability)]
    change Q.real {t | D t} = _
    rw [hq']
    rfl
  have hae (D : T11Observation J → Prop) :
      (∀ᵐ ω ∂S.law, D (S.observe ω)) ↔
        ∀ t, 0 < S.finiteStudy.law.mass t → D t := by
    have hmap : (∀ᵐ t ∂Q, D t) ↔ ∀ᵐ ω ∂S.law, D (S.observe ω) :=
      ae_map_iff S.measurable_observe.aemeasurable (by measurability)
    rw [← hmap, ae_iff_of_countable]
    constructor
    · intro ht t hpos
      apply ht
      have hreal : Q.real {t} ≠ 0 := by
        rw [← hmass]
        exact hpos.ne'
      exact (measureReal_ne_zero_iff (μ := Q) (s := ({t} : Set (T11Observation J)))).mp hreal
    · intro h t ht
      apply h t
      have hreal : Q.real {t} ≠ 0 :=
        (measureReal_ne_zero_iff (μ := Q) (s := ({t} : Set (T11Observation J)))).mpr ht
      rw [hmass]
      exact lt_of_le_of_ne (measureReal_nonneg) (Ne.symm hreal)
  exact ⟨fun f => ⟨hcomp f, hmean f⟩, hprob, hae⟩
