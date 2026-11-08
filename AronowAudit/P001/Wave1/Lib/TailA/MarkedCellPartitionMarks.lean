import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellSelectedWindow
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellWindowCounts

/-! Joint finite-partition and sample-selected bootstrap mark limits.

The original partition counts and the selected labels are functions of the same
original sample.  Independence of the limiting marks is proved by the uniform
conditional replacement bound, rather than assumed for selected labels.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellPartitionMarks (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- Every bounded test of a discrete original configuration and its selected
replica marks has the stated joint limit. -/
theorem marked_discrete_joint_test_limit
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Countable E] [TopologicalSpace E] [DiscreteTopology E]
    (P : (n : ℕ) → Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (X : (n : ℕ) → Ω n → E) (hX : ∀ n, Measurable (X n))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hweak : AronowAudit.Literature.RowWeak P X ν)
    (r k : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (labels : (n : ℕ) → Ω n → Fin k → Fin (m n))
    (hlabels : ∀ n, Measurable (labels n))
    (hinj : ∀ᶠ n in atTop, ∀ x, Function.Injective (labels n x))
    (f : E × MarkedLabelMarks r k → ℝ) {C : ℝ}
    (hC : 0 ≤ C) (hbound : ∀ y, |f y| ≤ C) :
    Tendsto (fun n => ∫ x, (∫ a,
      f (X n x, markedWindowMarks (labels n x) a)
        ∂Measure.pi (fun _ : Fin r => UniformResampling (m n))) ∂P n)
      atTop (𝓝 (∫ e, (∫ v, f (e,v) ∂markedPoissonMarkLaw r k) ∂ν)) := by
  have hfm : Measurable f := measurable_of_countable f
  let G : E → ℝ := fun e => ∫ v, f (e,v) ∂markedPoissonMarkLaw r k
  have hGb (e : E) : |G e| ≤ C := by
    have hb : ∀ v : MarkedLabelMarks r k, ‖f (e,v)‖ ≤ C := fun v => hbound (e,v)
    have hh := norm_integral_le_of_norm_le_const (μ := markedPoissonMarkLaw r k)
      (ae_of_all _ hb)
    simpa only [G, Real.norm_eq_abs, probReal_univ, mul_one] using hh
  have hG := hweak G continuous_of_discreteTopology ⟨C, hGb⟩
  have hD := marked_window_replacement_tendsto P hP r k m hm labels hlabels hinj
    (fun n x v => f (X n x, v))
    (fun n => hfm.comp (((hX n).comp measurable_fst).prodMk measurable_snd))
    hC (fun n x v => hbound (X n x,v))
  convert hD.add hG using 1
  · funext n
    dsimp only [G]
    ring
  · simp only [zero_add, G]

/-- Joint weak convergence under the actual original-sample and replica product
measure.  The limiting mark array is independent of the discrete configuration. -/
theorem marked_discrete_joint_limit
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    [Countable E] [TopologicalSpace E] [DiscreteTopology E]
    (P : (n : ℕ) → Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (X : (n : ℕ) → Ω n → E) (hX : ∀ n, Measurable (X n))
    (ν : Measure E) [IsProbabilityMeasure ν]
    (hweak : AronowAudit.Literature.RowWeak P X ν)
    (r k : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (labels : (n : ℕ) → Ω n → Fin k → Fin (m n))
    (hlabels : ∀ n, Measurable (labels n))
    (hinj : ∀ᶠ n in atTop, ∀ x, Function.Injective (labels n x)) :
    AronowAudit.Literature.RowWeak
      (fun n => (P n).prod (Measure.pi (fun _ : Fin r => UniformResampling (m n))))
      (fun n y => (X n y.1, markedWindowMarks (labels n y.1) y.2))
      (ν.prod (markedPoissonMarkLaw r k)) := by
  haveI instProbabilityMarkedJointRows (n : ℕ) : IsProbabilityMeasure (P n) := hP n
  intro f _ hf
  obtain ⟨C, hC⟩ := hf
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  have hb (y) : |f y| ≤ D := (hC y).trans (le_max_left _ _)
  have hfm : Measurable f := measurable_of_countable f
  have hj (n : ℕ) : Measurable (fun y : Ω n × (Fin r → Fin (m n) → Fin (m n)) =>
      (X n y.1, markedWindowMarks (labels n y.1) y.2)) := by
    apply ((hX n).comp measurable_fst).prodMk
    exact (measurable_of_finite (fun la :
      (Fin k → Fin (m n)) × (Fin r → Fin (m n) → Fin (m n)) =>
        markedWindowMarks la.1 la.2)).comp
      (((hlabels n).comp measurable_fst).prodMk measurable_snd)
  have hfi (n : ℕ) : Integrable (fun y =>
      f (X n y.1, markedWindowMarks (labels n y.1) y.2))
        ((P n).prod (Measure.pi (fun _ : Fin r => UniformResampling (m n)))) :=
    Integrable.of_bound (hfm.comp (hj n)).aestronglyMeasurable D
      (ae_of_all _ (fun y => hb (X n y.1, markedWindowMarks (labels n y.1) y.2)))
  have hfl : Integrable f (ν.prod (markedPoissonMarkLaw r k)) :=
    Integrable.of_bound hfm.aestronglyMeasurable D
      (ae_of_all _ (fun y => by simpa only [Real.norm_eq_abs] using hb y))
  have ht := marked_discrete_joint_test_limit P hP X hX ν hweak
    r k m hm labels hlabels hinj f hD hb
  convert ht using 1
  · funext n
    exact integral_prod _ (hfi n)
  · exact congrArg nhds (integral_prod f hfl)

/-- The actual donor/recipient partition counts jointly with marks on any
sample-selected labels.  The original sample has `m n` rows and each bootstrap
has `m n+1` rows, including the separate pinned original label. -/
theorem marked_type_partition_mark_limit (q r k : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4))
    (types : Fin q → Bool) (a b : Fin q → ℝ) (hab : ∀ i, a i ≤ b i)
    (hdis : ∀ i j, i ≠ j → types i ≠ types j ∨ b i ≤ a j ∨ b j ≤ a i)
    (rates : Fin q → ℝ≥0)
    (hrates : ∀ i, (rates i : ℝ) = (b i-a i)*markedTypeDensity (types i) p)
    (labels : (n : ℕ) → (Fin (m n) → MatchUnit) → Fin k → Fin (m n+1))
    (hlabels : ∀ n, Measurable (labels n))
    (hinj : ∀ᶠ n in atTop, ∀ z, Function.Injective (labels n z)) :
    AronowAudit.Literature.RowWeak
      (fun n => (MatchProduct (m n)).prod
        (Measure.pi (fun _ : Fin r => UniformResampling (m n+1))))
      (fun n y => ((fun i => markedWindowCount
          (markedTypeInterval (types i) (p+a i/(m n : ℝ)) (p+b i/(m n : ℝ))) y.1),
        markedWindowMarks (labels n y.1) y.2))
      ((Measure.pi (fun i => poissonMeasure (rates i))).prod (markedPoissonMarkLaw r k)) := by
  have hX (n : ℕ) : Measurable (fun z : Fin (m n) → MatchUnit =>
      fun i => markedWindowCount
        (markedTypeInterval (types i) (p+a i/(m n : ℝ)) (p+b i/(m n : ℝ))) z) :=
    measurable_pi_lambda (fun i => marked_window_count_measurable _ _
      (marked_type_interval_measurable _ _ _))
  have hres : Tendsto (fun n => m n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_succ (m n)) hm
  exact marked_discrete_joint_limit (fun n => MatchProduct (m n)) (fun _ => inferInstance)
    _ hX _ (marked_type_partition_counts q m hm p hp types a b hab hdis rates hrates)
    r k _ hres labels hlabels hinj

/-- Joint finite-partition convergence with the central mark at coordinate zero
and enough padded marks to include every window label on the count-cutoff event.
There is no selected-label independence hypothesis. -/
theorem marked_pinned_partition_mark_limit (q r k : ℕ) (m : ℕ → ℕ)
    (hm : Tendsto m atTop atTop) (p : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4))
    (types : Fin q → Bool) (a b : Fin q → ℝ) (hab : ∀ i, a i ≤ b i)
    (hdis : ∀ i j, i ≠ j → types i ≠ types j ∨ b i ≤ a j ∨ b j ≤ a i)
    (rates : Fin q → ℝ≥0)
    (hrates : ∀ i, (rates i : ℝ) = (b i-a i)*markedTypeDensity (types i) p)
    (D : (n : ℕ) → (Fin (m n) → MatchUnit) → Fin (m n) → Bool)
    (hD : ∀ n, Measurable (D n)) :
    AronowAudit.Literature.RowWeak
      (fun n => (MatchProduct (m n)).prod
        (Measure.pi (fun _ : Fin r => UniformResampling (m n+1))))
      (fun n y => ((fun i => markedWindowCount
          (markedTypeInterval (types i) (p+a i/(m n : ℝ)) (p+b i/(m n : ℝ))) y.1),
        markedWindowMarks (markedPinnedSelection k (m n)
          (Finset.univ.filter (fun j => D n y.1 j = true))) y.2))
      ((Measure.pi (fun i => poissonMeasure (rates i))).prod
        (markedPoissonMarkLaw r (k+1))) := by
  apply marked_type_partition_mark_limit q r (k+1) m hm p hp types a b hab hdis rates hrates
    _ (fun n => marked_pinned_selection_measurable k (m n) (D n) (hD n))
  filter_upwards [hm.eventually (eventually_ge_atTop k)] with n hn z
  exact marked_pinned_selection_injective hn _

end AronowAudit.P001.TailA
