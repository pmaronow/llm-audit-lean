import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellMarks
import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDensity
import Mathlib.Data.Finset.Sort

/-! Bootstrap mark replacement after observing a finite window.

All selections below depend on the original sample, before any replica is
drawn.  A bounded number of labels can be padded to a fixed number of distinct
labels; their joint mark law is then uniformly close to independent Poisson
marks, even for sample-dependent bounded test functions.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA

local instance instDecidableMarkedCellSelectedWindow (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

def markedWindowMarks {r k N : ℕ} (labels : Fin k → Fin N)
    (a : Fin r → Fin N → Fin N) : MarkedLabelMarks r k :=
  fun t i => (Finset.univ.filter (fun j => a t j = labels i)).card

theorem marked_window_marks_measurable {Ω : Type*} [MeasurableSpace Ω]
    {r k N : ℕ} (labels : Ω → Fin k → Fin N) (hlabels : Measurable labels)
    (a : Fin r → Fin N → Fin N) :
    Measurable (fun x => markedWindowMarks (labels x) a) := by
  exact (measurable_of_finite (fun l : Fin k → Fin N => markedWindowMarks l a)).comp hlabels

theorem marked_window_average_measurable {Ω : Type*} [MeasurableSpace Ω]
    {r k N : ℕ} (labels : Ω → Fin k → Fin N) (hlabels : Measurable labels)
    (f : Ω → MarkedLabelMarks r k → ℝ) (hf : Measurable (Function.uncurry f)) :
    Measurable (fun x => ∫ a, f x (markedWindowMarks (labels x) a)
      ∂Measure.pi (fun _ : Fin r => UniformResampling N)) := by
  have h (a : Fin r → Fin N → Fin N) :
      Measurable (fun x => f x (markedWindowMarks (labels x) a)) :=
    hf.comp (measurable_id.prodMk (marked_window_marks_measurable labels hlabels a))
  have heq (x : Ω) :
      (∫ a, f x (markedWindowMarks (labels x) a)
        ∂Measure.pi (fun _ : Fin r => UniformResampling N)) =
      ∑ a : Fin r → Fin N → Fin N,
        (Measure.pi (fun _ : Fin r => UniformResampling N)).real {a} *
          f x (markedWindowMarks (labels x) a) := by
    rw [integral_fintype Integrable.of_finite]
    simp only [smul_eq_mul]
  simp only [heq]
  exact Finset.measurable_sum _ (fun a _ => measurable_const.mul (h a))

/-- Integrating over the original sample preserves the same uniform error.
In particular no independence between the selected labels and positions is
assumed.  Independence is only between the original sample and resampling. -/
theorem marked_window_integrated_replacement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {r k N : ℕ} (hN : k+1 ≤ N)
    (labels : Ω → Fin k → Fin N) (hlabels : Measurable labels)
    (hinj : ∀ x, Function.Injective (labels x))
    (f : Ω → MarkedLabelMarks r k → ℝ) (hf : Measurable (Function.uncurry f))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x v, |f x v| ≤ C) :
    |(∫ x, (∫ a, f x (markedWindowMarks (labels x) a)
        ∂Measure.pi (fun _ : Fin r => UniformResampling N)) ∂P) -
      ∫ x, (∫ v, f x v ∂markedPoissonMarkLaw r k) ∂P| ≤
        C*markedMarkError r k N := by
  let F : Ω → ℝ := fun x => ∫ a, f x (markedWindowMarks (labels x) a)
    ∂Measure.pi (fun _ : Fin r => UniformResampling N)
  let G : Ω → ℝ := fun x => ∫ v, f x v ∂markedPoissonMarkLaw r k
  have hFm : Measurable F := marked_window_average_measurable labels hlabels f hf
  have hGm : Measurable G := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hFb (x : Ω) : ‖F x‖ ≤ C := by
    have hb : ∀ a : Fin r → Fin N → Fin N,
        ‖f x (markedWindowMarks (labels x) a)‖ ≤ C := by
      intro a
      exact hbound x (markedWindowMarks (labels x) a)
    have hh := norm_integral_le_of_norm_le_const
      (μ := Measure.pi (fun _ : Fin r => UniformResampling N)) (ae_of_all _ hb)
    simpa only [F, probReal_univ, mul_one] using hh
  have hGb (x : Ω) : ‖G x‖ ≤ C := by
    calc
      ‖G x‖ ≤ C*(markedPoissonMarkLaw r k).real Set.univ := by
        apply norm_integral_le_of_norm_le_const
        exact ae_of_all _ (fun v => by simpa only [Real.norm_eq_abs] using hbound x v)
      _ = C := by simp
  have hFi : Integrable F P := Integrable.of_bound hFm.aestronglyMeasurable C
    (ae_of_all _ hFb)
  have hGi : Integrable G P := Integrable.of_bound hGm.aestronglyMeasurable C
    (ae_of_all _ hGb)
  change |(∫ x, F x ∂P) - ∫ x, G x ∂P| ≤ _
  rw [← integral_sub hFi hGi]
  change ‖∫ x, F x-G x ∂P‖ ≤ _
  have hb (x : Ω) : ‖F x-G x‖ ≤ C*markedMarkError r k N := by
    exact marked_selected_test_difference hN ⟨labels x, hinj x⟩ (f x) hC (hbound x)
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := P) (ae_of_all _ hb))

/-- The replacement also holds for a changing original-sample space and tests
that vary with the row.  Only eventual injectivity is needed. -/
theorem marked_window_replacement_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) (hP : ∀ n, IsProbabilityMeasure (P n))
    (r k : ℕ) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (labels : (n : ℕ) → Ω n → Fin k → Fin (m n))
    (hlabels : ∀ n, Measurable (labels n))
    (hinj : ∀ᶠ n in atTop, ∀ x, Function.Injective (labels n x))
    (f : (n : ℕ) → Ω n → MarkedLabelMarks r k → ℝ)
    (hf : ∀ n, Measurable (Function.uncurry (f n)))
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ n x v, |f n x v| ≤ C) :
    Tendsto (fun n =>
      (∫ x, (∫ a, f n x (markedWindowMarks (labels n x) a)
        ∂Measure.pi (fun _ : Fin r => UniformResampling (m n))) ∂P n) -
      ∫ x, (∫ v, f n x v ∂markedPoissonMarkLaw r k) ∂P n)
      atTop (𝓝 0) := by
  haveI instProbabilityMarkedOriginalRows (n : ℕ) : IsProbabilityMeasure (P n) := hP n
  have he := (marked_mark_error_tendsto r k m hm).const_mul C
  simp only [mul_zero] at he
  apply squeeze_zero_norm' _ he
  filter_upwards [hm.eventually (eventually_ge_atTop (k+1)), hinj] with n hn hi
  exact marked_window_integrated_replacement (P n) hn (labels n) (hlabels n) hi
    (f n) (hf n) hC (hbound n)

/-- Finite sets of selected labels can be padded to a fixed number of labels. -/
theorem marked_label_padding_exists {k N : ℕ} (hN : k ≤ N)
    (D : Finset (Fin N)) (hD : D.card ≤ k) :
    ∃ e : Fin k ↪ Fin N, ∀ j ∈ D, j ∈ Set.range e := by
  obtain ⟨S, hDS, hS⟩ := Finset.exists_superset_card_eq hD (by simpa using hN)
  refine ⟨(S.orderEmbOfFin hS).toEmbedding, ?_⟩
  intro j hj
  change j ∈ Set.range (S.orderEmbOfFin hS)
  rw [Finset.range_orderEmbOfFin]
  exact hDS hj

/-- A fixed-size padded selection, determined entirely before resampling.
On the count-cutoff event it includes every requested label. -/
def markedPaddedLabels {k N : ℕ} (hN : k ≤ N) (D : Finset (Fin N)) : Fin k ↪ Fin N :=
  if hD : D.card ≤ k then Classical.choose (marked_label_padding_exists hN D hD)
  else ⟨Fin.castLE hN, Fin.castLE_injective hN⟩

theorem marked_padded_labels_cover {k N : ℕ} (hN : k ≤ N)
    (D : Finset (Fin N)) (hD : D.card ≤ k) (j : Fin N) (hj : j ∈ D) :
    j ∈ Set.range (markedPaddedLabels hN D) := by
  unfold markedPaddedLabels
  rw [dif_pos hD]
  exact Classical.choose_spec (marked_label_padding_exists hN D hD) j hj

theorem marked_padded_labels_measurable {Ω : Type*} [MeasurableSpace Ω]
    {k N : ℕ} (hN : k ≤ N) (D : Ω → Fin N → Bool) (hD : Measurable D) :
    Measurable (fun x i => markedPaddedLabels hN
      (Finset.univ.filter (fun j => D x j = true)) i) := by
  exact (measurable_of_finite (fun d : Fin N → Bool =>
    fun i => markedPaddedLabels hN (Finset.univ.filter (fun j => d j = true)) i)).comp hD

/-- Adjoin the pinned original label as coordinate zero of the selected array. -/
def markedPinnedLabels {k n : ℕ} (hkn : k ≤ n) (D : Finset (Fin n)) :
    Fin (k+1) ↪ Fin (n+1) where
  toFun := Fin.cases 0 (fun i => (markedPaddedLabels hkn D i).succ)
  inj' := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rfl
      · intro h
        exact False.elim ((Fin.succ_ne_zero _) h.symm)
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        exact False.elim ((Fin.succ_ne_zero _) h)
      · intro h
        have hij := (markedPaddedLabels hkn D).injective (Fin.succ_injective n h)
        exact congrArg Fin.succ hij

theorem marked_pinned_labels_zero {k n : ℕ} (hkn : k ≤ n) (D : Finset (Fin n)) :
    markedPinnedLabels hkn D 0 = 0 := rfl

theorem marked_pinned_labels_succ {k n : ℕ} (hkn : k ≤ n) (D : Finset (Fin n))
    (i : Fin k) :
    markedPinnedLabels hkn D i.succ = (markedPaddedLabels hkn D i).succ := rfl

theorem marked_pinned_labels_cover {k n : ℕ} (hkn : k ≤ n)
    (D : Finset (Fin n)) (hD : D.card ≤ k) (j : Fin n) (hj : j ∈ D) :
    j.succ ∈ Set.range (markedPinnedLabels hkn D) := by
  obtain ⟨i, hi⟩ := marked_padded_labels_cover hkn D hD j hj
  exact ⟨i.succ, by simpa only [marked_pinned_labels_succ, hi]⟩

/-- The central count is the actual pinned-label occupancy in every replica. -/
theorem marked_pinned_central_mark {r k n : ℕ} (hkn : k ≤ n) (D : Finset (Fin n))
    (a : Fin r → Fin (n+1) → Fin (n+1)) (t : Fin r) :
    markedSelectedMarks (markedPinnedLabels hkn D) a t 0 =
      (Finset.univ.filter (fun j => a t j = 0)).card := rfl

theorem marked_pinned_labels_measurable {Ω : Type*} [MeasurableSpace Ω]
    {k n : ℕ} (hkn : k ≤ n) (D : Ω → Fin n → Bool) (hD : Measurable D) :
    Measurable (fun x i => markedPinnedLabels hkn
      (Finset.univ.filter (fun j => D x j = true)) i) := by
  exact (measurable_of_finite (fun d : Fin n → Bool =>
    fun i => markedPinnedLabels hkn (Finset.univ.filter (fun j => d j = true)) i)).comp hD

/-- All-row version: the small initial rows use a constant vector, and every
row large enough for the cutoff uses the injective padded selection. -/
def markedPinnedSelection (k n : ℕ) (D : Finset (Fin n)) : Fin (k+1) → Fin (n+1) :=
  if hkn : k ≤ n then markedPinnedLabels hkn D else fun _ => 0

theorem marked_pinned_selection_injective {k n : ℕ} (hkn : k ≤ n)
    (D : Finset (Fin n)) : Function.Injective (markedPinnedSelection k n D) := by
  unfold markedPinnedSelection
  rw [dif_pos hkn]
  exact (markedPinnedLabels hkn D).injective

theorem marked_pinned_selection_zero (k n : ℕ) (D : Finset (Fin n)) :
    markedPinnedSelection k n D 0 = 0 := by
  unfold markedPinnedSelection
  split_ifs <;> rfl

theorem marked_pinned_selection_cover {k n : ℕ} (hkn : k ≤ n)
    (D : Finset (Fin n)) (hD : D.card ≤ k) (j : Fin n) (hj : j ∈ D) :
    j.succ ∈ Set.range (markedPinnedSelection k n D) := by
  simpa only [markedPinnedSelection, dif_pos hkn] using
    marked_pinned_labels_cover hkn D hD j hj

theorem marked_pinned_selection_measurable {Ω : Type*} [MeasurableSpace Ω]
    (k n : ℕ) (D : Ω → Fin n → Bool) (hD : Measurable D) :
    Measurable (fun x => markedPinnedSelection k n
      (Finset.univ.filter (fun j => D x j = true))) := by
  exact (measurable_of_finite (fun d : Fin n → Bool =>
    markedPinnedSelection k n (Finset.univ.filter (fun j => d j = true)))).comp hD

end AronowAudit.P001.TailA
