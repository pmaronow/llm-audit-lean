import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.BigOperators

/-! P008: exact finite-design formalizations for the tutorial, printed pp. 140–154. -/

namespace AronowAudit.P008

open scoped BigOperators
open MeasureTheory Filter

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-- Enumerating four-node toy sums, without any additional mathematical premise. -/
theorem univ_four : (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} := rfl

/-- Enumerating the five radii of the toy example. -/
theorem univ_five : (Finset.univ : Finset (Fin 5)) = {0, 1, 2, 3, 4} := rfl

/-- Enumerating the six complete-randomization assignments. -/
theorem univ_six : (Finset.univ : Finset (Fin 6)) = {0, 1, 2, 3, 4, 5} := rfl

attribute [simp] Finset.univ_fin2 Finset.filter_insert Finset.filter_singleton
  Finset.filter_empty

/-- “Z_i ∈ {0,1}” and “Z = (Z_1,...,Z_N)'”, p. 141. Bool is the binary assignment. -/
abbrev Assignment (N : ℕ) := Fin N → Bool

/-- Numerical treatment indicator, “Z_i” in the Hajek formula, p. 144. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- “the distribution of the treatment assignment vector ... is known”, p. 142.
Masses on a finite randomization space are nonnegative and sum to one. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ z, 0 ≤ mass z
  total : ∑ z, mass z = 1

/-- Finite expectation “E”, pp. 142–143; it is a weighted sum over assignments. -/
def FiniteLaw.expect {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ z, Q.mass z * f z

/-- Probability of an event in the assignment distribution, pp. 142, 144. -/
def FiniteLaw.prob {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (P : Ω → Prop) : ℝ :=
  by classical exact ∑ z ∈ Finset.univ.filter P, Q.mass z

/-- Design variance and covariance: finite centered sums, used in T5, T6, T23, T28. -/
def FiniteLaw.cov {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (f g : Ω → ℝ) : ℝ :=
  Q.expect (fun z => (f z - Q.expect f) * (g z - Q.expect g))

/-- Variance is covariance with itself (design-based). -/
def FiniteLaw.var {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  Q.cov f f

/-- Uniform law on a finite nonempty randomization space; p. 146, toy example. -/
def uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := (Fintype.card Ω : ℝ)⁻¹
  nonneg _ := by positivity
  total := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast (Fintype.card_ne_zero (α := Ω)))

/-- “hold node i to treatment value z and marginalize ... Z_-i”, p. 142.
Overriding i in a full assignment and summing with its design mass is precisely
the unconditional marginal law of the other nodes, including dependent designs. -/
def marginal {N : ℕ} (Q : FiniteLaw (Assignment N))
    (F : Assignment N → ℝ) (i : Fin N) (b : Bool) : ℝ :=
  Q.expect (fun z => F (Function.update z i b))

/-- Each point “equals a coordinate vector of length 2”, p. 141. Euclidean metric. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- “set ... spatial field X”, nodes x(i), outcomes Y_x(z), and “suitable
integration measure” ζ, pp. 141, 143. Nodes belong to the field; outcomes are
defined for every binary assignment. -/
structure SpatialModel (N : ℕ) where
  field : Set Plane
  node : Fin N → Plane
  node_mem : ∀ i, node i ∈ field
  ζ : Measure Plane
  Y : Plane → Assignment N → ℝ

/-- “{x : d_i(x) = d}”, p. 143, restricted to the spatial field X. -/
def SpatialModel.circle {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) : Set Plane :=
  {x | x ∈ P.field ∧ dist (P.node i) x = d}

/-- The measure ζ restricted to the circle in the displayed definition, p. 143. -/
def SpatialModel.circleMeasure {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) :=
  P.ζ.restrict (P.circle i d)

/-- “|{x : d_i(x) = d}|”, p. 143, interpreted as ζ-mass (T25).
Results using a genuine average require this mass to be positive and finite. -/
def SpatialModel.circleMass {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ) : ℝ :=
  (P.circleMeasure i d Set.univ).toReal

/-- “1/|{x : d_i(x)=d}| ∫ Y_x(z) dζ”, p. 143; generalized to any integrand. -/
def SpatialModel.average {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ)
    (f : Plane → ℝ) : ℝ :=
  (P.circleMass i d)⁻¹ * ∫ x, f x ∂P.circleMeasure i d

/-- “μ_i(Y(z);d)”, p. 143, the circle average of potential outcomes. -/
def SpatialModel.M {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ)
    (z : Assignment N) : ℝ := P.average i d (fun x => P.Y x z)

/-- “Y_ix(z;α)”, p. 142, marginalized point outcome. -/
def SpatialModel.marginalY {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (b : Bool) (x : Plane) : ℝ :=
  marginal Q (P.Y x) i b

/-- “τ_ix(α) = Y_ix(1;α) - Y_ix(0;α)”, p. 142. -/
def SpatialModel.pointEffect {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (x : Plane) : ℝ :=
  P.marginalY Q i true x - P.marginalY Q i false x

/-- “μ_i(z;d,α) = E_Z_-i[μ_i(Y(z,Z_-i);d)]”, p. 143. -/
def SpatialModel.m {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (b : Bool) (d : ℝ) : ℝ :=
  marginal Q (P.M i d) i b

/-- “τ_i(d;α) = μ_i(1;d,α) - μ_i(0;d,α)”, p. 143. -/
def SpatialModel.nodeEffect {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ) : ℝ :=
  P.m Q i true d - P.m Q i false d

/-- “simply the average d-radius effect over the intervention nodes”, p. 143.
This is the corrected AMR definition (T14), with i : Fin N and N > 0 in results. -/
def SpatialModel.amr {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (d : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, P.nodeEffect Q i d

/-- “N_1 = ∑ Z_i”, p. 144. -/
def nTreated {N : ℕ} (z : Assignment N) : ℝ := ∑ i, bit (z i)

/-- “N_0 = N - N_1”, p. 144. -/
def nControl {N : ℕ} (z : Assignment N) : ℝ := N - nTreated z

/-- The Hajek estimator displayed on p. 144. On empty arms Lean's inverse is
totalized; statements concerning the estimator require both arms, or specify
an explicit exceptional value for asymptotics. -/
def hajek {N : ℕ} (M : Fin N → Assignment N → ℝ) (z : Assignment N) : ℝ :=
  (∑ i, bit (z i) * M i z) / nTreated z -
    (∑ i, (1 - bit (z i)) * M i z) / nControl z

/-- Inclusive absolute-tail randomization probability, corrected rule T2/T4. -/
def tailP {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (T : Ω → ℝ) (z : Ω) : ℝ :=
  Q.prob (fun w => |T z| ≤ |T w|)

/-- The rejection region of the interpolated-percentile rule, p. 146. -/
def outside (lo hi t : ℝ) : Prop := t < lo ∨ hi < t

/-- R type-7 quantile; sorted observations are
zero-indexed. At q=1 the last order statistic is returned. -/
def quantile7 {n : ℕ} (s : Fin (n + 1) → ℝ) (q : ℝ) : ℝ :=
  let h := (n : ℝ) * q
  let j := min (Int.toNat ⌊h⌋) n
  let g := h - j
  (1 - g) * s ⟨j, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩ +
    g * s ⟨min (j + 1) n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- Finite arithmetic mean: counting-measure specialization of the circle
integral, p. 143. Only nonempty sets are used as averages. -/
def countMean {X : Type*} (C : Finset X) (f : X → ℝ) : ℝ :=
  (∑ x ∈ C, f x) / C.card

/-- A finite field on the x-axis of R², with Euclidean distance |x-node|;
the sparse-point/counting-measure option on pp. 142–144. -/
def lineCircle {N : ℕ} (field : Finset ℚ) (node : Fin N → ℚ)
    (i : Fin N) (d : ℚ) : Finset ℚ := field.filter (fun x => |x - node i| = d)

/-- Circle outcomes for the finite x-axis model, reusing the circle average. -/
def lineM {N : ℕ} (field : Finset ℚ) (node : Fin N → ℚ)
    (Y : ℚ → Assignment N → ℝ) (i : Fin N) (d : ℚ) (z : Assignment N) : ℝ :=
  countMean (lineCircle field node i d) (fun x => Y x z)

/-- The same finite x-axis circle for every real radius, p. 143: rational
coordinate distances are cast to real distances, as certified by line_embedding_distance. -/
def realLineCircle {N : ℕ} (field : Finset ℚ) (node : Fin N → ℚ)
    (i : Fin N) (d : ℝ) : Finset ℚ :=
  field.filter (fun x => ((|x - node i| : ℚ) : ℝ) = d)

/-- Counting-measure circle average with a real radius, for T26's universal
weak-null witness; it uses the same field, coordinates, outcomes and countMean. -/
def realLineM {N : ℕ} (field : Finset ℚ) (node : Fin N → ℚ)
    (Y : ℚ → Assignment N → ℝ) (i : Fin N) (d : ℝ) (z : Assignment N) : ℝ :=
  countMean (realLineCircle field node i d) (fun x => Y x z)

/- General finite-law lemmas, used by the corrections. -/

/-- Finite expectation preserves constants because design masses sum to one. -/
theorem expect_const {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (c : ℝ) :
    Q.expect (fun _ => c) = c := by
  simp [FiniteLaw.expect, ← Finset.sum_mul, Q.total]

/-- Finite design expectation is linear under subtraction. -/
theorem expect_sub {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f g : Ω → ℝ) :
    Q.expect (fun z => f z - g z) = Q.expect f - Q.expect g := by
  simp [FiniteLaw.expect, mul_sub, Finset.sum_sub_distrib]

/-- Event inclusion implies probability monotonicity. -/
theorem prob_mono {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    {P R : Ω → Prop} (h : ∀ z, P z → R z) : Q.prob P ≤ Q.prob R := by
  classical
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact h z hz
  · intro z _ _
    exact Q.nonneg z

/-- T2(a), T4(b), pp. 144, 153 corrected: inclusive design-law p-values
are superuniform, for arbitrary finite probability weights, with ties included. -/
theorem design_tail_valid {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (T : Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    Q.prob (fun z => tailP Q T z ≤ δ) ≤ δ := by
  classical
  let R := Finset.univ.filter (fun z => tailP Q T z ≤ δ)
  by_cases hR : R.Nonempty
  · obtain ⟨z, hz, hmin⟩ := Set.exists_min_image (↑R : Set Ω)
      (fun z => |T z|) R.finite_toSet hR
    have hp : tailP Q T z ≤ δ := (Finset.mem_filter.mp hz).2
    exact (prob_mono Q (fun w hw => hmin w (by simpa [R] using hw))).trans hp
  · have he : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hR
    simpa [FiniteLaw.prob, R, he] using hδ

/- Small exact corrections. -/

/-- T11(a,c), p. 149: sums of the printed estimates on [0.1,0.5] and [0.1,0.8]. -/
theorem printed_toy_sums :
    (1491 / 1000 : ℝ) + 1550 / 1000 + 1550 / 1000 + 1691 / 1000 + 1714 / 1000 =
      1999 / 250 ∧
    (1999 / 250 : ℝ) + 1700 / 1000 + 1678 / 1000 + 1002 / 1000 = 1547 / 125 := by
  norm_num

/-- T11(b), p. 149 corrected: every closed three-decimal rounding envelope
puts the five-term sum in [7.9935,7.9985], far from 12.38 and above 7.975. -/
theorem toy_sum_rounding (a b c e f : ℝ)
    (ha : |a - 1491 / 1000| ≤ 1 / 2000)
    (hb : |b - 1550 / 1000| ≤ 1 / 2000)
    (hc : |c - 1550 / 1000| ≤ 1 / 2000)
    (he : |e - 1691 / 1000| ≤ 1 / 2000)
    (hf : |f - 1714 / 1000| ≤ 1 / 2000) :
    15987 / 2000 ≤ a + b + c + e + f ∧
    a + b + c + e + f ≤ 15997 / 2000 ∧
    1 / 200 < |(a + b + c + e + f) - 619 / 50| ∧
    1595 / 200 < a + b + c + e + f := by
  rcases abs_le.mp ha with ⟨ha₁, ha₂⟩
  rcases abs_le.mp hb with ⟨hb₁, hb₂⟩
  rcases abs_le.mp hc with ⟨hc₁, hc₂⟩
  rcases abs_le.mp he with ⟨he₁, he₂⟩
  rcases abs_le.mp hf with ⟨hf₁, hf₂⟩
  have hn : a + b + c + e + f - 619 / 50 < 0 := by linarith
  rw [abs_of_neg hn]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Printed Uganda grid, p. 153: by=5/111, five points. -/
def printedGrid (k : Fin 5) : ℝ := 5 * (k : ℝ) / 111

/-- Corrected Uganda grid, T13: by=0.5/111, 41 points. -/
def correctedGrid (k : Fin 41) : ℝ := (k : ℝ) / 222

/-- The test.range printed on p. 153, in exact degree units. -/
def inUgandaRange (d : ℝ) : Prop := 1 / 111 ≤ d ∧ d ≤ 5 / 222

instance (d : ℝ) : Decidable (inUgandaRange d) := inferInstanceAs
  (Decidable (1 / 111 ≤ d ∧ d ≤ 5 / 222))

/-- T12, p. 153: the printed grid has no selected point, so every observed
or permutation sum is zero, inconsistent with all three reported nonzero values. -/
theorem printed_grid_counterexample :
    (∀ k : Fin 5, ¬ inUgandaRange (printedGrid k)) ∧
    (∀ f : Fin 5 → ℝ, ∑ k ∈ Finset.univ.filter
      (fun k => inUgandaRange (printedGrid k)), f k = 0) ∧
    (-321 / 10000 : ℝ) ≠ 0 ∧ (-19 / 625 : ℝ) ≠ 0 ∧ (21 / 625 : ℝ) ≠ 0 := by
  have hn : ∀ k : Fin 5, ¬ inUgandaRange (printedGrid k) := by
    intro k
    fin_cases k <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, inUgandaRange, printedGrid]
  refine ⟨hn, ?_, by norm_num, by norm_num, by norm_num⟩
  intro f
  have he : Finset.univ.filter (fun k => inUgandaRange (printedGrid k)) = ∅ := by
    exact Finset.filter_eq_empty_iff.mpr (fun k _ => hn k)
  rw [he, Finset.sum_empty]

/-- T13, p. 153 corrected: exactly indices 2–5 are selected, giving radii
1,1.5,2,2.5 km; the last grid point is 20/111 and the step is 1/222. -/
theorem corrected_grid :
    Fintype.card (Fin 41) = 41 ∧ correctedGrid 40 = 20 / 111 ∧
    (∀ k : Fin 41, inUgandaRange (correctedGrid k) ↔ 2 ≤ k.val ∧ k.val ≤ 5) ∧
    (∀ f : Fin 41 → ℝ, ∑ k ∈ Finset.univ.filter
      (fun k => inUgandaRange (correctedGrid k)), f k = f 2 + f 3 + f 4 + f 5) ∧
    (∀ k : Fin 40, correctedGrid k.succ - correctedGrid k.castSucc = 1 / 222) := by
  have hm : ∀ k : Fin 41, inUgandaRange (correctedGrid k) ↔
      2 ≤ k.val ∧ k.val ≤ 5 := by
    intro k
    unfold inUgandaRange correctedGrid
    constructor
    · rintro ⟨hl, hu⟩
      constructor
      · exact_mod_cast (by linarith : (2 : ℝ) ≤ k.val)
      · exact_mod_cast (by linarith : (k.val : ℝ) ≤ 5)
    · rintro ⟨hl, hu⟩
      have hl' : (2 : ℝ) ≤ k.val := by exact_mod_cast hl
      have hu' : (k.val : ℝ) ≤ 5 := by exact_mod_cast hu
      constructor <;> linarith
  have hs : Finset.univ.filter (fun k => inUgandaRange (correctedGrid k)) =
      ({2, 3, 4, 5} : Finset (Fin 41)) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hm,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by
        rcases h with ⟨hl, hu⟩
        have hv : k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 5 := by omega
        rcases hv with hv | hv | hv | hv
        · exact Or.inl (Fin.ext hv)
        · exact Or.inr (Or.inl (Fin.ext hv))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext hv)))
        · exact Or.inr (Or.inr (Or.inr (Fin.ext hv)))
      exact this
    · intro h
      rcases h with h | h | h | h <;> subst k <;> decide
  refine ⟨rfl, by norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, correctedGrid], hm, ?_, ?_⟩
  · intro f
    rw [hs]
    norm_num <;> ring
  · intro k
    simp [correctedGrid, Fin.val_succ, Fin.val_castSucc]
    ring

/-- T14(a), p. 143 corrected: the two expressions for the AMR are identical. -/
theorem amr_display {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (d : ℝ) :
    P.amr Q d = (N : ℝ)⁻¹ * ∑ i, (P.m Q i true d - P.m Q i false d) := rfl

/-- T14(b): literal juxtaposition is A², equal to A only at 0 or 1. -/
theorem amr_misprint (A : ℝ) : A * A = A ↔ A = 0 ∨ A = 1 := by
  constructor
  · intro h
    have : A * (A - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with hz | hz
    · exact Or.inl hz
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- T14(b), exact witness: two node effects 3 and 5 average to 4,
whereas the product of the two averages is 16. -/
theorem amr_misprint_witness :
    ((3 - 0 + (7 - 2)) / 2 : ℝ) = 4 ∧ (4 : ℝ) * 4 = 16 ∧ (16 : ℝ) ≠ 4 := by
  norm_num

/-- “band ... between d-k and d+k”, p. 143 corrected: a set of outcome points. -/
def SpatialModel.band {N : ℕ} (P : SpatialModel N) (i : Fin N) (d k : ℝ) : Set Plane :=
  {x | x ∈ P.field ∧ d - k ≤ dist (P.node i) x ∧ dist (P.node i) x ≤ d + k}

/-- Band average: the same normalized integral as the edge average, with
the band of outcome points as its integration domain (T15). -/
def SpatialModel.bandAverage {N : ℕ} (P : SpatialModel N) (i : Fin N) (d k : ℝ)
    (f : Plane → ℝ) : ℝ :=
  let μ := P.ζ.restrict (P.band i d k)
  (μ Set.univ).toReal⁻¹ * ∫ x, f x ∂μ

/-- T15(a), corrected p. 143: the normalized band average integrates outcomes
at points of the spatial field between radii d-k and d+k. -/
theorem band_average_display {N : ℕ} (P : SpatialModel N) (i : Fin N)
    (d k : ℝ) (hd : 0 ≤ d) (hk : 0 ≤ k) (z : Assignment N)
    (hmass : 0 < (P.ζ.restrict (P.band i d k) Set.univ).toReal)
    (hfinite : P.ζ.restrict (P.band i d k) Set.univ ≠ ⊤) :
    P.bandAverage i d k (fun x => P.Y x z) =
      (P.ζ.restrict {x | x ∈ P.field ∧ d - k ≤ dist (P.node i) x ∧
        dist (P.node i) x ≤ d + k} Set.univ).toReal⁻¹ *
      ∫ x, P.Y x z ∂P.ζ.restrict {x | x ∈ P.field ∧
        d - k ≤ dist (P.node i) x ∧ dist (P.node i) x ≤ d + k} := rfl

/-- T15(b), p. 143 corrected: a positive-inner-radius band below every
other node's distance contains no intervention nodes. -/
theorem band_contains_no_nodes {N : ℕ} (P : SpatialModel N) (i : Fin N)
    (d k : ℝ) (hinner : 0 < d - k)
    (hfar : ∀ j, j ≠ i → d + k < dist (P.node i) (P.node j)) :
    {j : Fin N | P.node j ∈ P.band i d k} = ∅ := by
  ext j
  simp only [Set.mem_setOf_eq, SpatialModel.band, Set.mem_empty_iff_false, iff_false]
  intro h
  by_cases hj : j = i
  · subst j
    simpa using (not_le.mpr hinner) (by simpa using h.2.1)
  · exact (not_le.mpr (hfar j hj)) h.2.2

/-- T17(b), nested equal-weight raster buffers: difference of sums divided
by difference of counts is the average on the added cells. -/
theorem nested_buffer_average {X : Type*} [DecidableEq X]
    (A B : Finset X) (Y : X → ℝ) (hAB : A ⊆ B) (hcard : A.card < B.card) :
    ((∑ x ∈ B, Y x) - (∑ x ∈ A, Y x)) / ((B.card : ℝ) - A.card) =
      countMean (B \ A) Y := by
  rw [countMean, Finset.sum_sdiff_eq_sub hAB, Finset.card_sdiff_of_subset hAB,
    Nat.cast_sub (Nat.le_of_lt hcard)]

/-- T17(a), the radial tolerance k gives thickness 2k; clipping at zero
is expressed by max(0,d-k), not by a negative inner radius. -/
theorem radial_band_geometry (r d k : ℝ) (hr : 0 ≤ r) :
    (|r - d| ≤ k ↔ max 0 (d - k) ≤ r ∧ r ≤ d + k) ∧
    (d + k) - (d - k) = 2 * k := by
  constructor
  · rw [abs_le, max_le_iff]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨⟨hr, by linarith⟩, by linarith⟩
    · rintro ⟨⟨_, h₁⟩, h₂⟩
      constructor <;> linarith
  · ring

/-- The six two-of-four assignments, p. 148 footnote 5 and T1–T4.
The sample space Fin 6 has uniform mass 1/6; the map lists every assignment. -/
def sixAssignment (k : Fin 6) : Assignment 4 :=
  ![![true, true, false, false], ![true, false, true, false],
    ![true, false, false, true], ![false, true, true, false],
    ![false, true, false, true], ![false, false, true, true]] k

/-- Four blocked assignments, treating one node in each pair, T1(B). -/
def blockedAssignment (k : Fin 4) : Assignment 4 := sixAssignment (![1, 2, 3, 4] k)

/-- Integer treated count, used to certify the exact enumerated support. -/
def treatedCount {N : ℕ} (z : Assignment N) : ℕ := ∑ i, if z i then 1 else 0

/-- The six-assignment table is exactly the support with two treated nodes,
without repetitions; the observed assignment 1010 is entry 1. -/
theorem six_support :
    Function.Injective sixAssignment ∧
    (∀ z : Assignment 4, treatedCount z = 2 ↔ ∃ k, sixAssignment k = z) ∧
    sixAssignment 1 = ![true, false, true, false] := by
  decide

/-- The blocked table is exactly the assignments treating one per pair. -/
theorem blocked_support :
    Function.Injective blockedAssignment ∧
    (∀ z : Assignment 4, (z 0 ≠ z 1 ∧ z 2 ≠ z 3) ↔
      ∃ k, blockedAssignment k = z) := by
  decide

/-- Fixed-outcome Hajek contrast with two nodes in each arm, pp. 144, 148. -/
def contrast4 (y : Fin 4 → ℝ) (z : Assignment 4) : ℝ :=
  (∑ i, bit (z i) * y i) / 2 - (∑ i, (1 - bit (z i)) * y i) / 2

/-- T1(B)/T3 reduction: this contrast is exactly the printed Hajek estimator
on each of the six assignments, with both arms of size two. -/
theorem contrast_is_hajek (y : Fin 4 → ℝ) (k : Fin 6) :
    nTreated (sixAssignment k) = 2 ∧ nControl (sixAssignment k) = 2 ∧
    hajek (fun i _ => y i) (sixAssignment k) = contrast4 y (sixAssignment k) := by
  have h : nTreated (sixAssignment k) = 2 := by
    fin_cases k <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, nTreated, sixAssignment, bit, Fin.sum_univ_succ]
  refine ⟨h, by norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, nControl, h], ?_⟩
  norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, hajek, contrast4, h, nControl]

/-- Complement map for the six assignments, T4(a): swaps 1100/0011,
1010/0101, and 1001/0110. -/
def sixComplement (k : Fin 6) : Fin 6 := ![5, 4, 3, 2, 1, 0] k

/-- Complementation preserves support, has no fixed points, and reverses
every fixed-outcome Hajek contrast (T4(a), p. 150 corrected). -/
theorem complement_contrast (y : Fin 4 → ℝ) (k : Fin 6) :
    sixComplement k ≠ k ∧
    sixAssignment (sixComplement k) = (fun i => !(sixAssignment k i)) ∧
    contrast4 y (sixAssignment (sixComplement k)) =
      -contrast4 y (sixAssignment k) := by
  fin_cases k <;> refine ⟨by decide, by decide, ?_⟩ <;>
    norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, sixComplement, sixAssignment, contrast4, bit, Fin.sum_univ_succ] <;> ring

/-- T1(B), p. 153's design-law correction: unrestricted and blocked laws
give inclusive tail probabilities 1/3 vs 1/2, or 2/3 vs 1/2, respectively.
The outcomes are assignment-independent, so these are sharp-null examples. -/
theorem reference_laws_counterexample :
    tailP (uniformLaw (Fin 6))
      (fun k => contrast4 ![0, 1, 0, 1] (sixAssignment k)) 1 = 1 / 3 ∧
    tailP (uniformLaw (Fin 4))
      (fun k => contrast4 ![0, 1, 0, 1] (blockedAssignment k)) 0 = 1 / 2 ∧
    tailP (uniformLaw (Fin 6))
      (fun k => contrast4 ![0, 1 / 3, 2 / 3, 1] (sixAssignment k)) 1 = 2 / 3 ∧
    tailP (uniformLaw (Fin 4))
      (fun k => contrast4 ![0, 1 / 3, 2 / 3, 1] (blockedAssignment k)) 0 = 1 / 2 ∧
    (1 / 3 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 2 / 3 := by
  classical
  refine ⟨?_, ?_, ?_, ?_, by norm_num, by norm_num⟩
  · have he : Finset.univ.filter (fun k : Fin 6 =>
        |contrast4 ![0, 1, 0, 1] (sixAssignment 1)| ≤
          |contrast4 ![0, 1, 0, 1] (sixAssignment k)|) = {1, 4} := by
      ext k
      fin_cases k <;> norm_num [contrast4, sixAssignment, bit, Fin.sum_univ_succ] <;>
        norm_num [sixAssignment, bit, Fin.sum_univ_succ]
    unfold tailP FiniteLaw.prob
    rw [he]
    norm_num [uniformLaw]
  · have he : Finset.univ.filter (fun k : Fin 4 =>
        |contrast4 ![0, 1, 0, 1] (blockedAssignment 0)| ≤
          |contrast4 ![0, 1, 0, 1] (blockedAssignment k)|) = {0, 3} := by
      ext k
      fin_cases k <;> norm_num [contrast4, blockedAssignment, sixAssignment, bit, Fin.sum_univ_succ]
    unfold tailP FiniteLaw.prob
    rw [he]
    norm_num [uniformLaw]
  · have he : Finset.univ.filter (fun k : Fin 6 =>
        |contrast4 ![0, 1 / 3, 2 / 3, 1] (sixAssignment 1)| ≤
          |contrast4 ![0, 1 / 3, 2 / 3, 1] (sixAssignment k)|) = {0, 1, 4, 5} := by
      ext k
      fin_cases k <;> norm_num [contrast4, sixAssignment, bit, Fin.sum_univ_succ] <;>
        norm_num [sixAssignment, bit, Fin.sum_univ_succ]
    unfold tailP FiniteLaw.prob
    rw [he]
    norm_num [uniformLaw]
  · have he : Finset.univ.filter (fun k : Fin 4 =>
        |contrast4 ![0, 1 / 3, 2 / 3, 1] (blockedAssignment 0)| ≤
          |contrast4 ![0, 1 / 3, 2 / 3, 1] (blockedAssignment k)|) = {0, 3} := by
      ext k
      fin_cases k <;> norm_num [contrast4, blockedAssignment, sixAssignment, bit, Fin.sum_univ_succ]
    unfold tailP FiniteLaw.prob
    rw [he]
    norm_num [uniformLaw]

/-- Sorted statistics of the exact sharp-null counterexample in T3. -/
def percentileExample (k : Fin 6) : ℝ := ![-2, -1, 0, 0, 1, 2] k

/-- T3 exact interpolation and enumeration: the rule rejects a true sharp
null with probability 1/3 > .05; five-radius sums have the same rejection set. -/
theorem interpolated_percentile_counterexample :
    (∀ k, contrast4 ![0, 1, 2, 3] (sixAssignment k) = percentileExample k) ∧
    quantile7 percentileExample (1 / 40) = -15 / 8 ∧
    quantile7 percentileExample (39 / 40) = 15 / 8 ∧
    (uniformLaw (Fin 6)).prob (fun k => outside (-15 / 8) (15 / 8)
      (percentileExample k)) = 1 / 3 ∧
    quantile7 (fun k => 5 * percentileExample k) (1 / 40) = -75 / 8 ∧
    quantile7 (fun k => 5 * percentileExample k) (39 / 40) = 75 / 8 ∧
    (uniformLaw (Fin 6)).prob (fun k => outside (-75 / 8) (75 / 8)
      (5 * percentileExample k)) = 1 / 3 ∧ (1 / 20 : ℝ) < 1 / 3 := by
  refine ⟨?_, ?_⟩
  · intro k
    fin_cases k <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, contrast4, sixAssignment, percentileExample,
      bit, Fin.sum_univ_succ]
  · norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, quantile7, percentileExample, FiniteLaw.prob, Finset.sum_filter,
      uniformLaw, outside, Fin.sum_univ_succ]

/-- T4(a), any linear functional of the four-node fixed-outcome contrasts
is antisymmetric under complementation. -/
theorem linear_functional_complement {J : ℕ} (a : Fin J → ℝ)
    (m : Fin J → Fin 4 → ℝ) (k : Fin 6) :
    (∑ j, a j * contrast4 (m j) (sixAssignment (sixComplement k))) =
      -(∑ j, a j * contrast4 (m j) (sixAssignment k)) := by
  simp_rw [(complement_contrast (m _) k).2.2, mul_neg]
  rw [Finset.sum_neg_distrib]

/-- T4(a): an inclusive absolute tail contains the observed assignment and
its distinct complement, so its probability is at least 1/3. -/
theorem six_tail_lower_bound (S : Fin 6 → ℝ)
    (hS : ∀ k, S (sixComplement k) = -S k) (k : Fin 6) :
    1 / 3 ≤ tailP (uniformLaw (Fin 6)) S k := by
  classical
  let A := Finset.univ.filter (fun w => |S k| ≤ |S w|)
  have hk : k ∈ A := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_rfl⟩
  have hc : sixComplement k ∈ A := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [hS k, abs_neg]⟩
  have hne : sixComplement k ≠ k := (complement_contrast (fun _ => 0) k).1
  have hsub : ({k, sixComplement k} : Finset (Fin 6)) ⊆ A := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hk
    · exact hc
  have hcA : 2 ≤ A.card := by
    simpa [hne, Ne.symm hne] using Finset.card_le_card hsub
  have hcR : (2 : ℝ) ≤ A.card := by exact_mod_cast hcA
  unfold tailP FiniteLaw.prob
  change (∑ _ ∈ A, (6 : ℝ)⁻¹) ≥ 1 / 3
  simp only [Finset.sum_const, nsmul_eq_mul]
  linarith

/-- T4(a,c): every nonempty rejection set on the uniform six-assignment
space has mass at least 1/6 > .05, and inclusive tails never reject at .05. -/
theorem six_no_five_percent_rejection (S : Fin 6 → ℝ)
    (hS : ∀ k, S (sixComplement k) = -S k) :
    (∀ k, ¬ tailP (uniformLaw (Fin 6)) S k ≤ 1 / 20) ∧
    (∀ R : Finset (Fin 6), R.Nonempty →
      1 / 20 < (uniformLaw (Fin 6)).prob (fun k => k ∈ R)) := by
  constructor
  · intro k
    have := six_tail_lower_bound S hS k
    linarith
  · intro R hR
    have hr : (1 : ℝ) ≤ R.card := by exact_mod_cast (Nat.succ_le_of_lt hR.card_pos)
    simp only [FiniteLaw.prob, Finset.filter_mem_eq_inter, Finset.univ_inter,
      uniformLaw, Fintype.card_fin, Finset.sum_const, nsmul_eq_mul]
    linarith

/-- T8(a): normalized radius sampling produces genuine probabilities;
its effect is the weighted AMR difference and lies between any common lower
and upper bounds on the individual-radius effects (hence their min/max). -/
theorem normalized_probability_effect {J : ℕ} (w q₀ q₁ : Fin J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1)
    (h₀ : ∀ j, 0 ≤ q₀ j ∧ q₀ j ≤ 1) (h₁ : ∀ j, 0 ≤ q₁ j ∧ q₁ j ≤ 1)
    (L U : ℝ) (hL : ∀ j, L ≤ q₁ j - q₀ j) (hU : ∀ j, q₁ j - q₀ j ≤ U) :
    (0 ≤ ∑ j, w j * q₀ j ∧ ∑ j, w j * q₀ j ≤ 1) ∧
    (0 ≤ ∑ j, w j * q₁ j ∧ ∑ j, w j * q₁ j ≤ 1) ∧
    (∑ j, w j * q₁ j) - (∑ j, w j * q₀ j) = ∑ j, w j * (q₁ j - q₀ j) ∧
    L ≤ ∑ j, w j * (q₁ j - q₀ j) ∧ ∑ j, w j * (q₁ j - q₀ j) ≤ U ∧
    |(∑ j, w j * q₁ j) - (∑ j, w j * q₀ j)| ≤ 1 := by
  have hb (q : Fin J → ℝ) (hq : ∀ j, 0 ≤ q j ∧ q j ≤ 1) :
      0 ≤ ∑ j, w j * q j ∧ ∑ j, w j * q j ≤ 1 := by
    constructor
    · exact Finset.sum_nonneg (fun j _ => mul_nonneg (hw j) (hq j).1)
    · calc
        (∑ j, w j * q j) ≤ ∑ j, w j * 1 :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hq j).2 (hw j))
        _ = 1 := by simpa using hs
  have h0 := hb q₀ h₀
  have h1 := hb q₁ h₁
  have he : (∑ j, w j * q₁ j) - (∑ j, w j * q₀ j) =
      ∑ j, w j * (q₁ j - q₀ j) := by simp [mul_sub, Finset.sum_sub_distrib]
  refine ⟨h0, h1, he, ?_, ?_, ?_⟩
  · calc
      L = ∑ j, w j * L := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hL j) (hw j))
  · calc
      _ ≤ ∑ j, w j * U :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hU j) (hw j))
      _ = U := by rw [← Finset.sum_mul, hs, one_mul]
  · rw [abs_le]
    constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- T8(b): constant effects average to t with normalized weights and sum
to J*t with unit weights. -/
theorem constant_radius_effect {J : ℕ} (w : Fin J → ℝ) (hs : ∑ j, w j = 1)
    (t : ℝ) : (∑ j, w j * t) = t ∧ (∑ _j : Fin J, t) = J * t := by
  simp [← Finset.sum_mul, hs, nsmul_eq_mul]

/-- T8(c): common positive scaling preserves ranks, absolute tails, and
type-7 interpolated quantiles. -/
theorem common_rescaling {n : ℕ} (s : Fin (n + 1) → ℝ) (q m x y : ℝ)
    (hm : 0 < m) :
    (x ≤ y ↔ x / m ≤ y / m) ∧
    (|x| ≤ |y| ↔ |x / m| ≤ |y / m|) ∧
    quantile7 (fun j => s j / m) q = quantile7 s q / m := by
  refine ⟨(div_le_div_iff_of_pos_right hm).symm, ?_, ?_⟩
  · simp only [abs_div, abs_of_pos hm]
    exact (div_le_div_iff_of_pos_right hm).symm
  · unfold quantile7
    ring

/-- T8(c), exact normalization of the three printed numbers over four radii. -/
theorem reported_values_divided_by_four :
    (-19 / 625 : ℝ) / 4 = -19 / 2500 ∧
    (-321 / 10000 : ℝ) / 4 = -321 / 40000 ∧
    (21 / 625 : ℝ) / 4 = 21 / 2500 ∧
    (-321 / 40000 : ℝ) < -19 / 2500 := by norm_num

/-- T16, later polygon-buffer counterexample: distances of nonmissing cells. -/
def bufferCellDistance : Fin 4 → ℝ := ![0, 19 / 8, 27 / 8, 35 / 8]

/-- T16: all four treated-cell outcomes (the control-cell outcomes are zero). -/
def bufferCellOutcome : Fin 4 → ℝ := ![4, 2, 0, 8]

/-- Nested nonmissing-cell buffer at radius r, polygon-buffer definition (T16/T17). -/
def bufferCells (r : ℝ) : Finset (Fin 4) :=
  Finset.univ.filter (fun c => bufferCellDistance c ≤ r)

/-- T16: the implemented annulus, symmetric band and full buffer give 1,4,2.
With one treated and one control polygon these are the Hajek contrasts. -/
theorem donut_counterexample :
    countMean (bufferCells 4 \ bufferCells 2) bufferCellOutcome = 1 ∧
    countMean (Finset.univ.filter (fun c =>
      3 ≤ bufferCellDistance c ∧ bufferCellDistance c ≤ 5)) bufferCellOutcome = 4 ∧
    countMean (bufferCells 4) bufferCellOutcome = 2 ∧
    (1 : ℝ) ≠ 4 := by
  have h₂ : bufferCells 2 = {0} := by
    ext c
    fin_cases c <;> norm_num [bufferCells, bufferCellDistance]
  have h₄ : bufferCells 4 = {0, 1, 2} := by
    ext c
    fin_cases c <;> norm_num [bufferCells, bufferCellDistance]
  have hband : Finset.univ.filter (fun c : Fin 4 =>
      3 ≤ bufferCellDistance c ∧ bufferCellDistance c ≤ 5) = {2, 3} := by
    ext c
    fin_cases c <;> norm_num [bufferCellDistance]
  rw [h₂, h₄, hband]
  norm_num [countMean, bufferCellOutcome, Finset.sdiff_eq_filter,
    Finset.filter_insert, Finset.filter_singleton]

/-- A 5×5 polygon's cells, indexed by local row and column (T19/T20).
Translating to [2,7]² or [12,17]×[2,7] embeds these at the required cell centres. -/
abbrev BlockCell := Fin 5 × Fin 5

/-- Eight-neighbour inner-boundary selector for a 5×5 raster block: outer
row or column, as in the eight-neighbour boundary-cell convention (T20(a)). -/
def blockBoundary : Finset BlockCell :=
  Finset.univ.filter (fun c => c.1 = 0 ∨ c.1 = 4 ∨ c.2 = 0 ∨ c.2 = 4)

/-- Binary causal outcomes in T19: only the treated polygon's central 3×3
cells respond to its treatment; the control polygon is identically zero. -/
def blockY (c : BlockCell) (z : Bool) : ℝ :=
  if c ∈ blockBoundary then 0 else bit z

/-- T19/T20(a,c): the same outcome field gives boundary contrast zero and
polygon contrast 9/25; marginalized node averaging gives AMRs 0 and 9/50. -/
theorem boundary_counterexample :
    (Finset.univ : Finset BlockCell).card = 25 ∧ blockBoundary.card = 16 ∧
    ((Finset.univ : Finset BlockCell) \ blockBoundary).card = 9 ∧
    countMean blockBoundary (fun c => blockY c true) = 0 ∧
    countMean Finset.univ (fun c => blockY c true) = 9 / 25 ∧
    countMean Finset.univ (fun c => blockY c false) = 0 ∧
    ((9 / 25 + 0) / 2 : ℝ) = 9 / 50 ∧ (0 : ℝ) ≠ 9 / 25 := by
  have hbd : blockBoundary.card = 16 := by decide
  have hint : ((Finset.univ : Finset BlockCell) \ blockBoundary).card = 9 := by decide
  have hf : (Finset.univ.filter (fun c : BlockCell => c ∉ blockBoundary)) =
      Finset.univ \ blockBoundary := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  refine ⟨by decide, hbd, hint, ?_, ?_, ?_, by norm_num, by norm_num⟩
  · unfold countMean
    have hs : (∑ c ∈ blockBoundary, blockY c true) = 0 :=
      Finset.sum_eq_zero (fun c hc => by simp [blockY, hc])
    rw [hs, zero_div]
  · simp [countMean, blockY, bit, Finset.sum_ite, hf, hint]
  · simp [countMean, blockY, bit]

/-- T20(b), p. 153 corrected: for a nonempty polygon boundary, distance
from its closed boundary is zero exactly on the boundary; all interior points
have strictly positive distance. Nonemptiness avoids infDist's empty-set value. -/
theorem zero_distance_is_boundary (P : Set Plane) (hbd : (frontier P).Nonempty) :
    {x | Metric.infDist x (frontier P) = 0} = frontier P ∧
    (∀ x ∈ interior P, 0 < Metric.infDist x (frontier P)) := by
  constructor
  · ext x
    exact (isClosed_frontier.mem_iff_infDist_zero hbd).symm
  · intro x hx
    apply (isClosed_frontier.notMem_iff_infDist_pos hbd).mp
    exact fun h => disjoint_interior_frontier.le_bot ⟨hx, h⟩

/- Circle identities and structural effects: the headline statements. -/


/-- Weighted integrability requires the potential outcome only at nonzero
randomization weights; zero-mass off-support assignments contribute zero. -/
theorem weighted_integrable {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (c : ℝ) (f : X → ℝ) (hf : c ≠ 0 → Integrable f μ) :
    Integrable (fun x => c * f x) μ := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (hf hc).const_mul c

/-- A circle in a measurable spatial field is measurable; this gives the
restricted integration measure its intended domain of outcome points. -/
theorem circle_measurable {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ)
    (hfield : MeasurableSet P.field) : MeasurableSet (P.circle i d) :=
  hfield.inter (isClosed_eq (continuous_const.dist continuous_id) continuous_const).measurableSet

/-- T25(a), p. 143: finite marginalization commutes with the normalized
circle integral, under the explicit integrability and mass conditions. -/
theorem circle_marginal_identity {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ) (b : Bool)
    (hmass : 0 < P.circleMass i d)
    (hfinite : P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ z, Q.mass z ≠ 0 → Integrable (fun x => P.Y x (Function.update z i b))
      (P.circleMeasure i d)) :
    P.m Q i b d = P.average i d (P.marginalY Q i b) := by
  simp only [SpatialModel.m, marginal, FiniteLaw.expect, SpatialModel.M,
    SpatialModel.average, SpatialModel.marginalY]
  rw [integral_finsetSum (Finset.univ : Finset (Assignment N))
    (fun z _ => weighted_integrable _ _ _ (hint z))]
  simp_rw [integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- T25(b), p. 143: the node effect is the circle average of the point
effects, with every override integrable and circle mass positive and finite. -/
theorem circle_effect_identity {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (i : Fin N) (d : ℝ)
    (hmass : 0 < P.circleMass i d)
    (hfinite : P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ b z, Q.mass z ≠ 0 → Integrable (fun x => P.Y x (Function.update z i b))
      (P.circleMeasure i d)) :
    P.nodeEffect Q i d = P.average i d (P.pointEffect Q i) := by
  have hi (b : Bool) : Integrable (P.marginalY Q i b) (P.circleMeasure i d) := by
    unfold SpatialModel.marginalY marginal FiniteLaw.expect
    exact integrable_finsetSum _ (fun z _ => weighted_integrable _ _ _ (hint b z))
  unfold SpatialModel.nodeEffect
  rw [circle_marginal_identity P Q i d true hmass hfinite (hint true),
    circle_marginal_identity P Q i d false hmass hfinite (hint false)]
  unfold SpatialModel.average SpatialModel.pointEffect
  rw [integral_sub (hi true) (hi false)]
  ring

/-- T25(b), p. 143: averaging the preceding circle identity over nodes
gives the corrected AMR integral display, for N > 0. -/
theorem amr_integral_identity {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (d : ℝ) (hN : 0 < N)
    (hmass : ∀ i, 0 < P.circleMass i d)
    (hfinite : ∀ i, P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ i b z, Q.mass z ≠ 0 → Integrable (fun x => P.Y x (Function.update z i b))
      (P.circleMeasure i d)) :
    P.amr Q d = (N : ℝ)⁻¹ * ∑ i, P.average i d (P.pointEffect Q i) := by
  unfold SpatialModel.amr
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact circle_effect_identity P Q i d (hmass i) (hfinite i) (hint i)

/-- “sharp null ... Y_x(Z) = Y_x(0)”, p. 144, universally over the full
potential-outcome domain. -/
def SpatialModel.sharpNull {N : ℕ} (P : SpatialModel N) : Prop :=
  ∀ x ∈ P.field, ∀ z, P.Y x z = P.Y x (fun _ => false)

/-- T26(a), p. 144: the sharp null forces every point effect, node effect
and AMR to vanish under every design, without any independence restriction. -/
theorem sharp_null_implies_weak {N : ℕ} (P : SpatialModel N)
    (hsharp : P.sharpNull) (hfield : MeasurableSet P.field)
    (Q : FiniteLaw (Assignment N)) :
    (∀ i x, x ∈ P.field → P.pointEffect Q i x = 0) ∧
    (∀ i d, P.nodeEffect Q i d = 0) ∧ (∀ d, P.amr Q d = 0) := by
  have hy (i : Fin N) (x : Plane) (hx : x ∈ P.field) (b : Bool) :
      P.marginalY Q i b x = P.Y x (fun _ => false) := by
    unfold SpatialModel.marginalY marginal
    have he : (fun z => P.Y x (Function.update z i b)) =
        (fun _ => P.Y x (fun _ => false)) := by
      funext z
      exact hsharp x hx _
    rw [he, expect_const]
  have hm (i : Fin N) (d : ℝ) (b : Bool) :
      P.m Q i b d = P.M i d (fun _ => false) := by
    unfold SpatialModel.m marginal
    have he : (fun z => P.M i d (Function.update z i b)) =
        (fun _ => P.M i d (fun _ => false)) := by
      funext z
      unfold SpatialModel.M SpatialModel.average
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (circle_measurable P i d hfield)] with x hx
      exact hsharp x hx.1 _
    rw [he, expect_const]
  have he : ∀ i d, P.nodeEffect Q i d = 0 := by
    intro i d
    simp [SpatialModel.nodeEffect, hm]
  refine ⟨?_, he, ?_⟩
  · intro i x hx
    simp [SpatialModel.pointEffect, hy i x hx]
  · intro d
    simp [SpatialModel.amr, he]

/-- T27's additive structural model (p. 140's attributed statement,
explicit model): baseline plus ∑ z_k g_k(x). -/
def additiveOutcome {N : ℕ} (base : Plane → ℝ) (g : Fin N → Plane → ℝ)
    (x : Plane) (z : Assignment N) : ℝ := base x + ∑ k, bit (z k) * g k x

/-- Switching one node in an additive outcome cancels every other node's
contribution, for every other-node assignment (T27(a), T18(a)). -/
theorem additive_switch {N : ℕ} (base : Plane → ℝ) (g : Fin N → Plane → ℝ)
    (i : Fin N) (x : Plane) (z : Assignment N) :
    additiveOutcome base g x (Function.update z i true) -
      additiveOutcome base g x (Function.update z i false) = g i x := by
  unfold additiveOutcome
  have ht (k : Fin N) :
      bit (Function.update z i true k) * g k x -
        bit (Function.update z i false k) * g k x = if k = i then g i x else 0 := by
    by_cases h : k = i
    · subst k
      simp [bit]
    · simp [Function.update_of_ne h, h]
  calc
    base x + (∑ k, bit (Function.update z i true k) * g k x) -
        (base x + ∑ k, bit (Function.update z i false k) * g k x) =
      ∑ k, (bit (Function.update z i true k) * g k x -
        bit (Function.update z i false k) * g k x) := by
          rw [Finset.sum_sub_distrib]
          ring
    _ = g i x := by simp_rw [ht]; simp

/-- T27(a), p. 140: under additive potential outcomes, the marginalized
point effect equals g_i(x) for every design, including dependent designs. -/
theorem additive_point_effect {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (base : Plane → ℝ) (g : Fin N → Plane → ℝ)
    (hadd : ∀ x ∈ P.field, ∀ z, P.Y x z = additiveOutcome base g x z)
    (i : Fin N) (x : Plane) (hx : x ∈ P.field) :
    P.pointEffect Q i x = g i x := by
  unfold SpatialModel.pointEffect SpatialModel.marginalY marginal
  rw [← expect_sub]
  have he : (fun z => P.Y x (Function.update z i true) -
      P.Y x (Function.update z i false)) = (fun _ => g i x) := by
    funext z
    simp only [hadd x hx]
    exact additive_switch base g i x z
  rw [he, expect_const]

/-- T27(a): node effects and the AMR are circle averages of the additive
coefficients on the spatial field, under positive finite mass and integrable
outcomes on nonzero-weight assignments. -/
theorem additive_amr {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (base : Plane → ℝ) (g : Fin N → Plane → ℝ)
    (hfield : MeasurableSet P.field)
    (hadd : ∀ x ∈ P.field, ∀ z, P.Y x z = additiveOutcome base g x z)
    (d : ℝ) (hN : 0 < N) (hmass : ∀ i, 0 < P.circleMass i d)
    (hfinite : ∀ i, P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ i b z, Q.mass z ≠ 0 → Integrable (fun x => P.Y x (Function.update z i b))
      (P.circleMeasure i d)) :
    (∀ i, P.nodeEffect Q i d = P.average i d (g i)) ∧
    P.amr Q d = (N : ℝ)⁻¹ * ∑ i, P.average i d (g i) := by
  have he (i : Fin N) : P.pointEffect Q i =ᵐ[P.circleMeasure i d] g i := by
    filter_upwards [ae_restrict_mem (circle_measurable P i d hfield)] with x hx
    exact additive_point_effect P Q base g hadd i x hx.1
  have hn (i : Fin N) : P.nodeEffect Q i d = P.average i d (g i) := by
    rw [circle_effect_identity P Q i d (hmass i) (hfinite i) (hint i)]
    unfold SpatialModel.average
    rw [integral_congr_ae (he i)]
  exact ⟨hn, by simp [SpatialModel.amr, hn]⟩

/-- T18 kernel, not printed as a
formula in Figure 2: 2 exp(-2r) - (128/3)r⁴ exp(-4r). -/
def toyKernel (r : ℝ) : ℝ := 2 * Real.exp (-2 * r) - (128 / 3) * r ^ 4 * Real.exp (-4 * r)

/-- T18(b), the exact global kernel lower bound. A fourth power of the
standard bound r exp(-r) ≤ exp(-1) replaces the derivative argument;
eight positive Taylor terms prove exp(4) > 437/9. -/
theorem toy_kernel_lower_bound (r : ℝ) (hr : 0 ≤ r) :
    -(384 / 437 : ℝ) < toyKernel r ∧ -(1 : ℝ) < -(384 / 437 : ℝ) := by
  have ht := Real.mul_exp_neg_le_exp_neg_one r
  have hpow : (r * Real.exp (-r)) ^ 4 ≤ (Real.exp (-1)) ^ 4 := by
    gcongr
  have heq₁ : (Real.exp (-r)) ^ 4 = Real.exp (-4 * r) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have heq₂ : (Real.exp (-1)) ^ 4 = (Real.exp 4)⁻¹ := by
    rw [← Real.exp_nat_mul]
    norm_num
    rw [Real.exp_neg]
  rw [mul_pow, heq₁, heq₂] at hpow
  have htaylor := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4 by norm_num) 8
  norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, Finset.sum_range_succ, Nat.factorial] at htaylor
  have he : (437 / 9 : ℝ) < Real.exp 4 := by linarith
  have hi : (Real.exp 4)⁻¹ < (437 / 9 : ℝ)⁻¹ :=
    by simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 437 / 9) he
  have hh : (128 / 3 : ℝ) * r ^ 4 * Real.exp (-4 * r) < 384 / 437 := by
    calc
      _ ≤ (128 / 3 : ℝ) * (Real.exp 4)⁻¹ := by nlinarith [hpow]
      _ < 384 / 437 := by norm_num at hi ⊢; linarith
  have hp : 0 < Real.exp (-2 * r) := Real.exp_pos _
  constructor
  · unfold toyKernel
    linarith
  · norm_num

/-- T18(a), raster circle averages use nonnegative normalized cell weights;
the AMR scales linearly with amplitude and has the asserted convex bound. -/
theorem toy_amplitude_and_bound {C : ℕ} (w r : Fin 4 → Fin C → ℝ)
    (hw : ∀ i c, 0 ≤ w i c) (hs : ∀ i, ∑ c, w i c = 1)
    (hr : ∀ i c, 0 ≤ r i c) :
    (1 / 4 : ℝ) * (∑ i, ∑ c, w i c * (3 * toyKernel (r i c))) =
      3 * ((1 / 4 : ℝ) * ∑ i, ∑ c, w i c * toyKernel (r i c)) ∧
    -(384 / 437 : ℝ) < (1 / 4 : ℝ) * ∑ i, ∑ c, w i c * toyKernel (r i c) := by
  constructor
  · simp_rw [show ∀ i c, w i c * (3 * toyKernel (r i c)) =
      3 * (w i c * toyKernel (r i c)) by intros; ring, ← Finset.mul_sum]
    ring
  · have hi (i : Fin 4) : -(384 / 437 : ℝ) <
        ∑ c, w i c * toyKernel (r i c) := by
      have hp : ∃ c, 0 < w i c := by
        by_contra hn
        push_neg at hn
        have hz : ∀ c, w i c = 0 := fun c => le_antisymm (hn c) (hw i c)
        have : (0 : ℝ) = 1 := by simpa [hz] using hs i
        norm_num at this
      obtain ⟨c₀, hc₀⟩ := hp
      calc
        -(384 / 437 : ℝ) = ∑ c, w i c * (-(384 / 437 : ℝ)) := by
          rw [← Finset.sum_mul, hs i, one_mul]
        _ < ∑ c, w i c * toyKernel (r i c) := by
          apply Finset.sum_lt_sum
          · intro c _
            exact mul_le_mul_of_nonneg_left (toy_kernel_lower_bound _ (hr i c)).1.le (hw i c)
          · exact ⟨c₀, Finset.mem_univ _,
              mul_lt_mul_of_pos_left (toy_kernel_lower_bound _ (hr i c₀)).1 hc₀⟩
    have hsum : (∑ _i : Fin 4, -(384 / 437 : ℝ)) <
        ∑ i, ∑ c, w i c * toyKernel (r i c) :=
      Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun i _ => hi i)
    norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, Fin.sum_univ_succ] at hsum ⊢
    linarith

/- Uniform-kernel HAC corrections. -/

/-- Group means of circle outcomes, p. 144's Hajek formula (T6, T9). -/
def groupMean {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) (b : Bool) : ℝ :=
  if b then (∑ i, bit (z i) * M i) / nTreated z
  else (∑ i, (1 - bit (z i)) * M i) / nControl z

/-- Residual of the intercept-and-treatment regression, T6(a), T9. -/
def groupResidual {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) (i : Fin N) : ℝ :=
  M i - groupMean z M (z i)

/-- “q_i = Z_i/N_1 - (1-Z_i)/N_0”, correction T6(a). -/
def contrastWeight {N : ℕ} (z : Assignment N) (i : Fin N) : ℝ :=
  bit (z i) / nTreated z - (1 - bit (z i)) / nControl z

/-- Residual-weighted treatment coefficient score g_i = q_i e_i, T9. -/
def regressionScore {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) (i : Fin N) : ℝ :=
  contrastWeight z i * groupResidual z M i

/-- Uniform-kernel spatial-HAC variance “∑∑ q_i q_j e_i e_j 1{D_ij≤c}”,
T6(a), T9, T10. The input scores are exactly the residual-weighted coefficients. -/
def hac {N : ℕ} (g : Fin N → ℝ) (D : Fin N → Fin N → ℝ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, g i * g j * (if D i j ≤ c then 1 else 0)

/-- The no-covariate regression design with rows X_i=(1,Z_i), T6(a), T9. -/
def binaryDesign {N : ℕ} (z : Assignment N) : Matrix (Fin N) (Fin 2) ℝ :=
  fun i j => if j = 0 then 1 else bit (z i)

/-- The actual least-squares residual r=M-X(X'X)⁻¹X'M, T9/T10. -/
def olsResidual {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) : Fin N → ℝ :=
  let X := binaryDesign z
  fun i => M i - (X.mulVec (((X.transpose * X)⁻¹).mulVec (X.transpose.mulVec M))) i

/-- The residual-weighted spatial HAC meat matrix displayed in T6(a). -/
def olsMeat {N : ℕ} (z : Assignment N) (M : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun a b => ∑ i, ∑ j, (if D i j ≤ c then 1 else 0) *
    olsResidual z M i * olsResidual z M j * binaryDesign z i a * binaryDesign z j b

/-- T6(a), the two finite binary-regression identities underlying the
HAC reduction: the treatment contrast row is q_i, and OLS residuals are
the deviations from the actual treatment-group means. -/
theorem binary_regression_weights_residuals {N : ℕ} (z : Assignment N) (M : Fin N → ℝ)
    (h₁ : 1 ≤ nTreated z) (h₀ : 1 ≤ nControl z) :
    let X := binaryDesign z
    let H := (X.transpose * X)⁻¹
    (∀ i, (H * X.transpose) 1 i = contrastWeight z i) ∧
    (∀ i, olsResidual z M i = groupResidual z M i) := by
  let X := binaryDesign z
  have ht : nTreated z ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h₁)
  have hc : nControl z ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one h₀)
  have hNc : (N : ℝ) = nTreated z + nControl z := by simp [nControl] <;> ring
  have hb (i : Fin N) : bit (z i) * bit (z i) = bit (z i) := by
    cases z i <;> norm_num [bit]
  have hgram : X.transpose * X =
      !![(N : ℝ), nTreated z; nTreated z, nTreated z] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [X, Matrix.mul_apply, Matrix.transpose_apply, binaryDesign, hb, nTreated]
  have hdet : (X.transpose * X).det = nTreated z * nControl z := by
    rw [hgram, Matrix.det_fin_two_of]
    rw [hNc]
    ring
  have hinv : (X.transpose * X)⁻¹ =
      !![(nControl z)⁻¹, -(nControl z)⁻¹;
        -(nControl z)⁻¹, (nTreated z)⁻¹ + (nControl z)⁻¹] := by
    rw [Matrix.inv_def, hdet, hgram, Matrix.adjugate_fin_two_of, Ring.inverse_eq_inv]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.smul_apply, hNc] <;>
      field_simp [ht, hc] <;> ring
  have hcontrol : (∑ j, (1 - bit (z j)) * M j) =
      (∑ j, M j) - ∑ j, bit (z j) * M j := by
    simp [sub_mul, Finset.sum_sub_distrib]
  refine ⟨?_, ?_⟩
  · intro i
    rw [hinv]
    simp [X, Matrix.mul_apply, Matrix.transpose_apply, binaryDesign, contrastWeight,
      Fin.sum_univ_succ, div_eq_mul_inv] <;> ring
  · intro i
    unfold olsResidual groupResidual groupMean
    rw [hinv, hcontrol]
    cases hz : z i <;>
      simp [Matrix.mulVec_apply_eq_sum, Matrix.vecMul, dotProduct,
        Fin.sum_univ_succ, X, binaryDesign, Matrix.transpose_apply, bit, hz,
        Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul] <;> field_simp [ht, hc] <;> ring
    all_goals
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      cases hj : z j <;> simp [hj, ht, hc] <;> field_simp [ht, hc] <;> ring

/-- T6(a)/T9/T10, the exact matrix-to-scalar reduction with both arms present:
the treatment row of (X'X)⁻¹X' is q, the OLS residual is the group residual,
and the treatment diagonal of the sandwich is the stated scalar HAC. -/
theorem matrix_hac_reduction {N : ℕ} (z : Assignment N) (M : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (c : ℝ)
    (h₁ : 1 ≤ nTreated z) (h₀ : 1 ≤ nControl z) :
    let X := binaryDesign z
    let H := (X.transpose * X)⁻¹
    (∀ i, (H * X.transpose) 1 i = contrastWeight z i) ∧
    (∀ i, olsResidual z M i = groupResidual z M i) ∧
    (H * olsMeat z M D c * H) 1 1 = hac (regressionScore z M) D c := by
  have h := binary_regression_weights_residuals z M h₁ h₀
  let X := binaryDesign z
  let H := (X.transpose * X)⁻¹
  have hsym : H.transpose = H := by
    simp only [H, Matrix.transpose_nonsing_inv, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  have hsym' (a b : Fin 2) : H a b = H b a :=
    congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A b a) hsym
  have hrow (i : Fin N) : (H.mulVec (X i)) 1 = contrastWeight z i := by
    simpa only [Matrix.mul_apply, Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply]
      using h.1 i
  have hcol (j : Fin N) : (Matrix.vecMul (X j) H) 1 = contrastWeight z j := by
    change (∑ b, X j b * H b 1) = contrastWeight z j
    calc
      _ = ∑ b, H 1 b * X j b := Finset.sum_congr rfl
        (fun b _ => by rw [hsym' b 1, mul_comm])
      _ = _ := hrow j
  have hmeat : olsMeat z M D c = ∑ i : Fin N, ∑ j : Fin N,
      ((if D i j ≤ c then (1 : ℝ) else 0) * olsResidual z M i * olsResidual z M j) •
        Matrix.vecMulVec (X i) (X j) := by
    ext a b
    simp only [olsMeat, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.vecMulVec_apply, X]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  refine ⟨h.1, h.2, ?_⟩
  change (H * olsMeat z M D c * H) 1 1 = _
  rw [hmeat]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, hrow, hcol, h.2,
    hac, regressionScore]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- T6(a), the coefficient-weighted Hajek contrast equals the displayed estimator. -/
theorem hajek_weighted_contrast {N : ℕ} (z : Assignment N) (M : Fin N → ℝ) :
    hajek (fun i _ => M i) z = ∑ i, contrastWeight z i * M i := by
  simp only [hajek, contrastWeight, sub_mul, div_mul_eq_mul_div,
    Finset.sum_sub_distrib, Finset.sum_div, sub_div]

/-- T6(a): when every distinct node pair is outside the cutoff, the HAC
variance is precisely HC0, the sum of squared residual scores. -/
theorem hac_equals_hc0 {N : ℕ} (g : Fin N → ℝ) (D : Fin N → Fin N → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hdiag : ∀ i, D i i = 0)
    (hsep : ∀ i j, i ≠ j → c < D i j) :
    hac g D c = ∑ i, (g i) ^ 2 := by
  have hk : ∀ i j, (if D i j ≤ c then (1 : ℝ) else 0) =
      if i = j then 1 else 0 := by
    intro i j
    by_cases h : i = j
    · subst j
      simp [hdiag i, hc]
    · simp [h, not_le.mpr (hsep i j h)]
  unfold hac
  simp_rw [hk, mul_ite]
  simp [pow_two]

/-- T6(a), full HC0 identity: the scalar HAC splits into treated and control
residual-square sums, and equals its zero-cutoff value. -/
theorem hac_group_hc0 {N : ℕ} (z : Assignment N) (M : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h₁ : 1 ≤ nTreated z) (h₀ : 1 ≤ nControl z)
    (hdiag : ∀ i, D i i = 0) (hsep : ∀ i j, i ≠ j → c < D i j) :
    hac (regressionScore z M) D c =
      (∑ i ∈ Finset.univ.filter (fun i => z i = true), (groupResidual z M i) ^ 2) /
        (nTreated z) ^ 2 +
      (∑ i ∈ Finset.univ.filter (fun i => z i = false), (groupResidual z M i) ^ 2) /
        (nControl z) ^ 2 ∧
    hac (regressionScore z M) D c = hac (regressionScore z M) D 0 := by
  classical
  have hs (i : Fin N) : (regressionScore z M i) ^ 2 =
      if z i = true then (groupResidual z M i) ^ 2 / (nTreated z) ^ 2
      else (groupResidual z M i) ^ 2 / (nControl z) ^ 2 := by
    cases hz : z i <;> simp [regressionScore, contrastWeight, bit, hz, div_pow, mul_pow, div_eq_mul_inv, mul_comm]
  have hsum : (∑ i, (regressionScore z M i) ^ 2) =
      (∑ i ∈ Finset.univ.filter (fun i => z i = true), (groupResidual z M i) ^ 2) /
        (nTreated z) ^ 2 +
      (∑ i ∈ Finset.univ.filter (fun i => z i = false), (groupResidual z M i) ^ 2) /
        (nControl z) ^ 2 := by
    simp_rw [hs]
    rw [Finset.sum_ite]
    simp only [Bool.not_eq_true, Finset.sum_div]
  have he := hac_equals_hc0 (regressionScore z M) D c hc hdiag hsep
  refine ⟨he.trans hsum, ?_⟩
  rw [he, hac_equals_hc0 (regressionScore z M) D 0 le_rfl hdiag
    (fun i j hne => hc.trans_lt (hsep i j hne))]

/-- T10(b): when every pair is included the uniform-kernel quadratic form
is the square of the score sum, so it is zero when the normal equations hold. -/
theorem hac_all_pairs_zero {N : ℕ} (g : Fin N → ℝ) (D : Fin N → Fin N → ℝ)
    (c : ℝ) (hall : ∀ i j, D i j ≤ c) (hscore : ∑ i, g i = 0) :
    hac g D c = 0 := by
  unfold hac
  simp_rw [if_pos (hall _ _), mul_one]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hscore]
  norm_num

/-- The bandwidth rule modeled in T9: for positive cutoff, add the
one-based grid position. The rule is an input from the archived code;
this definition does not verify the behavior of a package release. -/
def archivedVariance {N : ℕ} (g : Fin N → ℝ) (D : Fin N → Fin N → ℝ)
    (cutoff : ℝ) (position : ℕ) : ℝ :=
  hac g D (if 0 < cutoff then cutoff + position else cutoff)

/-- The corrected physical bandwidth formula, T10(a): retain cutoff at
every index. The grid position is an argument only to express invariance. -/
def physicalVariance {N : ℕ} (g : Fin N → ℝ) (D : Fin N → Fin N → ℝ)
    (cutoff : ℝ) (_position : ℕ) : ℝ := hac g D cutoff

/-- T10(a): with the repaired bandwidth the variance at a fixed radius
is identical on all grids, being a function only of scores, distances and cutoff. -/
theorem corrected_bandwidth_invariant {N : ℕ} (g : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (c : ℝ) (j k : ℕ) :
    physicalVariance g D c j = hac g D c ∧
    physicalVariance g D c j = physicalVariance g D c k := ⟨rfl, rfl⟩

/-- Node distances in the exact bandwidth example (T9): 0,2,4,6. -/
def bandwidthExampleDistance (i j : Fin 4) : ℝ := |2 * (i : ℝ) - 2 * (j : ℝ)|

/-- T9(i,ii), T10(a): the same radius and outcomes give variances 1 and
1/2 under positions 1 and 2; retaining physical cutoff gives 1 at both. -/
theorem grid_position_counterexample :
    (∀ i, regressionScore ![false, false, true, true] ![0, 2, 4, 6] i =
      (![1 / 2, -1 / 2, -1 / 2, 1 / 2] : Fin 4 → ℝ) i) ∧
    hajek (fun i _ => (![0, 2, 4, 6] : Fin 4 → ℝ) i)
      ![false, false, true, true] = 4 ∧
    archivedVariance ![1 / 2, -1 / 2, -1 / 2, 1 / 2] bandwidthExampleDistance
      (2 / 5) 1 = 1 ∧
    archivedVariance ![1 / 2, -1 / 2, -1 / 2, 1 / 2] bandwidthExampleDistance
      (2 / 5) 2 = 1 / 2 ∧
    physicalVariance ![1 / 2, -1 / 2, -1 / 2, 1 / 2] bandwidthExampleDistance
      (2 / 5) 1 = 1 ∧
    physicalVariance ![1 / 2, -1 / 2, -1 / 2, 1 / 2] bandwidthExampleDistance
      (2 / 5) 2 = 1 := by
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, regressionScore, contrastWeight, groupResidual,
      groupMean, nTreated, nControl, bit, Fin.sum_univ_succ]
  · norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, hajek, nTreated, nControl, bit, archivedVariance, physicalVariance,
      hac, bandwidthExampleDistance, Fin.sum_univ_succ]

/-- T9(iii): squared distances at most 32 are all covered by the implemented
sixth-position threshold 32/5. Normal equations force width zero, whereas
the printed sixth toy interval has strictly positive width 869/250. -/
theorem archived_sixth_row_incompatible {N : ℕ} (g : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (hD : ∀ i j, (D i j) ^ 2 ≤ 32)
    (hscore : ∑ i, g i = 0) :
    archivedVariance g D (2 / 5) 6 = 0 ∧
    (3438 / 1000 - (-38 / 1000) : ℝ) = 869 / 250 ∧ (0 : ℝ) < 869 / 250 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  have hall : ∀ i j, D i j ≤ 32 / 5 := by
    intro i j
    nlinarith [hD i j, sq_nonneg (D i j - 32 / 5)]
  norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, archivedVariance]
  exact hac_all_pairs_zero g D _ hall hscore

/-- T6(b), exact dyadic toy coordinates,
not asserted as exact coordinates printed in Fig. 2. -/
def toyNode (i : Fin 4) : Plane :=
  WithLp.toLp 2 ((![![2028297641 / 2147483648, 4318520789 / 2147483648],
    ![7976664621 / 2147483648, 1029755657 / 268435456],
    ![1053580245 / 536870912, 2017196647 / 2147483648],
    ![7110225301 / 2147483648, 499145583 / 1073741824]] : Fin 4 → Fin 2 → ℝ) i)

/-- T6(b), T10(c): every distinct reconstructed toy node distance exceeds
0.4, so HAC(.4) is HC0 for every possible score vector at every radius. -/
theorem toy_cutoff_is_hc0 (g : Fin 4 → ℝ) :
    (∀ i j : Fin 4, i ≠ j → (2 / 5 : ℝ) < dist (toyNode i) (toyNode j)) ∧
    hac g (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) = ∑ i, (g i) ^ 2 := by
  have hsep : ∀ i j : Fin 4, i ≠ j → (2 / 5 : ℝ) < dist (toyNode i) (toyNode j) := by
    intro i j hne
    have hsq : (2 / 5 : ℝ) ^ 2 < dist (toyNode i) (toyNode j) ^ 2 := by
      rw [EuclideanSpace.dist_sq_eq]
      fin_cases i <;> fin_cases j <;>
        norm_num at hne <;>
        norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, toyNode, Fin.sum_univ_succ, Real.dist_eq, WithLp.toLp]
    nlinarith [dist_nonneg (x := toyNode i) (y := toyNode j)]
  exact ⟨hsep, hac_equals_hc0 g _ _ (by norm_num) (fun _ => dist_self _) hsep⟩

/-- T5's four independent Bernoulli(1/2) assignments of two nodes. -/
def pairAssignment (k : Fin 4) : Assignment 2 :=
  ![![false, false], ![false, true], ![true, false], ![true, true]] k

/-- The enumeration is a bijection onto the binary square, establishing the
independent Bernoulli(1/2) design of T5. -/
theorem pair_support : Function.Bijective pairAssignment := by decide

/-- T5's field includes both nodes and all three outcome points; the
x-axis coordinates embed isometrically in the plane. -/
def pairField : Finset ℚ := {-1, 0, 1, 2, 3}

/-- T5's node coordinates are (0,0), (2,0). -/
def pairNode : Fin 2 → ℚ := ![0, 2]

/-- T5's potential outcomes: each treated node adds 1 at outcome points
within Euclidean distance 1, with zero effect beyond that range. -/
def pairOutcome (x : ℚ) (z : Assignment 2) : ℝ :=
  (if |x| ≤ 1 then bit (z 0) else 0) +
    (if |x - 2| ≤ 1 then bit (z 1) else 0)

/-- Linearization contribution “φ_i = 2 Z_i(μ_i-m_1) -
2(1-Z_i)(μ_i-m_0)”, T5/T6(c); these are not the finite ratio estimator. -/
def linearizationScore {N : ℕ} (M : Fin N → Assignment N → ℝ)
    (m₁ m₀ : ℝ) (i : Fin N) (z : Assignment N) : ℝ :=
  2 * bit (z i) * (M i z - m₁) -
    2 * (1 - bit (z i)) * (M i z - m₀)

/-- The actual two-node radius-1 circle averages in T5. -/
def pairM (i : Fin 2) (z : Assignment 2) : ℝ :=
  lineM pairField pairNode pairOutcome i 1 z

/-- T5 geometric/counting calculation: nodes are in the field; the two
radius-1 circles are {-1,1} and {1,3}, with the claimed outcome averages. -/
theorem pair_circle_calculation :
    (∀ i, pairNode i ∈ pairField) ∧
    lineCircle pairField pairNode 0 1 = {-1, 1} ∧
    lineCircle pairField pairNode 1 1 = {1, 3} ∧
    (∀ z, pairM 0 z = bit (z 0) + bit (z 1) / 2 ∧
      pairM 1 z = bit (z 1) + bit (z 0) / 2) := by
  refine ⟨?_, by norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, lineCircle, pairField, pairNode],
    by norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, lineCircle, pairField, pairNode], ?_⟩
  · intro i
    fin_cases i <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, pairNode, pairField]
  · intro z
    norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, pairM, lineM, lineCircle, pairField, pairNode, countMean, pairOutcome]
    constructor <;> ring

/-- T5 exact counterexample: each marginalized treated/control average is
5/4 and 1/4; AMR is 1; both scores have variance and covariance 1/4.
Including only diagonal node pairs gives 1/8, half the true linearization
variance 1/4. All four assignments and both nodes are explicitly represented. -/
theorem effect_range_cutoff_counterexample :
    (∀ i : Fin 2,
      (uniformLaw (Fin 4)).expect (fun k => pairM i
        (Function.update (pairAssignment k) i true)) = 5 / 4 ∧
      (uniformLaw (Fin 4)).expect (fun k => pairM i
        (Function.update (pairAssignment k) i false)) = 1 / 4) ∧
    (∀ i k, linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k) =
      (1 / 2 : ℝ) * (2 * bit (pairAssignment k 0) - 1) *
        (2 * bit (pairAssignment k 1) - 1)) ∧
    (uniformLaw (Fin 4)).var (fun k => linearizationScore pairM (5 / 4) (1 / 4) 0
      (pairAssignment k)) = 1 / 4 ∧
    (uniformLaw (Fin 4)).cov
      (fun k => linearizationScore pairM (5 / 4) (1 / 4) 0 (pairAssignment k))
      (fun k => linearizationScore pairM (5 / 4) (1 / 4) 1 (pairAssignment k)) = 1 / 4 ∧
    (uniformLaw (Fin 4)).var (fun k =>
      (linearizationScore pairM (5 / 4) (1 / 4) 0 (pairAssignment k) +
        linearizationScore pairM (5 / 4) (1 / 4) 1 (pairAssignment k)) / 2) = 1 / 4 ∧
    ((1 / 4 + 1 / 4) / 4 : ℝ) = 1 / 8 ∧ (1 / 8 : ℝ) < 1 / 4 := by
  have hm (i : Fin 2) (z : Assignment 2) : pairM i z =
      (![bit (z 0) + bit (z 1) / 2, bit (z 1) + bit (z 0) / 2] : Fin 2 → ℝ) i := by
    fin_cases i
    · exact (pair_circle_calculation.2.2.2 z).1
    · exact (pair_circle_calculation.2.2.2 z).2
  simp_rw [linearizationScore, hm]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, FiniteLaw.expect, uniformLaw, pairAssignment, bit,
      Fin.sum_univ_succ, Function.update_apply]
  · intro i k
    fin_cases i <;> fin_cases k <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, linearizationScore, hm,
      pairAssignment, bit]
  · norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, FiniteLaw.var, FiniteLaw.cov, FiniteLaw.expect, uniformLaw,
      linearizationScore, hm, pairAssignment, bit, Fin.sum_univ_succ]

/- Binary-risk normalization counterexample (T7). -/

/-- The 40000 counting-measure circle-point indices used in T7. -/
abbrev RiskCell := Fin 40000

/-- T7's heterogeneous baseline counts: 400,1000,400,1000. -/
def riskBaseline : Fin 4 → ℕ := ![400, 1000, 400, 1000]

/-- Complete binary potential-outcome rule on each node/radius circle:
Y=1{k<B_i-321 z_i}, with zero-based k. -/
def riskOutcome (i : Fin 4) (_radius : Fin 4) (k : RiskCell) (z : Assignment 4) : ℝ :=
  if k.val < riskBaseline i - 321 * (if z i then 1 else 0) then 1 else 0

/-- Counting-measure circle outcomes in the exact T7 construction. -/
def riskM (i : Fin 4) (j : Fin 4) (z : Assignment 4) : ℝ :=
  countMean Finset.univ (fun k => riskOutcome i j k z)

/-- Counting identity for binary outcomes on a circle of M points. -/
theorem binary_count_mean (M K : ℕ) (hK : K ≤ M) :
    countMean (Finset.univ : Finset (Fin M))
      (fun k => if k.val < K then (1 : ℝ) else 0) = (K : ℝ) / M := by
  unfold countMean
  rw [← Finset.sum_filter]
  simp [Fin.card_filter_val_lt, Nat.min_eq_right hK]

/-- T7(4): explicit circle averages and binary range for every potential
outcome, every assignment, every circle point, and every node and radius. -/
theorem risk_circle_calculation :
    (∀ i j k z, riskOutcome i j k z = 0 ∨ riskOutcome i j k z = 1) ∧
    (∀ i j z, riskM i j z = ((riskBaseline i : ℝ) - 321 * bit (z i)) / 40000) := by
  constructor
  · intro i j k z
    unfold riskOutcome
    split_ifs <;> simp
  · intro i j z
    unfold riskM riskOutcome
    have hk : riskBaseline i - 321 * (if z i then 1 else 0) ≤ 40000 := by
      cases hz : z i <;> fin_cases i <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, riskBaseline, hz]
    rw [binary_count_mean 40000 _ hk]
    cases hz : z i <;> fin_cases i <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, riskBaseline, bit, hz]

/-- T7(4–7): for every design the AMR at each of the four radii is
-321/40000. At attainable assignment 1100 each Hajek estimate is the same;
their sum is -.0321, whereas the normalized probability change is -.008025.
The companion binary model has sum -4, impossible for any probability difference. -/
theorem summed_risk_counterexample (Q : FiniteLaw (Assignment 4)) :
    (∀ i j b, marginal Q (riskM i j) i b =
      ((riskBaseline i : ℝ) - 321 * bit b) / 40000) ∧
    (∀ j, (1 / 4 : ℝ) * ∑ i,
      (marginal Q (riskM i j) i true - marginal Q (riskM i j) i false) = -321 / 40000) ∧
    (∀ j, hajek (fun i z => riskM i j z) ![true, true, false, false] = -321 / 40000) ∧
    (∑ _j : Fin 4, (-321 / 40000 : ℝ)) = -321 / 10000 ∧
    (379 / 40000 - 7 / 400 : ℝ) = -321 / 40000 ∧
    (7 / 400 - 321 / 10000 : ℝ) = -73 / 5000 ∧
    (-73 / 5000 : ℝ) < 0 ∧
    (∑ _j : Fin 4, (-1 : ℝ)) = -4 ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → a - b ≠ -4) := by
  have hm (i j : Fin 4) (b : Bool) : marginal Q (riskM i j) i b =
      ((riskBaseline i : ℝ) - 321 * bit b) / 40000 := by
    unfold marginal
    have he : (fun z => riskM i j (Function.update z i b)) =
        (fun _ => ((riskBaseline i : ℝ) - 321 * bit b) / 40000) := by
      funext z
      rw [risk_circle_calculation.2]
      simp
    rw [he, expect_const]
  refine ⟨hm, ?_, ?_, ?_⟩
  · intro j
    simp_rw [hm]
    norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, bit, riskBaseline, Fin.sum_univ_succ]
  · intro j
    simp_rw [hajek, risk_circle_calculation.2]
    norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, nTreated, nControl, riskBaseline, bit, Fin.sum_univ_succ]
  · norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, Fin.sum_univ_succ]
    intro a b ha ha' hb hb'
    linarith

/- Finite randomization laws and conditional tests. -/

/-- Uniform finite-support mass for the two design laws of T1(A).
Assignments are their sets of treated positions (0-based). -/
def supportMass (S : Finset (Finset ℕ)) (z : Finset ℕ) : ℝ :=
  if z ∈ S then (S.card : ℝ)⁻¹ else 0

/-- T1(A) unrestricted 60-of-121 support. -/
def unrestricted121 : Finset (Finset ℕ) := (Finset.range 121).powersetCard 60

/-- T1(A) blocked support: 5 of positions 0–9 and 55 of positions 10–120. -/
def blocked121 : Finset (Finset ℕ) :=
  (((Finset.range 10).powersetCard 5).product
    ((Finset.Ico 10 121).powersetCard 55)).image (fun ab => ab.1 ∪ ab.2)

/-- The observed 121-node assignment and its single within-count swap,
exactly the labelled example of T1(A). -/
def observed121 : Finset ℕ := Finset.range 5 ∪ Finset.Ico 10 65

/-- Swap position 6 into treatment and position 11 out (1-based labels). -/
def alternative121 : Finset ℕ := insert 5 (observed121.erase 10)

/-- T1(A), p. 153 correction: the observed vector/count do not identify
the law. Both uniform laws normalize, but their supports and a positive-mass
assignment differ; the cardinalities are the stated binomial coefficients. -/
theorem observed_count_does_not_identify_law :
    unrestricted121.card = Nat.choose 121 60 ∧
    blocked121.card = Nat.choose 10 5 * Nat.choose 111 55 ∧
    blocked121 ⊂ unrestricted121 ∧
    observed121 ∈ unrestricted121 ∧ observed121 ∈ blocked121 ∧
    alternative121 ∈ unrestricted121 ∧ alternative121 ∉ blocked121 ∧
    0 < supportMass unrestricted121 observed121 ∧
    0 < supportMass blocked121 observed121 ∧
    0 < supportMass unrestricted121 alternative121 ∧
    supportMass blocked121 alternative121 = 0 ∧
    (∑ z ∈ unrestricted121, supportMass unrestricted121 z) = 1 ∧
    (∑ z ∈ blocked121, supportMass blocked121 z) = 1 := by
  let L := (Finset.range 10).powersetCard 5
  let R := (Finset.Ico 10 121).powersetCard 55
  have hsplit (ab : Finset ℕ × Finset ℕ) (hab : ab ∈ L.product R) :
      (ab.1 ∪ ab.2).filter (fun n => n < 10) = ab.1 ∧
      (ab.1 ∪ ab.2).filter (fun n => 10 ≤ n) = ab.2 := by
    have hA := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hab).1).1
    have hB := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hab).2).1
    constructor
    · ext n
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨ha | hb, hn⟩
        · exact ha
        · have := (Finset.mem_Ico.mp (hB hb)).1
          omega
      · intro ha
        exact ⟨Or.inl ha, Finset.mem_range.mp (hA ha)⟩
    · ext n
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨ha | hb, hn⟩
        · have := Finset.mem_range.mp (hA ha)
          omega
        · exact hb
      · intro hb
        exact ⟨Or.inr hb, (Finset.mem_Ico.mp (hB hb)).1⟩
  have hinj : Set.InjOn (fun ab : Finset ℕ × Finset ℕ => ab.1 ∪ ab.2)
      (↑(L.product R) : Set (Finset ℕ × Finset ℕ)) := by
    intro ab hab cd hcd he
    apply Prod.ext
    · have hh := congrArg (fun t : Finset ℕ => t.filter (fun n => n < 10)) he
      simpa only [(hsplit ab hab).1, (hsplit cd hcd).1] using hh
    · have hh := congrArg (fun t : Finset ℕ => t.filter (fun n => 10 ≤ n)) he
      simpa only [(hsplit ab hab).2, (hsplit cd hcd).2] using hh
  have hcardU : unrestricted121.card = Nat.choose 121 60 := by
    simp only [unrestricted121, Finset.card_powersetCard, Finset.card_range]
  have hcardB : blocked121.card = Nat.choose 10 5 * Nat.choose 111 55 := by
    change ((L.product R).image (fun ab => ab.1 ∪ ab.2)).card = _
    rw [Finset.card_image_of_injOn hinj]
    change (L ×ˢ R).card = _
    rw [Finset.card_product]
    simp only [L, R, Finset.card_powersetCard, Finset.card_range, Nat.card_Ico]
  have hsub : blocked121 ⊆ unrestricted121 := by
    intro z hz
    obtain ⟨ab, hab, rfl⟩ := Finset.mem_image.mp hz
    have ha := Finset.mem_powersetCard.mp (Finset.mem_product.mp hab).1
    have hb := Finset.mem_powersetCard.mp (Finset.mem_product.mp hab).2
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro n hn
      rcases Finset.mem_union.mp hn with hn | hn
      · have := Finset.mem_range.mp (ha.1 hn)
        apply Finset.mem_range.mpr
        omega
      · exact Finset.mem_range.mpr (Finset.mem_Ico.mp (hb.1 hn)).2
    · have hd : Disjoint ab.1 ab.2 := by
        apply Finset.disjoint_left.mpr
        intro n hn hn'
        have := Finset.mem_range.mp (ha.1 hn)
        have := (Finset.mem_Ico.mp (hb.1 hn')).1
        omega
      rw [Finset.card_union_of_disjoint hd, ha.2, hb.2]
  have hobsB : observed121 ∈ blocked121 := by
    apply Finset.mem_image.mpr
    refine ⟨(Finset.range 5, Finset.Ico 10 65), ?_, rfl⟩
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_powersetCard.mpr
      exact ⟨by intro n hn; apply Finset.mem_range.mpr; have := Finset.mem_range.mp hn; omega,
        by simp⟩
    · apply Finset.mem_powersetCard.mpr
      exact ⟨by intro n hn; apply Finset.mem_Ico.mpr; have := Finset.mem_Ico.mp hn; omega,
        by norm_num⟩
  have hobsU := hsub hobsB
  have haltU : alternative121 ∈ unrestricted121 := by
    apply Finset.mem_powersetCard.mpr
    constructor <;> decide
  have haltB : alternative121 ∉ blocked121 := by
    intro h
    obtain ⟨ab, hab, he⟩ := Finset.mem_image.mp h
    have hh : (alternative121.filter (fun n => n < 10)).card = 6 := by decide
    rw [← he, (hsplit ab hab).1] at hh
    have hc := (Finset.mem_powersetCard.mp (Finset.mem_product.mp hab).1).2
    omega
  have hstrict : blocked121 ⊂ unrestricted121 := by
    exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro he
      rw [he] at haltB
      exact haltB haltU⟩
  have hposU : 0 < (unrestricted121.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨observed121, hobsU⟩
  have hposB : 0 < (blocked121.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨observed121, hobsB⟩
  have hnorm (S : Finset (Finset ℕ)) (hS : 0 < (S.card : ℝ)) :
      (∑ z ∈ S, supportMass S z) = 1 := by
    calc
      _ = ∑ _z ∈ S, (S.card : ℝ)⁻¹ :=
        Finset.sum_congr rfl (fun z hz => if_pos hz)
      _ = 1 := by simp [nsmul_eq_mul, ne_of_gt hS]
  refine ⟨hcardU, hcardB, hstrict, hobsU, hobsB, haltU, haltB, ?_, ?_, ?_, ?_,
    hnorm _ hposU, hnorm _ hposB⟩
  · simpa only [supportMass, if_pos hobsU] using inv_pos.mpr hposU
  · simpa only [supportMass, if_pos hobsB] using inv_pos.mpr hposB
  · simpa only [supportMass, if_pos haltU] using inv_pos.mpr hposU
  · simp only [supportMass, if_neg haltB]

/-- Conditioning a finite design on an event of positive probability, T2(a). -/
def conditionalLaw {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (A : Ω → Prop)
    (hA : 0 < Q.prob A) : FiniteLaw Ω := by
  classical
  exact {
  mass z := if A z then Q.mass z / Q.prob A else 0
  nonneg z := by
    classical
    split_ifs
    · exact div_nonneg (Q.nonneg z) hA.le
    · exact le_rfl
  total := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_div]
    change Q.prob A / Q.prob A = 1
    exact div_self (ne_of_gt hA) }

/-- T2(a) conditional validity follows under the actual conditional design
law, with no uniformity, independence or equal-probability restriction. -/
theorem conditional_tail_valid {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (A : Ω → Prop) (hA : 0 < Q.prob A) (T : Ω → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    (conditionalLaw Q A hA).prob
      (fun z => tailP (conditionalLaw Q A hA) T z ≤ δ) ≤ δ :=
  design_tail_valid _ T δ hδ hδ'

/-- Common independent Bernoulli assignment, spelled out as its joint
product mass; the probability-space axioms are already carried by Q. -/
def commonBernoulli {N : ℕ} (Q : FiniteLaw (Assignment N)) (p : ℝ) : Prop :=
  ∀ z, Q.mass z = ∏ i, if z i then p else 1 - p

/-- T2(b), exact conditional mass under common independent Bernoulli(p):
every assignment with M treated has mass 1/choose(N,M), including M=0,N.
The count event has positive probability; complete randomization is this
same uniform law by its definition. -/
theorem bernoulli_given_count_uniform {N : ℕ} (Q : FiniteLaw (Assignment N))
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hQ : commonBernoulli Q p)
    (M : ℕ) (hM : M ≤ N) :
    0 < Q.prob (fun z => treatedCount z = M) ∧
    (∀ z, treatedCount z = M →
      Q.mass z / Q.prob (fun w => treatedCount w = M) =
        (Nat.choose N M : ℝ)⁻¹) := by
  classical
  let e : Assignment N ≃ Finset (Fin N) := {
    toFun z := Finset.univ.filter (fun i => z i = true)
    invFun S i := decide (i ∈ S)
    left_inv z := by
      funext i
      cases hz : z i <;> simp [hz]
    right_inv S := by
      ext i
      simp }
  let A := Finset.univ.filter (fun z : Assignment N => treatedCount z = M)
  have hecard (z : Assignment N) : (e z).card = treatedCount z := by
    simp [e, treatedCount]
  have hcard : A.card = Nat.choose N M := by
    calc
      A.card = ((Finset.univ : Finset (Finset (Fin N))).filter
          (fun S => S.card = M)).card := by
        apply Finset.card_bijective e e.bijective
        intro z
        simp [A, hecard]
      _ = Nat.choose N M := by
        simp only [Finset.univ_filter_card_eq, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin]
  let c := p ^ M * (1 - p) ^ (N - M)
  have hc : 0 < c := mul_pos (pow_pos hp _) (pow_pos (sub_pos.mpr hp') _)
  have hmass (z : Assignment N) (hz : treatedCount z = M) : Q.mass z = c := by
    have ht : (Finset.univ.filter (fun i => z i = true)).card = M := by
      simpa [treatedCount] using hz
    have hf : (Finset.univ.filter (fun i => ¬ z i = true)).card = N - M := by
      have hsum := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (fun i : Fin N => z i = true)
      simp only [Finset.card_univ, Fintype.card_fin, ht] at hsum
      omega
    rw [hQ z, Finset.prod_ite]
    simp only [Finset.prod_const, ht, hf]
    rfl
  have hprob : Q.prob (fun z => treatedCount z = M) = (Nat.choose N M : ℝ) * c := by
    unfold FiniteLaw.prob
    calc
      _ = ∑ z ∈ A, Q.mass z := by
        apply Finset.sum_congr
        · ext z
          simp only [A, Finset.mem_filter]
        · intro z _
          rfl
      _ = ∑ _z ∈ A, c := Finset.sum_congr rfl
        (fun z hz => hmass z (Finset.mem_filter.mp hz).2)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  have hchoose : 0 < (Nat.choose N M : ℝ) := by
    exact_mod_cast Nat.choose_pos hM
  refine ⟨by rw [hprob]; exact mul_pos hchoose hc, ?_⟩
  intro z hz
  rw [hmass z hz, hprob]
  field_simp


/-- Event probabilities are expectations of indicators. -/
theorem prob_as_expect {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (P : Ω → Prop) [DecidablePred P] : Q.prob P = Q.expect (fun z => if P z then 1 else 0) := by
  classical
  simp only [FiniteLaw.prob, FiniteLaw.expect, mul_ite, mul_one, mul_zero,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> rfl

/-- Relabeling a finite probability space by a mass-preserving bijection
preserves every event probability. -/
theorem prob_equiv {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (e : Ω ≃ Ω)
    (hm : ∀ z, Q.mass (e z) = Q.mass z) (P : Ω → Prop) :
    Q.prob (fun z => P (e z)) = Q.prob P := by
  classical
  simp only [FiniteLaw.prob, Finset.sum_filter]
  exact Fintype.sum_equiv e _ _ (fun z => by rw [hm z])

/-- T4(d), finite IID Monte Carlo correction: the observed statistic and B
independent design draws share product mass, and the plus-one inclusive
rank is superuniform. This is stated for an arbitrary finite design Q. -/
theorem monte_carlo_rank_valid {Ω : Type*} [Fintype Ω]
    (Q : FiniteLaw Ω) (B : ℕ) (R : FiniteLaw (Fin (B + 1) → Ω))
    (hIID : ∀ z, R.mass z = ∏ k, Q.mass (z k)) (S : Ω → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    R.prob (fun z =>
      (1 + ((Finset.univ.filter (fun b : Fin B =>
        |S (z 0)| ≤ |S (z b.succ)|)).card : ℝ)) / (B + 1) ≤ δ) ≤ δ := by
  classical
  let U := uniformLaw (Fin (B + 1))
  let p (z : Fin (B + 1) → Ω) (k : Fin (B + 1)) := tailP U (fun j => S (z j)) k
  have hp (z : Fin (B + 1) → Ω) (k : Fin (B + 1)) :
      p z k = ((Finset.univ.filter (fun j => |S (z k)| ≤ |S (z j)|)).card : ℝ) /
        (B + 1) := by
    simp [p, tailP, U, FiniteLaw.prob, uniformLaw, nsmul_eq_mul, div_eq_mul_inv]
  have hzero (z : Fin (B + 1) → Ω) : p z 0 =
      (1 + ((Finset.univ.filter (fun b : Fin B =>
        |S (z 0)| ≤ |S (z b.succ)|)).card : ℝ)) / (B + 1) := by
    rw [hp]
    congr 1
    have hcount : ((Finset.univ.filter (fun j : Fin (B + 1) =>
        |S (z 0)| ≤ |S (z j)|)).card : ℝ) =
        1 + ((Finset.univ.filter (fun b : Fin B =>
        |S (z 0)| ≤ |S (z b.succ)|)).card : ℝ) := by
      rw [← Finset.sum_boole, ← Finset.sum_boole]
      rw [Fin.sum_univ_succ]
      simp only [le_refl, ite_true]
    exact hcount
  have hsym (k : Fin (B + 1)) :
      R.prob (fun z => p z 0 ≤ δ) = R.prob (fun z => p z k ≤ δ) := by
    let e := Equiv.swap (0 : Fin (B + 1)) k
    let E := e.arrowCongr (Equiv.refl Ω)
    have hm (z : Fin (B + 1) → Ω) : R.mass (E z) = R.mass z := by
      rw [hIID, hIID]
      exact Fintype.prod_equiv e.symm _ _ (fun j => rfl)
    have hrank (z : Fin (B + 1) → Ω) : p (E z) 0 = p z k := by
      rw [hp, hp]
      congr 2
      apply Finset.card_bijective e.symm e.symm.bijective
      intro j
      simp [E, Equiv.arrowCongr, e]
    calc
      _ = R.prob (fun z => p (E z) 0 ≤ δ) := (prob_equiv R E hm _).symm
      _ = _ := by simp_rw [hrank]
  have hpoint (z : Fin (B + 1) → Ω) :
      (∑ k : Fin (B + 1), if p z k ≤ δ then (1 : ℝ) else 0) ≤ (B + 1) * δ := by
    have ht := design_tail_valid U (fun k => S (z k)) δ hδ hδ'
    rw [prob_as_expect] at ht
    change (∑ k : Fin (B + 1), U.mass k *
      (if p z k ≤ δ then (1 : ℝ) else 0)) ≤ δ at ht
    have ht' : (∑ k : Fin (B + 1), if p z k ≤ δ then (1 : ℝ) else 0) /
        (B + 1) ≤ δ := by
      simpa only [U, uniformLaw, Fintype.card_fin, Nat.cast_add, Nat.cast_one,
        ← Finset.mul_sum, div_eq_mul_inv, mul_comm] using ht
    have hn : (0 : ℝ) < B + 1 := by positivity
    simpa only [mul_comm] using (div_le_iff₀ hn).mp ht'
  have havg : (B + 1 : ℝ) * R.prob (fun z => p z 0 ≤ δ) ≤ (B + 1) * δ := by
    calc
      _ = ∑ k : Fin (B + 1), R.prob (fun z => p z k ≤ δ) := by
        simp_rw [← hsym]
        simp
      _ = ∑ z, R.mass z * (∑ k : Fin (B + 1), if p z k ≤ δ then 1 else 0) := by
        simp_rw [prob_as_expect, FiniteLaw.expect, Finset.mul_sum]
        exact Finset.sum_comm
      _ ≤ ∑ z, R.mass z * ((B + 1) * δ) := Finset.sum_le_sum
        (fun z _ => mul_le_mul_of_nonneg_left (hpoint z) (R.nonneg z))
      _ = _ := by rw [← Finset.sum_mul, R.total, one_mul]
  have hn : (0 : ℝ) < B + 1 := by positivity
  simpa only [hzero] using (mul_le_mul_iff_right₀ hn).mp havg


/-- Averaging one independent fair bit leaves a cube expectation unchanged. -/
theorem uniform_average_update {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → ℝ) (i : I) :
    (uniformLaw (I → Bool)).expect f =
      (uniformLaw (I → Bool)).expect (fun z =>
        (f (Function.update z i false) + f (Function.update z i true)) / 2) := by
  classical
  let e := Equiv.funSplitAt i Bool
  have hupdate (u : Bool × ({j : I // j ≠ i} → Bool)) (b : Bool) :
      Function.update (e.symm u) i b = e.symm (b, u.2) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, Function.update_of_ne hj, hj]
  have hsum (g : (I → Bool) → ℝ) :
      (∑ z, g z) = ∑ u : Bool × ({j : I // j ≠ i} → Bool), g (e.symm u) :=
    Fintype.sum_equiv e _ _ (fun z => by simp)
  unfold FiniteLaw.expect
  rw [hsum, hsum]
  simp_rw [uniformLaw, Fintype.sum_prod_type, Fintype.sum_bool, hupdate]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- Switching a single bit in an additive circle outcome. -/
theorem additive_vector_update {N : ℕ} (base : Fin N → ℝ)
    (a : Fin N → Fin N → ℝ) (i k : Fin N) (z : Assignment N) (b : Bool) :
    base i + (∑ l, a i l * bit (Function.update z k b l)) =
      base i + (∑ l, a i l * bit (z l)) + a i k * (bit b - bit (z k)) := by
  classical
  have hh : (∑ l, (a i l * bit (Function.update z k b l) - a i l * bit (z l))) =
      a i k * (bit b - bit (z k)) := by
    rw [Finset.sum_eq_single k]
    · simp [mul_sub]
    · intro l _ hl
      simp [Function.update_of_ne hl]
    · simp
  rw [Finset.sum_sub_distrib] at hh
  linarith

/-- T6(c): under the uniform binary cube, off-diagonal additive Hajek
score covariance is a_ij a_ji, independent of the centering constants. -/
theorem additive_score_covariance {N : ℕ} (base : Fin N → ℝ)
    (a : Fin N → Fin N → ℝ) (m₁ m₀ : ℝ) (i j : Fin N) (hne : i ≠ j) :
    (uniformLaw (Assignment N)).cov
      (fun z => linearizationScore (fun i z => base i + ∑ k, a i k * bit (z k)) m₁ m₀ i z)
      (fun z => linearizationScore (fun i z => base i + ∑ k, a i k * bit (z k)) m₁ m₀ j z) =
    a i j * a j i := by
  classical
  let Q := uniformLaw (Assignment N)
  let M (i : Fin N) (z : Assignment N) := base i + ∑ k, a i k * bit (z k)
  let φ (k : Fin N) (z : Assignment N) := linearizationScore M m₁ m₀ k z
  have hM (k : Fin N) (z : Assignment N) (b : Bool) :
      M k (Function.update z i b) = M k z + a k i * (bit b - bit (z i)) :=
    additive_vector_update base a k i z b
  have hM' (k : Fin N) (z : Assignment N) (b : Bool) :
      M k (Function.update z j b) = M k z + a k j * (bit b - bit (z j)) :=
    additive_vector_update base a k j z b
  have hmean (k : Fin N) : Q.expect (φ k) = a k k - m₁ + m₀ := by
    rw [uniform_average_update (φ k) k]
    have hv (z : Assignment N) :
        (φ k (Function.update z k false) + φ k (Function.update z k true)) / 2 =
          a k k - m₁ + m₀ := by
      simp only [φ, linearizationScore, Function.update_self]
      change (2 * bit false * (M k (Function.update z k false) - m₁) -
        2 * (1 - bit false) * (M k (Function.update z k false) - m₀) +
        (2 * bit true * (M k (Function.update z k true) - m₁) -
        2 * (1 - bit true) * (M k (Function.update z k true) - m₀))) / 2 = _
      simp only [M]
      rw [additive_vector_update base a k k z false,
        additive_vector_update base a k k z true]
      cases hz : z k <;> norm_num [bit, hz] <;> ring
    simp_rw [hv]
    exact expect_const Q _
  have hraw : Q.expect (fun z => φ i z * φ j z) =
      a i j * a j i + (a i i - m₁ + m₀) * (a j j - m₁ + m₀) := by
    rw [uniform_average_update (fun z => φ i z * φ j z) i,
      uniform_average_update _ j]
    have hv (z : Assignment N) :
        (((φ i (Function.update (Function.update z j false) i false) *
            φ j (Function.update (Function.update z j false) i false) +
          φ i (Function.update (Function.update z j false) i true) *
            φ j (Function.update (Function.update z j false) i true)) / 2) +
         ((φ i (Function.update (Function.update z j true) i false) *
            φ j (Function.update (Function.update z j true) i false) +
          φ i (Function.update (Function.update z j true) i true) *
            φ j (Function.update (Function.update z j true) i true)) / 2)) / 2 =
        a i j * a j i + (a i i - m₁ + m₀) * (a j j - m₁ + m₀) := by
      simp only [φ, linearizationScore, Function.update_self,
        Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne)]
      simp_rw [hM, hM']
      simp only [Function.update_of_ne hne, Function.update_of_ne (Ne.symm hne), bit, Bool.false_eq_true,
        ite_false, ite_true]
      ring
    simp_rw [hv]
    exact expect_const Q _
  unfold FiniteLaw.cov
  have he (z : Assignment N) :
      (φ i z - Q.expect (φ i)) * (φ j z - Q.expect (φ j)) =
        φ i z * φ j z - Q.expect (φ i) * φ j z -
        Q.expect (φ j) * φ i z + Q.expect (φ i) * Q.expect (φ j) := by ring
  change Q.expect (fun z => (φ i z - Q.expect (φ i)) * (φ j z - Q.expect (φ j))) = _
  simp_rw [he]
  unfold FiniteLaw.expect
  simp_rw [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hm (c : ℝ) (f : Assignment N → ℝ) :
      (∑ z, Q.mass z * (c * f z)) = c * Q.expect f := by
    unfold FiniteLaw.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hm, hm, ← Finset.sum_mul, Q.total, one_mul]
  change Q.expect (fun z => φ i z * φ j z) - Q.expect (φ i) * Q.expect (φ j) -
    Q.expect (φ j) * Q.expect (φ i) + Q.expect (φ i) * Q.expect (φ j) = _
  rw [hraw, hmean i, hmean j]
  ring

/-- T6(d), geometric support bound: a node at separation > d+r cannot
affect any point on a radius-d circle if its direct effect vanishes beyond r. -/
theorem circle_outside_effect_range (p q x : Plane) (d r : ℝ)
    (hcircle : dist p x = d) (hfar : d + r < dist p q) : r < dist q x := by
  have ht := dist_triangle p x q
  rw [hcircle, dist_comm x q] at ht
  linarith

/-- T6(d), finite counting-measure coefficient: zero beyond the geometric
bound implies its average a_ik is zero, so cutoff ≥d+r covers all mutual
additive score covariances. -/
theorem finite_far_coefficient_zero (C : Finset Plane) (p q : Plane) (d r : ℝ)
    (g : Plane → ℝ) (hcircle : ∀ x ∈ C, dist p x = d)
    (heffect : ∀ x, r < dist q x → g x = 0) (hfar : d + r < dist p q) :
    countMean C g = 0 := by
  unfold countMean
  have hz : ∑ x ∈ C, g x = 0 := Finset.sum_eq_zero
    (fun x hx => heffect x (circle_outside_effect_range p q x d r (hcircle x hx) hfar))
  rw [hz, zero_div]

/-- T17(a), full planar geometry: distance to the radius-d circle is
|dist(x,p)-d| for d>0, justifying the corrected symmetric tolerance band. -/
theorem distance_to_circle (p x : Plane) (d : ℝ) (hd : 0 < d) :
    Metric.infDist x {q : Plane | dist q p = d} = |dist x p - d| := by
  let u : Plane := WithLp.toLp 2 ![1, 0]
  have hu : ‖u‖ = 1 := by
    have hs : ‖u‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, u, Fin.sum_univ_succ]
    nlinarith [norm_nonneg u]
  have hbasic : dist (p + d • u) p = d := by
    rw [dist_eq_norm]
    simp [norm_smul, Real.norm_eq_abs, abs_of_pos hd, hu]
  obtain ⟨q, hq, hnear⟩ : ∃ q : Plane,
      dist q p = d ∧ dist x q = |dist x p - d| := by
    by_cases hxp : x = p
    · subst x
      refine ⟨p + d • u, hbasic, ?_⟩
      rw [dist_comm p, hbasic]
      simp [abs_of_pos hd]
    · let v := x - p
      let r := ‖v‖
      have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hxp)
      let q := p + (d / r) • v
      have hqp : dist q p = d := by
        rw [dist_eq_norm]
        change ‖p + (d / r) • v - p‖ = d
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (div_pos hd hr)]
        change (d / r) * r = d
        exact div_mul_cancel₀ _ (ne_of_gt hr)
      refine ⟨q, hqp, ?_⟩
      have he : x - q = (1 - d / r) • v := by
        rw [sub_smul, one_smul]
        dsimp [q, v]
        abel
      calc
        dist x q = ‖x - q‖ := dist_eq_norm _ _
        _ = |1 - d / r| * r := by rw [he, norm_smul, Real.norm_eq_abs]
        _ = |(1 - d / r) * r| := by rw [abs_mul, abs_of_pos hr]
        _ = |r - d| := by congr 1 <;> field_simp
        _ = |dist x p - d| := by rw [dist_eq_norm]
  apply le_antisymm
  · exact (Metric.infDist_le_dist_of_mem (x := x)
      (s := {q : Plane | dist q p = d}) (y := q) hq).trans_eq hnear
  · apply (Metric.le_infDist ⟨q, hq⟩).mpr
    intro y hy
    change dist y p = d at hy
    simpa only [hy] using abs_dist_sub_le x y p

/-- T25(c), p. 147: under the uniform sixteen-assignment toy design,
marginalization equals the mean over the eight assignments with own treatment b. -/
theorem toy_eight_assignment_mean (Y : Assignment 4 → ℝ) (i : Fin 4) (b : Bool) :
    marginal (uniformLaw (Assignment 4)) Y i b =
      (1 / 8 : ℝ) * ∑ z ∈ Finset.univ.filter (fun z => z i = b), Y z := by
  classical
  let e := Equiv.funSplitAt i Bool
  have heval (u : Bool × ({j : Fin 4 // j ≠ i} → Bool)) : (e.symm u) i = u.1 := by
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  have hupdate (u : Bool × ({j : Fin 4 // j ≠ i} → Bool)) :
      Function.update (e.symm u) i b = e.symm (b, u.2) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [heval]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, Function.update_of_ne hj, hj]
  have hsum (f : Assignment 4 → ℝ) :
      (∑ z, f z) = ∑ u : Bool × ({j : Fin 4 // j ≠ i} → Bool), f (e.symm u) :=
    Fintype.sum_equiv e _ _ (fun z => by simp)
  unfold marginal FiniteLaw.expect
  simp only [uniformLaw, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [← Finset.mul_sum, Finset.sum_filter, hsum, hsum]
  simp_rw [hupdate, heval, Fintype.sum_prod_type, Fintype.sum_bool]
  cases b <;> simp <;> ring

/-- T26(b)'s explicit weak-but-not-sharp witness: one node at 0, field
{-1,0,1} on the x-axis, outcomes +z at 1, -z at -1, zero at the node. -/
def cancellingOutcome (x : ℚ) (z : Assignment 1) : ℝ :=
  if x = 1 then bit (z 0) else if x = -1 then -bit (z 0) else 0

/-- T26(b), p. 144: the node is included in the field; the only nonempty
circles have radii 0 and 1 and both have mean zero under every assignment.
Every design's circle effect and AMR are zero although an outcome changes. -/
theorem weak_not_sharp_example :
    (0 : ℚ) ∈ ({-1, 0, 1} : Finset ℚ) ∧
    (∀ z : Assignment 1, ∀ d : ℝ,
      realLineM {-1, 0, 1} ![0] cancellingOutcome 0 d z = 0) ∧
    cancellingOutcome 1 ![true] ≠ cancellingOutcome 1 ![false] := by
  refine ⟨by norm_num, ?_, by norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, cancellingOutcome, bit]⟩
  intro z d
  by_cases hd₀ : d = 0
  · subst d
    norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, realLineM, realLineCircle, countMean, cancellingOutcome]
  by_cases hd₁ : d = 1
  · subst d
    norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, realLineM, realLineCircle, countMean, cancellingOutcome]
  · have hn : realLineCircle {-1, 0, 1} ![0] 0 d = ∅ := by
      norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, realLineCircle, hd₀, hd₁, Ne.symm hd₀, Ne.symm hd₁]
    simp [realLineM, hn, countMean]

/-- T27(b), additive and homogeneous case: when g_i(x)=g(dist(node_i,x)),
each nonempty finite-mass circle effect and the AMR equal the structural
coefficient g(d). The field measurability and integrability are explicit. -/
theorem homogeneous_additive_amr {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (base : Plane → ℝ) (g : ℝ → ℝ)
    (hfield : MeasurableSet P.field)
    (hadd : ∀ x ∈ P.field, ∀ z, P.Y x z = additiveOutcome base
      (fun i x => g (dist (P.node i) x)) x z)
    (d : ℝ) (hN : 0 < N) (hmass : ∀ i, 0 < P.circleMass i d)
    (hfinite : ∀ i, P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ i b z, Q.mass z ≠ 0 → Integrable (fun x => P.Y x (Function.update z i b))
      (P.circleMeasure i d)) :
    (∀ i x, x ∈ P.field → P.pointEffect Q i x = g (dist (P.node i) x)) ∧
    (∀ i, P.nodeEffect Q i d = g d) ∧ P.amr Q d = g d := by
  have havg (i : Fin N) : P.average i d (fun x => g (dist (P.node i) x)) = g d := by
    have hclosed : IsClosed {x : Plane | dist (P.node i) x = d} :=
      isClosed_eq (continuous_const.dist continuous_id) continuous_const
    have hmeas : MeasurableSet (P.circle i d) := hfield.inter hclosed.measurableSet
    have hae : (fun x => g (dist (P.node i) x)) =ᵐ[P.circleMeasure i d]
        (fun _ => g d) := by
      filter_upwards [ae_restrict_mem hmeas] with x hx
      exact congrArg g hx.2
    unfold SpatialModel.average
    rw [integral_congr_ae hae, integral_const]
    change (P.circleMass i d)⁻¹ * (P.circleMass i d * g d) = g d
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hmass i)), one_mul]
  have hnode (i : Fin N) : P.nodeEffect Q i d = g d := by
    rw [(additive_amr P Q base (fun i x => g (dist (P.node i) x)) hfield hadd
      d hN hmass hfinite hint).1 i, havg]
  refine ⟨?_, hnode, ?_⟩
  · intro i x hx
    exact additive_point_effect P Q base (fun i x => g (dist (P.node i) x)) hadd i x hx
  · unfold SpatialModel.amr
    simp_rw [hnode]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_zero_of_lt hN)), one_mul]

/- T28: sufficient conditions for consistency, distinct from the cited
theorem of Wang et al. -/

/-- Dependence on a collection of node-level pairs, for the
dependency-graph definition (T28). -/
def dependsOn {N : ℕ} (P : (Fin N → Bool × ℝ) → Prop) (A : Finset (Fin N)) : Prop :=
  ∀ u v, (∀ i ∈ A, u i = v i) → (P u ↔ P v)

/-- T28 dependency graph: disjoint nonadjacent collections of pairs
(Z_i,M_i(Z)) are independent, not merely pairwise uncorrelated. -/
def boundedPairDependency {N : ℕ} (Q : FiniteLaw (Assignment N))
    (M : Fin N → Assignment N → ℝ) (D : ℕ) : Prop := by
  classical
  exact ∃ G : Fin N → Fin N → Prop,
    (∀ i j, G i j ↔ G j i) ∧
    (∀ i, (Finset.univ.filter (fun j => j ≠ i ∧ G i j)).card ≤ D) ∧
    (∀ A B : Finset (Fin N), Disjoint A B →
      (∀ i ∈ A, ∀ j ∈ B, ¬ G i j) →
      ∀ P R : (Fin N → Bool × ℝ) → Prop, dependsOn P A → dependsOn R B →
      Q.prob (fun z => P (fun i => (z i, M i z)) ∧ R (fun i => (z i, M i z))) =
        Q.prob (fun z => P (fun i => (z i, M i z))) *
          Q.prob (fun z => R (fun i => (z i, M i z))))

/-- T28, S_b=N⁻¹∑1{Z_i=b}M_i(Z): the two normalized
numerators in the Hajek ratio. -/
def normalizedNumerator {N : ℕ} (M : Fin N → Assignment N → ℝ)
    (b : Bool) (z : Assignment N) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (if z i = b then (1 : ℝ) else 0) * M i z

/-- T28, r_b=N⁻¹∑m_i(b): the mean marginalized circle
outcome in condition b. -/
def marginalMean {N : ℕ} (Q : FiniteLaw (Assignment N))
    (M : Fin N → Assignment N → ℝ) (b : Bool) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, marginal Q (M i) i b

/-- The fixed-radius AMR expressed through its potential circle averages,
T28: N⁻¹∑[m_i(1)-m_i(0)]. -/
def finiteAMR {N : ℕ} (Q : FiniteLaw (Assignment N))
    (M : Fin N → Assignment N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i, (marginal Q (M i) i true - marginal Q (M i) i false)

/-- Hajek completion on the two empty-arm assignments, as explicitly
allowed by T28's sufficient version; otherwise the printed formula is used. -/
def completedHajek {N : ℕ} (M : Fin N → Assignment N → ℝ)
    (exceptional : ℝ) (z : Assignment N) : ℝ :=
  if nTreated z = 0 ∨ nControl z = 0 then exceptional else hajek M z


/-- T28 finite lemma (i): independent assignments with arbitrary interior
probabilities identify the two weighted numerators with the unconditional
marginal circle means. This does not assert unbiasedness of a ratio. -/
theorem bernoulli_numerator_identity {N : ℕ} (Q : FiniteLaw (Assignment N))
    (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hQ : ∀ z, Q.mass z = ∏ i, if z i then p i else 1 - p i)
    (M : Fin N → Assignment N → ℝ) (i : Fin N) :
    Q.expect (fun z => bit (z i) * M i z) = p i * marginal Q (M i) i true ∧
    Q.expect (fun z => (1 - bit (z i)) * M i z) =
      (1 - p i) * marginal Q (M i) i false := by
  classical
  let e := Equiv.funSplitAt i Bool
  let om (w : {j : Fin N // j ≠ i} → Bool) : ℝ :=
    ∏ k : {j : Fin N // j ≠ i}, if w k then p k else 1 - p k
  have heval (u : Bool × ({j : Fin N // j ≠ i} → Bool)) : (e.symm u) i = u.1 := by
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
  have hupdate (u : Bool × ({j : Fin N // j ≠ i} → Bool)) (b : Bool) :
      Function.update (e.symm u) i b = e.symm (b, u.2) := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [heval]
    · simp [e, Equiv.funSplitAt, Equiv.piSplitAt, Function.update_of_ne hj, hj]
  have hm (u : Bool × ({j : Fin N // j ≠ i} → Bool)) :
      Q.mass (e.symm u) = (if u.1 then p i else 1 - p i) * om u.2 := by
    rw [hQ, Fintype.prod_eq_mul_prod_subtype_ne _ i]
    rw [heval]
    congr 1
    apply Finset.prod_congr rfl
    intro k _
    simp [e, Equiv.funSplitAt, Equiv.piSplitAt, om, k.property]
  have hsum (f : Assignment N → ℝ) :
      (∑ z, f z) = ∑ u : Bool × ({j : Fin N // j ≠ i} → Bool), f (e.symm u) :=
    Fintype.sum_equiv e _ _ (fun z => by simp)
  unfold marginal FiniteLaw.expect
  simp_rw [hsum, hm, heval, hupdate, Fintype.sum_prod_type, Fintype.sum_bool]
  constructor <;> simp [bit, ← Finset.mul_sum, mul_assoc,
    ne_of_gt (hp i).1, ne_of_gt (sub_pos.mpr (hp i).2)] <;> ring


/-- T28 finite lemma (iv), deterministic ratio bound on the good
denominator event. This is the exact inequality used for consistency. -/
theorem ratio_deviation_bound (S U p r H : ℝ) (hp : 0 < p)
    (hU : p / 2 ≤ U) (hr : |r| ≤ H) :
    |S / U - r| ≤ (2 / p) * (|S - p * r| + H * |U - p|) := by
  have hUp : 0 < U := lt_of_lt_of_le (half_pos hp) hU
  have he : S / U - r = (S - p * r - r * (U - p)) / U := by
    field_simp <;> ring
  have hb : |S - p * r - r * (U - p)| ≤ |S - p * r| + H * |U - p| := by
    calc
      _ ≤ |S - p * r| + |r * (U - p)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (S - p * r) (-(r * (U - p)))
      _ = |S - p * r| + |r| * |U - p| := by rw [abs_mul]
      _ ≤ _ := by gcongr
  have hnon : 0 ≤ |S - p * r| + H * |U - p| := by
    have hH : 0 ≤ H := (abs_nonneg r).trans hr
    positivity
  rw [he, abs_div, abs_of_pos hUp]
  calc
    _ ≤ (|S - p * r| + H * |U - p|) / U := by gcongr
    _ ≤ (|S - p * r| + H * |U - p|) / (p / 2) := by gcongr
    _ = _ := by field_simp

/-- T21(i), p. 153, the true numerical comparison; T2 supplies the
conditional calibrated tail rule. No empirical design p-value is asserted. -/
theorem uganda_printed_comparison : (-321 / 10000 : ℝ) < -19 / 625 := by norm_num

/- T22(i), p. 146: the printed fully enumerated interpolated-percentile
calibration claim is false; T3 gives a counterexample. -/


/- T24, p. 153: the printed claim that an unweighted multi-radius sum of
probability differences is itself a probability difference is false (T7). -/


/-- Finite expectation distributes over any finite sum of node variables. -/
theorem expect_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (Q : FiniteLaw Ω) (f : I → Ω → ℝ) :
    Q.expect (fun z => ∑ i, f i z) = ∑ i, Q.expect (f i) := by
  unfold FiniteLaw.expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

/-- Finite expectation commutes with a fixed real multiplier. -/
theorem expect_mul_const {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (c : ℝ) (f : Ω → ℝ) : Q.expect (fun z => c * f z) = c * Q.expect f := by
  unfold FiniteLaw.expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- A finite normalized design preserves pointwise [0,1] bounds. -/
theorem expect_probability_bounds {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (f : Ω → ℝ) (hf : ∀ z, 0 ≤ f z ∧ f z ≤ 1) :
    0 ≤ Q.expect f ∧ Q.expect f ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg (fun z _ => mul_nonneg (Q.nonneg z) (hf z).1)
  · calc
      Q.expect f ≤ Q.expect (fun _ => 1) :=
        Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hf z).2 (Q.nonneg z))
      _ = 1 := expect_const Q 1


/-- Probability bounds on positive-mass assignments suffice for a design
expectation; outcomes at zero-mass assignments are unrestricted. -/
theorem expect_probability_bounds_on_support {Ω : Type*} [Fintype Ω]
    (Q : FiniteLaw Ω) (f : Ω → ℝ)
    (hf : ∀ z, Q.mass z ≠ 0 → 0 ≤ f z ∧ f z ≤ 1) :
    0 ≤ Q.expect f ∧ Q.expect f ≤ 1 := by
  have hl (z : Ω) : 0 ≤ Q.mass z * f z := by
    by_cases hz : Q.mass z = 0
    · simp [hz]
    · exact mul_nonneg (Q.nonneg z) (hf z hz).1
  have hu (z : Ω) : Q.mass z * f z ≤ Q.mass z := by
    by_cases hz : Q.mass z = 0
    · simp [hz]
    · simpa using mul_le_mul_of_nonneg_left (hf z hz).2 (Q.nonneg z)
  exact ⟨Finset.sum_nonneg (fun z _ => hl z),
    (Finset.sum_le_sum (fun z _ => hu z)).trans_eq Q.total⟩

/-- T8(a): a genuine positive finite-mass circle average of a [0,1]
outcome is in [0,1]. This precludes zero-measure shortcuts. -/
theorem circle_probability_bounds {N : ℕ} (P : SpatialModel N) (i : Fin N) (d : ℝ)
    (f : Plane → ℝ) (hmass : 0 < P.circleMass i d)
    (hfinite : P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : Integrable f (P.circleMeasure i d)) (hcircle : MeasurableSet (P.circle i d))
    (hf : ∀ x ∈ P.circle i d, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ P.average i d f ∧ P.average i d f ≤ 1 := by
  letI : IsFiniteMeasure (P.circleMeasure i d) :=
    ⟨lt_top_iff_ne_top.mpr hfinite⟩
  have hae : ∀ᵐ x ∂P.circleMeasure i d, 0 ≤ f x ∧ f x ≤ 1 :=
    (ae_restrict_mem hcircle).mono (fun x hx => hf x hx)
  have hl : 0 ≤ ∫ x, f x ∂P.circleMeasure i d :=
    integral_nonneg_of_ae (hae.mono (fun _ h => h.1))
  have hu : (∫ x, f x ∂P.circleMeasure i d) ≤ P.circleMass i d := by
    calc
      _ ≤ ∫ _x, (1 : ℝ) ∂P.circleMeasure i d :=
        integral_mono_ae hint (integrable_const 1) (hae.mono (fun _ h => h.2))
      _ = P.circleMass i d := by simp [integral_const, SpatialModel.circleMass, Measure.real]
  unfold SpatialModel.average
  constructor
  · exact mul_nonneg (inv_nonneg.mpr hmass.le) hl
  · calc
      _ ≤ (P.circleMass i d)⁻¹ * P.circleMass i d := by gcongr
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hmass)

/-- “q_b(d)=N⁻¹∑ μ_i(b;d,α)”, T8's normalized node/point sampling risk. -/
def SpatialModel.risk {N : ℕ} (P : SpatialModel N) (Q : FiniteLaw (Assignment N))
    (b : Bool) (d : ℝ) : ℝ := (N : ℝ)⁻¹ * ∑ i, P.m Q i b d

/-- T8(a): binary potential outcomes yield bona fide sampling risks and
the AMR is precisely their difference, for any finite design. -/
theorem spatial_risk_normalization {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (d : ℝ) (hN : 0 < N)
    (hfield : MeasurableSet P.field)
    (hmass : ∀ i, 0 < P.circleMass i d)
    (hfinite : ∀ i, P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ i b z, Q.mass z ≠ 0 → Integrable (fun x => P.Y x (Function.update z i b))
      (P.circleMeasure i d))
    (hbinary : ∀ x ∈ P.field, ∀ z, P.Y x z = 0 ∨ P.Y x z = 1) :
    (∀ b, 0 ≤ P.risk Q b d ∧ P.risk Q b d ≤ 1) ∧
    P.amr Q d = P.risk Q true d - P.risk Q false d := by
  have hm (i : Fin N) (b : Bool) : 0 ≤ P.m Q i b d ∧ P.m Q i b d ≤ 1 := by
    apply expect_probability_bounds_on_support
    intro z hz
    apply circle_probability_bounds P i d _ (hmass i) (hfinite i) (hint i b z hz)
      (circle_measurable P i d hfield)
    intro x hx
    rcases hbinary x hx.1 (Function.update z i b) with hz | hz <;> rw [hz] <;> norm_num
  constructor
  · intro b
    unfold SpatialModel.risk
    constructor
    · exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => (hm i b).1))
    · have hsum : (∑ i, P.m Q i b d) ≤ (N : ℝ) := by
        calc
          _ ≤ ∑ _i : Fin N, (1 : ℝ) := Finset.sum_le_sum (fun i _ => (hm i b).2)
          _ = _ := by simp
      calc
        _ ≤ (N : ℝ)⁻¹ * N := by gcongr
        _ = 1 := inv_mul_cancel₀ (by exact_mod_cast (Nat.ne_zero_of_lt hN))
  · simp [SpatialModel.amr, SpatialModel.nodeEffect, SpatialModel.risk,
      Finset.sum_sub_distrib, mul_sub]

/-- Finite expectation distributes over addition. -/
theorem expect_add {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f g : Ω → ℝ) :
    Q.expect (fun z => f z + g z) = Q.expect f + Q.expect g := by
  simp [FiniteLaw.expect, mul_add, Finset.sum_add_distrib]

/-- Finite covariance equals the raw second moment minus the product of
means, derived from normalized masses rather than postulated. -/
theorem covariance_raw {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f g : Ω → ℝ) :
    Q.cov f g = Q.expect (fun z => f z * g z) - Q.expect f * Q.expect g := by
  unfold FiniteLaw.cov
  have he : (fun z => (f z - Q.expect f) * (g z - Q.expect g)) =
      (fun z => f z * g z - Q.expect f * g z - Q.expect g * f z +
        Q.expect f * Q.expect g) := by
    funext z
    ring
  rw [he, expect_add, expect_sub, expect_sub, expect_mul_const, expect_mul_const,
    expect_const]
  ring

/-- T6(c)/T23(i): exact variance of a finite sum equals the sum of all
ordered covariances under an arbitrary finite probability design. -/
theorem variance_sum_covariances {Ω I : Type*} [Fintype Ω] [Fintype I]
    (Q : FiniteLaw Ω) (φ : I → Ω → ℝ) :
    Q.var (fun z => ∑ i, φ i z) = ∑ i, ∑ j, Q.cov (φ i) (φ j) := by
  unfold FiniteLaw.var
  rw [covariance_raw]
  simp_rw [covariance_raw, Finset.sum_mul, Finset.mul_sum, expect_sum,
    Finset.sum_sub_distrib]
  rw [Finset.sum_mul_sum]

/-- T23(i), the instruction read as bounding contribution dependence:
zero covariances outside cutoff make the truncated covariance sum exact. -/
theorem dependence_cutoff_identity {Ω : Type*} [Fintype Ω] {N : ℕ}
    (Q : FiniteLaw Ω) (φ : Fin N → Ω → ℝ) (D : Fin N → Fin N → ℝ)
    (c : ℝ) (hzero : ∀ i j, c < D i j → Q.cov (φ i) (φ j) = 0) :
    (∑ i, ∑ j, Q.cov (φ i) (φ j) * (if D i j ≤ c then 1 else 0)) =
      Q.var (fun z => ∑ i, φ i z) := by
  rw [variance_sum_covariances]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : D i j ≤ c
  · simp [h]
  · simp [h, hzero i j (lt_of_not_ge h)]

/-- T12: a distribution consisting entirely of empty sums has every
type-7 interpolated quantile zero, including both reported percentile levels. -/
theorem zero_sum_quantiles {n : ℕ} (q : ℝ) :
    quantile7 (fun _ : Fin (n + 1) => 0) q = 0 := by simp [quantile7]


/-- T20(a): the outer-row/column selector is exactly the eight-neighbour
boundary definition on a 5×5 block; the unselected cells form the central 3×3. -/
theorem block_boundary_is_eight_neighbour :
    (∀ c : BlockCell, c ∈ blockBoundary ↔
      ∃ a b : Fin 3,
        (a.val ≠ 1 ∨ b.val ≠ 1) ∧
        ((c.1.val : ℤ) + a.val - 1 < 0 ∨ 5 ≤ (c.1.val : ℤ) + a.val - 1 ∨
         (c.2.val : ℤ) + b.val - 1 < 0 ∨ 5 ≤ (c.2.val : ℤ) + b.val - 1)) ∧
    (∀ c : BlockCell, c ∈ (Finset.univ \ blockBoundary) ↔
      1 ≤ c.1.val ∧ c.1.val ≤ 3 ∧ 1 ≤ c.2.val ∧ c.2.val ≤ 3) := by
  decide

/-- T26(b): the explicit cancelling schedule has weak null at every
radius for every design, not just at radius 1 or under one chosen law. -/
theorem cancelling_schedule_all_designs (Q : FiniteLaw (Assignment 1)) (d : ℝ) :
    finiteAMR Q (fun i z => realLineM {-1, 0, 1} ![0] cancellingOutcome i d z) = 0 := by
  have hm (i : Fin 1) (z : Assignment 1) :
      realLineM {-1, 0, 1} ![0] cancellingOutcome i d z = 0 := by
    fin_cases i
    exact weak_not_sharp_example.2.1 z d
  unfold finiteAMR marginal
  simp_rw [hm, expect_const]
  simp

/-- T6(d), general integral form of the geometric support bound: whenever
the source node is farther than d+r, its coefficient averaged over the
circle is zero. Field measurability ensures the restricted measure selects
the stated circle, and positive finite mass keeps it a genuine average. -/
theorem integral_far_coefficient_zero {N : ℕ} (P : SpatialModel N)
    (i k : Fin N) (d r : ℝ) (g : Plane → ℝ)
    (hfield : MeasurableSet P.field) (hmass : 0 < P.circleMass i d)
    (hfinite : P.circleMeasure i d Set.univ ≠ ⊤)
    (heffect : ∀ x, r < dist (P.node k) x → g x = 0)
    (hfar : d + r < dist (P.node i) (P.node k)) : P.average i d g = 0 := by
  have hs : MeasurableSet (P.circle i d) := hfield.inter
    (isClosed_eq (continuous_const.dist continuous_id) continuous_const).measurableSet
  have hae : g =ᵐ[P.circleMeasure i d] (fun _ => 0) := by
    filter_upwards [ae_restrict_mem hs] with x hx
    exact heffect x (circle_outside_effect_range _ _ x d r hx.2 hfar)
  unfold SpatialModel.average
  rw [integral_congr_ae hae]
  simp

/-- The normal equations for the binary intercept/treatment regression,
derived directly from the two group means (T10(b)), with both arms nonempty. -/
theorem regression_score_sum_zero {N : ℕ} (z : Assignment N) (M : Fin N → ℝ)
    (h₁ : nTreated z ≠ 0) (h₀ : nControl z ≠ 0) :
    ∑ i, regressionScore z M i = 0 := by
  have he₁ (i : Fin N) : bit (z i) * groupResidual z M i =
      bit (z i) * (M i - groupMean z M true) := by
    cases hz : z i <;> simp [groupResidual, bit, hz]
  have he₀ (i : Fin N) : (1 - bit (z i)) * groupResidual z M i =
      (1 - bit (z i)) * (M i - groupMean z M false) := by
    cases hz : z i <;> simp [groupResidual, bit, hz]
  have hcnt : (∑ i, (1 - bit (z i))) = nControl z := by
    simp [nControl, nTreated, Finset.sum_sub_distrib]
  have ht : (∑ i, bit (z i) * groupResidual z M i) = 0 := by
    simp_rw [he₁, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    change (∑ i, bit (z i) * M i) - nTreated z *
      ((∑ i, bit (z i) * M i) / nTreated z) = 0
    field_simp <;> ring
  have hc : (∑ i, (1 - bit (z i)) * groupResidual z M i) = 0 := by
    simp_rw [he₀, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcnt]
    change (∑ i, (1 - bit (z i)) * M i) - nControl z *
      ((∑ i, (1 - bit (z i)) * M i) / nControl z) = 0
    field_simp <;> ring
  calc
    _ = (∑ i, bit (z i) * groupResidual z M i) / nTreated z -
        (∑ i, (1 - bit (z i)) * groupResidual z M i) / nControl z := by
      simp only [regressionScore, contrastWeight, sub_mul, div_mul_eq_mul_div,
        Finset.sum_sub_distrib, Finset.sum_div, sub_div]
    _ = 0 := by rw [ht, hc]; simp

/-- T10(b) with actual regression residuals, rather than an assumed score
sum: including every node pair makes the treatment-coefficient HAC zero. -/
theorem regression_all_pairs_zero {N : ℕ} (z : Assignment N) (M : Fin N → ℝ)
    (D : Fin N → Fin N → ℝ) (c : ℝ) (h₁ : nTreated z ≠ 0) (h₀ : nControl z ≠ 0)
    (hall : ∀ i j, D i j ≤ c) : hac (regressionScore z M) D c = 0 :=
  hac_all_pairs_zero _ D c hall (regression_score_sum_zero z M h₁ h₀)

/-- T5's replicated pairs: independent Bernoulli assignments indexed by
pair and node, with both pair scores equal to half the product of their signs. -/
def replicatedPairScore {M : ℕ} (i : Fin M × Fin 2)
    (z : (Fin M × Fin 2) → Bool) : ℝ :=
  (1 / 2 : ℝ) * (2 * bit (z (i.1, 0)) - 1) * (2 * bit (z (i.1, 1)) - 1)


/-- Explicit embedding of the rational x-axis coordinates used in the
finite examples into the paper's two-coordinate Euclidean spatial field. -/
def lineEmbedding (x : ℚ) : Plane := WithLp.toLp 2 ![(x : ℝ), 0]

/-- The absolute rational coordinate distances used by lineCircle are
exactly the Euclidean distances of the embedded points. -/
theorem line_embedding_distance (x y : ℚ) :
    dist (lineEmbedding x) (lineEmbedding y) = ((|x - y| : ℚ) : ℝ) := by
  have hs : dist (lineEmbedding x) (lineEmbedding y) ^ 2 =
      (((x - y : ℚ) : ℝ)) ^ 2 := by
    rw [EuclideanSpace.dist_sq_eq]
    simp [lineEmbedding, Fin.sum_univ_succ, Real.dist_eq, sq_abs]
  have ha : |((x - y : ℚ) : ℝ)| = ((|x - y| : ℚ) : ℝ) := by norm_cast
  rw [← ha]
  nlinarith [dist_nonneg (x := lineEmbedding x) (y := lineEmbedding y), abs_nonneg (((x - y : ℚ) : ℝ)),
    sq_abs (((x - y : ℚ) : ℝ))]

/-- Sparse-point realization of T3's constant circle outcomes. It includes
all four intervention nodes and one outcome point on each of their five
required circles; counting measure gives each circle positive mass one.
Coordinates embed by lineEmbedding; the paper permits this finite field. -/
def percentileField : Finset ℚ :=
  {0, 1 / 10, 1 / 5, 3 / 10, 2 / 5, 1 / 2,
   10, 101 / 10, 51 / 5, 103 / 10, 52 / 5, 21 / 2,
   20, 201 / 10, 101 / 5, 203 / 10, 102 / 5, 41 / 2,
   30, 301 / 10, 151 / 5, 303 / 10, 152 / 5, 61 / 2}

/-- T3's four nodes, (0,0),(10,0),(20,0),(30,0). -/
def percentileNode (i : Fin 4) : ℚ := 10 * i.val

/-- Assignment-independent outcomes 0,1,2,3 on the four spatial clusters,
and hence the sharp null everywhere on the finite spatial field. -/
def percentileOutcome (x : ℚ) (_z : Assignment 4) : ℝ :=
  if x < 1 then 0 else if x < 11 then 1 else if x < 21 then 2 else 3

/-- T3 spatial hypotheses: nodes lie in the field, outcomes satisfy the
sharp null, each required circle has one point, and its average is 0,1,2,3. -/
theorem percentile_spatial_hypotheses :
    (∀ i, percentileNode i ∈ percentileField) ∧
    (∀ x z, percentileOutcome x z = percentileOutcome x (fun _ => false)) ∧
    (∀ i : Fin 4, ∀ j : Fin 5,
      (lineCircle percentileField percentileNode i ((j.val + 1 : ℚ) / 10)).card = 1) ∧
    (∀ i : Fin 4, ∀ j : Fin 5, ∀ z,
      lineM percentileField percentileNode percentileOutcome i ((j.val + 1 : ℚ) / 10) z = i.val) := by
  have hcircle (i : Fin 4) (j : Fin 5) :
      lineCircle percentileField percentileNode i ((j.val + 1 : ℚ) / 10) =
        {percentileNode i + (j.val + 1 : ℚ) / 10} := by
    fin_cases i <;> fin_cases j <;> decide +kernel
  refine ⟨?_, fun _ _ => rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num [percentileNode, percentileField]
  · intro i j
    rw [hcircle]
    simp
  · intro i j z
    unfold lineM
    rw [hcircle]
    simp only [countMean, Finset.sum_singleton, Finset.card_singleton,
      Nat.cast_one, div_one]
    fin_cases i <;> fin_cases j <;> norm_num [percentileNode, percentileOutcome]

/-- T3's counterexample with spatial hypotheses certified: for every
required radius the actual Hajek statistic is -2,-1,0,0,1,2 under the six
two-of-four assignments. Its interpolated percentile test has size 1/3>.05. -/
theorem finite_field_percentile_counterexample :
    (∀ j : Fin 5, ∀ k : Fin 6,
      hajek (fun i z => lineM percentileField percentileNode percentileOutcome i
        ((j.val + 1 : ℚ) / 10) z) (sixAssignment k) = percentileExample k) ∧
    quantile7 percentileExample (1 / 40) = -15 / 8 ∧
    quantile7 percentileExample (39 / 40) = 15 / 8 ∧
    (uniformLaw (Fin 6)).prob (fun k => outside (-15 / 8) (15 / 8)
      (percentileExample k)) = 1 / 3 ∧ (1 / 20 : ℝ) < 1 / 3 := by
  refine ⟨?_, interpolated_percentile_counterexample.2.1,
    interpolated_percentile_counterexample.2.2.1,
    interpolated_percentile_counterexample.2.2.2.1, by norm_num⟩
  intro j k
  simp_rw [percentile_spatial_hypotheses.2.2.2]
  rw [(contrast_is_hajek (fun i : Fin 4 => (i.val : ℝ)) k).2.2]
  fin_cases k <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, contrast4, percentileExample, sixAssignment, bit, Fin.sum_univ_succ]

/-- Design variance under a fixed real scaling, a finite moment identity. -/
theorem variance_mul_const {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (c : ℝ) (f : Ω → ℝ) : Q.var (fun z => c * f z) = c ^ 2 * Q.var f := by
  unfold FiniteLaw.var
  rw [covariance_raw, covariance_raw, expect_mul_const]
  have he : (fun z => c * f z * (c * f z)) = (fun z => c ^ 2 * (f z * f z)) := by
    funext z
    ring
  rw [he, expect_mul_const]
  ring

/-- T28 finite lemma (ii): the treated fraction has mean p and variance
p(1-p)/N under common independent Bernoulli(p), for each fixed N>0. -/
theorem bernoulli_fraction_moments {N : ℕ} (hN : 0 < N)
    (Q : FiniteLaw (Assignment N)) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hQ : commonBernoulli Q p) :
    Q.expect (fun z => nTreated z / N) = p ∧
    Q.var (fun z => nTreated z / N) = p * (1 - p) / N := by
  have hm : ∀ z, Q.mass z = ∏ _i : Fin N, if z _i then p else 1 - p := hQ
  have hb (i : Fin N) : Q.expect (fun z => bit (z i)) = p := by
    have hi := (bernoulli_numerator_identity Q (fun _ => p) (fun _ => ⟨hp, hp'⟩)
      hm (fun _ _ => 1) i).1
    simpa [marginal, expect_const] using hi
  have hc (i j : Fin N) : Q.cov (fun z => bit (z i)) (fun z => bit (z j)) =
      if i = j then p * (1 - p) else 0 := by
    by_cases hij : i = j
    · subst j
      have he : (fun z : Assignment N => bit (z i) * bit (z i)) = (fun z : Assignment N => bit (z i)) := by
        funext z
        cases z i <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, bit]
      rw [covariance_raw, he, hb]
      simp <;> ring
    · have hi := (bernoulli_numerator_identity Q (fun _ => p) (fun _ => ⟨hp, hp'⟩)
        hm (fun _ z => bit (z j)) i).1
      have ht : marginal Q (fun z => bit (z j)) i true = p := by
        simpa [marginal, Function.update_of_ne (Ne.symm hij)] using hb j
      rw [ht] at hi
      rw [covariance_raw, hi, hb i, hb j, if_neg hij]
      ring
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  constructor
  · change Q.expect (fun z => (∑ i, bit (z i)) / N) = p
    simp only [div_eq_mul_inv]
    simp_rw [mul_comm _ (N : ℝ)⁻¹]
    rw [expect_mul_const, expect_sum]
    simp_rw [hb]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hNr, one_mul]
  · change Q.var (fun z => (∑ i, bit (z i)) / N) = p * (1 - p) / N
    simp only [div_eq_mul_inv]
    simp_rw [mul_comm _ (N : ℝ)⁻¹]
    rw [variance_mul_const, variance_sum_covariances]
    simp_rw [hc]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp <;> ring

/-- T28 finite probability lemma: Chebyshev's inequality on the actual finite
randomization law, with the centered variance used by the asymptotic argument. -/
theorem finite_chebyshev {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (f : Ω → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Q.prob (fun z => ε ≤ |f z - Q.expect f|) ≤ Q.var f / ε ^ 2 := by
  classical
  let R := Finset.univ.filter (fun z => ε ≤ |f z - Q.expect f|)
  have hbound : ε ^ 2 * Q.prob (fun z => ε ≤ |f z - Q.expect f|) ≤ Q.var f := by
    calc
      _ = ∑ z ∈ R, Q.mass z * ε ^ 2 := by
        unfold FiniteLaw.prob
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ ≤ ∑ z ∈ R, Q.mass z * (f z - Q.expect f) ^ 2 := by
        apply Finset.sum_le_sum
        intro z hz
        have ha := (Finset.mem_filter.mp hz).2
        have hs : ε ^ 2 ≤ (f z - Q.expect f) ^ 2 := by
          nlinarith [sq_abs (f z - Q.expect f), abs_nonneg (f z - Q.expect f)]
        exact mul_le_mul_of_nonneg_left hs (Q.nonneg z)
      _ ≤ ∑ z, Q.mass z * (f z - Q.expect f) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro z _ _
        exact mul_nonneg (Q.nonneg z) (sq_nonneg _)
      _ = Q.var f := by
        simp only [FiniteLaw.var, FiniteLaw.cov, FiniteLaw.expect, pow_two]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  simpa only [mul_comm] using hbound

/-- T7(7)'s companion schedule: every point of node i's radius-j circle
has binary outcome 1-Z_i; circle sets retain all 40000 points. -/
def companionRiskOutcome (i : Fin 4) (_j : Fin 4) (_k : RiskCell)
    (z : Assignment 4) : ℝ := 1 - bit (z i)

/-- T7(7)'s companion circle averages, using the same counting mean. -/
def companionRiskM (i j : Fin 4) (z : Assignment 4) : ℝ :=
  countMean Finset.univ (fun k => companionRiskOutcome i j k z)

/-- T7(7), the fully specified binary companion has AMR -1 at every radius
and sum -4. A sum of AMRs therefore need not be any probability difference. -/
theorem binary_companion_counterexample (Q : FiniteLaw (Assignment 4)) :
    (∀ i j k z, companionRiskOutcome i j k z = 0 ∨ companionRiskOutcome i j k z = 1) ∧
    (∀ i j z, companionRiskM i j z = 1 - bit (z i)) ∧
    (∀ j, finiteAMR Q (fun i z => companionRiskM i j z) = -1) ∧
    (∑ j : Fin 4, finiteAMR Q (fun i z => companionRiskM i j z)) = -4 ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      a - b ≠ ∑ j : Fin 4, finiteAMR Q (fun i z => companionRiskM i j z)) := by
  have hm (i j : Fin 4) (z : Assignment 4) : companionRiskM i j z = 1 - bit (z i) := by
    simp [companionRiskM, companionRiskOutcome, countMean, nsmul_eq_mul]
    field_simp <;> ring
  have he (i j : Fin 4) (b : Bool) : marginal Q (fun z => companionRiskM i j z) i b =
      1 - bit b := by
    simp [marginal, hm, expect_const]
  have ha (j : Fin 4) : finiteAMR Q (fun i z => companionRiskM i j z) = -1 := by
    simp only [finiteAMR, he]
    norm_num [bit, Fin.sum_univ_succ]
  have hsum : (∑ j : Fin 4, finiteAMR Q (fun i z => companionRiskM i j z)) = -4 := by
    simp_rw [ha]
    norm_num
  refine ⟨?_, hm, ha, hsum, ?_⟩
  · intro i j k z
    cases hz : z i <;> norm_num [companionRiskOutcome, bit, hz]
  · intro a b ha ha' hb hb'
    rw [hsum]
    linarith

/-- T22(ii), p. 150: conditional on the printed numbers, the nominal
percentile rule rejects because 12.38 lies above 7.97. This asserts the
decision only; it does not assert that the rule has error rate .05. -/
theorem printed_toy_rule_rejects :
    outside (-797 / 100) (797 / 100) (619 / 50) := by
  norm_num [outside]

/-- The rational-radius and real-radius implementations select precisely
the same finite circle. The latter extends the quantifier without changing the object. -/
theorem real_rational_circle {N : ℕ} (field : Finset ℚ) (node : Fin N → ℚ)
    (i : Fin N) (d : ℚ) :
    realLineCircle field node i (d : ℝ) = lineCircle field node i d := by
  ext x
  simp only [realLineCircle, lineCircle, Finset.mem_filter, Rat.cast_inj]

/-- T26's converse witness uses genuine positive counting mass: the node's
radius-0 circle has one point and its radius-1 circle has two points. -/
theorem cancelling_circle_masses :
    (realLineCircle {-1, 0, 1} ![0] 0 0).card = 1 ∧
    (realLineCircle {-1, 0, 1} ![0] 0 1).card = 2 := by
  norm_num [realLineCircle, Finset.filter_insert, Finset.filter_singleton]

/-- T9(iii), the concrete sixth-row incompatibility at the four
reconstructed toy nodes: their squared separations are at most 32, every
normal-equation score vector therefore gives zero variance at index 6,
and no Wald multiplier can give the printed positive interval width. -/
theorem toy_archived_sixth_row_incompatible (z : Assignment 4) (M : Fin 4 → ℝ)
    (h₁ : nTreated z ≠ 0) (h₀ : nControl z ≠ 0) :
    (∀ i j, dist (toyNode i) (toyNode j) ^ 2 ≤ 32) ∧
    archivedVariance (regressionScore z M)
      (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) 6 = 0 ∧
    (∀ a : ℝ, 2 * a * Real.sqrt (archivedVariance (regressionScore z M)
      (fun i j => dist (toyNode i) (toyNode j)) (2 / 5) 6) ≠ 869 / 250) := by
  have hsq (i j : Fin 4) : dist (toyNode i) (toyNode j) ^ 2 ≤ 32 := by
    rw [EuclideanSpace.dist_sq_eq]
    fin_cases i <;> fin_cases j <;>
      norm_num [toyNode, Fin.sum_univ_succ, Real.dist_eq, WithLp.toLp]
  have hz := (archived_sixth_row_incompatible (regressionScore z M)
    (fun i j => dist (toyNode i) (toyNode j)) hsq
      (regression_score_sum_zero z M h₁ h₀)).1
  refine ⟨hsq, hz, ?_⟩
  intro a
  rw [hz]
  norm_num

/-- The rectangle in the fixed T3 construction: [-1,31]×[-1,1], which
contains the closed radius-1 discs about (0,0),(10,0),(20,0),(30,0). -/
def validatorRectangle : Set Plane :=
  {x | -1 ≤ x 0 ∧ x 0 ≤ 31 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1}

/-- T3's complete potential outcomes on the rectangle: outcome `i.val` in the
closed unit disc about zero-based node `i : Fin 4`, zero outside all four discs,
under every assignment. The discs are disjoint, so this sum gives an unambiguous
piecewise rule. -/
def validatorRectangleOutcome (x : Plane) (_z : Assignment 4) : ℝ :=
  ∑ i : Fin 4, if dist x (lineEmbedding (percentileNode i)) ≤ 1 then (i.val : ℝ) else 0

/-- A concrete suitable ζ for T3: counting mass on 24 distinct points,
namely each node and its five rightward radius-grid points. The spatial field
remains the full rectangle, and potential outcomes are defined everywhere in it. -/
def validatorRectangleMeasure : Measure Plane :=
  ∑ a : Fin 4 × Fin 6,
    Measure.dirac (lineEmbedding (percentileNode a.1 + (a.2.val : ℚ) / 10))

/-- The T3 rectangle, its four nodes, full sharp-null outcome
schedule, and explicit finite counting measure. This is distinct from the
additional finite-field witness above; no positive-circle assumption is hidden. -/
def validatorRectangleModel : SpatialModel 4 where
  field := validatorRectangle
  node i := lineEmbedding (percentileNode i)
  node_mem := by
    intro i
    fin_cases i <;> norm_num [validatorRectangle, percentileNode, lineEmbedding, WithLp.toLp]
  ζ := validatorRectangleMeasure
  Y := validatorRectangleOutcome

/-- The five radii in T3, in exact real units: .1,.2,.3,.4,.5. -/
def validatorRadius (j : Fin 5) : ℝ := (j.val + 1 : ℝ) / 10

/-- The actual Hajek statistic from the fixed T3 rectangle circle integrals. -/
def validatorRectangleStatistic (j : Fin 5) (k : Fin 6) : ℝ :=
  hajek (fun i z => validatorRectangleModel.M i (validatorRadius j) z) (sixAssignment k)

/-- T3's exact rectangle construction: the full unit discs lie in the
field, all five relevant circles have positive finite mass and integrable outcomes,
the sharp null holds, and the actual circle means are 0,1,2,3. The full-enumeration
single-radius and five-radius-sum type-7 tests both reject with probability 1/3>.05.
The suitable integration measure is explicitly specified. -/
theorem spatial_percentile_counterexample :
    (∀ i : Fin 4, {x : Plane | dist x (validatorRectangleModel.node i) ≤ 1} ⊆
      validatorRectangleModel.field) ∧
    (∀ i k : Fin 4, i ≠ k → Disjoint
      {x : Plane | dist x (validatorRectangleModel.node i) ≤ 1}
      {x : Plane | dist x (validatorRectangleModel.node k) ≤ 1}) ∧
    (∀ i : Fin 4, ∀ j : Fin 5,
      0 < validatorRectangleModel.circleMass i (validatorRadius j) ∧
      validatorRectangleModel.circleMeasure i (validatorRadius j) Set.univ ≠ ⊤ ∧
      ∀ z, Integrable (fun x => validatorRectangleModel.Y x z)
        (validatorRectangleModel.circleMeasure i (validatorRadius j))) ∧
    (∀ x z, validatorRectangleModel.Y x z =
      validatorRectangleModel.Y x (fun _ => false)) ∧
    (∀ i : Fin 4, ∀ j : Fin 5, ∀ z,
      validatorRectangleModel.M i (validatorRadius j) z = i.val) ∧
    (∀ j k, validatorRectangleStatistic j k = percentileExample k) ∧
    (∀ j, quantile7 (validatorRectangleStatistic j) (1 / 40) = -15 / 8 ∧
      quantile7 (validatorRectangleStatistic j) (39 / 40) = 15 / 8 ∧
      (uniformLaw (Fin 6)).prob (fun k => outside (-15 / 8) (15 / 8)
        (validatorRectangleStatistic j k)) = 1 / 3) ∧
    quantile7 (fun k => ∑ j, validatorRectangleStatistic j k) (1 / 40) = -75 / 8 ∧
    quantile7 (fun k => ∑ j, validatorRectangleStatistic j k) (39 / 40) = 75 / 8 ∧
    (uniformLaw (Fin 6)).prob (fun k => outside (-75 / 8) (75 / 8)
      (∑ j, validatorRectangleStatistic j k)) = 1 / 3 ∧ (1 / 20 : ℝ) < 1 / 3 := by
  classical
  have hcm (i : Fin 4) (j : Fin 5) :
      validatorRectangleModel.circleMeasure i (validatorRadius j) =
        Measure.dirac (lineEmbedding (percentileNode i + (j.val + 1 : ℚ) / 10)) := by
    unfold SpatialModel.circleMeasure validatorRectangleModel validatorRectangleMeasure
    simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Measure.restrict_add,
      Measure.restrict_zero, restrict_dirac]
    simp only [SpatialModel.circle, validatorRectangleModel, Set.mem_setOf_eq]
    simp_rw [line_embedding_distance]
    fin_cases i <;> fin_cases j <;>
      norm_num [SpatialModel.circle, validatorRectangleModel, validatorRectangle,
        validatorRadius, percentileNode, line_embedding_distance, lineEmbedding, WithLp.toLp]
  have hm (i : Fin 4) (j : Fin 5) :
      validatorRectangleModel.circleMass i (validatorRadius j) = 1 := by
    simp [SpatialModel.circleMass, hcm]
  have hy (i : Fin 4) (j : Fin 5) (z : Assignment 4) :
      validatorRectangleModel.Y
        (lineEmbedding (percentileNode i + (j.val + 1 : ℚ) / 10)) z = i.val := by
    change validatorRectangleOutcome _ z = _
    fin_cases i <;> fin_cases j <;>
      norm_num [validatorRectangleOutcome, Fin.sum_univ_succ, percentileNode,
        line_embedding_distance]
  have havg (i : Fin 4) (j : Fin 5) (z : Assignment 4) :
      validatorRectangleModel.M i (validatorRadius j) z = i.val := by
    simp only [SpatialModel.M, SpatialModel.average, hm, inv_one, one_mul, hcm,
      integral_dirac, hy]
  have hs (j : Fin 5) (k : Fin 6) :
      validatorRectangleStatistic j k = percentileExample k := by
    unfold validatorRectangleStatistic
    simp_rw [havg]
    rw [(contrast_is_hajek (fun i : Fin 4 => (i.val : ℝ)) k).2.2]
    fin_cases k <;>
      norm_num [contrast4, percentileExample, sixAssignment, bit, Fin.sum_univ_succ]
  have hsfun (j : Fin 5) : validatorRectangleStatistic j = percentileExample :=
    funext (hs j)
  have hsep (i k : Fin 4) (hik : i ≠ k) :
      2 < dist (validatorRectangleModel.node i) (validatorRectangleModel.node k) := by
    change 2 < dist (lineEmbedding (percentileNode i)) (lineEmbedding (percentileNode k))
    rw [line_embedding_distance]
    fin_cases i <;> fin_cases k <;> norm_num at hik <;> norm_num [percentileNode]
  have hsum : (fun k => ∑ j : Fin 5, validatorRectangleStatistic j k) =
      (fun k => 5 * percentileExample k) := by
    funext k
    simp_rw [hs]
    simp
  refine ⟨?_, ?_, ?_, fun _ _ => rfl, havg, hs, ?_, ?_, ?_, ?_, by norm_num⟩
  · intro i x hx
    change dist x (lineEmbedding (percentileNode i)) ≤ 1 at hx
    have hnorm : ‖x - lineEmbedding (percentileNode i)‖ ≤ 1 := by
      simpa only [dist_eq_norm] using hx
    have h0 := (PiLp.norm_apply_le (x - lineEmbedding (percentileNode i)) 0).trans hnorm
    have h1 := (PiLp.norm_apply_le (x - lineEmbedding (percentileNode i)) 1).trans hnorm
    have hi0 : 0 ≤ (percentileNode i : ℝ) := by
      simp only [percentileNode, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]
      positivity
    have hi30 : (percentileNode i : ℝ) ≤ 30 := by
      fin_cases i <;> norm_num [percentileNode]
    simp only [PiLp.sub_apply, lineEmbedding, PiLp.toLp_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Real.norm_eq_abs, sub_zero] at h0 h1
    change -1 ≤ x 0 ∧ x 0 ≤ 31 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1
    rcases abs_le.mp h0 with ⟨h0lo, h0hi⟩
    rcases abs_le.mp h1 with ⟨h1lo, h1hi⟩
    exact ⟨by linarith, by linarith, h1lo, h1hi⟩
  · intro i k hik
    apply Set.disjoint_left.mpr
    intro x hx hxk
    have hi : dist (validatorRectangleModel.node i) x ≤ 1 := by
      simpa only [Set.mem_setOf_eq, dist_comm] using hx
    have hk : dist x (validatorRectangleModel.node k) ≤ 1 := hxk
    have ht := dist_triangle (validatorRectangleModel.node i) x (validatorRectangleModel.node k)
    have hfar := hsep i k hik
    linarith
  · intro i j
    refine ⟨by rw [hm]; norm_num, ?_, ?_⟩
    · rw [hcm]
      simp
    · intro z
      rw [hcm]
      exact integrable_dirac (by simp)
  · intro j
    rw [hsfun]
    exact ⟨interpolated_percentile_counterexample.2.1,
      interpolated_percentile_counterexample.2.2.1,
      interpolated_percentile_counterexample.2.2.2.1⟩
  · rw [hsum]
    exact interpolated_percentile_counterexample.2.2.2.2.1
  · rw [hsum]
    exact interpolated_percentile_counterexample.2.2.2.2.2.1
  · change (uniformLaw (Fin 6)).prob (fun k => outside (-75 / 8) (75 / 8)
      ((fun k => ∑ j : Fin 5, validatorRectangleStatistic j k) k)) = _
    rw [hsum]
    exact interpolated_percentile_counterexample.2.2.2.2.2.2.1

/-- T19's two possible assignments with one treated and one control polygon. -/
def polygonAssignment (k : Fin 2) : Assignment 2 :=
  ![![true, false], ![false, true]] k

/-- T19's zero-radius boundary circle means: the first polygon has blockY,
and the translated second polygon's outcomes are zero for every assignment. -/
def blockBoundaryM (i : Fin 2) (z : Assignment 2) : ℝ :=
  if i = 0 then countMean blockBoundary (fun c => blockY c (z 0)) else 0

/-- T19's full-polygon area means for the same complete outcome schedule. -/
def blockAreaM (i : Fin 2) (z : Assignment 2) : ℝ :=
  if i = 0 then countMean Finset.univ (fun c => blockY c (z 0)) else 0

/-- T19/T20(c), the actual design-based counterexample: both assignments
have one treated polygon; observed 10 has boundary Hajek contrast 0 and
area contrast 9/25. The two corresponding AMRs are 0 and 9/50 under every
law on the complete potential-outcome schedule. -/
theorem boundary_hajek_counterexample :
    (∀ k, treatedCount (polygonAssignment k) = 1) ∧
    (uniformLaw (Fin 2)).mass 0 = 1 / 2 ∧
    hajek blockBoundaryM (polygonAssignment 0) = 0 ∧
    hajek blockAreaM (polygonAssignment 0) = 9 / 25 ∧
    (∀ Q : FiniteLaw (Assignment 2), finiteAMR Q blockBoundaryM = 0 ∧
      finiteAMR Q blockAreaM = 9 / 50) := by
  have hb (i : Fin 2) (z : Assignment 2) : blockBoundaryM i z = 0 := by
    fin_cases i
    · simp only [blockBoundaryM, if_pos rfl]
      cases hz : z 0
      · simp [blockY, bit, hz, countMean]
      · simpa [blockBoundaryM, hz] using boundary_counterexample.2.2.2.1
    · simp [blockBoundaryM]
  have ha (z : Assignment 2) : countMean Finset.univ (fun c => blockY c (z 0)) =
      (9 / 25 : ℝ) * bit (z 0) := by
    cases hz : z 0
    · simpa [hz, bit] using
        boundary_counterexample.2.2.2.2.2.1
    · simpa [hz, bit] using boundary_counterexample.2.2.2.2.1
  have ham (i : Fin 2) (z : Assignment 2) : blockAreaM i z =
      if i = 0 then (9 / 25 : ℝ) * bit (z 0) else 0 := by
    simp only [blockAreaM, ha]
  refine ⟨?_, by norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, uniformLaw], ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;> norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, treatedCount, polygonAssignment]
  · simp_rw [hajek, hb]
    simp
  · simp_rw [hajek, ham]
    norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, polygonAssignment, nTreated, nControl, bit]
  · intro Q
    have hb' (i : Fin 2) (b : Bool) : marginal Q (blockBoundaryM i) i b = 0 := by
      simp only [marginal, hb, expect_const]
    have ha' (i : Fin 2) (b : Bool) : marginal Q (blockAreaM i) i b =
        if i = 0 then (9 / 25 : ℝ) * bit b else 0 := by
      fin_cases i <;> simp [marginal, ham, Function.update_apply, expect_const]
    simp only [finiteAMR, hb', ha']
    norm_num [univ_four, univ_five, univ_six, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton, bit]

/-- T7(6)'s actual normalized sampling probability: a uniform node, radius
and one of that circle's 40000 points, with its own node fixed to condition b.
This is Q_b, distinct from the unweighted sum of four AMRs. -/
def riskSamplingProbability (Q : FiniteLaw (Assignment 4)) (b : Bool) : ℝ :=
  (16 : ℝ)⁻¹ * ∑ i : Fin 4, ∑ j : Fin 4, marginal Q (riskM i j) i b

/-- T7(6): the normalized sampling risks in the complete binary schedule
are 7/400 and 379/40000 under every design, with difference -321/40000. -/
theorem risk_sampling_probabilities (Q : FiniteLaw (Assignment 4)) :
    riskSamplingProbability Q false = 7 / 400 ∧
    riskSamplingProbability Q true = 379 / 40000 ∧
    riskSamplingProbability Q true - riskSamplingProbability Q false = -321 / 40000 := by
  have hm := (summed_risk_counterexample Q).1
  simp only [riskSamplingProbability, hm]
  norm_num [riskBaseline, bit, Fin.sum_univ_succ]

/-- T7(3,5,7): the specified design is independent Bernoulli(1/2), its
observed 1100 has probability 1/16, and the companion schedule gives an
actual Hajek estimate -1 at each radius and observed cumulative estimate -4. -/
theorem risk_design_and_companion_estimates :
    commonBernoulli (uniformLaw (Assignment 4)) (1 / 2) ∧
    (uniformLaw (Assignment 4)).mass ![true, true, false, false] = 1 / 16 ∧
    (∀ j : Fin 4, hajek (fun i z => companionRiskM i j z)
      ![true, true, false, false] = -1) ∧
    (∑ j : Fin 4, hajek (fun i z => companionRiskM i j z)
      ![true, true, false, false]) = -4 := by
  have hb (b : Bool) : (if b then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := by
    cases b <;> norm_num
  have hm := (binary_companion_counterexample (uniformLaw (Assignment 4))).2.1
  have hh (j : Fin 4) : hajek (fun i z => companionRiskM i j z)
      ![true, true, false, false] = -1 := by
    simp only [hajek, hm]
    norm_num [nTreated, nControl, bit, Fin.sum_univ_succ, univ_four]
  refine ⟨?_, ?_, hh, ?_⟩
  · intro z
    simp_rw [hb]
    norm_num [uniformLaw]
  · norm_num [uniformLaw]
  · simp_rw [hh]
    norm_num

/-- T5's actual covariance cutoff sum at b=r=1 uses the given Euclidean
node distances and is 1/8, while the true linearization variance is 1/4.
Thus the effect-range cutoff really omits the nonzero off-diagonal terms. -/
theorem effect_range_covariance_omission :
    ((1 / 2 : ℝ) ^ 2 * ∑ i : Fin 2, ∑ j : Fin 2,
      if dist (lineEmbedding (pairNode i)) (lineEmbedding (pairNode j)) ≤ 1 then
        (uniformLaw (Fin 4)).cov
          (fun k => linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k))
          (fun k => linearizationScore pairM (5 / 4) (1 / 4) j (pairAssignment k))
      else 0) = 1 / 8 ∧
    (uniformLaw (Fin 4)).var (fun k => (1 / 2 : ℝ) * ∑ i : Fin 2,
      linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k)) = 1 / 4 ∧
    (1 / 8 : ℝ) < 1 / 4 := by
  have hs (i : Fin 2) :
      (fun k => linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k)) =
      (fun k => (1 / 2 : ℝ) * (2 * bit (pairAssignment k 0) - 1) *
        (2 * bit (pairAssignment k 1) - 1)) :=
    funext (effect_range_cutoff_counterexample.2.1 i)
  have hc (i j : Fin 2) : (uniformLaw (Fin 4)).cov
      (fun k => linearizationScore pairM (5 / 4) (1 / 4) i (pairAssignment k))
      (fun k => linearizationScore pairM (5 / 4) (1 / 4) j (pairAssignment k)) = 1 / 4 := by
    rw [hs i, hs j]
    norm_num [FiniteLaw.cov, FiniteLaw.expect, uniformLaw, pairAssignment, bit,
      Fin.sum_univ_succ]
  refine ⟨?_, ?_, by norm_num⟩
  · simp_rw [hc, line_embedding_distance]
    norm_num [pairNode, Fin.sum_univ_succ]
  · calc
      _ = (uniformLaw (Fin 4)).var (fun k =>
        (linearizationScore pairM (5 / 4) (1 / 4) 0 (pairAssignment k) +
          linearizationScore pairM (5 / 4) (1 / 4) 1 (pairAssignment k)) / 2) := by
        congr 1
        funext k
        simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.succ_zero_eq_one]
        ring
      _ = 1 / 4 := effect_range_cutoff_counterexample.2.2.2.2.1

/-- T28 finite lemma (iv)'s good-denominator probability bound, with the
actual independent Bernoulli fraction, not an assumed concentration premise. -/
theorem bernoulli_good_denominator_bound {N : ℕ} (hN : 0 < N)
    (Q : FiniteLaw (Assignment N)) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hQ : commonBernoulli Q p) :
    Q.prob (fun z => nTreated z / N < p / 2 ∨
      1 - nTreated z / N < (1 - p) / 2) ≤
      4 * p * (1 - p) / ((N : ℝ) * (min p (1 - p)) ^ 2) := by
  have hm : 0 < min p (1 - p) := lt_min hp (sub_pos.mpr hp')
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hch := finite_chebyshev Q (fun z => nTreated z / N)
    (min p (1 - p) / 2) (half_pos hm)
  rw [(bernoulli_fraction_moments hN Q p hp hp' hQ).1,
    (bernoulli_fraction_moments hN Q p hp hp' hQ).2] at hch
  calc
    _ ≤ Q.prob (fun z => min p (1 - p) / 2 ≤ |nTreated z / N - p|) := by
      apply prob_mono
      intro z hz
      rcases hz with hz | hz
      · have ha := neg_le_abs (nTreated z / N - p)
        have hmin := min_le_left p (1 - p)
        linarith
      · have ha := le_abs_self (nTreated z / N - p)
        have hmin := min_le_right p (1 - p)
        linarith
    _ ≤ (p * (1 - p) / N) / (min p (1 - p) / 2) ^ 2 := hch
    _ = _ := by
      field_simp [hN', ne_of_gt hm]
      ring

/-- T28 finite lemma (i)'s aggregate identity: the two normalized
numerators have means p r_1 and (1-p) r_0, for every circle-outcome schedule. -/
theorem common_numerator_means {N : ℕ} (Q : FiniteLaw (Assignment N))
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hQ : commonBernoulli Q p)
    (M : Fin N → Assignment N → ℝ) :
    ∀ b, Q.expect (normalizedNumerator M b) =
      (if b then p else 1 - p) * marginalMean Q M b := by
  have hind (b : Bool) (i : Fin N) (z : Assignment N) :
      (if z i = b then (1 : ℝ) else 0) * M i z =
      (if b then bit (z i) * M i z else (1 - bit (z i)) * M i z) := by
    cases b <;> cases z i <;> norm_num [bit]
  intro b
  change Q.expect (fun z => (N : ℝ)⁻¹ * ∑ i,
    (if z i = b then (1 : ℝ) else 0) * M i z) = _
  cases b
  · simp only [hind, Bool.false_eq_true, ↓reduceIte]
    rw [expect_mul_const, expect_sum]
    simp_rw [(bernoulli_numerator_identity Q (fun _ => p) (fun _ => ⟨hp, hp'⟩)
      hQ M _).2]
    simp only [marginalMean, ← Finset.mul_sum]
    ring
  · simp only [hind, ↓reduceIte]
    rw [expect_mul_const, expect_sum]
    simp_rw [(bernoulli_numerator_identity Q (fun _ => p) (fun _ => ⟨hp, hp'⟩)
      hQ M _).1]
    simp only [marginalMean, ← Finset.mul_sum]
    ring

/-- T28 finite lemma (iv)'s exact ratio decomposition when both arms are
nonempty: Hajek minus AMR is (S_1/U-r_1)-(S_0/(1-U)-r_0). -/
theorem hajek_ratio_decomposition {N : ℕ} (hN : 0 < N)
    (Q : FiniteLaw (Assignment N)) (M : Fin N → Assignment N → ℝ)
    (z : Assignment N) (h₁ : nTreated z ≠ 0) (h₀ : nControl z ≠ 0) :
    hajek M z - finiteAMR Q M =
      (normalizedNumerator M true z / (nTreated z / N) - marginalMean Q M true) -
      (normalizedNumerator M false z / (1 - nTreated z / N) - marginalMean Q M false) := by
  have hind (b : Bool) (i : Fin N) :
      (if z i = b then (1 : ℝ) else 0) * M i z =
      (if b then bit (z i) * M i z else (1 - bit (z i)) * M i z) := by
    cases b <;> cases z i <;> norm_num [bit]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  have hdiff : (N : ℝ) - nTreated z ≠ 0 := h₀
  simp only [hajek, finiteAMR, normalizedNumerator, marginalMean, hind,
    Bool.false_eq_true, ↓reduceIte, Finset.sum_sub_distrib, nControl]
  field_simp [hNr, h₁, hdiff]
  ring

/-- T20(a)'s boundary for any finite raster polygon R: cells with at least
one of their eight integer-grid neighbours outside R (p. 145, corrected). -/
def rasterBoundary (R : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) := by
  classical
  exact R.filter (fun x => ∃ a b : Fin 3,
    (a.val ≠ 1 ∨ b.val ≠ 1) ∧
    (x.1 + a.val - 1, x.2 + b.val - 1) ∉ R)

/-- T20(a)'s corrected edge functional at radius zero, using boundary cells. -/
def rasterEdgeZeroAverage (R : Finset (ℤ × ℤ)) (Y : (ℤ × ℤ) → ℝ) : ℝ :=
  countMean (rasterBoundary R) Y

/-- T20(a)'s within-polygon functional, using every cell in R. -/
def rasterAreaAverage (R : Finset (ℤ × ℤ)) (Y : (ℤ × ℤ) → ℝ) : ℝ :=
  countMean R Y

/-- T20(a), for an arbitrary raster polygon with nonempty boundary: the
two summaries normalize the boundary sum and the full-polygon sum separately.
The boundary predicate is exactly the eight-neighbour definition. -/
theorem raster_zero_summaries (R : Finset (ℤ × ℤ)) (Y : (ℤ × ℤ) → ℝ)
    (hbd : (rasterBoundary R).Nonempty) :
    (∀ x, x ∈ rasterBoundary R ↔ x ∈ R ∧ ∃ a b : Fin 3,
      (a.val ≠ 1 ∨ b.val ≠ 1) ∧ (x.1 + a.val - 1, x.2 + b.val - 1) ∉ R) ∧
    rasterEdgeZeroAverage R Y =
      (∑ x ∈ rasterBoundary R, Y x) / (rasterBoundary R).card ∧
    rasterAreaAverage R Y = (∑ x ∈ R, Y x) / R.card := by
  classical
  exact ⟨fun x => by simp only [rasterBoundary, Finset.mem_filter], rfl, rfl⟩

/-- T19's entire unit-cell raster: indices (u,v) represent centres
(u+.5,v+.5) in [0,20]×[0,10], so there are 200 cells. -/
abbrev PolygonRasterCell := Fin 20 × Fin 10

/-- T19's two polygons have left edges 2 and 12, respectively. -/
def rasterPolygonLeft (i : Fin 2) : ℕ := if i = 0 then 2 else 12

/-- The cells whose half-integer centres lie in T19's closed polygons
[2,7]×[2,7] and [12,17]×[2,7]. -/
def rasterPolygonCells (i : Fin 2) : Finset PolygonRasterCell :=
  Finset.univ.filter (fun c => rasterPolygonLeft i ≤ c.1.val ∧
    c.1.val < rasterPolygonLeft i + 5 ∧ 2 ≤ c.2.val ∧ c.2.val < 7)

/-- T19's inner eight-neighbour boundary cells, the outer row or column
of each 5×5 polygon. The theorem below verifies this selector's neighbour rule. -/
def rasterPolygonBoundary (i : Fin 2) : Finset PolygonRasterCell :=
  (rasterPolygonCells i).filter (fun c => c.1.val = rasterPolygonLeft i ∨
    c.1.val = rasterPolygonLeft i + 4 ∨ c.2.val = 2 ∨ c.2.val = 6)

/-- T19's complete potential outcomes on all 200 cells: z_T in the nine
central treated-polygon cells with centres 3.5,4.5,5.5, zero in the other 191. -/
def polygonRasterOutcome (c : PolygonRasterCell) (z : Assignment 2) : ℝ :=
  if 3 ≤ c.1.val ∧ c.1.val ≤ 5 ∧ 3 ≤ c.2.val ∧ c.2.val ≤ 5 then bit (z 0) else 0

/-- T19's actual zero-radius edge means on the full raster. -/
def polygonRasterEdgeM (i : Fin 2) (z : Assignment 2) : ℝ :=
  countMean (rasterPolygonBoundary i) (fun c => polygonRasterOutcome c z)

/-- T19's actual within-polygon area means on that same raster. -/
def polygonRasterAreaM (i : Fin 2) (z : Assignment 2) : ℝ :=
  countMean (rasterPolygonCells i) (fun c => polygonRasterOutcome c z)

/-- T19's full raster witness under the specified independent Bernoulli
design: all 200 potential outcomes are defined, the polygon and boundary
counts are 25 and 16, observed 10 has probability 1/4, edge Hajek is zero,
area Hajek is 9/25, and the actual two AMRs are zero and 9/50. -/
theorem polygon_raster_counterexample :
    (Finset.univ : Finset PolygonRasterCell).card = 200 ∧
    (∀ i, (rasterPolygonCells i).card = 25 ∧ (rasterPolygonBoundary i).card = 16) ∧
    (∀ i c, c ∈ rasterPolygonCells i → (c ∈ rasterPolygonBoundary i ↔
      ∃ a b : Fin 3, (a.val ≠ 1 ∨ b.val ≠ 1) ∧
        ((c.1.val : ℤ) + a.val - 1 < rasterPolygonLeft i ∨
         (rasterPolygonLeft i + 5 : ℤ) ≤ (c.1.val : ℤ) + a.val - 1 ∨
         (c.2.val : ℤ) + b.val - 1 < 2 ∨ 7 ≤ (c.2.val : ℤ) + b.val - 1))) ∧
    (∀ c z, polygonRasterOutcome c z = 0 ∨ polygonRasterOutcome c z = 1) ∧
    (∀ i z, polygonRasterEdgeM i z = 0) ∧
    (∀ i z, polygonRasterAreaM i z = if i = 0 then (9 / 25 : ℝ) * bit (z 0) else 0) ∧
    commonBernoulli (uniformLaw (Assignment 2)) (1 / 2) ∧
    (uniformLaw (Assignment 2)).mass ![true, false] = 1 / 4 ∧
    hajek polygonRasterEdgeM ![true, false] = 0 ∧
    hajek polygonRasterAreaM ![true, false] = 9 / 25 ∧
    finiteAMR (uniformLaw (Assignment 2)) polygonRasterEdgeM = 0 ∧
    finiteAMR (uniformLaw (Assignment 2)) polygonRasterAreaM = 9 / 50 ∧
    (0 : ℝ) ≠ 9 / 25 := by
  classical
  have hcard (i : Fin 2) : (rasterPolygonCells i).card = 25 ∧
      (rasterPolygonBoundary i).card = 16 := by
    fin_cases i <;> decide +kernel
  have hcentral (i : Fin 2) : ((rasterPolygonCells i).filter
      (fun c => 3 ≤ c.1.val ∧ c.1.val ≤ 5 ∧ 3 ≤ c.2.val ∧ c.2.val ≤ 5)).card =
        if i = 0 then 9 else 0 := by
    fin_cases i <;> decide +kernel
  have he (i : Fin 2) (z : Assignment 2) : polygonRasterEdgeM i z = 0 := by
    unfold polygonRasterEdgeM countMean
    have hz : ∑ c ∈ rasterPolygonBoundary i, polygonRasterOutcome c z = 0 := by
      apply Finset.sum_eq_zero
      intro c hc
      have hR := (Finset.mem_filter.mp (Finset.mem_filter.mp hc).1).2
      have hbd := (Finset.mem_filter.mp hc).2
      unfold polygonRasterOutcome
      split_ifs with hresp
      · fin_cases i <;> norm_num [rasterPolygonLeft] at hR hbd <;> omega
      · rfl
    rw [hz, zero_div]
  have ha (i : Fin 2) (z : Assignment 2) : polygonRasterAreaM i z =
      if i = 0 then (9 / 25 : ℝ) * bit (z 0) else 0 := by
    simp only [polygonRasterAreaM, countMean, polygonRasterOutcome, Finset.sum_ite,
      Finset.sum_const, nsmul_eq_mul, hcentral, (hcard i).1]
    fin_cases i <;> norm_num <;> ring
  have hae (i : Fin 2) (b : Bool) : marginal (uniformLaw (Assignment 2))
      (polygonRasterAreaM i) i b = if i = 0 then (9 / 25 : ℝ) * bit b else 0 := by
    fin_cases i <;> simp [marginal, ha, expect_const]
  have hee (i : Fin 2) (b : Bool) : marginal (uniformLaw (Assignment 2))
      (polygonRasterEdgeM i) i b = 0 := by simp [marginal, he, expect_const]
  refine ⟨by decide, hcard, ?_, ?_, he, ha, ?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · decide +kernel
  · intro c z
    unfold polygonRasterOutcome
    split_ifs
    · cases z 0 <;> norm_num [bit]
    · simp
  · intro z
    have hb (b : Bool) : (if b then (1 / 2 : ℝ) else 1 - 1 / 2) = 1 / 2 := by
      cases b <;> norm_num
    simp_rw [hb]
    norm_num [uniformLaw]
  · norm_num [uniformLaw]
  · simp only [hajek, he]
    simp
  · simp only [hajek, ha]
    norm_num [nTreated, nControl, bit]
  · simp only [finiteAMR, hee]
    simp
  · simp only [finiteAMR, hae]
    norm_num [bit]

/-- T18's complete finite-raster outcome schedule:
Y_c^(a)(z)=Y_0c+a∑_j z_j f(r_jc), where r_jc are the supplied centroid distances.
This is the finite-cell specialization of additiveOutcome, not a new effect model. -/
def toyRasterOutcome {C : ℕ} (a : ℝ) (base : Fin C → ℝ)
    (r : Fin 4 → Fin C → ℝ) (c : Fin C) (z : Assignment 4) : ℝ :=
  base c + ∑ j, bit (z j) * (a * toyKernel (r j c))

/-- T18's actual AMR with normalized raster-circle weights: average the
marginal point response over cells and then uniformly over the four nodes.
The weights and centroid distances are inputs. -/
def toyRasterAMR {C : ℕ} (Q : FiniteLaw (Assignment 4)) (a : ℝ)
    (base : Fin C → ℝ) (r w : Fin 4 → Fin C → ℝ) : ℝ :=
  (1 / 4 : ℝ) * ∑ i, ∑ c, w i c *
    (marginal Q (toyRasterOutcome a base r c) i true -
      marginal Q (toyRasterOutcome a base r c) i false)

/-- T18(a–c), connecting the full potential-outcome schedule to its actual
design-marginal AMR: own-node switching and its marginalized response equal
a f(r_ic), the weighted AMR has the claimed formula, amplitude three scales
it by three, and the amplitude-one AMR is strictly greater than -384/437. -/
theorem toy_raster_amr_formula {C : ℕ} (Q : FiniteLaw (Assignment 4))
    (base : Fin C → ℝ) (r w : Fin 4 → Fin C → ℝ)
    (hw : ∀ i c, 0 ≤ w i c) (hs : ∀ i, ∑ c, w i c = 1)
    (hr : ∀ i c, 0 ≤ r i c) :
    (∀ a i c z, toyRasterOutcome a base r c (Function.update z i true) -
      toyRasterOutcome a base r c (Function.update z i false) = a * toyKernel (r i c)) ∧
    (∀ a i c, marginal Q (toyRasterOutcome a base r c) i true -
      marginal Q (toyRasterOutcome a base r c) i false = a * toyKernel (r i c)) ∧
    (∀ a, toyRasterAMR Q a base r w =
      (1 / 4 : ℝ) * ∑ i, ∑ c, w i c * (a * toyKernel (r i c))) ∧
    toyRasterAMR Q 3 base r w = 3 * toyRasterAMR Q 1 base r w ∧
    -(384 / 437 : ℝ) < toyRasterAMR Q 1 base r w := by
  have hswitch (a : ℝ) (i : Fin 4) (c : Fin C) (z : Assignment 4) :
      toyRasterOutcome a base r c (Function.update z i true) -
      toyRasterOutcome a base r c (Function.update z i false) = a * toyKernel (r i c) := by
    simpa only [toyRasterOutcome, additiveOutcome] using
      additive_switch (fun _ => base c) (fun j _ => a * toyKernel (r j c)) i (0 : Plane) z
  have hpoint (a : ℝ) (i : Fin 4) (c : Fin C) :
      marginal Q (toyRasterOutcome a base r c) i true -
      marginal Q (toyRasterOutcome a base r c) i false = a * toyKernel (r i c) := by
    unfold marginal
    rw [← expect_sub]
    have he : (fun z => toyRasterOutcome a base r c (Function.update z i true) -
        toyRasterOutcome a base r c (Function.update z i false)) =
        (fun _ => a * toyKernel (r i c)) := funext (hswitch a i c)
    rw [he, expect_const]
  have hformula (a : ℝ) : toyRasterAMR Q a base r w =
      (1 / 4 : ℝ) * ∑ i, ∑ c, w i c * (a * toyKernel (r i c)) := by
    simp only [toyRasterAMR, hpoint]
  refine ⟨hswitch, hpoint, hformula, ?_, ?_⟩
  · rw [hformula, hformula]
    simpa only [one_mul] using (toy_amplitude_and_bound w r hw hs hr).1
  · rw [hformula]
    simpa only [one_mul] using (toy_amplitude_and_bound w r hw hs hr).2

end

noncomputable section

/-- Independent products of the two fair signs within each replicated pair
have mean zero and covariance one on the diagonal, zero between pairs. -/
theorem replicated_sign_moments {G : Type*} [Fintype G] [DecidableEq G] :
    let Q := uniformLaw ((G × Fin 2) → Bool)
    let T := fun (g : G) (z : (G × Fin 2) → Bool) =>
      (2 * bit (z (g, 0)) - 1) * (2 * bit (z (g, 1)) - 1)
    (∀ g, Q.expect (T g) = 0) ∧
    (∀ g h, Q.cov (T g) (T h) = if g = h then 1 else 0) := by
  classical
  dsimp only
  let Q := uniformLaw ((G × Fin 2) → Bool)
  let T := fun (g : G) (z : (G × Fin 2) → Bool) =>
      (2 * bit (z (g, 0)) - 1) * (2 * bit (z (g, 1)) - 1)
  have hmean (g : G) : Q.expect (T g) = 0 := by
    rw [uniform_average_update (T g) (g, 0)]
    have hz (z : (G × Fin 2) → Bool) :
        (T g (Function.update z (g, 0) false) +
          T g (Function.update z (g, 0) true)) / 2 = 0 := by
      simp [T, bit, Function.update_of_ne, Prod.mk.injEq]
      ring
    simp_rw [hz]
    exact expect_const Q _
  refine ⟨hmean, ?_⟩
  intro g h
  change Q.cov (T g) (T h) = if g = h then 1 else 0
  rw [covariance_raw, hmean, hmean]
  simp only [mul_zero, sub_zero]
  by_cases hgh : g = h
  · subst h
    have hz (z : (G × Fin 2) → Bool) : T g z * T g z = 1 := by
      cases ha : z (g, 0) <;> cases hb : z (g, 1) <;> norm_num [T, bit, ha, hb]
    simp_rw [hz]
    exact expect_const Q 1
  · rw [uniform_average_update (fun z => T g z * T h z) (g, 0)]
    have hz (z : (G × Fin 2) → Bool) :
        (T g (Function.update z (g, 0) false) * T h (Function.update z (g, 0) false) +
          T g (Function.update z (g, 0) true) * T h (Function.update z (g, 0) true)) / 2 = 0 := by
      simp [T, bit, Function.update_of_ne, Prod.mk.injEq, hgh, Ne.symm hgh]
      ring
    simp_rw [hz]
    simp [hgh, expect_const]

/-- T5 replication: for N=2M the exact variance is 1/(2N), while the
diagonal covariance sum is 1/(4N), for every M≥1. This concerns the
linearization and makes no false claim about the exact Hajek ratio variance. -/
theorem replicated_cutoff_variance (M : ℕ) (hM : 0 < M) :
    (uniformLaw ((Fin M × Fin 2) → Bool)).var
      (fun z => (2 * M : ℝ)⁻¹ * ∑ i, replicatedPairScore i z) =
        1 / (2 * (2 * M)) ∧
    (2 * M : ℝ)⁻¹ ^ 2 * ∑ i,
      (uniformLaw ((Fin M × Fin 2) → Bool)).var (replicatedPairScore i) =
        1 / (4 * (2 * M)) := by
  classical
  let Q := uniformLaw ((Fin M × Fin 2) → Bool)
  let T (g : Fin M) (z : (Fin M × Fin 2) → Bool) :=
    (2 * bit (z (g, 0)) - 1) * (2 * bit (z (g, 1)) - 1)
  have hc (g h : Fin M) : Q.cov (T g) (T h) = if g = h then 1 else 0 :=
    (replicated_sign_moments (G := Fin M)).2 g h
  have hs (z : (Fin M × Fin 2) → Bool) :
      (∑ i, replicatedPairScore i z) = ∑ g, T g z := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Finset.univ_unique,
      Finset.sum_singleton, replicatedPairScore]
    apply Finset.sum_congr rfl
    intro g _
    dsimp [T]
    ring
  have hv (i : Fin M × Fin 2) : Q.var (replicatedPairScore i) = 1 / 4 := by
    have he : replicatedPairScore i = (fun z => (1 / 2 : ℝ) * T i.1 z) := by
      funext z
      dsimp [replicatedPairScore, T]
      ring
    rw [he, variance_mul_const]
    change (1 / 2 : ℝ) ^ 2 * Q.cov (T i.1) (T i.1) = 1 / 4
    rw [hc]
    norm_num
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hM)
  constructor
  · simp_rw [hs]
    rw [variance_mul_const, variance_sum_covariances]
    change (2 * M : ℝ)⁻¹ ^ 2 * (∑ g : Fin M, ∑ h : Fin M, Q.cov (T g) (T h)) = _
    simp_rw [hc]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp <;> ring
  · change (2 * M : ℝ)⁻¹ ^ 2 * ∑ i, Q.var (replicatedPairScore i) = _
    simp_rw [hv]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp <;> ring

/-- Finite expectations can be collected over the distinct values of f. -/
theorem expect_value_fibres {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (f : Ω → ℝ) :
    Q.expect f = ∑ a ∈ Finset.univ.image f, a * Q.prob (fun z => f z = a) := by
  classical
  let A := Finset.univ.image f
  have hd (z : Ω) : f z = ∑ a ∈ A, a * (if f z = a then (1 : ℝ) else 0) := by
    have hz : f z ∈ A := Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
    simp [mul_ite, eq_comm, hz]
  calc
    _ = Q.expect (fun z => ∑ a ∈ A, a * (if f z = a then 1 else 0)) :=
      congrArg Q.expect (funext hd)
    _ = _ := by
      unfold FiniteLaw.expect
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [prob_as_expect]
      unfold FiniteLaw.expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

/-- Independence of all finite value fibres makes covariance zero; this is
a finite-sum consequence, without importing a measure-independence axiom. -/
theorem covariance_zero_of_fibres {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (f g : Ω → ℝ)
    (h : ∀ a b : ℝ, Q.prob (fun z => f z = a ∧ g z = b) =
      Q.prob (fun z => f z = a) * Q.prob (fun z => g z = b)) : Q.cov f g = 0 := by
  classical
  let A := Finset.univ.image f
  let B := Finset.univ.image g
  have hd (z : Ω) : f z * g z =
      ∑ a ∈ A, ∑ b ∈ B, a * b * (if f z = a ∧ g z = b then (1 : ℝ) else 0) := by
    have hf : f z ∈ A := Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
    have hg : g z ∈ B := Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
    have hh (a : ℝ) : (∑ b ∈ B, a * b *
        (if f z = a ∧ g z = b then (1 : ℝ) else 0)) =
        if f z = a then a * g z else 0 := by
      by_cases ha : f z = a
      · simp [ha, mul_ite, eq_comm, hg]
      · simp [ha]
    simp_rw [hh]
    simp [eq_comm, hf]
  have hr : Q.expect (fun z => f z * g z) =
      ∑ a ∈ A, ∑ b ∈ B, a * b * Q.prob (fun z => f z = a ∧ g z = b) := by
    calc
      _ = Q.expect (fun z => ∑ a ∈ A, ∑ b ∈ B,
        a * b * (if f z = a ∧ g z = b then (1 : ℝ) else 0)) :=
          congrArg Q.expect (funext hd)
      _ = _ := by
        unfold FiniteLaw.expect
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        rw [prob_as_expect]
        unfold FiniteLaw.expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        ring
  rw [covariance_raw, hr, expect_value_fibres Q f, expect_value_fibres Q g]
  simp_rw [h]
  rw [Finset.sum_mul_sum]
  suffices he : (∑ a ∈ A, ∑ b ∈ B, a * b *
      (Q.prob (fun z => f z = a) * Q.prob (fun z => g z = b))) =
      ∑ a ∈ A, ∑ b ∈ B,
        (a * Q.prob (fun z => f z = a)) * (b * Q.prob (fun z => g z = b)) by
    exact sub_eq_zero.mpr he
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Bounded outcomes give a design variance bound H². -/
theorem variance_le_bound_sq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (f : Ω → ℝ) (H : ℝ) (hH : 0 ≤ H) (hf : ∀ z, |f z| ≤ H) : Q.var f ≤ H ^ 2 := by
  have hsq (z : Ω) : f z * f z ≤ H ^ 2 := by
    nlinarith [hf z, abs_nonneg (f z), sq_abs (f z)]
  have he : Q.expect (fun z => f z * f z) ≤ H ^ 2 := by
    calc
      _ ≤ Q.expect (fun _ => H ^ 2) := Finset.sum_le_sum
        (fun z _ => mul_le_mul_of_nonneg_left (hsq z) (Q.nonneg z))
      _ = _ := expect_const Q _
  unfold FiniteLaw.var
  rw [covariance_raw]
  nlinarith [sq_nonneg (Q.expect f)]

/-- Two variables bounded by H have covariance at most H². -/
theorem covariance_le_bound_sq {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (f g : Ω → ℝ) (H : ℝ) (hH : 0 ≤ H)
    (hf : ∀ z, |f z| ≤ H) (hg : ∀ z, |g z| ≤ H) : Q.cov f g ≤ H ^ 2 := by
  have hc : 2 * Q.cov f g ≤ Q.var f + Q.var g := by
    calc
      _ = Q.expect (fun z => 2 * ((f z - Q.expect f) * (g z - Q.expect g))) :=
        (expect_mul_const Q 2 _).symm
      _ ≤ Q.expect (fun z => (f z - Q.expect f) ^ 2 + (g z - Q.expect g) ^ 2) := by
        apply Finset.sum_le_sum
        intro z _
        apply mul_le_mul_of_nonneg_left _ (Q.nonneg z)
        nlinarith [sq_nonneg ((f z - Q.expect f) - (g z - Q.expect g))]
      _ = _ := by simp only [expect_add, FiniteLaw.var, FiniteLaw.cov, pow_two]
  have hf' := variance_le_bound_sq Q f H hH hf
  have hg' := variance_le_bound_sq Q g H hH hg
  linarith

/-- T28 finite lemma (iii): bounded pairs and degree D imply the stated
finite variance bound on either normalized numerator. -/
theorem dependency_numerator_variance_bound {N : ℕ} (hN : 0 < N)
    (Q : FiniteLaw (Assignment N)) (M : Fin N → Assignment N → ℝ)
    (H : ℝ) (D : ℕ) (hH : 0 ≤ H) (hbound : ∀ i z, |M i z| ≤ H)
    (hdep : boundedPairDependency Q M D) (b : Bool) :
    Q.var (normalizedNumerator M b) ≤ H ^ 2 * (D + 1) / N := by
  classical
  let V (i : Fin N) (z : Assignment N) := (if z i = b then (1 : ℝ) else 0) * M i z
  have hV (i : Fin N) (z : Assignment N) : |V i z| ≤ H := by
    by_cases hz : z i = b
    · simpa [V, hz] using hbound i z
    · simpa [V, hz] using hH
  obtain ⟨G, hsym, hdegree, hindep⟩ := hdep
  have hzero (i j : Fin N) (hne : i ≠ j) (hnot : ¬ G i j) : Q.cov (V i) (V j) = 0 := by
    apply covariance_zero_of_fibres Q (V i) (V j)
    intro x y
    let P (u : Fin N → Bool × ℝ) := (if (u i).1 = b then (1 : ℝ) else 0) * (u i).2 = x
    let R (u : Fin N → Bool × ℝ) := (if (u j).1 = b then (1 : ℝ) else 0) * (u j).2 = y
    have hP : dependsOn P {i} := by
      intro u v huv
      have he := huv i (by simp)
      simp only [P, he]
    have hR : dependsOn R {j} := by
      intro u v huv
      have he := huv j (by simp)
      simp only [R, he]
    have hh := hindep {i} {j} (by simp [hne]) (by simpa using hnot) P R hP hR
    exact hh
  have hrow (i : Fin N) : (∑ j, Q.cov (V i) (V j)) ≤ H ^ 2 * (D + 1) := by
    let A := Finset.univ.filter (fun j => j = i ∨ G i j)
    let B := Finset.univ.filter (fun j => j ≠ i ∧ G i j)
    have hset : A = insert i B := by
      ext j
      by_cases hji : j = i
      · simp [A, B, hji]
      · simp [A, B, hji]
    have hi : i ∉ B := by simp [B]
    have hcard : A.card ≤ D + 1 := by
      rw [hset, Finset.card_insert_of_notMem hi]
      have hh := hdegree i
      change B.card ≤ D at hh
      omega
    calc
      _ ≤ ∑ j : Fin N, if j = i ∨ G i j then H ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j = i ∨ G i j
        · rw [if_pos hj]
          exact covariance_le_bound_sq Q (V i) (V j) H hH (hV i) (hV j)
        · have hne : i ≠ j := by intro he; exact hj (Or.inl he.symm)
          have hnot : ¬ G i j := fun hg => hj (Or.inr hg)
          rw [if_neg hj, hzero i j hne hnot]
      _ = (A.card : ℝ) * H ^ 2 := by
        simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul, A]
      _ ≤ H ^ 2 * (D + 1) := by
        have hh : (A.card : ℝ) ≤ D + 1 := by exact_mod_cast hcard
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (sq_nonneg H)
  have hsum : (∑ i, ∑ j, Q.cov (V i) (V j)) ≤ (N : ℝ) * (H ^ 2 * (D + 1)) := by
    calc
      _ ≤ ∑ _i : Fin N, H ^ 2 * (D + 1) := Finset.sum_le_sum (fun i _ => hrow i)
      _ = _ := by simp
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  change Q.var (fun z => (N : ℝ)⁻¹ * ∑ i, V i z) ≤ _
  rw [variance_mul_const, variance_sum_covariances]
  calc
    _ ≤ (N : ℝ)⁻¹ ^ 2 * ((N : ℝ) * (H ^ 2 * (D + 1))) :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := by field_simp <;> ring

/-- The four nodes (0,0),(2,0),(4,0),(6,0) in T9(i–ii). -/
def bandwidthSpatialNode (i : Fin 4) : ℚ := 2 * i.val

/-- The field in T9 is the plane; outcomes are 0,2,4,6 in the disjoint
closed radius-3/10 discs and zero elsewhere. -/
def bandwidthSpatialOutcome (x : Plane) (_z : Assignment 4) : ℝ :=
  ∑ i : Fin 4, if dist x (lineEmbedding (bandwidthSpatialNode i)) ≤ 3 / 10
    then 2 * (i.val : ℝ) else 0

/-- Explicit suitable counting measure: each node and its three rightward
points at distances .1,.2,.3. The outcome schedule is defined on the full plane. -/
def bandwidthSpatialMeasure : Measure Plane :=
  ∑ a : Fin 4 × Fin 4,
    Measure.dirac (lineEmbedding (bandwidthSpatialNode a.1 + (a.2.val : ℚ) / 10))

/-- The complete spatial object for T9's grid-position example. -/
def bandwidthSpatialModel : SpatialModel 4 where
  field := Set.univ
  node i := lineEmbedding (bandwidthSpatialNode i)
  node_mem _ := Set.mem_univ _
  ζ := bandwidthSpatialMeasure
  Y := bandwidthSpatialOutcome

/-- The three radii .1,.2,.3 in the two grids of T9(i–ii). -/
def bandwidthSpatialRadius (j : Fin 3) : ℝ := (j.val + 1 : ℝ) / 10

/-- T9's spatial construction has actual circle integrals 0,2,4,6 at
all three radii, with mass one and integrable outcomes on each circle;
the Euclidean distances between its nodes are 2|i-j|. -/
theorem bandwidth_spatial_realization :
    (∀ i j, dist (bandwidthSpatialModel.node i) (bandwidthSpatialModel.node j) =
      |2 * (i : ℝ) - 2 * (j : ℝ)|) ∧
    (∀ i : Fin 4, ∀ j : Fin 3,
      bandwidthSpatialModel.circleMass i (bandwidthSpatialRadius j) = 1 ∧
      bandwidthSpatialModel.circleMeasure i (bandwidthSpatialRadius j) Set.univ ≠ ⊤ ∧
      ∀ z, Integrable (fun x => bandwidthSpatialModel.Y x z)
        (bandwidthSpatialModel.circleMeasure i (bandwidthSpatialRadius j))) ∧
    (∀ i : Fin 4, ∀ j : Fin 3, ∀ z,
      bandwidthSpatialModel.M i (bandwidthSpatialRadius j) z = 2 * (i : ℝ)) := by
  classical
  have hcm (i : Fin 4) (j : Fin 3) :
      bandwidthSpatialModel.circleMeasure i (bandwidthSpatialRadius j) =
        Measure.dirac (lineEmbedding (bandwidthSpatialNode i + (j.val + 1 : ℚ) / 10)) := by
    unfold SpatialModel.circleMeasure bandwidthSpatialModel bandwidthSpatialMeasure
    simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Measure.restrict_add,
      Measure.restrict_zero, restrict_dirac]
    simp only [SpatialModel.circle, bandwidthSpatialModel, Set.mem_setOf_eq]
    simp_rw [line_embedding_distance]
    fin_cases i <;> fin_cases j <;>
      norm_num [SpatialModel.circle, bandwidthSpatialModel, bandwidthSpatialRadius,
        bandwidthSpatialNode, line_embedding_distance, lineEmbedding, WithLp.toLp]
  have hm (i : Fin 4) (j : Fin 3) :
      bandwidthSpatialModel.circleMass i (bandwidthSpatialRadius j) = 1 := by
    simp [SpatialModel.circleMass, hcm]
  have hy (i : Fin 4) (j : Fin 3) (z : Assignment 4) :
      bandwidthSpatialModel.Y
        (lineEmbedding (bandwidthSpatialNode i + (j.val + 1 : ℚ) / 10)) z = 2 * i.val := by
    change bandwidthSpatialOutcome _ z = _
    fin_cases i <;> fin_cases j <;>
      norm_num [bandwidthSpatialOutcome, Fin.sum_univ_succ, bandwidthSpatialNode,
        line_embedding_distance]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    simp [bandwidthSpatialModel, line_embedding_distance, bandwidthSpatialNode]
  · intro i j
    refine ⟨hm i j, ?_, ?_⟩
    · rw [hcm]; simp
    · intro z
      rw [hcm]
      exact integrable_dirac (by simp)
  · intro i j z
    simp only [SpatialModel.M, SpatialModel.average, hm, inv_one, one_mul,
      hcm, integral_dirac, hy]

/-- Two far-apart rectangular intervention polygons used to realize T16:
[a,a+1]×[-1,1], where a=0 or 100. This is their full boundary. -/
def donutPolygonBoundary (a : ℝ) : Set Plane :=
  {x | a ≤ x 0 ∧ x 0 ≤ a + 1 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1 ∧
    (x 0 = a ∨ x 0 = a + 1 ∨ x 1 = -1 ∨ x 1 = 1)}


/-- Cell centroids just to the right of each rectangle: the closest boundary
point is its right edge on the x-axis. The eight cells are nonmissing. -/
def donutSpatialCell (i : Fin 2) (c : Fin 4) : Plane :=
  WithLp.toLp 2 ![100 * (i : ℝ) + 1 + bufferCellDistance c, 0]

/-- Full potential outcomes for the eight cells in T16: treatment at the
first polygon activates its listed outcomes; the second polygon always has zero. -/
def donutSpatialY (ic : Fin 2 × Fin 4) (z : Assignment 2) : ℝ :=
  if ic.1 = 0 then bit (z 0) * bufferCellOutcome ic.2 else 0

/-- Distance from a nonmissing cell to a polygon boundary (the package's
polygon-buffer convention, pp. 145 and T16). -/
def donutSpatialDistance (i : Fin 2) (ic : Fin 2 × Fin 4) : ℝ :=
  Metric.infDist (donutSpatialCell ic.1 ic.2) (donutPolygonBoundary (100 * (i : ℝ)))

/-- An actual polygon buffer selects every nonmissing cell with boundary
distance at most r, including cells inside or on the polygon. -/
def donutSpatialBuffer (i : Fin 2) (r : ℝ) : Finset (Fin 2 × Fin 4) :=
  Finset.univ.filter (fun ic => donutSpatialDistance i ic ≤ r)

/-- Exact polygon-to-cell geometry for T16: own-polygon distances are
0,19/8,27/8,35/8; the other polygon is more than five units away. -/
theorem donut_spatial_distances :
    (∀ i c, donutSpatialDistance i (i, c) = bufferCellDistance c) ∧
    (∀ i j c, i ≠ j → 5 < donutSpatialDistance i (j, c)) := by
  classical
  have hpoint (a : ℝ) : WithLp.toLp 2 (![a + 1, 0] : Fin 2 → ℝ) ∈
      donutPolygonBoundary a := by
    simp [donutPolygonBoundary, PiLp.toLp_apply]
  have hnonempty (a : ℝ) : (donutPolygonBoundary a).Nonempty := ⟨_, hpoint a⟩
  have hcoord (u v : Plane) : |u 0 - v 0| ≤ dist u v := by
    simpa only [dist_eq_norm, PiLp.sub_apply, Real.norm_eq_abs] using
      PiLp.norm_apply_le (u - v) 0
  refine ⟨?_, ?_⟩
  · intro i c
    have hd : 0 ≤ bufferCellDistance c := by fin_cases c <;> norm_num [bufferCellDistance]
    apply le_antisymm
    · have hu := Metric.infDist_le_dist_of_mem (x := donutSpatialCell i c) (hpoint (100 * (i : ℝ)))
      have he : dist (donutSpatialCell i c)
          (WithLp.toLp 2 (![100 * (i : ℝ) + 1, 0] : Fin 2 → ℝ)) =
          bufferCellDistance c := by
        have hs : dist (donutSpatialCell i c)
            (WithLp.toLp 2 (![100 * (i : ℝ) + 1, 0] : Fin 2 → ℝ)) ^ 2 =
            (bufferCellDistance c) ^ 2 := by
          rw [EuclideanSpace.dist_sq_eq]
          simp [donutSpatialCell, Fin.sum_univ_succ, Real.dist_eq, sq_abs]
        nlinarith [dist_nonneg (x := donutSpatialCell i c)
          (y := WithLp.toLp 2 (![100 * (i : ℝ) + 1, 0] : Fin 2 → ℝ))]
      simpa only [donutSpatialDistance, he] using hu
    · apply (Metric.le_infDist (hnonempty _)).mpr
      intro x hx
      have hb := hx.2.1
      have hc := hcoord (donutSpatialCell i c) x
      simp only [donutSpatialCell, PiLp.toLp_apply, Matrix.cons_val_zero] at hc
      have ha := (abs_le.mp hc).2
      change bufferCellDistance c ≤ dist
        (WithLp.toLp 2 (![100 * (i : ℝ) + 1 + bufferCellDistance c, 0] : Fin 2 → ℝ)) x
      linarith
  · intro i j c hij
    have hlow : 6 ≤ donutSpatialDistance i (j, c) := by
      apply (Metric.le_infDist (hnonempty _)).mpr
      intro x hx
      have hb0 := hx.1
      have hb1 := hx.2.1
      have hc := hcoord (donutSpatialCell j c) x
      simp only [donutSpatialCell, PiLp.toLp_apply, Matrix.cons_val_zero] at hc
      have ha := abs_le.mp hc
      fin_cases i <;> fin_cases j <;> norm_num at hij <;>
        fin_cases c <;> norm_num [bufferCellDistance, donutSpatialCell] at ha hb0 hb1 ⊢ <;> linarith
    linarith

/-- T16's centered band contains all nonmissing cells with distance in [3,5]. -/
def donutSpatialCentered (i : Fin 2) : Finset (Fin 2 × Fin 4) :=
  Finset.univ.filter (fun ic => 3 ≤ donutSpatialDistance i ic ∧ donutSpatialDistance i ic ≤ 5)

/-- T16's three averages, in order: implemented donut (2,4], centered band
[3,5], and full radius-4 buffer. The same cell outcomes are used in each. -/
def donutSpatialMeans (mode : Fin 3) (i : Fin 2) (z : Assignment 2) : ℝ :=
  countMean (if mode = 0 then donutSpatialBuffer i 4 \ donutSpatialBuffer i 2
    else if mode = 1 then donutSpatialCentered i else donutSpatialBuffer i 4)
    (fun ic => donutSpatialY ic z)

/-- T16's complete spatial counterexample, with two actual rectangle
boundaries, eight nonmissing cells and the full potential-outcome schedule.
The observed 10 assignment gives implemented donut, centered-band and disk
Hajek estimates 1,4,2. Hence the implemented donut is not the centered band. -/
theorem polygon_donut_counterexample :
    (∀ i c, donutSpatialDistance i (i, c) = bufferCellDistance c) ∧
    (∀ i j c, i ≠ j → 5 < donutSpatialDistance i (j, c)) ∧
    (donutSpatialBuffer 0 2).card = 1 ∧
    (∑ ic ∈ donutSpatialBuffer 0 2, donutSpatialY ic ![true, false]) = 4 ∧
    (donutSpatialBuffer 0 4).card = 3 ∧
    (∑ ic ∈ donutSpatialBuffer 0 4, donutSpatialY ic ![true, false]) = 6 ∧
    (∀ mode, donutSpatialMeans mode 1 ![true, false] = 0) ∧
    hajek (donutSpatialMeans 0) ![true, false] = 1 ∧
    hajek (donutSpatialMeans 1) ![true, false] = 4 ∧
    hajek (donutSpatialMeans 2) ![true, false] = 2 ∧
    hajek (donutSpatialMeans 0) ![true, false] ≠
      hajek (donutSpatialMeans 1) ![true, false] := by
  classical
  have hb (i : Fin 2) (r : ℝ) (hr : r ≤ 5) (j : Fin 2) (c : Fin 4) :
      donutSpatialDistance i (j, c) ≤ r ↔ j = i ∧ bufferCellDistance c ≤ r := by
    by_cases hij : i = j
    · subst j
      simp only [donut_spatial_distances.1, true_and]
    · have hfar := donut_spatial_distances.2 i j c hij
      have hnot : ¬ donutSpatialDistance i (j, c) ≤ r := by linarith
      simp [hnot, Ne.symm hij]
  have h₂ (i : Fin 2) : donutSpatialBuffer i 2 = {(i, 0)} := by
    ext ⟨j, c⟩
    simp only [donutSpatialBuffer, Finset.mem_filter, Finset.mem_univ, true_and,
      hb i 2 (by norm_num)]
    fin_cases c <;> norm_num [bufferCellDistance, Prod.mk.injEq]
  have h₄ (i : Fin 2) : donutSpatialBuffer i 4 = {(i, 0), (i, 1), (i, 2)} := by
    ext ⟨j, c⟩
    simp only [donutSpatialBuffer, Finset.mem_filter, Finset.mem_univ, true_and,
      hb i 4 (by norm_num)]
    fin_cases c <;> norm_num [bufferCellDistance, Prod.mk.injEq]
  have hcent (i : Fin 2) : donutSpatialCentered i = {(i, 2), (i, 3)} := by
    ext ⟨j, c⟩
    simp only [donutSpatialCentered, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hij : i = j
    · subst j
      simp only [donut_spatial_distances.1]
      fin_cases c <;> norm_num [bufferCellDistance, Prod.mk.injEq]
    · have hfar := donut_spatial_distances.2 i j c hij
      simp [not_le_of_gt hfar, Ne.symm hij, Prod.mk.injEq]
  have hvalues (mode : Fin 3) (i : Fin 2) :
      donutSpatialMeans mode i ![true, false] =
        if i = 0 then (![1, 4, 2] : Fin 3 → ℝ) mode else 0 := by
    unfold donutSpatialMeans
    rw [h₂, h₄, hcent]
    fin_cases mode <;> fin_cases i <;>
      norm_num [countMean, donutSpatialY, bufferCellOutcome, bit,
        Finset.sdiff_eq_filter, Finset.filter_insert, Finset.filter_singleton]
  have hstat (mode : Fin 3) : hajek (donutSpatialMeans mode) ![true, false] =
      (![1, 4, 2] : Fin 3 → ℝ) mode := by
    norm_num [hajek, Fin.sum_univ_succ, nTreated, nControl, bit, hvalues]
  refine ⟨donut_spatial_distances.1, donut_spatial_distances.2, ?_, ?_, ?_, ?_, ?_,
    hstat 0, hstat 1, hstat 2, ?_⟩
  · rw [h₂]; simp
  · rw [h₂]; norm_num [donutSpatialY, bufferCellOutcome, bit]
  · rw [h₄]; norm_num
  · rw [h₄]; norm_num [donutSpatialY, bufferCellOutcome, bit]
  · intro mode; simp [hvalues]
  · rw [hstat, hstat]; norm_num


/-- The short grid (.2,.3) in T9(i). -/
def bandwidthShortGrid : Fin 2 → ℝ := ![1 / 5, 3 / 10]

/-- The long grid (.1,.2,.3) in T9(ii). -/
def bandwidthLongGrid : Fin 3 → ℝ := ![1 / 10, 1 / 5, 3 / 10]

/-- T9(i–ii), the complete spatial grid-position counterexample. The
defined plane outcome field and counting measure give the same circle
data at radius .2; the true Euclidean node distances and actual regression
scores give variances 1 and 1/2 under the implemented bandwidth when that
radius moves from grid position one to position two. Both groups contain two nodes. -/
theorem spatial_grid_position_counterexample :
    bandwidthShortGrid 0 = bandwidthLongGrid 1 ∧
    bandwidthShortGrid 0 = (1 / 5 : ℝ) ∧
    nTreated (![false, false, true, true] : Assignment 4) = 2 ∧
    nControl (![false, false, true, true] : Assignment 4) = 2 ∧
    (∀ i j z, bandwidthSpatialModel.M i (bandwidthSpatialRadius j) z = 2 * (i : ℝ)) ∧
    (∀ i j, dist (bandwidthSpatialModel.node i) (bandwidthSpatialModel.node j) =
      bandwidthExampleDistance i j) ∧
    hajek (fun i z => bandwidthSpatialModel.M i (1 / 5) z)
      ![false, false, true, true] = 4 ∧
    archivedVariance
      (regressionScore ![false, false, true, true]
        (fun i => bandwidthSpatialModel.M i (1 / 5) ![false, false, true, true]))
      (fun i j => dist (bandwidthSpatialModel.node i) (bandwidthSpatialModel.node j))
      (2 / 5) 1 = 1 ∧
    archivedVariance
      (regressionScore ![false, false, true, true]
        (fun i => bandwidthSpatialModel.M i (1 / 5) ![false, false, true, true]))
      (fun i j => dist (bandwidthSpatialModel.node i) (bandwidthSpatialModel.node j))
      (2 / 5) 2 = 1 / 2 := by
  have hmeans (z : Assignment 4) :
      (fun i => bandwidthSpatialModel.M i (1 / 5) z) = (![0, 2, 4, 6] : Fin 4 → ℝ) := by
    funext i
    have hh := bandwidth_spatial_realization.2.2 i 1 z
    norm_num [bandwidthSpatialRadius] at hh
    rw [hh]
    fin_cases i <;> norm_num
  have hmeans' : (fun i z => bandwidthSpatialModel.M i (1 / 5) z) =
      (fun i _ => (![0, 2, 4, 6] : Fin 4 → ℝ) i) := by
    funext i z
    exact congrFun (hmeans z) i
  have hD : (fun i j => dist (bandwidthSpatialModel.node i) (bandwidthSpatialModel.node j)) =
      bandwidthExampleDistance := funext (fun i => funext (fun j => bandwidth_spatial_realization.1 i j))
  have hg : regressionScore ![false, false, true, true] (![0, 2, 4, 6] : Fin 4 → ℝ) =
      ![1 / 2, -1 / 2, -1 / 2, 1 / 2] := funext grid_position_counterexample.1
  refine ⟨by norm_num [bandwidthShortGrid, bandwidthLongGrid],
    by norm_num [bandwidthShortGrid], ?_, ?_, bandwidth_spatial_realization.2.2,
    bandwidth_spatial_realization.1, ?_, ?_, ?_⟩
  · norm_num [univ_four, nTreated, bit, Fin.sum_univ_succ]
  · norm_num [univ_four, nControl, nTreated, bit, Fin.sum_univ_succ]
  · rw [hmeans']; exact grid_position_counterexample.2.1
  · rw [hmeans, hg, hD]; exact grid_position_counterexample.2.2.1
  · rw [hmeans, hg, hD]; exact grid_position_counterexample.2.2.2.1

/-- T2(a): under the full spatial sharp null, the actual cumulative
Hajek statistic has a valid inclusive-tail test under the actual conditional
design law. This asserts calibration without specifying the Uganda p-value. -/
theorem sharp_null_cumulative_test_valid {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (A : Assignment N → Prop) (hA : 0 < Q.prob A)
    (D : Finset ℝ) (hfield : MeasurableSet P.field) (hsharp : P.sharpNull)
    (hN : 0 < N) (hmass : ∀ i d, d ∈ D → 0 < P.circleMass i d)
    (hfinite : ∀ i d, d ∈ D → P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ i d, d ∈ D → ∀ z, Integrable (fun x => P.Y x z) (P.circleMeasure i d))
    (harms : ∀ z, A z → 0 < Q.mass z → nTreated z ≠ 0 ∧ nControl z ≠ 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    let S := fun z => ∑ d ∈ D, hajek (fun i w => P.M i d w) z
    (conditionalLaw Q A hA).prob (fun z => tailP (conditionalLaw Q A hA) S z ≤ δ) ≤ δ ∧
    (∀ z, S z = ∑ d ∈ D, hajek (fun i _ => P.M i d (fun _ => false)) z) := by
  dsimp only
  refine ⟨conditional_tail_valid Q A hA _ δ hδ hδ', ?_⟩
  have hm (i : Fin N) (d : ℝ) (z : Assignment N) :
      P.M i d z = P.M i d (fun _ => false) := by
    unfold SpatialModel.M SpatialModel.average
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (circle_measurable P i d hfield)] with x hx
    exact hsharp x hx.1 z
  intro z
  simp_rw [hm]

/-- T14(a) restricted to the paper's nonzero population and genuine,
positive finite-mass circle averages. The unrestricted equality amr_display
is retained solely as an auxiliary definitional lemma. -/
theorem amr_display_on_valid_circles {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (d : ℝ) (hN : 0 < N)
    (hmass : ∀ i, 0 < P.circleMass i d)
    (hfinite : ∀ i, P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ i z, Integrable (fun x => P.Y x z) (P.circleMeasure i d)) :
    P.amr Q d = (N : ℝ)⁻¹ * ∑ i, (P.m Q i true d - P.m Q i false d) :=
  amr_display P Q d

/-- T17(a) at its exact geometric domain: d>0, k≥0, and the radius
is the actual Euclidean distance. It gives the circle neighborhood and
the radial width 2k when d≥k. -/
theorem positive_radius_band_geometry (p x : Plane) (d k : ℝ) (hd : 0 < d) (hk : 0 ≤ k) :
    (Metric.infDist x {q : Plane | dist q p = d} ≤ k ↔
      max 0 (d - k) ≤ dist x p ∧ dist x p ≤ d + k) ∧
    (k ≤ d → (d + k) - (d - k) = 2 * k) := by
  rw [distance_to_circle p x d hd]
  exact ⟨(radial_band_geometry (dist x p) d k dist_nonneg).1,
    fun _ => (radial_band_geometry (dist x p) d k dist_nonneg).2⟩

/-- T8(b): normalized nonnegative radius weights preserve a constant
AMR; the unweighted sum is the number of evaluated radii times that AMR. -/
theorem constant_radius_effect_for_sampling {J : ℕ}
    (w : Fin J → ℝ) (hw : ∀ j, 0 ≤ w j) (hs : ∑ j, w j = 1) (t : ℝ) :
    (∑ _j : Fin J, t) = (J : ℝ) * t ∧ (∑ j, w j * t) = t :=
  ⟨(constant_radius_effect w hs t).2, (constant_radius_effect w hs t).1⟩

/-- T8(c) restricted to a sorted sample and q∈[0,1], the declared
domain of the type-7 percentile. A common positive normalization preserves
tail comparisons and divides every percentile by that same constant. -/
theorem common_rescaling_for_percentiles {n : ℕ} (s : Fin (n + 1) → ℝ)
    (hs : Monotone s) (q m x y : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1) (hm : 0 < m) :
    (x ≤ y ↔ x / m ≤ y / m) ∧ (|x| ≤ |y| ↔ |x / m| ≤ |y / m|) ∧
    quantile7 (fun j => s j / m) q = quantile7 s q / m :=
  common_rescaling s q m x y hm

/-- T10(a) on the actual spatial-regression objects with both arms present:
the repaired physical cutoff gives the same variance at every grid position. -/
theorem corrected_spatial_bandwidth_invariant {N : ℕ} (node : Fin N → Plane)
    (z : Assignment N) (M : Fin N → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h₁ : nTreated z ≠ 0) (h₀ : nControl z ≠ 0) (j k : ℕ) (hj : 0 < j) (hk : 0 < k) :
    physicalVariance (regressionScore z M) (fun i l => dist (node i) (node l)) c j =
      hac (regressionScore z M) (fun i l => dist (node i) (node l)) c ∧
    physicalVariance (regressionScore z M) (fun i l => dist (node i) (node l)) c j =
      physicalVariance (regressionScore z M) (fun i l => dist (node i) (node l)) c k :=
  corrected_bandwidth_invariant _ _ c j k

/-- A finite design preserves an absolute outcome bound. -/
theorem expect_abs_bound {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω)
    (f : Ω → ℝ) (H : ℝ) (hf : ∀ z, |f z| ≤ H) : |Q.expect f| ≤ H := by
  apply abs_le.mpr
  constructor
  · calc
      _ = Q.expect (fun _ => -H) := (expect_const Q _).symm
      _ ≤ _ := Finset.sum_le_sum
        (fun z _ => mul_le_mul_of_nonneg_left (abs_le.mp (hf z)).1 (Q.nonneg z))
  · calc
      _ ≤ Q.expect (fun _ => H) := Finset.sum_le_sum
        (fun z _ => mul_le_mul_of_nonneg_left (abs_le.mp (hf z)).2 (Q.nonneg z))
      _ = _ := expect_const Q _

/-- T28: averaging marginalized circle outcomes preserves their bound H. -/
theorem marginal_mean_abs_bound {N : ℕ} (hN : 0 < N)
    (Q : FiniteLaw (Assignment N)) (M : Fin N → Assignment N → ℝ)
    (H : ℝ) (hbound : ∀ i z, |M i z| ≤ H) (b : Bool) :
    |marginalMean Q M b| ≤ H := by
  have hi (i : Fin N) : |marginal Q (M i) i b| ≤ H :=
    expect_abs_bound Q _ H (fun z => hbound i _)
  have hs : |∑ i, marginal Q (M i) i b| ≤ (N : ℝ) * H := by
    calc
      _ ≤ ∑ i : Fin N, |marginal Q (M i) i b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, H := Finset.sum_le_sum (fun i _ => hi i)
      _ = _ := by simp
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
  unfold marginalMean
  rw [abs_mul, abs_inv, abs_of_nonneg (Nat.cast_nonneg N)]
  calc
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * H) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = H := by rw [← mul_assoc, inv_mul_cancel₀ hNr, one_mul]

/-- The union bound on the finite randomization law. -/
theorem prob_or_le {Ω : Type*} [Fintype Ω] (Q : FiniteLaw Ω) (A B : Ω → Prop) :
    Q.prob (fun z => A z ∨ B z) ≤ Q.prob A + Q.prob B := by
  classical
  rw [prob_as_expect, prob_as_expect, prob_as_expect, ← expect_add]
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ (Q.nonneg z)
  by_cases ha : A z <;> by_cases hb : B z <;> simp [ha, hb]

/-- T28 finite consistency estimate. Choose a positive deviation tolerance η
small enough to keep both denominators away from zero and the two ratio
errors below ε. The probability of estimation error is bounded by C/N. -/
theorem finite_hajek_error_bound {N : ℕ} (hN : 0 < N)
    (Q : FiniteLaw (Assignment N)) (M : Fin N → Assignment N → ℝ)
    (p H exceptional ε η : ℝ) (D : ℕ) (hp : 0 < p) (hp' : p < 1)
    (hH : 0 ≤ H) (hε : 0 < ε) (hη : 0 < η)
    (hη₁ : η ≤ p / 2) (hη₀ : η ≤ (1 - p) / 2)
    (hηε : (2 / p + 2 / (1 - p)) * (H + 1) * η ≤ ε / 2)
    (hQ : commonBernoulli Q p) (hbound : ∀ i z, |M i z| ≤ H)
    (hdep : boundedPairDependency Q M D) :
    Q.prob (fun z => ε < |completedHajek M exceptional z - finiteAMR Q M|) ≤
      ((p * (1 - p) + 2 * H ^ 2 * (D + 1)) / η ^ 2) / N := by
  classical
  let U (z : Assignment N) := nTreated z / N
  let S₁ := normalizedNumerator M true
  let S₀ := normalizedNumerator M false
  let r₁ := marginalMean Q M true
  let r₀ := marginalMean Q M false
  let A (z : Assignment N) := η ≤ |U z - p|
  let B (z : Assignment N) := η ≤ |S₁ z - p * r₁|
  let C (z : Assignment N) := η ≤ |S₀ z - (1 - p) * r₀|
  have hsub (z : Assignment N) (herr : ε < |completedHajek M exceptional z - finiteAMR Q M|) :
      A z ∨ B z ∨ C z := by
    by_contra hbad
    have hu : |U z - p| < η := lt_of_not_ge (fun ha => hbad (Or.inl ha))
    have h₁ : |S₁ z - p * r₁| < η := lt_of_not_ge (fun hb => hbad (Or.inr (Or.inl hb)))
    have h₀ : |S₀ z - (1 - p) * r₀| < η := lt_of_not_ge (fun hc => hbad (Or.inr (Or.inr hc)))
    have hulo : p / 2 ≤ U z := by have hh := (abs_le.mp hu.le).1; linarith
    have huhi : (1 - p) / 2 ≤ 1 - U z := by have hh := (abs_le.mp hu.le).2; linarith
    have hu0 : 0 < U z := lt_of_lt_of_le (half_pos hp) hulo
    have hu1 : U z < 1 := by linarith
    have ht : nTreated z ≠ 0 := by intro hh; simp [U, hh] at hu0
    have hc : nControl z ≠ 0 := by
      intro hh
      have hh' : nTreated z = N := by unfold nControl at hh; linarith
      have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hN)
      simp [U, hh', hn] at hu1
    have hr1 := ratio_deviation_bound (S₁ z) (U z) p r₁ H hp hulo
      (marginal_mean_abs_bound hN Q M H hbound true)
    have hr0 := ratio_deviation_bound (S₀ z) (1 - U z) (1 - p) r₀ H
      (sub_pos.mpr hp') huhi (marginal_mean_abs_bound hN Q M H hbound false)
    have hdev0 : |(1 - U z) - (1 - p)| = |U z - p| := by
      rw [show (1 - U z) - (1 - p) = -(U z - p) by ring, abs_neg]
    rw [hdev0] at hr0
    have hdecomp := hajek_ratio_decomposition hN Q M z ht hc
    have hcompleted : completedHajek M exceptional z = hajek M z := by
      simp [completedHajek, ht, hc]
    rw [hcompleted, hdecomp] at herr
    change ε < |(S₁ z / U z - r₁) - (S₀ z / (1 - U z) - r₀)| at herr
    have htri := abs_sub (S₁ z / U z - r₁) (S₀ z / (1 - U z) - r₀)
    have hpcoef : 0 ≤ 2 / p := by positivity
    have hcCoef : 0 ≤ 2 / (1 - p) := by positivity
    have ht1 : |S₁ z / U z - r₁| ≤ (2 / p) * (η + H * η) := by
      apply hr1.trans
      gcongr
    have ht0 : |S₀ z / (1 - U z) - r₀| ≤ (2 / (1 - p)) * (η + H * η) := by
      apply hr0.trans
      gcongr
    have halg : (2 / p) * (η + H * η) + (2 / (1 - p)) * (η + H * η) =
        (2 / p + 2 / (1 - p)) * (H + 1) * η := by ring
    linarith
  have hmom := bernoulli_fraction_moments hN Q p hp hp' hQ
  have hmean := common_numerator_means Q p hp hp' hQ M
  have ha : Q.prob A ≤ (p * (1 - p) / N) / η ^ 2 := by
    have hh := finite_chebyshev Q U η hη
    change Q.expect U = p ∧ Q.var U = p * (1 - p) / N at hmom
    rw [hmom.1, hmom.2] at hh
    exact hh
  have hb : Q.prob B ≤ (H ^ 2 * (D + 1) / N) / η ^ 2 := by
    have hh := finite_chebyshev Q S₁ η hη
    have hv := dependency_numerator_variance_bound hN Q M H D hH hbound hdep true
    have hh' : Q.prob B ≤ Q.var S₁ / η ^ 2 := by
      have he : Q.expect S₁ = p * r₁ := hmean true
      rw [he] at hh
      exact hh
    exact hh'.trans (div_le_div_of_nonneg_right hv (sq_nonneg η))
  have hc : Q.prob C ≤ (H ^ 2 * (D + 1) / N) / η ^ 2 := by
    have hh := finite_chebyshev Q S₀ η hη
    have hv := dependency_numerator_variance_bound hN Q M H D hH hbound hdep false
    have hh' : Q.prob C ≤ Q.var S₀ / η ^ 2 := by
      have he : Q.expect S₀ = (1 - p) * r₀ := hmean false
      rw [he] at hh
      exact hh
    exact hh'.trans (div_le_div_of_nonneg_right hv (sq_nonneg η))
  calc
    _ ≤ Q.prob (fun z => A z ∨ B z ∨ C z) := prob_mono Q hsub
    _ ≤ Q.prob A + Q.prob (fun z => B z ∨ C z) := prob_or_le Q A _
    _ ≤ Q.prob A + (Q.prob B + Q.prob C) := add_le_add_right (prob_or_le Q B C) _
    _ ≤ (p * (1 - p) / N) / η ^ 2 +
        ((H ^ 2 * (D + 1) / N) / η ^ 2 + (H ^ 2 * (D + 1) / N) / η ^ 2) :=
      add_le_add ha (add_le_add hb hc)
    _ = _ := by ring

/-- T28: fixed common p∈(0,1), bounded outcomes and a uniformly
bounded dependency graph imply convergence in probability of estimator minus
AMR to zero, with no assumption that the changing AMRs themselves converge. -/
theorem sufficient_hajek_consistency
    (Q : ∀ n, FiniteLaw (Assignment (n + 1)))
    (M : ∀ n, Fin (n + 1) → Assignment (n + 1) → ℝ)
    (p H exceptional : ℝ) (D : ℕ) (hp : 0 < p) (hp' : p < 1) (hH : 0 ≤ H)
    (hQ : ∀ n, commonBernoulli (Q n) p)
    (hbound : ∀ n i z, |M n i z| ≤ H)
    (hdep : ∀ n, boundedPairDependency (Q n) (M n) D) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun n => (Q n).prob (fun z => ε <
        |completedHajek (M n) exceptional z - finiteAMR (Q n) (M n)|))
      atTop (nhds 0) := by
  intro ε hε
  let K := 2 / p + 2 / (1 - p)
  have hK : 0 < K := add_pos (by positivity) (by positivity)
  let η := min (min (p / 2) ((1 - p) / 2)) (ε / (2 * K * (H + 1)))
  have hη : 0 < η := lt_min (lt_min (half_pos hp) (half_pos (sub_pos.mpr hp')))
    (by positivity)
  have hη1 : η ≤ p / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hη0 : η ≤ (1 - p) / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hηε : K * (H + 1) * η ≤ ε / 2 := by
    have hlim : η ≤ ε / (2 * K * (H + 1)) := min_le_right _ _
    have hpden : 0 < 2 * K * (H + 1) := by positivity
    have hh := (le_div_iff₀ hpden).mp hlim
    nlinarith
  let C := (p * (1 - p) + 2 * H ^ 2 * (D + 1)) / η ^ 2
  have hupper (n : ℕ) : (Q n).prob (fun z => ε <
      |completedHajek (M n) exceptional z - finiteAMR (Q n) (M n)|) ≤ C / (n + 1) := by
    simpa only [C, Nat.cast_succ, Nat.cast_add, Nat.cast_one] using finite_hajek_error_bound
      (Nat.succ_pos n) (Q n) (M n) p H exceptional ε η D hp hp' hH hε hη
      hη1 hη0 hηε (hQ n) (hbound n) (hdep n)
  have hlower (n : ℕ) : 0 ≤ (Q n).prob (fun z => ε <
      |completedHajek (M n) exceptional z - finiteAMR (Q n) (M n)|) :=
    Finset.sum_nonneg (fun z _ => (Q n).nonneg z)
  have hlim : Tendsto (fun n : ℕ => C / (n + 1)) atTop (nhds (0 : ℝ)) :=
    by simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat C)
  exact squeeze_zero hlower hupper hlim


/-- T5 replication's exact x-axis node coordinates, g=0,...,M-1:
the two nodes of pair g are (6g,0) and (6g+2,0). -/
def replicatedNode {M : ℕ} (i : Fin M × Fin 2) : ℚ := 6 * i.1.val + 2 * i.2.val

/-- The replicated finite field contains the three outcome points and both
intervention nodes of each pair, with counting measure (T5). -/
def replicatedField (M : ℕ) : Finset ℚ :=
  Finset.univ.image (fun gc : Fin M × Fin 5 => 6 * (gc.1.val : ℚ) + gc.2.val - 1)

/-- T5's same range-one additive outcome rule on every point of the field. -/
def replicatedOutcome {M : ℕ} (x : ℚ) (z : (Fin M × Fin 2) → Bool) : ℝ :=
  ∑ i, if |x - replicatedNode i| ≤ 1 then bit (z i) else 0

/-- Actual radius-one circles in the replicated counting-measure field. -/
def replicatedCircle {M : ℕ} (i : Fin M × Fin 2) : Finset ℚ :=
  (replicatedField M).filter (fun x => |x - replicatedNode i| = 1)

/-- The circle averages, using all points selected by replicatedCircle. -/
def replicatedCircleM {M : ℕ} (i : Fin M × Fin 2) (z : (Fin M × Fin 2) → Bool) : ℝ :=
  countMean (replicatedCircle i) (fun x => replicatedOutcome x z)

/-- The actual linearization contribution at m1=5/4 and m0=1/4, T5. -/
def replicatedSpatialScore {M : ℕ} (i : Fin M × Fin 2) (z : (Fin M × Fin 2) → Bool) : ℝ :=
  2 * bit (z i) * (replicatedCircleM i z - 5 / 4) -
    2 * (1 - bit (z i)) * (replicatedCircleM i z - 1 / 4)

/-- Other replicated pairs cannot affect points of the five-point field
of pair g: the outcome-to-other-node distance is strictly larger than one. -/
theorem replicated_other_pair_far {M : ℕ} (g h : Fin M) (k : Fin 2) (t : ℚ)
    (htlo : -1 ≤ t) (hthi : t ≤ 3) (hgh : g ≠ h) :
    1 < |(6 * (g.val : ℚ) + t) - replicatedNode (h, k)| := by
  have hval : g.val ≠ h.val := fun he => hgh (Fin.ext he)
  by_contra hh
  have hb := abs_le.mp (le_of_not_gt hh)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hn : (g.val : ℚ) + 1 ≤ h.val := by exact_mod_cast Nat.succ_le_of_lt hlt
    fin_cases k <;> norm_num [replicatedNode] at hb <;> linarith
  · have hn : (h.val : ℚ) + 1 ≤ g.val := by exact_mod_cast Nat.succ_le_of_lt hgt
    fin_cases k <;> norm_num [replicatedNode] at hb <;> linarith

/-- Exact spatial outcomes inside each replicated pair's field, derived
from the full sum over every intervention node, without assuming independence. -/
theorem replicated_local_outcome {M : ℕ} (g : Fin M) (t : ℚ)
    (htlo : -1 ≤ t) (hthi : t ≤ 3) (z : (Fin M × Fin 2) → Bool) :
    replicatedOutcome (6 * (g.val : ℚ) + t) z =
      (if |t| ≤ 1 then bit (z (g, 0)) else 0) +
      (if |t - 2| ≤ 1 then bit (z (g, 1)) else 0) := by
  classical
  unfold replicatedOutcome
  rw [Fintype.sum_prod_type, Finset.sum_eq_single g]
  · rw [Fin.sum_univ_two]
    have h₀ : 6 * (g.val : ℚ) + t - replicatedNode (g, (0 : Fin 2)) = t := by
      simp [replicatedNode]
    have h₁ : 6 * (g.val : ℚ) + t - replicatedNode (g, (1 : Fin 2)) = t - 2 := by
      simp [replicatedNode] <;> ring
    change (if |6 * (g.val : ℚ) + t - replicatedNode (g, (0 : Fin 2))| ≤ 1 then bit (z (g, 0)) else 0) +
      (if |6 * (g.val : ℚ) + t - replicatedNode (g, (1 : Fin 2))| ≤ 1 then bit (z (g, 1)) else 0) = _
    rw [h₀, h₁]
  · intro h _ hh
    apply Finset.sum_eq_zero
    intro k _
    simp only [if_neg (not_le_of_gt (replicated_other_pair_far g h k t htlo hthi (Ne.symm hh)))]
  · simp

/-- T5's spatial replication construction, for every number of pairs.
Every node belongs to the field, outcomes are bounded by two, and the
radius-one averages give exactly the independently proved pair scores.
The final two equalities are the actual full and diagonal score variances. -/
theorem replicated_spatial_counterexample (M : ℕ) (hM : 0 < M) :
    (∀ i : Fin M × Fin 2, replicatedNode i ∈ replicatedField M) ∧
    (∀ x ∈ replicatedField M, ∀ z : (Fin M × Fin 2) → Bool, 0 ≤ replicatedOutcome x z ∧ replicatedOutcome x z ≤ 2) ∧
    (∀ i : Fin M × Fin 2, replicatedCircle i = {replicatedNode i - 1, replicatedNode i + 1}) ∧
    (∀ g : Fin M, ∀ z,
      replicatedCircleM (g, 0) z = bit (z (g, 0)) + bit (z (g, 1)) / 2 ∧
      replicatedCircleM (g, 1) z = bit (z (g, 1)) + bit (z (g, 0)) / 2) ∧
    (∀ i : Fin M × Fin 2, ∀ z, replicatedSpatialScore i z = replicatedPairScore i z) ∧
    (uniformLaw ((Fin M × Fin 2) → Bool)).var
      (fun z => (2 * M : ℝ)⁻¹ * ∑ i, replicatedSpatialScore i z) = 1 / (2 * (2 * M)) ∧
    (2 * M : ℝ)⁻¹ ^ 2 * ∑ i,
      (uniformLaw ((Fin M × Fin 2) → Bool)).var (replicatedSpatialScore i) = 1 / (4 * (2 * M)) := by
  classical
  have hfield (g : Fin M) (c : Fin 5) :
      6 * (g.val : ℚ) + c.val - 1 ∈ replicatedField M :=
    Finset.mem_image.mpr ⟨(g, c), Finset.mem_univ _, rfl⟩
  have hcircle (i : Fin M × Fin 2) :
      replicatedCircle i = {replicatedNode i - 1, replicatedNode i + 1} := by
    have hminus : replicatedNode i - 1 ∈ replicatedField M := by
      rcases i with ⟨g, k⟩
      fin_cases k
      · simpa [replicatedNode] using hfield g 0
      · convert hfield g 2 using 1 <;> simp [replicatedNode] <;> ring
    have hplus : replicatedNode i + 1 ∈ replicatedField M := by
      rcases i with ⟨g, k⟩
      fin_cases k
      · convert hfield g 2 using 1 <;> simp [replicatedNode] <;> ring
      · convert hfield g 4 using 1 <;> simp [replicatedNode] <;> ring
    ext x
    simp only [replicatedCircle, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, he⟩
      have hh := eq_or_eq_neg_of_abs_eq he
      rcases hh with hh | hh
      · right; linarith
      · left; linarith
    · rintro (rfl | rfl)
      · exact ⟨hminus, by norm_num⟩
      · exact ⟨hplus, by norm_num⟩
  have hmeans (g : Fin M) (z : (Fin M × Fin 2) → Bool) :
      replicatedCircleM (g, 0) z = bit (z (g, 0)) + bit (z (g, 1)) / 2 ∧
      replicatedCircleM (g, 1) z = bit (z (g, 1)) + bit (z (g, 0)) / 2 := by
    have hYneg := replicated_local_outcome g (-1) (by norm_num) (by norm_num) z
    have hY₁ := replicated_local_outcome g 1 (by norm_num) (by norm_num) z
    have hY₃ := replicated_local_outcome g 3 (by norm_num) (by norm_num) z
    norm_num at hYneg hY₁ hY₃
    have hneq (q : ℚ) : q - 1 ≠ q + 1 := by linarith
    unfold replicatedCircleM
    rw [hcircle, hcircle]
    have he₀ : replicatedNode (g, (0 : Fin 2)) - 1 = 6 * g.val + (-1 : ℚ) := by simp [replicatedNode] <;> ring
    have he₁ : replicatedNode (g, (0 : Fin 2)) + 1 = 6 * g.val + (1 : ℚ) := by simp [replicatedNode]
    have he₂ : replicatedNode (g, (1 : Fin 2)) - 1 = 6 * g.val + (1 : ℚ) := by simp [replicatedNode] <;> ring
    have he₃ : replicatedNode (g, (1 : Fin 2)) + 1 = 6 * g.val + (3 : ℚ) := by simp [replicatedNode] <;> ring
    constructor
    · simp only [countMean, Finset.sum_pair (hneq _), Finset.card_pair (hneq _)]
      rw [he₀, he₁, hYneg, hY₁]
      norm_num <;> ring
    · simp only [countMean, Finset.sum_pair (hneq _), Finset.card_pair (hneq _)]
      rw [he₂, he₃, hY₁, hY₃]
      norm_num <;> ring
  have hscore (i : Fin M × Fin 2) (z : (Fin M × Fin 2) → Bool) :
      replicatedSpatialScore i z = replicatedPairScore i z := by
    rcases i with ⟨g, k⟩
    unfold replicatedSpatialScore replicatedPairScore
    fin_cases k
    · simp only [Prod.fst, Prod.snd, Fin.reduceFinMk]
      rw [(hmeans g z).1]
      cases ha : z (g, 0) <;> cases hb : z (g, 1) <;> norm_num [bit, ha, hb]
    · simp only [Prod.fst, Prod.snd, Fin.reduceFinMk]
      rw [(hmeans g z).2]
      cases ha : z (g, 0) <;> cases hb : z (g, 1) <;> norm_num [bit, ha, hb]
  refine ⟨?_, ?_, hcircle, hmeans, hscore, ?_, ?_⟩
  · rintro ⟨g, k⟩
    fin_cases k
    · convert hfield g 1 using 1 <;> simp [replicatedNode]
    · convert hfield g 3 using 1 <;> simp [replicatedNode] <;> ring
  · intro x hx z
    obtain ⟨⟨g, c⟩, _, rfl⟩ := Finset.mem_image.mp hx
    have htlo : (-1 : ℚ) ≤ c.val - 1 := by
      have hc : (0 : ℚ) ≤ c.val := by positivity
      linarith
    have hthi : (c.val : ℚ) - 1 ≤ 3 := by
      have hc : c.val ≤ 4 := by omega
      have hc' : (c.val : ℚ) ≤ 4 := by exact_mod_cast hc
      linarith
    rw [show 6 * (g.val : ℚ) + c.val - 1 = 6 * g.val + (c.val - 1) by ring,
      replicated_local_outcome g _ htlo hthi]
    have hb (a : Bool) : 0 ≤ bit a ∧ bit a ≤ 1 := by cases a <;> norm_num [bit]
    split_ifs <;> constructor <;> linarith [(hb (z (g, 0))).1,
      (hb (z (g, 0))).2, (hb (z (g, 1))).1, (hb (z (g, 1))).2]
  · simp_rw [hscore]
    exact (replicated_cutoff_variance M hM).1
  · have he (i : Fin M × Fin 2) : replicatedSpatialScore i = replicatedPairScore i := funext (hscore i)
    simp_rw [he]
    exact (replicated_cutoff_variance M hM).2

/-- Distinct nodes in the replication are separated by at least two:
this holds uniformly for every population size in T5's replication. -/
theorem replicated_nodes_separated {M : ℕ} (i j : Fin M × Fin 2) (hij : i ≠ j) :
    2 ≤ |replicatedNode i - replicatedNode j| := by
  rcases i with ⟨g, k⟩
  rcases j with ⟨h, l⟩
  by_cases hgh : g = h
  · subst h
    have hkl : k ≠ l := fun he => hij (by rw [he])
    fin_cases k <;> fin_cases l <;> norm_num [replicatedNode] at *
  · have hval : g.val ≠ h.val := fun he => hgh (Fin.ext he)
    by_contra habs
    have hb := abs_le.mp (le_of_lt (lt_of_not_ge habs))
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hn : (g.val : ℚ) + 1 ≤ h.val := by exact_mod_cast Nat.succ_le_of_lt hlt
      fin_cases k <;> fin_cases l <;> norm_num [replicatedNode] at hb <;> first | linarith [hb.1, hb.2] | omega
    · have hn : (h.val : ℚ) + 1 ≤ g.val := by exact_mod_cast Nat.succ_le_of_lt hgt
      fin_cases k <;> fin_cases l <;> norm_num [replicatedNode] at hb <;> first | linarith [hb.1, hb.2] | omega

/-- Each actual replicated circle average depends on just the two
assignments in its own pair, as required by the regularity claims of T5. -/
theorem replicated_circle_depends_on_pair (M : ℕ) (hM : 0 < M)
    (i : Fin M × Fin 2) (z z' : (Fin M × Fin 2) → Bool)
    (h₀ : z (i.1, 0) = z' (i.1, 0)) (h₁ : z (i.1, 1) = z' (i.1, 1)) :
    replicatedCircleM i z = replicatedCircleM i z' := by
  have hmeans := (replicated_spatial_counterexample M hM).2.2.2.1
  rcases i with ⟨g, k⟩
  fin_cases k
  · simp only [Prod.fst, Prod.snd, Fin.reduceFinMk] at h₀ h₁ ⊢
    rw [(hmeans g z).1, (hmeans g z').1, h₀, h₁]
  · simp only [Prod.fst, Prod.snd, Fin.reduceFinMk] at h₀ h₁ ⊢
    rw [(hmeans g z).2, (hmeans g z').2, h₀, h₁]

/-- At cutoff one the actual replication's covariance sum keeps only
its diagonal, so it is half the full linearization variance for every M. -/
theorem replicated_spatial_cutoff_omission (M : ℕ) (hM : 0 < M) :
    (2 * M : ℝ)⁻¹ ^ 2 * ∑ i : Fin M × Fin 2, ∑ j : Fin M × Fin 2,
      (if |replicatedNode i - replicatedNode j| ≤ 1 then
        (uniformLaw ((Fin M × Fin 2) → Bool)).cov
          (replicatedSpatialScore i) (replicatedSpatialScore j) else 0) =
      1 / (4 * (2 * M)) := by
  classical
  have he (i : Fin M × Fin 2) :
      (∑ j : Fin M × Fin 2, if |replicatedNode i - replicatedNode j| ≤ 1 then
        (uniformLaw ((Fin M × Fin 2) → Bool)).cov
          (replicatedSpatialScore i) (replicatedSpatialScore j) else 0) =
      (uniformLaw ((Fin M × Fin 2) → Bool)).var (replicatedSpatialScore i) := by
    rw [Finset.sum_eq_single i]
    · simp [FiniteLaw.var]
    · intro j _ hji
      have hf := replicated_nodes_separated i j (Ne.symm hji)
      rw [if_neg (by linarith)]
    · simp
  simp_rw [he]
  exact (replicated_spatial_counterexample M hM).2.2.2.2.2.2


/-- T5's separation condition in actual two-coordinate Euclidean space,
uniformly for the entire replicated spatial family. -/
theorem replicated_plane_separation {M : ℕ} (i j : Fin M × Fin 2) (hij : i ≠ j) :
    2 ≤ dist (lineEmbedding (replicatedNode i)) (lineEmbedding (replicatedNode j)) := by
  rw [line_embedding_distance]
  exact_mod_cast replicated_nodes_separated i j hij

/-- The replicated counting-circle selector is precisely the Euclidean
radius-one selector after embedding the finite field into the plane (T5). -/
theorem replicated_plane_circle {M : ℕ} (i : Fin M × Fin 2) (x : ℚ) :
    x ∈ replicatedCircle i ↔ x ∈ replicatedField M ∧
      dist (lineEmbedding (replicatedNode i)) (lineEmbedding x) = 1 := by
  simp only [replicatedCircle, Finset.mem_filter, line_embedding_distance]
  norm_cast
  rw [abs_sub_comm]

/-- T6(a) on the paper's spatial-regression objects: cutoff below every
distinct Euclidean node separation gives the HC0 group-residual variance. -/
theorem spatial_hac_hc0 {N : ℕ} (node : Fin N → Plane) (z : Assignment N)
    (M : Fin N → ℝ) (c : ℝ) (hc : 0 ≤ c) (h₁ : 1 ≤ nTreated z) (h₀ : 1 ≤ nControl z)
    (hsep : ∀ i j, i ≠ j → c < dist (node i) (node j)) :
    hac (regressionScore z M) (fun i j => dist (node i) (node j)) c =
      (∑ i ∈ Finset.univ.filter (fun i => z i = true), (groupResidual z M i) ^ 2) /
        (nTreated z) ^ 2 +
      (∑ i ∈ Finset.univ.filter (fun i => z i = false), (groupResidual z M i) ^ 2) /
        (nControl z) ^ 2 ∧
    hac (regressionScore z M) (fun i j => dist (node i) (node j)) c =
      hac (regressionScore z M) (fun i j => dist (node i) (node j)) 0 :=
  hac_group_hc0 z M _ c hc h₁ h₀ (fun i => dist_self _) hsep

/-- T10(b) at its spatial-regression scope: any physical cutoff that
includes all node pairs makes the uniform-kernel HAC variance zero. -/
theorem spatial_all_pairs_zero {N : ℕ} (node : Fin N → Plane) (z : Assignment N)
    (M : Fin N → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h₁ : nTreated z ≠ 0) (h₀ : nControl z ≠ 0)
    (hall : ∀ i j, dist (node i) (node j) ≤ c) :
    hac (regressionScore z M) (fun i j => dist (node i) (node j)) c = 0 :=
  regression_all_pairs_zero z M _ c h₁ h₀ hall

/-- T8(a) with integrability of every potential-outcome schedule, exactly
the sufficient domain for binary outcomes and genuine circles. -/
theorem spatial_risk_normalization_all_assignments {N : ℕ} (P : SpatialModel N)
    (Q : FiniteLaw (Assignment N)) (d : ℝ) (hN : 0 < N)
    (hfield : MeasurableSet P.field) (hmass : ∀ i, 0 < P.circleMass i d)
    (hfinite : ∀ i, P.circleMeasure i d Set.univ ≠ ⊤)
    (hint : ∀ i z, Integrable (fun x => P.Y x z) (P.circleMeasure i d))
    (hbinary : ∀ x ∈ P.field, ∀ z, P.Y x z = 0 ∨ P.Y x z = 1) :
    (∀ b, 0 ≤ P.risk Q b d ∧ P.risk Q b d ≤ 1) ∧
    P.amr Q d = P.risk Q true d - P.risk Q false d :=
  spatial_risk_normalization P Q d hN hfield hmass hfinite (fun i _ z _ => hint i _) hbinary

/-- T12's actual empty permutation statistic has zero reported type-7
percentiles for every number of permutations; all three printed values
are therefore incompatible with the printed grid and window. -/
theorem printed_grid_empty_percentiles {n : ℕ} (M : Fin (n + 1) → Fin 5 → ℝ) :
    (∀ z, ∑ j ∈ Finset.univ.filter (fun j => inUgandaRange (printedGrid j)), M z j = 0) ∧
    quantile7 (fun z => ∑ j ∈ Finset.univ.filter
      (fun j => inUgandaRange (printedGrid j)), M z j) (1 / 40) = 0 ∧
    quantile7 (fun z => ∑ j ∈ Finset.univ.filter
      (fun j => inUgandaRange (printedGrid j)), M z j) (39 / 40) = 0 ∧
    (-321 / 10000 : ℝ) ≠ 0 ∧ (-19 / 625 : ℝ) ≠ 0 ∧ (21 / 625 : ℝ) ≠ 0 := by
  have hz := printed_grid_counterexample.2.1
  refine ⟨fun z => hz (M z), ?_, ?_, printed_grid_counterexample.2.2⟩
  all_goals simp_rw [hz]; exact zero_sum_quantiles _


/-- T7: the corresponding exact clause under the specified independent Bernoulli(1/2) design, rather than an arbitrary design. The broader result remains an auxiliary lemma. -/
theorem summed_risk_counterexample_bernoulli :
    (∀ i j b, marginal (uniformLaw (Assignment 4)) (riskM i j) i b =
      ((riskBaseline i : ℝ) - 321 * bit b) / 40000) ∧
    (∀ j, (1 / 4 : ℝ) * ∑ i,
      (marginal (uniformLaw (Assignment 4)) (riskM i j) i true - marginal (uniformLaw (Assignment 4)) (riskM i j) i false) = -321 / 40000) ∧
    (∀ j, hajek (fun i z => riskM i j z) ![true, true, false, false] = -321 / 40000) ∧
    (∑ _j : Fin 4, (-321 / 40000 : ℝ)) = -321 / 10000 ∧
    (379 / 40000 - 7 / 400 : ℝ) = -321 / 40000 ∧
    (7 / 400 - 321 / 10000 : ℝ) = -73 / 5000 ∧
    (-73 / 5000 : ℝ) < 0 ∧
    (∑ _j : Fin 4, (-1 : ℝ)) = -4 ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → a - b ≠ -4) :=
  summed_risk_counterexample (uniformLaw (Assignment 4))

/-- T7: the corresponding exact clause under the specified independent Bernoulli(1/2) design, rather than an arbitrary design. The broader result remains an auxiliary lemma. -/
theorem binary_companion_counterexample_bernoulli :
    (∀ i j k z, companionRiskOutcome i j k z = 0 ∨ companionRiskOutcome i j k z = 1) ∧
    (∀ i j z, companionRiskM i j z = 1 - bit (z i)) ∧
    (∀ j, finiteAMR (uniformLaw (Assignment 4)) (fun i z => companionRiskM i j z) = -1) ∧
    (∑ j : Fin 4, finiteAMR (uniformLaw (Assignment 4)) (fun i z => companionRiskM i j z)) = -4 ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      a - b ≠ ∑ j : Fin 4, finiteAMR (uniformLaw (Assignment 4)) (fun i z => companionRiskM i j z)) :=
  binary_companion_counterexample (uniformLaw (Assignment 4))

/-- T7: the corresponding exact clause under the specified independent Bernoulli(1/2) design, rather than an arbitrary design. The broader result remains an auxiliary lemma. -/
theorem risk_sampling_probabilities_bernoulli :
    riskSamplingProbability (uniformLaw (Assignment 4)) false = 7 / 400 ∧
    riskSamplingProbability (uniformLaw (Assignment 4)) true = 379 / 40000 ∧
    riskSamplingProbability (uniformLaw (Assignment 4)) true - riskSamplingProbability (uniformLaw (Assignment 4)) false = -321 / 40000 :=
  risk_sampling_probabilities (uniformLaw (Assignment 4))

/-- T18(a–c) with actual node-to-cell-centroid Euclidean distances.
At the supplied index `d`, the weights are arbitrary nonnegative normalized
cell weights; no hypothesis identifies them with shares of a radius-`d` circle. -/
theorem spatial_toy_raster_amr_formula {C : ℕ} (Q : FiniteLaw (Assignment 4))
    (node : Fin 4 → Plane) (cell : Fin C → Plane) (base : Fin C → ℝ)
    (w : ℝ → Fin 4 → Fin C → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (hw : ∀ i c, 0 ≤ w d i c) (hs : ∀ i, ∑ c, w d i c = 1) :
    (∀ a i c z, toyRasterOutcome a base (fun i c => dist (node i) (cell c)) c (Function.update z i true) -
      toyRasterOutcome a base (fun i c => dist (node i) (cell c)) c (Function.update z i false) = a * toyKernel ((fun i c => dist (node i) (cell c)) i c)) ∧
    (∀ a i c, marginal Q (toyRasterOutcome a base (fun i c => dist (node i) (cell c)) c) i true -
      marginal Q (toyRasterOutcome a base (fun i c => dist (node i) (cell c)) c) i false = a * toyKernel ((fun i c => dist (node i) (cell c)) i c)) ∧
    (∀ a, toyRasterAMR Q a base (fun i c => dist (node i) (cell c)) (w d) =
      (1 / 4 : ℝ) * ∑ i, ∑ c, (w d) i c * (a * toyKernel ((fun i c => dist (node i) (cell c)) i c))) ∧
    toyRasterAMR Q 3 base (fun i c => dist (node i) (cell c)) (w d) = 3 * toyRasterAMR Q 1 base (fun i c => dist (node i) (cell c)) (w d) ∧
    -(384 / 437 : ℝ) < toyRasterAMR Q 1 base (fun i c => dist (node i) (cell c)) (w d) :=
  toy_raster_amr_formula Q base (fun i c => dist (node i) (cell c)) (w d)
    hw hs (fun _ _ => dist_nonneg)

/-- T5/T6 finite fair-design fact: under independent Bernoulli(1/2)
assignment, each numerical treatment indicator has expectation one half. -/
theorem uniform_bit_expect {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    (uniformLaw (I → Bool)).expect (fun z => bit (z i)) = 1 / 2 := by
  rw [uniform_average_update _ i]
  have he : (fun z : I → Bool =>
      (bit (Function.update z i false i) + bit (Function.update z i true i)) / 2) =
      (fun _ => (1 / 2 : ℝ)) := by
    funext z
    simp [bit]
  rw [he, expect_const]

/-- T5's replicated construction has the same actual marginalized means
at every node: treatment b gives bit(b)+1/4, hence m1=5/4 and m0=1/4. -/
theorem replicated_spatial_marginals (M : ℕ) (hM : 0 < M)
    (i : Fin M × Fin 2) (b : Bool) :
    (uniformLaw ((Fin M × Fin 2) → Bool)).expect
      (fun z => replicatedCircleM i (Function.update z i b)) = bit b + 1 / 4 := by
  classical
  have hm := (replicated_spatial_counterexample M hM).2.2.2.1
  rcases i with ⟨g, k⟩
  fin_cases k
  · simp only [Prod.fst, Prod.snd, Fin.reduceFinMk]
    have he : (fun z : (Fin M × Fin 2) → Bool =>
        replicatedCircleM (g, 0) (Function.update z (g, 0) b)) =
        (fun z => bit b + (1 / 2 : ℝ) * bit (z (g, 1))) := by
      funext z
      rw [(hm g _).1]
      simp <;> ring
    rw [he, expect_add, expect_const, expect_mul_const, uniform_bit_expect]
    ring
  · simp only [Prod.fst, Prod.snd, Fin.reduceFinMk]
    have he : (fun z : (Fin M × Fin 2) → Bool =>
        replicatedCircleM (g, 1) (Function.update z (g, 1) b)) =
        (fun z => bit b + (1 / 2 : ℝ) * bit (z (g, 0))) := by
      funext z
      rw [(hm g _).2]
      simp <;> ring
    rw [he, expect_add, expect_const, expect_mul_const, uniform_bit_expect]
    ring

/-- T5's replication counterexample uses the actual Euclidean cutoff
indicator: its cutoff-one covariance variance is 1/(4N), while the full
variance, proved in replicated_spatial_counterexample, is 1/(2N). -/
theorem replicated_plane_cutoff_omission (M : ℕ) (hM : 0 < M) :
    (2 * M : ℝ)⁻¹ ^ 2 * ∑ i : Fin M × Fin 2, ∑ j : Fin M × Fin 2,
      (if dist (lineEmbedding (replicatedNode i)) (lineEmbedding (replicatedNode j)) ≤ 1 then
        (uniformLaw ((Fin M × Fin 2) → Bool)).cov
          (replicatedSpatialScore i) (replicatedSpatialScore j) else 0) =
      1 / (4 * (2 * M)) := by
  have hdist (i j : Fin M × Fin 2) :
      (dist (lineEmbedding (replicatedNode i)) (lineEmbedding (replicatedNode j)) ≤ 1) ↔
      |replicatedNode i - replicatedNode j| ≤ 1 := by
    rw [line_embedding_distance]
    norm_cast
  simp_rw [hdist]
  exact replicated_spatial_cutoff_omission M hM


end

end AronowAudit.P008
