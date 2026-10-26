import AronowAudit.P046.P046_Audit

/-!
# P046-T6: refutation of Proposition 3 as printed

Proposition 3 (p. 7, Appendix A pp. 15–16) asserts that the random-`ξ`
Hoeffding radius centred at the population `μ` has tail probability at most `α`
for every valid study, `n > 0` and `0 < α < 1`. `Target` is its negation.

The witness is `IntervalExample.study`: independent uniform `W`, `U`;
`π(w) = 13/20` for `w ≤ 3/5`, `99/100` otherwise; `X = 1{U ≤ π(W)}`,
`Y0 = 0`, `Y1 = 1{W ≤ 3/5}`, `δ = 1/200`, with `n = 100` and `α = 10⁻⁷`.
On the count state `(K, S) = (k, s)`, where `K` counts low units and `S` counts
low treated units, `HT = s/65`, `μ = 39/65`, `ξ = xiK k`. The integer cutoff
`cut17` and `log 20000000 < 17` give strict noncoverage, and
`lower_mass_exceeds_alpha` gives mass `> α`. Statement S7 bounds the
noncoverage probability below by the sum of the cut-17 count-state masses.

`Sk` denotes statement k; `Nk` expresses the implication from its hypotheses
to `Sk`.
-/

set_option autoImplicit false

namespace AronowAudit.P046.Wave1.PropositionThree

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

/-! ## Target -/

/-- Target P046-T6: the negation of Proposition 3 as printed. -/
def Target : Prop :=
  ¬ ∀ (M : Study) (_hM : ValidStudy M) (n : ℕ) (_hn : 0 < n) (alpha : ℝ)
      (_ha : 0 < alpha ∧ alpha < 1),
      tailProb M (ht M) (printedRadius M alpha (n := n)) ≤ alpha

/-! ## Count-state objects -/

/-- The three unit categories: `0` = low (`W ≤ 3/5`) treated, `1` = low untreated, `2` = high. -/
def cat (o : AronowAudit.P046.Unit) : Fin 3 :=
  if o.1 ≤ 3 / 5 then (if o.2.1 then 0 else 1) else 2

/-- Their probabilities `39/100, 21/100, 40/100`. -/
def catProb (j : Fin 3) : ℝ := ![39 / 100, 21 / 100, 40 / 100] j

/-- `K`: the number of low units in a sample. -/
def countK {N : ℕ} (a : Sample N) : ℕ := (univ.filter (fun i => cat (a i) ≠ 2)).card

/-- `S`: the number of low treated units in a sample. -/
def countS {N : ℕ} (a : Sample N) : ℕ := (univ.filter (fun i => cat (a i) = 0)).card

/-! ## Mathematical statements -/

/-- S1: the propensity identity for the variable-propensity study.
For bounded measurable f(W), Fubini and the length of [0,p(w)] give
E[f(W)X]=∫_0^1 f(w)p(w)dw, characterizing the conditional propensity. -/
def S1 : Prop :=
  condExp covariateSigma IntervalExample.study.law X =ᵐ[IntervalExample.study.law]
    fun o => IntervalExample.study.pi (W o)

/-- S2: validity of the study, with S1 giving the propensity identity.
Y0 = 0 almost surely and Y1 = m(W) almost surely, so the potential outcomes
are conditionally independent of treatment given W. -/
def S2 : Prop := ValidStudy IntervalExample.study

/-- S3: the category map is measurable with masses 39/100, 21/100, 40/100
under the continuous law. These follow by integrating the uniform generator. -/
def S3 : Prop :=
  Measurable cat ∧ ∀ j : Fin 3, IntervalExample.study.law {o | cat o = j} = ENNReal.ofReal (catProb j)

/-- S4: the generic trinomial count law of an i.i.d. categorical sample.
A labelled category sequence has probability equal to the product of its
category masses. There are binom(N,k) choices of low positions and
binom(k,s) choices of treated positions among them. Equivalently, the
category functions correspond to pairs of nested subsets. -/
def S4 : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν] (c : α → Fin 3),
    Measurable c → ∀ p : Fin 3 → ℝ, (∀ j, 0 ≤ p j) →
    (∀ j, ν {x | c x = j} = ENNReal.ofReal (p j)) →
    ∀ N k s : ℕ, s ≤ k → k ≤ N →
      (Measure.pi fun _ : Fin N => ν)
          {a | (univ.filter (fun i => c (a i) ≠ 2)).card = k ∧
            (univ.filter (fun i => c (a i) = 0)).card = s} =
        ENNReal.ofReal ((N.choose k : ℝ) * (k.choose s : ℝ) * p 0 ^ s * p 1 ^ (k - s) *
          p 2 ^ (N - k))

/-- S5: on every sample with Y0 = false and Y1 = 1{W ≤ 3/5},
a cut-17 count state strictly excludes μ. On that count event HT=S/65,
μ=39/65 and ξ=xiK K; the cutoff gives ξ*17/200 < (S-39)²/65²,
so the logarithm bound implies printedRadius < |HT-μ|. -/
def S5 : Prop :=
  ∀ a : Sample 100, (∀ i, (a i).2.2 = (false, decide ((a i).1 ≤ 3 / 5))) →
    cut17 (countK a) (countS a) = true →
    printedRadius IntervalExample.study (1 / 10000000) a <
      |ht IntervalExample.study a - mu IntervalExample.study|

/-- S6: almost every sample satisfies the potential-outcome identities
of the generator. The one-unit almost-sure identity lifts to each
coordinate of the finite product law. -/
def S6 : Prop :=
  ∀ᵐ a ∂(sampleLaw IntervalExample.study 100), ∀ i, (a i).2.2 = (false, decide ((a i).1 ≤ 3 / 5))

/-- S7: the noncoverage probability is at least the cut-17 count-state mass.
Up to the null set in S6, the strict noncoverage event contains the
disjoint union of the count events from S5. Their masses follow from
S3 and S4 with `p = catProb`, `massNumerator` and `lowerNumerator`. -/
def S7 : Prop :=
  (lowerNumerator : ℝ) / (100 : ℝ) ^ 100 ≤
    (sampleLaw IntervalExample.study 100
      {a | printedRadius IntervalExample.study (1 / 10000000) a <
        |ht IntervalExample.study a - mu IntervalExample.study|}).toReal

/-! ## Implications (`Nk` = hypotheses → `Sk`) -/

/-- Alias for `S1`. -/
def N1 : Prop := S1
/-- N2: S1 implies S2. -/
def N2 : Prop := S1 → S2
/-- Alias for `S3`. -/
def N3 : Prop := S3
/-- Alias for `S4`. -/
def N4 : Prop := S4
/-- Alias for `S5`. -/
def N5 : Prop := S5
/-- Alias for `S6`. -/
def N6 : Prop := S6
/-- N7: S3, S4, S5 and S6 imply S7. -/
def N7 : Prop := S3 → S4 → S5 → S6 → S7

/-! ## Refutation -/

/-- The seven statements imply the refutation. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7) :
    Target := by
  have hV : ValidStudy IntervalExample.study := h2 h1
  have hb : S7 := h7 h3 h4 h5 h6
  unfold S7 at hb
  intro hall
  have h := hall IntervalExample.study hV 100 (by norm_num) (1 / 10000000)
    ⟨by norm_num, by norm_num⟩
  have := hV.probability
  have hmono : (sampleLaw IntervalExample.study 100
      {a | printedRadius IntervalExample.study (1 / 10000000) a <
        |ht IntervalExample.study a - mu IntervalExample.study|}).toReal ≤
      tailProb IntervalExample.study (ht IntervalExample.study)
        (printedRadius IntervalExample.study (1 / 10000000) (n := 100)) := by
    unfold tailProb
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono fun a ha => ?_)
    simp only [Set.mem_ofPred_eq] at ha ⊢
    exact le_of_lt ha
  have hnat : ((100 ^ 100 : ℕ) : ℝ) < ((10000000 * lowerNumerator : ℕ) : ℝ) := by
    exact_mod_cast lower_mass_exceeds_alpha
  push_cast at hnat
  have hlow : (1 / 10000000 : ℝ) < (lowerNumerator : ℝ) / (100 : ℝ) ^ 100 := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  linarith

end

end AronowAudit.P046.Wave1.PropositionThree
