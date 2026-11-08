import AronowAudit.P046.P046_Audit

/-!
# Blueprint: P046-T6, refutation of `proposition3_printed`

Wave 1, group P005-P006-P017-P023-P046-P047. Resolution `refute` (mapper §8, accepted by both
referees with no fixes).

The frozen record `AronowAudit.P046.proposition3_printed` (P046_Audit.lean, line 231) asserts
Proposition 3 as printed (p. 7, Appendix A pp. 15–16): the random-`ξ` Hoeffding radius centred at
the population `μ` has tail probability at most `α` for every valid study, `n > 0` and
`0 < α < 1`. `Target` is its exact negation (checked by `rfl`; no universe parameters).

Witness (mapper, existing definitions): `IntervalExample.study` (independent uniform `W`, `U`;
`π(w) = 13/20` for `w ≤ 3/5`, `99/100` otherwise; `X = 1{U ≤ π(W)}`, `Y0 = 0`,
`Y1 = 1{W ≤ 3/5}`, `δ = 1/200`), `n = 100`, `α = 10⁻⁷`. On the count state `(K, S) = (k, s)`
(`K` = #low units, `S` = #low treated units) `HT = s/65`, `μ = 39/65`, `ξ = xiK k`; the proved
integer cutoff `cut17` and `log 20000000 < 17` give strict noncoverage, and the proved certificate
`lower_mass_exceeds_alpha` gives mass `> α`. The final step is exactly the (currently admitted)
statement of `IntervalExample.count_mass_bridge`, which is node S7 here under a fresh name.

Writers: prove `theorem nk_proof : Nk` in `AronowAudit/P046/Wave1/PropositionThree/Nk.lean`.
`Sk` is the statement of node k; `Nk` is `Sk` with, as hypotheses, the statements it may use.
Do not use the admitted `count_mass_bridge`, `exact_noncoverage`, `IntervalExample.counterexample`
or `proposition3_*` (proofs are `sorry`). Proved and usable: `probability_continuity_mean`,
`measurable_generate`, `covariate_law`, `score_positivity`, `unitUniform_Iic`,
`unitUniform_bernE`, `measurable_threshold`, `atomless_of_uniform_marginal`,
`condIndepFun_congr_left`, `indepFun_map_iff`, `cutoff_implies_squared_exclusion`,
`log_lt_seventeen`, `lower_mass_exceeds_alpha`; template `ConditionalExample.study_valid`.
-/

set_option autoImplicit false

namespace AronowAudit.P046.Wave1.PropositionThree

open AronowAudit.P046 AronowAudit.P046.IntervalExample MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

noncomputable section

/-! ## Frozen target -/

/-- **Target (P046-T6).** The exact negation of the frozen printed contract
`proposition3_printed` (Proposition 3 as printed). -/
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

/-! ## Node statements -/

/-- **Statement S1** (mapper §8 step 1, "For every bounded measurable test f(W), Fubini and the
length of [0,p(w)] give E[f(W)X]=∫_0^1 f(w)p(w)dw ... this characterizes the stored conditional
propensity"): the `propensity` field of `ValidStudy` for the variable-propensity study. Use
`ae_eq_condExp_of_forall_setIntegral_eq` (sets of `covariateSigma` are `W ⁻¹' B`),
`integral_map` with `measurable_generate`, `integral_prod` and `unitUniform_Iic`
(`score w ∈ [0,1]`). -/
def S1 : Prop :=
  condExp covariateSigma IntervalExample.study.law X =ᵐ[IntervalExample.study.law]
    fun o => IntervalExample.study.pi (W o)

/-- **Statement S2** (mapper §8 step 1, "Verify ValidStudy"): all fields, with S1 for the
propensity field. Follow `ConditionalExample.study_valid` (Y0 = 0 a.s.; Y1 = m(W) a.s., hence
`condIndepFun_of_measurable_left`; `condExp_of_stronglyMeasurable` for the regression). -/
def S2 : Prop := ValidStudy IntervalExample.study

/-- **Statement S3** (mapper §8 step 2, "Their probabilities are respectively 39/100,21/100,40/100"):
the category map is measurable with the stated masses under the actual continuous law. Use
`Measure.map_apply` with `measurable_generate`, `Measure.prod_apply`/`lintegral` over `W`, and
`unitUniform_Iic`. -/
def S3 : Prop :=
  Measurable cat ∧ ∀ j : Fin 3, IntervalExample.study.law {o | cat o = j} = ENNReal.ofReal (catProb j)

/-- **Statement S4** (mapper §8 step 2, "fix a labeled category sequence. Independence gives the
product of its 100 category masses. Choose its k low positions in binom(100,k) ways and then its
s treated-low positions in binom(k,s) ways"): the generic trinomial count law of an i.i.d.
categorical sample. Suggested route: push forward by `fun a i => c (a i)` to
`Measure.pi (fun _ => ν.map c)` (`Measure.pi_map_pi`), compute singleton masses
(`Measure.pi_pi`), and count functions `Fin N → Fin 3` with prescribed fibre sizes
(`Finset.card_powersetCard`, an explicit bijection with pairs of nested subsets). -/
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

/-- **Statement S5** (mapper §8 steps 3–4, "On that count event ... HT=S/65, μ=39/65,
ξ=ξ_k ... C(k,s) implies ξ_k*17/200 < (s-39)²/65² ... printedRadius<|HT-μ|"): on every sample
whose units lie in the support of the generator (`Y0 = false`, `Y1 = 1{W ≤ 3/5}`), a cut-17
count state strictly excludes `μ`. Use `probability_continuity_mean` (`μ = 3/5`),
`cutoff_implies_squared_exclusion`, `Real.sqrt_lt'`/`Real.sqrt_lt_sqrt` with
`Real.sqrt_sq_eq_abs`, and `Finset.sum_ite`/`Finset.card_filter` for the two sums. -/
def S5 : Prop :=
  ∀ a : Sample 100, (∀ i, (a i).2.2 = (false, decide ((a i).1 ≤ 3 / 5))) →
    cut17 (countK a) (countS a) = true →
    printedRadius IntervalExample.study (1 / 10000000) a <
      |ht IntervalExample.study a - mu IntervalExample.study|

/-- **Statement S6** (mapper §8 step 2, generator support): almost every sample has all units in
the image of `generate`. Use `ae_map_iff` with `measurable_generate` for one unit, then
`ae_all_iff` and `Measure.quasiMeasurePreserving_eval` (or `Measure.pi`'s `ae` lemmas). -/
def S6 : Prop :=
  ∀ᵐ a ∂(sampleLaw IntervalExample.study 100), ∀ i, (a i).2.2 = (false, decide ((a i).1 ≤ 3 / 5))

/-- **Statement S7** (mapper §8 step 5, "By disjointness and step 4, tailProb ≥ P(strict
noncoverage) ≥ A/100^100"): exactly the statement of the admitted `count_mass_bridge`. The strict
event contains, up to the null set of S6, the disjoint union of the cut-17 count events (S5);
sum their masses (S3, S4 with `p = catProb`, `massNumerator`, `lowerNumerator`). The instance
`IsProbabilityMeasure study.law` is `probability_continuity_mean.1`. -/
def S7 : Prop :=
  (lowerNumerator : ℝ) / (100 : ℝ) ^ 100 ≤
    (sampleLaw IntervalExample.study 100
      {a | printedRadius IntervalExample.study (1 / 10000000) a <
        |ht IntervalExample.study a - mu IntervalExample.study|}).toReal

/-! ## Nodes (`Nk` = statements it may use → `Sk`) -/

/-- Node N1 = S1. -/
def N1 : Prop := S1
/-- Node N2: may use S1. -/
def N2 : Prop := S1 → S2
/-- Node N3 = S3. -/
def N3 : Prop := S3
/-- Node N4 = S4 (generic). -/
def N4 : Prop := S4
/-- Node N5 = S5. -/
def N5 : Prop := S5
/-- Node N6 = S6. -/
def N6 : Prop := S6
/-- Node N7: may use S3, S4, S5, S6. -/
def N7 : Prop := S3 → S4 → S5 → S6 → S7

/-! ## Assembly -/

/-- **Assembly.** The nodes suffice for the refutation. -/
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

/-- Fidelity check: `Target` is literally the negation of the frozen statement
`AronowAudit.P046.proposition3_printed` (only its type is read). -/
example : Target = ¬ type_of% @AronowAudit.P046.proposition3_printed := rfl

/-- Node S7 is literally the statement of the admitted `IntervalExample.count_mass_bridge`. -/
example : S7 = type_of% @AronowAudit.P046.IntervalExample.count_mass_bridge := rfl

end

end AronowAudit.P046.Wave1.PropositionThree
