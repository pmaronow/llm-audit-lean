import AronowAudit.P013.Wave1.CorrectedCoverageBlueprint

/-!
# P013-T18: refutation of printed Proposition 6.2

The printed claim asserts liminf Wald coverage `≥ 1-α` under nesting, standing positivity,
all-exposure Condition 3, literal Condition 5 and Condition 6. `Target` is its exact negation.

The witness is defined at every population size `N = n+1`: units `2b, 2b+1` share
randomization coordinate `b`; the `⌈N/2⌉` coordinates are independent draws from the
four-atom pair law `(ε,q,q,ε)` on `00,01,10,11`, `ε = 1/max(4,N)²`, `q = 1/2-ε`
(`pairAtomDesign`). Unit `i` takes the first or second bit of its coordinate
(`pairExposure`), so at odd `N` the last unit uses only the first bit of its own coordinate
(an independent fair singleton). Potential outcomes are `+1` at even and `-1` at odd
zero-based unit index at both exposures. At even `N ≥ 4` this is the paired witness
`pairedDesign (N/2)` (here `max 4 N = N`); the product support is relabelled by `Fin`
(`relabelDesign`). Small sizes `N ≤ 3` use the same positive law.

The even-size CLT follows from the general HT CLT `CorrectedCoverage.N5`, applied to the
witness (which satisfies comparison C3, genuine C5 and C6) and restricted to the cofinal
indices `n = 2k+3`. The finite-design and normal-limit statements `CorrectedCoverage.N1`–`N7`
provide the common probability infrastructure.
-/

set_option autoImplicit false

namespace AronowAudit.P013.Wave1.PrintedWald

open AronowAudit.P013 AronowAudit.P013.Wave1.CorrectedCoverage Filter Finset
open scoped BigOperators Topology NNReal ENNReal

noncomputable section

/-! ## The all-size witness -/

/-- Number of randomization coordinates at index `n` (population size `N = n+1`): `⌈N/2⌉`. -/
def wCoords (n : ℕ) : ℕ := (n + 2) / 2

/-- The pair atom law `(ε,q,q,ε)` with `ε = pairEpsilon (max 4 N)`. -/
def wAtom (n : ℕ) : Design (Fin 4) := pairAtomDesign (max 4 (n + 1)) (le_max_left 4 (n + 1))

/-- Independent coordinates (product law, before relabelling). -/
def wBase (n : ℕ) : Design (Fin (wCoords n) → Fin 4) := replicateDesign (wAtom n) (wCoords n)

/-- Unit `i` uses coordinate `⌊i/2⌋`. -/
def wIndex (n : ℕ) (i : Fin (n + 1)) : Fin (wCoords n) :=
  ⟨i.val / 2, by have := i.isLt; unfold wCoords; omega⟩

/-- Own binary exposure from the coordinate bit; outcome `+1` at even, `-1` at odd index. -/
def wBasePop (n : ℕ) : Population (wBase n) (n + 1) 2 where
  exposure z i := pairExposure (z (wIndex n i)) (decide (i.val % 2 = 1))
  outcome i _ := if i.val % 2 = 0 then 1 else -1

/-- Support size `4^⌈N/2⌉`. -/
def wSupport (n : ℕ) : ℕ := Fintype.card (Fin (wCoords n) → Fin 4)

/-- Support relabelling. -/
def wEquiv (n : ℕ) : (Fin (wCoords n) → Fin 4) ≃ Fin (wSupport n) := Fintype.equivFin _

/-- Relabelled design at index `n`. -/
def wDesign (n : ℕ) : Design (Fin (wSupport n)) := relabelDesign (wBase n) (wEquiv n)

/-- Relabelled population at index `n`. -/
def wPop (n : ℕ) : Population (wDesign n) (n + 1) 2 := relabelPopulation (wBasePop n) (wEquiv n)

/-- The experiment of size `n+1`. -/
def wExperiment (n : ℕ) : Experiment (n + 1) where
  supportSize := wSupport n
  exposureSize := 2
  design := wDesign n
  population := wPop n

/-- **N1.** Every marginal exposure probability is `1/2`, including fair singletons.
This follows from `pi_relabel`, `replicate_marginal` and the four-atom computation
as in `paired_pi`. -/
def N1 : Prop := ∀ (n : ℕ) (i : Fin (n + 1)) (d : Fin 2), pi (wPop n) i d = 1 / 2

/-- The witness sequence is parametrised by a proof of N1 for its positivity
fields. Treated label `1`, control label `0`. -/
def wSeq (h : N1) : ExperimentSequence where
  experiment := wExperiment
  treated _ := (1 : Fin 2)
  control _ := (0 : Fin 2)
  distinct _ := by show (1 : Fin 2) ≠ 0; decide
  positiveTreated n i := by
    show 0 < pi (wPop n) i 1 ∧ pi (wPop n) i 1 < 1
    rw [h n i 1]; norm_num
  positiveControl n i := by
    show 0 < pi (wPop n) i 0 ∧ pi (wPop n) i 0 < 1
    rw [h n i 0]; norm_num

/-- Genuine dependency graph: same coordinate (includes the diagonal). -/
def wGraph (n : ℕ) (i j : Fin (n + 1)) : Bool := decide (i.val / 2 = j.val / 2)

/-- The event "every pair is split" (`A_N`), on the relabelled support. -/
def wSplit (n : ℕ) (z : Fin (wSupport n)) : Prop :=
  ∀ i j : Fin (n + 1), i.val / 2 = j.val / 2 → i ≠ j →
    (wPop n).exposure z i ≠ (wPop n).exposure z j

/-- The deterministic ratio `V̂_N / V_N = (8-2/t_N)/(8t_N)` on the all-split event, at the
even size `N = 2k+4`. -/
def evenRatio (k : ℕ) : ℝ :=
  (8 - 2 / pairSplitProbability (2 * k + 4)) / (8 * pairSplitProbability (2 * k + 4))

/-!
## Printed coverage statement -/

/-- **Target (P013-T18).** Negation of printed Proposition 6.2
(p. 1926; Appendix A.7, p. 1943). -/
def Target : Prop :=
  ¬ ∀ S : ExperimentSequence, NestedPopulationSetup S → StandingPositivity S →
      Condition3 S → Condition5Printed S → Condition6 S →
        ∀ α : ℝ, 0 < α → α < 1 → 1 - α ≤ liminf (seqCoverage S α) atTop

/-- The explicit witness statement is stronger than `Target`: it also includes
genuine Condition 5 as a property of the witness. -/
def Witness : Prop :=
  ∃ S : ExperimentSequence, NestedPopulationSetup S ∧ StandingPositivity S ∧ Condition3 S ∧
    Condition5Printed S ∧ Condition5Genuine S ∧ Condition6 S ∧
    liminf (seqCoverage S (1 / 2 : ℝ)) atTop < (1 / 2 : ℝ)

/-!
## Supporting statements (N1 appears before `wSeq`) -/

/-- **N2.** The same-coordinate graph is a genuine dependency graph with row bound 2.
Separated disjoint unit sets depend on disjoint independent pair/singleton coordinates.
The proof uses `probability_relabel`, `coordinate_population_genuine_dependency`
(with index `wIndex n`) and the counting argument of `paired_row_bound`. -/
def N2 : Prop :=
  ∀ n : ℕ, GenuineDependency (wDesign n) (wPop n).exposure (wGraph n) ∧ RowBound (wGraph n) 2

/-- Score of coordinate `b`: `4(Z_first - Z_second)` for a full pair
(units `2b, 2b+1`), and `2(2Z_first - 1)` for the odd singleton (unit `2b` alone). -/
def coordScore (n : ℕ) (b : Fin (wCoords n)) (a : Fin 4) : ℝ :=
  if 2 * b.val + 1 < n + 1 then
    4 * (((pairExposure a false).val : ℝ) - ((pairExposure a true).val : ℝ))
  else 2 * (2 * ((pairExposure a false).val : ℝ) - 1)

/-- **N3.** With all marginals `1/2` (N1), `N τ̂_N` is the sum of the coordinate
scores of the underlying product assignment. A full pair has score `4(Z_a-Z_b)`;
an independent odd singleton has score `2(2Z-1)`. -/
def N3 : Prop :=
  N1 → ∀ (n : ℕ) (z : Fin (wSupport n)),
    ((n : ℝ) + 1) * htEffect (wPop n) 1 0 z = ∑ b, coordScore n b ((wEquiv n).symm z b)

/-- **N4.** The variance of a sum of coordinate functions under an independent
product design is the sum of the coordinate variances, by `replicate_marginal`,
`replicate_pair_marginal` and `covariance_sum_sum`. -/
def N4 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] (P : Design Ω) (R : ℕ) (g : Fin R → Ω → ℝ),
    variance (replicateDesign P R) (fun zs => ∑ r, g r (zs r)) = ∑ r, variance P (g r)

/-- **N5.** The exact true variance at every size satisfies
`N²V_N = 16⌊N/2⌋t + 4(N mod 2)`, with `t = pairSplitProbability (max 4 N)`.
This follows from N1, N3, N4, `expectation_relabel`, and the four-atom moments
of a full pair (`pair_score_moments`) and of the singleton bit. -/
def N5 : Prop :=
  N1 → N3 → N4 → ∀ n : ℕ,
    ((n : ℝ) + 1) ^ 2 * variance (wDesign n) (htEffect (wPop n) 1 0) =
      16 * (((n + 1) / 2 : ℕ) : ℝ) * pairSplitProbability (max 4 (n + 1)) +
        4 * (((n + 1) % 2 : ℕ) : ℝ)

/-- **N6.** The limit `N V_N → 8` gives Condition 6 with `c = 8` along every size. -/
def N6 : Prop :=
  Tendsto (fun n : ℕ => (16 * (((n + 1) / 2 : ℕ) : ℝ) * pairSplitProbability (max 4 (n + 1)) +
      4 * (((n + 1) % 2 : ℕ) : ℝ)) / ((n : ℝ) + 1)) atTop (𝓝 8)

/-- **N7.** At even sizes `N = 2k+4` (index `n = 2k+3`), distinct units
in a pair have same-exposure joint ε_N and cross-exposure joint q_N.
Joints between pairs are 1/4, as in `paired_joint`. -/
def N7 : Prop :=
  ∀ (k : ℕ) (i j : Fin (2 * k + 3 + 1)) (d e : Fin 2), i ≠ j →
    jointPi (wPop (2 * k + 3)) i j d e =
      if i.val / 2 = j.val / 2 then
        (if d = e then pairEpsilon (2 * k + 4) else 1 / 2 - pairEpsilon (2 * k + 4))
      else 1 / 4

/-- **N8.** On the all-split event at `N = 2k+4`, expression (7) consists of its
diagonal terms. Each unit realizes exactly one label and `(1-1/2)/(1/2)^2=2`.
Same-pair terms vanish on this event; distinct-pair covariance numerators vanish.
The identity follows by finite algebra from N1 and N7. -/
def N8 : Prop :=
  N1 → N7 → ∀ (k : ℕ) (z : Fin (wSupport (2 * k + 3))), wSplit (2 * k + 3) z →
    ∀ d : Fin 2, varianceHT (wPop (2 * k + 3)) d z =
      2 * ∑ i, indicator (wPop (2 * k + 3)).exposure i d z

/-- **N9.** The `Â₂` corrections of (11) vanish at every assignment at `N = 2k+4`,
since ε_N > 0. -/
def N9 : Prop :=
  N7 → ∀ (k : ℕ) (z : Fin (wSupport (2 * k + 3))) (d : Fin 2),
    correctionA2 (wPop (2 * k + 3)) d z = 0

/-- **N10.** On the all-split event at `N = 2k+4`, the positive-joint part of
expression (10) equals `r(1/q_N - 4)`, with `r = k+2` pairs. Each split pair
contributes one observed ordered (1,0) covariance term. Finite algebra from N1 and N7. -/
def N10 : Prop :=
  N1 → N7 → ∀ (k : ℕ) (z : Fin (wSupport (2 * k + 3))), wSplit (2 * k + 3) z →
    (∑ i, ∑ j ∈ univ.erase i, if 0 < jointPi (wPop (2 * k + 3)) i j 1 0 then
        pairTerm (wPop (2 * k + 3)) i j 1 0 z else 0) =
      ((k : ℝ) + 2) * (1 / (1 / 2 - pairEpsilon (2 * k + 4)) - 4)

/-- **N11.** The zero-joint correction subtracted in expression (10) equals
`N = 2k+4` at every assignment. Same-unit cross-exposure joints are zero and
distinct-unit cross-exposure joints are positive; each diagonal correction is
`I_1 y_1^2/(2π_1)+I_0 y_0^2/(2π_0)=1`. -/
def N11 : Prop :=
  N1 → N7 → ∀ (k : ℕ) (z : Fin (wSupport (2 * k + 3))),
    (∑ i, ∑ j, if jointPi (wPop (2 * k + 3)) i j 1 0 = 0 then
        indicator (wPop (2 * k + 3)).exposure i 1 z * (wPop (2 * k + 3)).outcome i 1 ^ 2 /
            (2 * pi (wPop (2 * k + 3)) i 1) +
          indicator (wPop (2 * k + 3)).exposure j 0 z * (wPop (2 * k + 3)).outcome j 0 ^ 2 /
            (2 * pi (wPop (2 * k + 3)) j 0) else 0) =
      2 * (k : ℝ) + 4

/-- **N12.** A finite union bound over coordinates gives `P(A_Nᶜ) ≤ r·2ε_N = 1/N`,
using `probability_relabel` and `replicate_marginal`. -/
def N12 : Prop :=
  ∀ k : ℕ, probability (wDesign (2 * k + 3)) (fun z => ¬ wSplit (2 * k + 3) z) ≤
    1 / (2 * (k : ℝ) + 4)

/-- **N13.** If `V̂ = bV` on `E`, with `V>0` and `b,z ≥ 0`, defined Wald
coverage and the true-variance event `|(X-τ)/√V| ≤ z√b` differ in probability
by at most `P(¬E)`. This compares the coverage and moving-width events on `A_N`. -/
def N13 : Prop :=
  ∀ {Ω : Type} [Fintype Ω] (P : Design Ω) (X Vhat : Ω → ℝ) (target V b z : ℝ) (E : Ω → Prop),
    0 < V → 0 ≤ b → 0 ≤ z → (∀ ω, E ω → Vhat ω = b * V) →
      |probability P (fun ω => 0 ≤ Vhat ω ∧ |X ω - target| ≤ z * Real.sqrt (Vhat ω)) -
        probability P (fun ω => |(X ω - target) / Real.sqrt V| ≤ z * Real.sqrt b)| ≤
      probability P (fun ω => ¬ E ω)

/-- **N14.** The variance ratio is nonnegative and tends to `3/4`; hence
`z√((8-2/t_N)/(8t_N)) → z√(3/4)`. -/
def N14 : Prop := (∀ k, 0 ≤ evenRatio k) ∧ Tendsto evenRatio atTop (𝓝 (3 / 4))

/-!
## Refutation -/

/-- `ε_N = 1/N²` at `N = 2k+4` is positive and at most `1/16`. -/
theorem pairEpsilon_even_bounds (k : ℕ) :
    0 < pairEpsilon (2 * k + 4) ∧ pairEpsilon (2 * k + 4) ≤ 1 / 16 := by
  unfold pairEpsilon
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h16 : (16 : ℝ) ≤ (((2 * k + 4 : ℕ) : ℝ)) ^ 2 := by push_cast; nlinarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- Each unit has exactly one of the two exposures. -/
theorem indicator_sum_fin_two {Ω : Type*} {N : ℕ} (D : Ω → Fin N → Fin 2) (z : Ω) :
    ∑ i, indicator D i 1 z + ∑ i, indicator D i 0 z = (N : ℝ) := by
  rw [← Finset.sum_add_distrib]
  have h : ∀ i, indicator D i 1 z + indicator D i 0 z = 1 := by
    intro i
    unfold indicator
    generalize D z i = x
    fin_cases x <;> simp
  simp [h]

/-- The exact even-size true variance, `V_N = 16(k+2)t/(2k+4)²` (from N5). -/
theorem even_variance (h1 : N1) (h3 : N3) (h4 : N4) (h5 : N5) (k : ℕ) :
    variance (wDesign (2 * k + 3)) (htEffect (wPop (2 * k + 3)) 1 0) =
      16 * ((k : ℝ) + 2) * pairSplitProbability (2 * k + 4) / (2 * (k : ℝ) + 4) ^ 2 := by
  have hV := h5 h1 h3 h4 (2 * k + 3)
  rw [show (2 * k + 3 + 1) / 2 = k + 2 by omega, show (2 * k + 3 + 1) % 2 = 0 by omega,
    show max 4 (2 * k + 3 + 1) = 2 * k + 4 by omega] at hV
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (2 * (k : ℝ) + 4) ≠ 0 := by positivity
  push_cast at hV
  field_simp
  linarith

/-- On the all-split event, `V̂_N = evenRatio k · V_N`, by N5 and N8–N11. -/
theorem split_estimator (h1 : N1) (h3 : N3) (h4 : N4) (h5 : N5) (h7 : N7) (h8 : N8)
    (h9 : N9) (h10 : N10) (h11 : N11) (k : ℕ)
    (z : Fin (wSupport (2 * k + 3))) (hz : wSplit (2 * k + 3) z) :
    effectVariance (wPop (2 * k + 3)) 1 0 z =
      evenRatio k * variance (wDesign (2 * k + 3)) (htEffect (wPop (2 * k + 3)) 1 0) := by
  have hs := indicator_sum_fin_two (wPop (2 * k + 3)).exposure z
  obtain ⟨he0, he1⟩ := pairEpsilon_even_bounds k
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hN : (2 * (k : ℝ) + 4) ≠ 0 := by positivity
  have hq : (1 / 2 - pairEpsilon (2 * k + 4)) ≠ 0 := by intro h; linarith
  have ht : (1 - 2 * pairEpsilon (2 * k + 4)) ≠ 0 := by intro h; linarith
  unfold effectVariance covarianceA
  rw [h8 h1 h7 k z hz 1, h8 h1 h7 k z hz 0, h9 h7 k z 1, h9 h7 k z 0, h10 h1 h7 k z hz,
    h11 h1 h7 k z, even_variance h1 h3 h4 h5 k]
  rw [show ∑ i, indicator (wPop (2 * k + 3)).exposure i 0 z =
      ((2 * k + 3 + 1 : ℕ) : ℝ) - ∑ i, indicator (wPop (2 * k + 3)).exposure i 1 z by
    linarith]
  unfold evenRatio pairSplitProbability
  push_cast
  field_simp
  ring

/-- The supporting statements give an explicit counterexample. -/
theorem assemble_witness (c1 : CorrectedCoverage.N1) (c2 : CorrectedCoverage.N2)
    (c3 : CorrectedCoverage.N3) (c4 : CorrectedCoverage.N4) (c5 : CorrectedCoverage.N5)
    (c6 : CorrectedCoverage.N6) (c7 : CorrectedCoverage.N7) (h1 : N1) (h2 : N2) (h3 : N3)
    (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7) (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11)
    (h12 : N12) (h13 : N13) (h14 : N14) : Witness := by
  let S := wSeq h1
  -- nesting: one global outcome table, labels `Fin.val`
  have hnest : NestedPopulationSetup S :=
    ⟨fun _ => ⟨Fin.val, Fin.val_injective⟩, 1, 0, fun i _ => if i % 2 = 0 then 1 else -1,
      by decide, fun _ => ⟨rfl, rfl⟩, fun _ _ _ => rfl⟩
  have hpos : StandingPositivity S := by
    intro n d i
    show 0 < pi (wPop n) i d ∧ pi (wPop n) i d < 1
    rw [h1 n i d]; norm_num
  have hc3 : Condition3 S := by
    refine ⟨1, 2, by norm_num, by norm_num, fun n i d => ⟨?_, ?_⟩⟩
    · show |(if i.val % 2 = 0 then (1 : ℝ) else -1)| ≤ 1
      split_ifs <;> norm_num
    · show |1 / pi (wPop n) i d| ≤ 2
      rw [h1 n i d]; norm_num
  have hc5p : Condition5Printed S :=
    ⟨1, fun n i j => decide (i = j), fun n => printed_identity_dependency _ _⟩
  have hc5g : Condition5Genuine S :=
    ⟨2, wGraph, fun n => ⟨fun i j => by simp [wGraph, eq_comm], (h2 n).1, (h2 n).2⟩⟩
  have hc6 : Condition6 S := by
    refine ⟨8, by norm_num, h6.congr (fun n => ?_)⟩
    show _ = ((n : ℝ) + 1) * variance (wDesign n) (htEffect (wPop n) 1 0)
    rw [← h5 h1 h3 h4 n]
    have : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  refine ⟨S, hnest, hpos, hc3, hc5p, hc5g, hc6, ?_⟩
  -- Gaussian constants
  have hmono := c6.2.1
  obtain ⟨hz0, hzcdf⟩ := c6.2.2.2 (1 / 2) (by norm_num) (by norm_num)
  set zc := normalCritical (1 / 2) with hzc
  set Lc := 2 * normalCDF (zc * Real.sqrt (3 / 4)) - 1 with hLc
  have hsq : Real.sqrt (3 / 4) < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hsq0 : 0 < Real.sqrt (3 / 4) := Real.sqrt_pos.mpr (by norm_num)
  have hL : Lc < 1 / 2 := by
    have hlt : zc * Real.sqrt (3 / 4) < zc := by
      have := mul_lt_mul_of_pos_left hsq hz0
      simpa using this
    have := hmono hlt
    rw [hzcdf] at this
    rw [hLc]; linarith
  -- even-size CLT from the general HT CLT, restricted to `n = 2k+3`
  have hclt := c5 c1 c3 (c4 c2) S (condition3_implies_comparison S hc3) hc5g hc6
  have hφ : Tendsto (fun k : ℕ => 2 * k + 3) atTop atTop := by
    apply tendsto_atTop_mono (fun k => (by omega : k ≤ 2 * k + 3)) tendsto_id
  have hsub : TendsNormal (fun k : ℕ => seqLaw S (2 * k + 3))
      (fun k z => (seqEstimate S (2 * k + 3) z - seqTarget S (2 * k + 3)) /
        Real.sqrt (seqTrueVariance S (2 * k + 3))) 0 1 := fun x => (hclt x).comp hφ
  have hw : Tendsto (fun k => zc * Real.sqrt (evenRatio k)) atTop
      (𝓝 (zc * Real.sqrt (3 / 4))) :=
    ((Real.continuous_sqrt.tendsto _).comp h14.2).const_mul zc
  have hlim := c7 c6 _ _ _ _ hsub (mul_pos hz0 hsq0) hw
  -- the defined coverage differs from the moving-width event by at most `1/N`
  have hcmp : ∀ k : ℕ, |seqCoverage S (1 / 2) (2 * k + 3) -
      probability (seqLaw S (2 * k + 3)) (fun z =>
        |(seqEstimate S (2 * k + 3) z - seqTarget S (2 * k + 3)) /
          Real.sqrt (seqTrueVariance S (2 * k + 3))| ≤ zc * Real.sqrt (evenRatio k))| ≤
      1 / (2 * (k : ℝ) + 4) := by
    intro k
    have hVpos : 0 < variance (wDesign (2 * k + 3)) (htEffect (wPop (2 * k + 3)) 1 0) := by
      rw [even_variance h1 h3 h4 h5 k]
      obtain ⟨he0, he1⟩ := pairEpsilon_even_bounds k
      have ht : 0 < pairSplitProbability (2 * k + 4) := by
        unfold pairSplitProbability; linarith
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      positivity
    exact (h13 (wDesign (2 * k + 3)) (htEffect (wPop (2 * k + 3)) 1 0)
      (effectVariance (wPop (2 * k + 3)) 1 0) (causalEffect (wPop (2 * k + 3)) 1 0)
      (variance (wDesign (2 * k + 3)) (htEffect (wPop (2 * k + 3)) 1 0)) (evenRatio k) zc
      (wSplit (2 * k + 3)) hVpos (h14.1 k) hz0.le
      (fun z hz => split_estimator h1 h3 h4 h5 h7 h8 h9 h10 h11 k z hz)).trans (h12 k)
  -- hence the even-size coverage tends to `Lc`
  have hcov : Tendsto (fun k : ℕ => seqCoverage S (1 / 2) (2 * k + 3)) atTop (𝓝 Lc) := by
    have hdiff : Tendsto (fun k : ℕ => seqCoverage S (1 / 2) (2 * k + 3) -
        probability (seqLaw S (2 * k + 3)) (fun z =>
          |(seqEstimate S (2 * k + 3) z - seqTarget S (2 * k + 3)) /
            Real.sqrt (seqTrueVariance S (2 * k + 3))| ≤ zc * Real.sqrt (evenRatio k)))
        atTop (𝓝 0) := by
      have hb : Tendsto (fun k : ℕ => 1 / (2 * (k : ℝ) + 4)) atTop (𝓝 0) := by
        have : Tendsto (fun k : ℕ => 2 * (k : ℝ) + 4) atTop atTop :=
          tendsto_atTop_add_const_right _ 4
            (Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
        exact tendsto_const_nhds.div_atTop this
      exact squeeze_zero_norm (fun k => by simpa [Real.norm_eq_abs] using hcmp k) hb
    have := hdiff.add hlim
    simp only [sub_add_cancel, zero_add] at this
    exact this
  -- liminf of the full sequence is at most the subsequential limit
  have hfreq : ∃ᶠ n in atTop, seqCoverage S (1 / 2) n ≤ Lc + (1 / 2 - Lc) / 2 := by
    rw [frequently_atTop]
    intro N0
    have hev := (hcov.eventually (gt_mem_nhds (by linarith : Lc < Lc + (1 / 2 - Lc) / 2)))
    obtain ⟨K, hK⟩ := eventually_atTop.mp hev
    exact ⟨2 * (max K N0) + 3, by omega, (hK (max K N0) (le_max_left _ _)).le⟩
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (seqCoverage S (1 / 2)) :=
    isBoundedUnder_of ⟨0, fun n => probability_nonneg _ _⟩
  have := liminf_le_of_frequently_le hfreq hbdd
  linarith

/-- The explicit counterexample refutes the printed claim. -/
theorem assemble (c1 : CorrectedCoverage.N1) (c2 : CorrectedCoverage.N2)
    (c3 : CorrectedCoverage.N3) (c4 : CorrectedCoverage.N4) (c5 : CorrectedCoverage.N5)
    (c6 : CorrectedCoverage.N6) (c7 : CorrectedCoverage.N7) (h1 : N1) (h2 : N2) (h3 : N3)
    (h4 : N4) (h5 : N5) (h6 : N6) (h7 : N7) (h8 : N8) (h9 : N9) (h10 : N10) (h11 : N11)
    (h12 : N12) (h13 : N13) (h14 : N14) : Target := by
  intro hall
  obtain ⟨S, hn, hp, hc3, hc5, -, hc6, hlt⟩ :=
    assemble_witness c1 c2 c3 c4 c5 c6 c7 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  have := hall S hn hp hc3 hc5 hc6 (1 / 2) (by norm_num) (by norm_num)
  linarith

end

end AronowAudit.P013.Wave1.PrintedWald
