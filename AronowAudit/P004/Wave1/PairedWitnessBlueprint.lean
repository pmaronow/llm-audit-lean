import AronowAudit.P004.Wave1.LinePopulationBlueprint

/-! # Shared blueprint module: the paired spatial-block witness for both T35 refutations

Paper proof: map-P004 REPORT, records 3 and 4 (identical "Paper proof" sections), accepted by
both referees. For even `N`, nodes are matched `0↔1, 2↔3, …` and `R_i(z) = z_i − z_{mate(i)}`;
for odd `N` the table is zero. The spatial realization is `linePopulation` (points `(10 i,0)`,
unit Dirac masses, band `[0,d]`). The logistic part is `k = 1`, `O_i = 1`, `θ₀ = 0`,
`Θ = {0}`, `θ̂ = 0`, so every propensity is `1/2`. The scalar parameters are `d = 0`, `h = 10`.

For every positive even `N` the population fits are `±1/2`, the true variance of the printed
augmented estimator is `2/N`, while both printed quantities (`printedSecondMomentBound` and
`printedVarianceFormula`, with the literal `i` fit in the `j` residual and the unsigned pair
term) equal `1/N`; `printedHomophilyQ = 0` for every `N`.

Nodes `PW1`-`PW11` are leaves. Two assembled facts are proved here: `guards` (all outer
hypotheses of both T35 contracts at this witness) and `mismatch` (the exact values used by
both refutations, rewritten into the form in which they occur in the contracts).
-/

namespace AronowAudit.P004.Wave1.PairedWitness

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators Classical

/-- The paired table: for even `N`, `R_i(z) = bit z_i − bit z_{mate i}`, where the mate of
`i` is the other index with the same `i / 2`; for odd `N` it is zero. -/
def pairedTable (N : ℕ) : CircleTable N := fun i z =>
  if Even N then
    bit (z i) - ∑ j : Fin N, (if j ≠ i ∧ j.val / 2 = i.val / 2 then bit (z j) else 0)
  else 0

/-- The spatial witness: the counting-measure line realization of `pairedTable`. -/
def pairedPop (N : ℕ) : SpatialPopulation N (EuclideanSpace ℝ (Fin 2)) :=
  linePopulation (pairedTable N)

/-- One constant regressor. -/
def pairO (N : ℕ) : Fin N → Fin 1 → ℝ := fun _ _ => 1

/-- The true coefficient `θ₀ = 0`. -/
def pairTheta : Fin 1 → ℝ := fun _ => 0

/-- The compact singleton parameter set `{0}` (allowed: no interiority guard is recorded). -/
def pairThetaSet : Set (Fin 1 → ℝ) := {pairTheta}

/-- The constrained MLE over the singleton set. -/
def pairThetaHat (N : ℕ) : Assignment N → Fin 1 → ℝ := fun _ => pairTheta

/-- The population fits `g_i(1) = 1/2`, `g_i(0) = −1/2` at positive even `N`. -/
def pairFit (N : ℕ) : Fin N → Bool → ℝ := fun _ a => if a then 1/2 else -1/2

/-- PW1 (paper proof: "Take k=1 and O_i=(1), θ₀=(0), Θ={0}, θhat_N(z)=0. The parameter set
is compact and contains θ₀. Its only point is a maximizer of every likelihood ... Regressors
have absolute value one, and for N≥1 the Gram form is ... v², so the positive lower bound c=1
works"). Use `isCompact_singleton`, `Filter.eventually_ge_atTop 1`, `dot`, `Fin.sum_univ_one`. -/
def PW1 : Prop := LogisticConditions pairO pairTheta pairThetaSet pairThetaHat

/-- PW2 (paper proof: "Logistic(0)=1/2, and overlap holds with ε=1/4"). -/
def PW2 : Prop := Overlap (fun N => propensities (pairO N) pairTheta)

/-- PW3: every true propensity equals `1/2` (`logistic 0 = 1/2`, `Real.exp_zero`). -/
def PW3 : Prop := ∀ N, propensities (pairO N) pairTheta = fun _ => 1/2

/-- PW4 (paper proof: "has absolute value ≤1 at them"): the table is bounded by one. At most
one summand of the mate sum is nonzero. -/
def PW4 : Prop := ∀ N (i : Fin N) (z : Assignment N), |pairedTable N i z| ≤ 1

/-- PW5 (paper proof: "Each R_k depends only on its own coin and its mate's coin, at distance
at most 10 from c_k"): flipping a coordinate at index distance `> 1` leaves `R_j` unchanged. -/
def PW5 : Prop :=
  ∀ N (j k : Fin N) (z : Assignment N) (b : Bool),
    10 < 10 * |(j : ℝ) - (k : ℝ)| → pairedTable N j (Function.update z k b) = pairedTable N j z

/-- PW6 (paper proof: "At d=0 shared sources occur only within a matched pair, so the chosen
h=10 is valid"): the target-band locality at cutoff `h = 10`, stated for the table itself
(the assembly rewrites the band-0 average by `LinePopulation.N3`). Use `LinePopulation.N1`:
interference of `pairedTable` at `l` forces `l = i` or `l` the mate of `i`. -/
def PW6 : Prop := ∀ N, LocalAt (pairedTable N) (nodeSeparation (pairedPop N)) 10

/-- PW7 (paper proof: "conditional on Z_i=1, R_i has mean 1/2 ... the scalar information
matrix is 1/4 and the two beta coefficients are 1/2 and −1/2"): exact printed fits at positive
even `N`. Use `marginal_is_marginalization`, `expect_split`, the `1×1` inverse
(`Matrix.inv_def` or `Matrix.inv_eq_left_inv`), `beta`, `information`, `dot`. -/
def PW7 : Prop :=
  ∀ N, Even N → 0 < N →
    printedFits (fun _ => 1/2) (pairedTable N) (pairO N) = pairFit N

/-- PW8 (paper proof: "residualEffect=1−(1/2−(−1/2))=0. For odd N the table, both fits, and
residual effects are zero. At N=0 there are no i. Hence printedHomophilyQ=0 for every N and
every chosen neighborhood"). Every summand has the factor `residualEffect … i = 0`. -/
def PW8 : Prop :=
  ∀ N (B : Fin N → Finset (Fin N)),
    printedHomophilyQ (fun _ => 1/2) (pairedTable N) B
      (printedFits (fun _ => 1/2) (pairedTable N) (pairO N)) = 0

/-- PW9 (paper proof: "augmented_N=1−(2/N)Σ_{matched pairs}s_i s_j. The N/2 pair products
are independent Rademacher variables ... Var(augmented_N)=4(N/2)/N²=2/N"). Compute
`E[aug] = 1` and `E[aug²] = 1 + 2/N` from `E[s_i s_{m i} s_k s_{m k}] = [k ∈ {i, m i}]`;
use `GraphCompletion.expect_mul_of_disjoint_depends`, `bernoulli_positive_power`. -/
def PW9 : Prop :=
  ∀ N, Even N → 0 < N →
    variance (fun _ => 1/2) (augmented (fun _ => 1/2) (pairedTable N) (pairFit N)) = 2 / N

/-- PW10 (paper proof: "each diagonal contribution (1/4)/(1/2)+(1/4)/(1/2) is 1 ... For a
matched ordered pair ... [Σ_a(1/2−a)][Σ_b(1/2−b)]=0. For distinct nodes in different pairs
... conditional mean zero ... printedSecondMomentBound ... =1/N"). Every off-diagonal
`pairMarginal` sum vanishes for EVERY ordered pair `i ≠ j`, so the value is `1/N` for every
neighborhood family `B`. -/
def PW10 : Prop :=
  ∀ N, Even N → 0 < N → ∀ B : Fin N → Finset (Fin N),
    printedSecondMomentBound (fun _ => 1/2) (pairedTable N) B (pairFit N) = 1 / N

/-- PW11 (paper proof: "every marginal residual mean is zero, so the subtracted squared-effect
and signed mean-product terms in printedVarianceFormula vanish ... printedVarianceFormula=1/N"),
again for every `B`. Shares its diagonal and pair computations with PW10. -/
def PW11 : Prop :=
  ∀ N, Even N → 0 < N → ∀ B : Fin N → Finset (Fin N),
    printedVarianceFormula (fun _ => 1/2) (pairedTable N) B (pairFit N) = 1 / N

/-- The seven outer guards shared by both T35 contracts, at the paired witness with `d = 0`,
`h = 10` (proved from the nodes). -/
theorem guards (l3 : LinePopulation.N3) (l4 : LinePopulation.N4)
    (l5 : LinePopulation.N5) (l6 : LinePopulation.N6) (l7 : LinePopulation.N7)
    (hPW1 : PW1) (hPW2 : PW2) (hPW4 : PW4) (hPW5 : PW5) (hPW6 : PW6) :
    SpatialLocalConditions pairedPop ∧
    (∀ᶠ N in atTop, WellDefined (pairedPop N) 0) ∧
    (∀ᶠ N in atTop, LocalAt (circleAverage (pairedPop N) 0) (nodeSeparation (pairedPop N)) 10) ∧
    LogisticConditions pairO pairTheta pairThetaSet pairThetaHat ∧
    Overlap (fun N => propensities (pairO N) pairTheta) := by
  refine ⟨LinePopulation.spatialLocal_of l5 l6 l7 pairedTable 1 10 zero_le_one
      (by norm_num) hPW4 hPW5, Filter.Eventually.of_forall fun N => l4 _ 0 le_rfl,
    Filter.Eventually.of_forall fun N => ?_, hPW1, hPW2⟩
  change LocalAt (circleAverage (linePopulation (pairedTable N)) 0)
    (nodeSeparation (pairedPop N)) 10
  rw [l3]
  exact hPW6 N

/-- The exact values used by both refutations, in the form in which they occur in the
contracts (proved from the nodes). -/
theorem mismatch (l3 : LinePopulation.N3) (hPW3 : PW3) (hPW7 : PW7) (hPW8 : PW8)
    (hPW9 : PW9) (hPW10 : PW10) (hPW11 : PW11) :
    (∀ N, 0 ≤ printedHomophilyQ (propensities (pairO N) pairTheta)
      (circleSequence pairedPop 0 N) (spatialNeighborhoods pairedPop 10 N)
      (printedFits (propensities (pairO N) pairTheta) (circleSequence pairedPop 0 N) (pairO N))) ∧
    (∀ N, Even N → 0 < N →
      variance (propensities (pairO N) pairTheta)
        (augmented (propensities (pairO N) pairTheta) (circleSequence pairedPop 0 N)
          (printedFits (propensities (pairO N) pairTheta) (circleSequence pairedPop 0 N)
            (pairO N))) = 2 / N ∧
      printedSecondMomentBound (propensities (pairO N) pairTheta)
        (circleSequence pairedPop 0 N) (spatialNeighborhoods pairedPop 10 N)
        (printedFits (propensities (pairO N) pairTheta) (circleSequence pairedPop 0 N)
          (pairO N)) = 1 / N ∧
      printedVarianceFormula (propensities (pairO N) pairTheta)
        (circleSequence pairedPop 0 N) (spatialNeighborhoods pairedPop 10 N)
        (printedFits (propensities (pairO N) pairTheta) (circleSequence pairedPop 0 N)
          (pairO N)) = 1 / N) := by
  have htab : ∀ N, circleSequence pairedPop 0 N = pairedTable N := fun N => l3 _
  refine ⟨fun N => ?_, fun N hE hN => ?_⟩
  · rw [htab, hPW3, hPW8]
  · rw [htab, hPW3, hPW7 N hE hN]
    exact ⟨hPW9 N hE hN, hPW10 N hE hN _, hPW11 N hE hN _⟩

/-- Elementary arithmetic used by both refutations: an eventual property holds at some
positive even `N`. -/
theorem exists_even_pos_of_eventually {Q : ℕ → Prop} (h : ∀ᶠ N in atTop, Q N) :
    ∃ N, Even N ∧ 0 < N ∧ Q N := by
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp h
  refine ⟨2 * (N0 + 1), even_two_mul _, by omega, hN0 _ (by omega)⟩

end
end AronowAudit.P004.Wave1.PairedWitness
