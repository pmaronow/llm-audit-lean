import AronowAudit.P004.Wave1.LinePopulationBlueprint
import AronowAudit.P004.Wave1.DesignLimitsBlueprint
import AronowAudit.P004.Wave1.FiniteConditioningBlueprint

/-! # Refutation of printed observational coverage (P004-T36)

Supplement A Proposition 4(i) asserts that the Wald interval formed from the fitted-IPW
numerator and the double-weighted observational SAH statistic has a coverage limit
`≥ 1−α` for every `α ∈ (0,1/2)`, under its hypotheses and a variance floor.
The target negates the full universal closure, with the `Space` binder and its instance
binders inside the negation, at universe `0`.

The witness `activePopulation` has two signed active nodes per eight, `R_i = a_i Z_i`,
group-indicator regressors, and `θ₀ = (0, −log 9)` interior to `[−log 19, log 19]²`.
Thus `p_H = 1/2` and `p_L = 1/10`. The groupwise clipped-proportion MLE satisfies the
logistic hypotheses. Information-inverse identities require both groups to be present
(`3 ≤ N`), and the random-radius limit uses `σ > 0`.

The limits are `N·Var(augmented) → 1/4`, `√N(fittedIPW − AME) ⇒ N(0,1/4)`, and
`N·printedSAH → 2/25`. At `α = 1/4`, coverage therefore tends to
`2Φ(z_{7/8}√(8/25))−1 < 3/4`, contradicting the asserted coverage by uniqueness of limits.
-/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

/-- Negation of the full universal closure (universe `0`) of the printed
observational-coverage assertion (P004-T36). -/
def Target : Prop :=
  ¬ (∀ {Space : ℕ → Type} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
      {k : ℕ} (P : PopulationSequence Space)
      (O : ∀ N, Fin N → Fin k → ℝ) (θ₀ : Fin k → ℝ) (Θ : Set (Fin k → ℝ))
      (θhat : ∀ N, Assignment N → Fin k → ℝ) (d h : ℝ)
      (_hd : 0 ≤ d) (_hh : 0 ≤ h) (_hP : SpatialLocalConditions P)
      (_hWD : ∀ᶠ N in atTop, WellDefined (P N) d)
      (_hloc : ∀ᶠ N in atTop, LocalAt (circleAverage (P N) d) (nodeSeparation (P N)) h)
      (_hlog : LogisticConditions O θ₀ Θ θhat)
      (_hoverlap : Overlap (fun N => propensities (O N) θ₀))
      (_hv : Nondegenerate (fun N => variance (propensities (O N) θ₀)
        (augmented (propensities (O N) θ₀) (circleAverage (P N) d)
          (printedFits (propensities (O N) θ₀) (circleAverage (P N) d) (O N))))),
      ∀ α : ℝ, 0 < α → α < 1/2 → PrintedCoverage (fun N =>
        prob (propensities (O N) θ₀) (fun z =>
          let R := circleAverage (P N) d
          let phat := propensities (O N) (θhat N z)
          let g := fun i a => dot (O N i) (fittedBeta phat R (O N) a z)
          |fittedIPW R (O N) (θhat N) z-ame (propensities (O N) θ₀) R| ≤
            normalQuantile (1-α/2)*Real.sqrt (printedSAH phat R (spatialNeighborhoods P h N) g z))) α)

/-! ## The witness objects (all `N`, including partial last blocks) -/

/-- `a_i ∈ {1,−1,0}`: `+1` at residue 0, `−1` at residue 1 modulo 8 (so
`activeTable N i z = activeSign N i * bit (z i)`). -/
def activeSign (N : ℕ) (i : Fin N) : ℝ :=
  if i.val % 8 = 0 then 1 else if i.val % 8 = 1 then -1 else 0

/-- `n_H`, the number of active nodes (residues 0 and 1). -/
def nH (N : ℕ) : ℝ := ((Finset.univ.filter (fun i : Fin N => activeGroup N i)).card : ℝ)

/-- `n_L = N − n_H`. -/
def nL (N : ℕ) : ℝ := ((Finset.univ.filter (fun i : Fin N => ¬ activeGroup N i)).card : ℝ)

/-- `s = Σ_H a_i ∈ {0, 1}` (and hence `AME = s/N`). -/
def sAct (N : ℕ) : ℝ := ∑ i : Fin N, activeSign N i

/-- `S = Σ_H a_i Z_i`. -/
def SAct (N : ℕ) (z : Assignment N) : ℝ := ∑ i, activeSign N i * bit (z i)

/-- `K = Σ_H Z_i`, the treated count of the active group. -/
def KAct (N : ℕ) (z : Assignment N) : ℝ := ∑ i, if activeGroup N i then bit (z i) else 0

/-- `J = Σ_L Z_i`, the treated count of the inactive group. -/
def JAct (N : ℕ) (z : Assignment N) : ℝ := ∑ i, if activeGroup N i then 0 else bit (z i)

/-- Clipping to `[1/20, 19/20]` (the logistic image of `[−log 19, log 19]`). -/
def clip (q : ℝ) : ℝ := max (1/20) (min (19/20) q)

/-- `logit q = log (q/(1−q))`. -/
def logit (q : ℝ) : ℝ := Real.log (q / (1 - q))

/-- `p̂_H`, the clipped treated proportion of the active group. -/
def pHatH (N : ℕ) (z : Assignment N) : ℝ := clip (KAct N z / nH N)

/-- `p̂_L`, the clipped treated proportion of the inactive group. -/
def pHatL (N : ℕ) (z : Assignment N) : ℝ := clip (JAct N z / nL N)

/-- The constrained MLE over `[−log 19, log 19]²`: groupwise logits of the clipped
proportions; an absent group keeps its true coordinate. -/
def activeMLE (N : ℕ) (z : Assignment N) : Fin 2 → ℝ :=
  ![if nH N = 0 then 0 else logit (pHatH N z),
    if nL N = 0 then -Real.log 9 else logit (pHatL N z)]

/-- `R = Σ_H Z_i (a_i − β̂_{1,H})²` with `β̂_{1,H} = S/(n_H p̂_H)`. -/
def RAct (N : ℕ) (z : Assignment N) : ℝ :=
  ∑ i, if activeGroup N i then
    bit (z i) * (activeSign N i - SAct N z / (nH N * pHatH N z))^2 else 0

/-! ## Auxiliary propositions -/

/-- O1: the table is bounded by one, depends only on its own assignment coordinate,
and satisfies target-band locality at cutoff `0`. -/
def O1 : Prop :=
  (∀ N (i : Fin N) (z : Assignment N), |activeTable N i z| ≤ 1) ∧
  (∀ N (j k : Fin N) (z : Assignment N) (b : Bool),
    0 < 10 * |(j : ℝ) - (k : ℝ)| → activeTable N j (Function.update z k b) = activeTable N j z) ∧
  (∀ N, LocalAt (activeTable N) (nodeSeparation (activePopulation N)) 0)

/-- O2: clipped logits lie in `[−log 19, log 19]` and invert the logistic map.
For positive group size and a treated count between zero and that size, the clipped
logit of the treated proportion maximizes the scalar likelihood on this interval. -/
def O2 : Prop :=
  (∀ q, -Real.log 19 ≤ logit (clip q) ∧ logit (clip q) ≤ Real.log 19) ∧
  (∀ q, logistic (logit (clip q)) = clip q) ∧
  (∀ n K : ℝ, 0 < n → 0 ≤ K → K ≤ n → ∀ θ, -Real.log 19 ≤ θ → θ ≤ Real.log 19 →
    K * θ - n * Real.log (1 + Real.exp θ) ≤
      K * logit (clip (K / n)) - n * Real.log (1 + Real.exp (logit (clip (K / n)))))

/-- O3: the group regressors, true parameter, parameter box and constrained MLE
satisfy `LogisticConditions`. -/
def O3 : Prop := LogisticConditions activeO activeTheta activeParameterSet activeMLE

/-- O4: the treatment probabilities are `1/2` in the active group and `1/10`
in the inactive group. -/
def O4 : Prop :=
  ∀ N, propensities (activeO N) activeTheta = fun i => if activeGroup N i then 1/2 else 1/10

/-- O5: the variance of the printed augmented estimator satisfies `Nondegenerate`
at the true propensities and population fits. -/
def O5 : Prop :=
  Nondegenerate (fun N => variance (propensities (activeO N) activeTheta)
    (augmented (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)
      (printedFits (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)
        (activeO N))))

/-- O6: for positive `N`, the fitted-IPW estimator equals `S/(N p̂_H)`
on every assignment. For every `N`, the AME equals `s/N`. -/
def O6 : Prop :=
  (∀ N, 0 < N → ∀ z, fittedIPW (activeTable N) (activeO N) (activeMLE N) z =
    SAct N z / (N * pHatH N z)) ∧
  (∀ N, ame (propensities (activeO N) activeTheta) (activeTable N) = sAct N / N)

/-- O7: for `N ≥ 3`, the printed SAH statistic equals
`Q² R/(N² p̂_H⁴)` on every assignment, where `Q` is the overall treated fraction. -/
def O7 : Prop :=
  ∀ N, 3 ≤ N → ∀ z,
    printedSAH (propensities (activeO N) (activeMLE N z)) (activeTable N)
      (spatialNeighborhoods activePopulation 0 N)
      (fun i a => dot (activeO N i)
        (fittedBeta (propensities (activeO N) (activeMLE N z)) (activeTable N) (activeO N) a z)) z =
      (armCount z true / N)^2 * RAct N z / ((N : ℝ)^2 * (pHatH N z)^4)

/-- O8: the centered signed treated count, divided by `√(n_H/4)`,
has a standard normal limit. -/
def O8 : Prop :=
  NormalLimit (fun N => propensities (activeO N) activeTheta)
    (fun N z => (SAct N z - sAct N / 2) / Real.sqrt (nH N / 4))

/-- O9: for positive `N`, the second moment of `S` is at most `N`, and
the second moment of `1−2p̂_H` is at most `1/n_H`. -/
def O9 : Prop :=
  ∀ N, 0 < N →
    expect (propensities (activeO N) activeTheta) (fun z => (SAct N z)^2) ≤ N ∧
    expect (propensities (activeO N) activeTheta) (fun z => (1 - 2 * pHatH N z)^2) ≤ 1 / nH N

/-- O10: `K/N`, `J/N`, `S/N` and `p̂_H` converge in probability to
`1/8`, `3/40`, `0` and `1/2`, respectively; `n_H/N` tends to `1/4`. -/
def O10 : Prop :=
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z => KAct N z / N - 1/8) ∧
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z => JAct N z / N - 3/40) ∧
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z => SAct N z / N - 0) ∧
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z => pHatH N z - 1/2) ∧
  Tendsto (fun N => nH N / N) atTop (nhds (1/4))

/-- O11: the fitted-IPW estimator minus the AME, multiplied by `√N`
and divided by `1/2`, has a standard normal limit. -/
def O11 : Prop :=
  NormalLimit (fun N => propensities (activeO N) activeTheta) (fun N z =>
    Real.sqrt N * (fittedIPW (circleAverage (activePopulation N) 0) (activeO N) (activeMLE N) z -
      ame (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)) / (1/2))

/-- O12: convergence in probability of `N·printedSAH` to `2/25` for the fitted witness. -/
def O12 : Prop :=
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z =>
    (N : ℝ) * printedSAH (propensities (activeO N) (activeMLE N z))
      (circleAverage (activePopulation N) 0) (spatialNeighborhoods activePopulation 0 N)
      (fun i a => dot (activeO N i) (fittedBeta (propensities (activeO N) (activeMLE N z))
        (circleAverage (activePopulation N) 0) (activeO N) a z)) z - 2/25)

/-- Congruence of design probabilities under pointwise equivalent events. -/
theorem prob_congr {N : ℕ} (p : Fin N → ℝ) (A B : Assignment N → Prop)
    (h : ∀ z, A z ↔ B z) : prob p A = prob p B := by
  have hAB : A = B := funext fun z => propext (h z)
  rw [hAB]

/-- The strict coverage deficit (proved from NF): `2Φ(2 z_{7/8} √(2/25)) − 1 < 3/4`. -/
theorem coverage_gap (nf : NF) :
    0 < normalQuantile (1 - 1/4/2) ∧
    2 * normalCDF (normalQuantile (1 - 1/4/2) * Real.sqrt (2/25) / (1/2)) - 1 < 3/4 := by
  obtain ⟨-, hmono, h0, -, hq, -, -⟩ := nf
  have hc : normalCDF (normalQuantile (1 - 1/4/2)) = 1 - 1/4/2 := hq _ (by norm_num) (by norm_num)
  have hcpos : 0 < normalQuantile (1 - 1/4/2) := by
    rw [← hmono.lt_iff_lt, h0, hc]
    norm_num
  refine ⟨hcpos, ?_⟩
  have hs : Real.sqrt (2/25) < 1/2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hlt : normalQuantile (1 - 1/4/2) * Real.sqrt (2/25) / (1/2) <
      normalQuantile (1 - 1/4/2) := by
    rw [div_lt_iff₀ (by norm_num)]
    nlinarith
  have := hmono hlt
  rw [hc] at this
  linarith

/-- The component bounds imply the result: instantiate the assumed universal assertion at the active sequence with
`d = h = 0` and `α = 1/4`, identify its coverage with the DL8 random-radius probability
(`|X| ≤ c√S ⟺ |√N X| ≤ c√(N S)` for `N > 0`), and contradict `3/4 ≤ L` by uniqueness of
limits and `coverage_gap`. -/
theorem assemble (l3 : LinePopulation.N3) (l4 : LinePopulation.N4) (l5 : LinePopulation.N5)
    (l6 : LinePopulation.N6) (l7 : LinePopulation.N7) (hO1 : O1) (hO3 : O3) (hO4 : O4)
    (hO5 : O5) (hO11 : O11) (hO12 : O12) (dl8 : DL8) (nf : NF) : Target := by
  intro H
  obtain ⟨hbd, hrng, hloc0⟩ := hO1
  have hP : SpatialLocalConditions activePopulation :=
    LinePopulation.spatialLocal_of l5 l6 l7 activeTable 1 0 zero_le_one le_rfl hbd hrng
  have hWD : ∀ᶠ N in atTop, WellDefined (activePopulation N) 0 :=
    Filter.Eventually.of_forall fun N => l4 _ 0 le_rfl
  have hloc : ∀ᶠ N in atTop,
      LocalAt (circleAverage (activePopulation N) 0) (nodeSeparation (activePopulation N)) 0 := by
    refine Filter.Eventually.of_forall fun N => ?_
    change LocalAt (circleAverage (linePopulation (activeTable N)) 0)
      (nodeSeparation (activePopulation N)) 0
    rw [l3]
    exact hloc0 N
  have hov : Overlap (fun N => propensities (activeO N) activeTheta) := by
    refine ⟨1/25, by norm_num, by norm_num, fun N i => ?_⟩
    show 1/25 < propensities (activeO N) activeTheta i ∧
      propensities (activeO N) activeTheta i < 1 - 1/25
    rw [hO4 N]
    dsimp only
    split_ifs <;> norm_num
  have hadm : AdmissibleSeq (fun N => propensities (activeO N) activeTheta) := by
    intro N i
    show 0 < propensities (activeO N) activeTheta i ∧ propensities (activeO N) activeTheta i < 1
    rw [hO4 N]
    dsimp only
    split_ifs <;> norm_num
  obtain ⟨L, hL, hLge⟩ := H activePopulation activeO activeTheta activeParameterSet activeMLE
    0 0 le_rfl le_rfl hP hWD hloc hO3 hov hO5 (1/4) (by norm_num) (by norm_num)
  obtain ⟨hcpos, hgap⟩ := coverage_gap nf
  have hlim := dl8 _ hadm
    (fun N z => Real.sqrt N *
      (fittedIPW (circleAverage (activePopulation N) 0) (activeO N) (activeMLE N) z -
        ame (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)))
    (fun N z => (N : ℝ) * printedSAH (propensities (activeO N) (activeMLE N z))
      (circleAverage (activePopulation N) 0) (spatialNeighborhoods activePopulation 0 N)
      (fun i a => dot (activeO N i) (fittedBeta (propensities (activeO N) (activeMLE N z))
        (circleAverage (activePopulation N) 0) (activeO N) a z)) z)
    (1/2) (2/25) (normalQuantile (1 - 1/4/2)) (by norm_num) (by norm_num) hcpos hO11 hO12
  suffices hLeq : L =
      2 * normalCDF (normalQuantile (1 - 1/4/2) * Real.sqrt (2/25) / (1/2)) - 1 by
    rw [hLeq] at hLge
    linarith
  refine tendsto_nhds_unique (hL.congr' ?_) hlim
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNpos
  refine prob_congr _ _ _ (fun z => ?_)
  dsimp only
  rw [abs_mul, abs_of_pos hsN, Real.sqrt_mul hNpos.le, mul_left_comm,
    mul_le_mul_iff_right₀ hsN]

end
end AronowAudit.P004.Wave1.ObservationalCoverage
