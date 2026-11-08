import AronowAudit.P004.Wave1.LinePopulationBlueprint
import AronowAudit.P004.Wave1.DesignLimitsBlueprint
import AronowAudit.P004.Wave1.FiniteConditioningBlueprint

/-! # Blueprint: refutation of `AronowAudit.P004.printed_observational_coverage` (P004-T36)

Dossier group P004, record 5. The frozen contract (a `sorry` draft) is the validators' formal
reading of printed Supplement A Proposition 4 item (i): with the fitted-IPW numerator and the
actual double-weighted observational SAH statistic, the Wald interval has a coverage limit
`≥ 1−α` for every `α ∈ (0,1/2)`, under the printed guards and a variance floor.
Resolution: `refute` (map-P004; referee 1 accept with helper fixes, referee 2 accept with the
full-universal-closure fix; both applied).

Referee fixes applied: (referee 2) the target negates the FULL universal closure, with the
`Space` binder and its instance binders inside the negation (universe `0`; the Euclidean
witness is in `Type`); (referee 1) the information-inverse identities are stated only when
both groups are present (`3 ≤ N`, node `O7`), and the random-radius helper `DL8` assumes
`σ > 0`.

Paper proof (map-P004 REPORT, record 5): the existing `activePopulation` (two signed active
nodes per eight, `R_i = a_i Z_i`, group-indicator regressors, `θ₀ = (0, −log 9)` interior to
`[−log 19, log 19]²`, so `p_H = 1/2`, `p_L = 1/10`) with the groupwise clipped-proportion MLE
satisfies every guard; `N·Var(augmented) → 1/4`; `√N(fittedIPW − AME) ⇒ N(0,1/4)`;
`N·printedSAH → 2/25`; hence at `α = 1/4` the coverage tends to `2Φ(z_{7/8}√(8/25))−1 < 3/4`,
contradicting `PrintedCoverage` by uniqueness of limits. The unproved draft
`observational_sah_counterexample` is NOT used.

The final declaration (writer) is `AronowAudit.P004.Wave1.printed_observational_coverage_refuted`
in `AronowAudit/P004/Wave1/ObservationalCoverage.lean`.
-/

namespace AronowAudit.P004.Wave1.ObservationalCoverage

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators Classical

/-- Frozen target: the negation of the full universal closure (universe `0`) of the exact
recorded contract `AronowAudit.P004.printed_observational_coverage`. -/
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

/-- Fidelity check: `Target` is literally the negation of the frozen contract at universe 0,
with every binder (including `Space` and its instances) inside the negation. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P004.printed_observational_coverage.{0}) := Iff.rfl

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
proportions; an absent group keeps its true coordinate (paper proof: "For an absent group set
its coordinate to its true coordinate"). -/
def activeMLE (N : ℕ) (z : Assignment N) : Fin 2 → ℝ :=
  ![if nH N = 0 then 0 else logit (pHatH N z),
    if nL N = 0 then -Real.log 9 else logit (pHatL N z)]

/-- `R = Σ_H Z_i (a_i − β̂_{1,H})²` with `β̂_{1,H} = S/(n_H p̂_H)`. -/
def RAct (N : ℕ) (z : Assignment N) : ℝ :=
  ∑ i, if activeGroup N i then
    bit (z i) * (activeSign N i - SAct N z / (nH N * pHatH N z))^2 else 0

/-! ## Nodes -/

/-- O1 (paper proof: "The raw field is bounded by 1 ... its nonconstant contributions depend
only on coins located within distance d of the averaging node ... At the target d=0, h=0
gives singleton neighborhoods exactly"): the table bound, own-coordinate dependence (source
range `ρ = 0` for `LinePopulation.N7`), and the target-band locality at cutoff `0`. -/
def O1 : Prop :=
  (∀ N (i : Fin N) (z : Assignment N), |activeTable N i z| ≤ 1) ∧
  (∀ N (j k : Fin N) (z : Assignment N) (b : Bool),
    0 < 10 * |(j : ℝ) - (k : ℝ)| → activeTable N j (Function.update z k b) = activeTable N j z) ∧
  (∀ N, LocalAt (activeTable N) (nodeSeparation (activePopulation N)) 0)

/-- O2 (paper proof: "The group log likelihood has derivative K_G−n_G logistic(θ) and second
derivative −n_G logistic(θ)(1−logistic(θ))<0. It is therefore maximized at the logit of the
clipped proportion on the interval [−log19,log19]"): the scalar constrained maximization.
Use `Real.log_div`, `Real.exp_log`, monotonicity of `logistic`, and either concavity
(`ConcaveOn` via the second derivative) or the sign of the derivative on each side. -/
def O2 : Prop :=
  (∀ q, -Real.log 19 ≤ logit (clip q) ∧ logit (clip q) ≤ Real.log 19) ∧
  (∀ q, logistic (logit (clip q)) = clip q) ∧
  (∀ n K : ℝ, 0 < n → 0 ≤ K → K ≤ n → ∀ θ, -Real.log 19 ≤ θ → θ ≤ Real.log 19 →
    K * θ - n * Real.log (1 + Real.exp θ) ≤
      K * logit (clip (K / n)) - n * Real.log (1 + Real.exp (logit (clip (K / n)))))

/-- O3 (paper proof: "Summing the two separated likelihoods proves exactly LogisticConditions,
including membership and maximization for every N,z"; Gram bound `c = 1/8` eventually; box
compact by `isCompact_univ_pi`). Uses O2. -/
def O3 : Prop := LogisticConditions activeO activeTheta activeParameterSet activeMLE

/-- O4 (paper proof: "the treatment probabilities are p_H=1/2 and p_L=1/10, exactly
logistic(activeO_i·activeTheta)"). -/
def O4 : Prop :=
  ∀ N, propensities (activeO N) activeTheta = fun i => if activeGroup N i then 1/2 else 1/10

/-- O5 (paper proof: "V_L,N=Var(augmented)=Σ_H(a_i−δ)²/N²=(n_H−s²/n_H)/N² ... In particular
the exact required Nondegenerate predicate holds, for example with eventual lower bound 1/8"):
the outer variance guard, in exactly the form of the contract. Use `LinePopulation.N3`, O4,
the diagonal `2×2` information inverse (`Matrix.inv_diagonal`) for `N ≥ 3`. -/
def O5 : Prop :=
  Nondegenerate (fun N => variance (propensities (activeO N) activeTheta)
    (augmented (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)
      (printedFits (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)
        (activeO N))))

/-- O6 (paper proof: "Hence the ACTUAL fitted estimator is fittedIPW=S/(N p̂_H) ... The AME is
s/N"): exact all-assignment formulas (O2's `logistic ∘ logit ∘ clip = clip`). -/
def O6 : Prop :=
  (∀ N, 0 < N → ∀ z, fittedIPW (activeTable N) (activeO N) (activeMLE N) z =
    SAct N z / (N * pHatH N z)) ∧
  (∀ N, ame (propensities (activeO N) activeTheta) (activeTable N) = sAct N / N)

/-- O7 (paper proof: "Its active treated coefficient is exactly β̂_{1,H}=S/(n_H p̂_H) ... The
other treated coefficient and both control coefficients are zero ... Singleton neighborhoods
have c_i=1 ... printedSAH=Q²R/(N² p̂_H⁴)"; referee-1 fix: only when both groups are present,
here `3 ≤ N`). -/
def O7 : Prop :=
  ∀ N, 3 ≤ N → ∀ z,
    printedSAH (propensities (activeO N) (activeMLE N z)) (activeTable N)
      (spatialNeighborhoods activePopulation 0 N)
      (fun i a => dot (activeO N i)
        (fittedBeta (propensities (activeO N) (activeMLE N z)) (activeTable N) (activeO N) a z)) z =
      (armCount z true / N)^2 * RAct N z / ((N : ℝ)^2 * (pHatH N z)^4)

/-- O8 (paper proof: "center the independent bounded summands a_i(Z_i−1/2); their total
variance is n_H/4 ... The existing bounded-degree graph CLT applies with singleton
neighborhoods, giving a standard normal after exact variance standardization"). Use
`corrected_dependency_clt` with `B N i = {i}`, `CLTCompletion.designMeasure`,
`CLTCompletion.designMeasure_apply`, and O4. -/
def O8 : Prop :=
  NormalLimit (fun N => propensities (activeO N) activeTheta)
    (fun N z => (SAct N z - sAct N / 2) / Real.sqrt (nH N / 4))

/-- O9 (paper proof: "Independence gives E S=s/2, Var(S)=n_H/4, E K=n_H/2, Var(K)=n_H/4 ...
Clipping cannot increase distance from the interior true probability"): the two second
moments used for the Markov bound on the fitted-IPW remainder. -/
def O9 : Prop :=
  ∀ N, 0 < N →
    expect (propensities (activeO N) activeTheta) (fun z => (SAct N z)^2) ≤ N ∧
    expect (propensities (activeO N) activeTheta) (fun z => (1 - 2 * pHatH N z)^2) ≤ 1 / nH N

/-- O10 (paper proof: "Chebyshev gives ... K/n_H−1/2=O_p(N^−1/2), J/n_L−1/10=O_p(N^−1/2) ...
p̂_H−1/2=O_p(N^−1/2) ... n_H/N→1/4"): the laws of large numbers used for `N·printedSAH`.
Uses DL2, DL4 and exact Bernoulli moments. -/
def O10 : Prop :=
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z => KAct N z / N - 1/8) ∧
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z => JAct N z / N - 3/40) ∧
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z => SAct N z / N - 0) ∧
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z => pHatH N z - 1/2) ∧
  Tendsto (fun N => nH N / N) atTop (nhds (1/4))

/-- O11 (paper proof: "fittedIPW=S/(N p̂_H)=2S/N+O_p(N^−1) ... After subtracting AME=s/N, its
root-N limit is N(0,1/4)"): the standardized fitted-IPW limit, in the form consumed by DL8
(`σ = 1/2`). Write `2√N(fittedIPW−AME) = 2√(n_H/N)·Z_N + E_N` with `Z_N` from O8 and
`E_N = (2/√N) S (1−2p̂_H)/p̂_H`; `E|E_N| ≤ 40·||S||·||1−2p̂_H||/√N → 0` by O9 and FC7
Cauchy–Schwarz (`p̂_H ≥ 1/20`). Uses `LinePopulation.N3`, O6, O8, O9, O10, DL2, DL5, DL7, FC7. -/
def O11 : Prop :=
  NormalLimit (fun N => propensities (activeO N) activeTheta) (fun N z =>
    Real.sqrt N * (fittedIPW (circleAverage (activePopulation N) 0) (activeO N) (activeMLE N) z -
      ame (propensities (activeO N) activeTheta) (circleAverage (activePopulation N) 0)) / (1/2))

/-- O12 (paper proof: "R=K−2β̂_{1,H}S+Kβ̂_{1,H}²=K+O_p(1), so R/N→1/8. The pooled treatment
fraction Q=(K+J)/N tends to 1/5 ... N printedSAH→(1/5)²(1/8)/(1/2)⁴=2/25"): the scaled printed
SAH limit, in exactly the form of the contract's event. Eventually (`N ≥ 3`) O7 gives
`N·printedSAH = F(K/N, J/N, S/N, p̂_H, n_H/N)` with `F` continuous at `(1/8,3/40,0,1/2,1/4)`.
Uses `LinePopulation.N3`, O7, O10, DL9. -/
def O12 : Prop :=
  InProb (fun N => propensities (activeO N) activeTheta) (fun N z =>
    (N : ℝ) * printedSAH (propensities (activeO N) (activeMLE N z))
      (circleAverage (activePopulation N) 0) (spatialNeighborhoods activePopulation 0 N)
      (fun i a => dot (activeO N i) (fittedBeta (propensities (activeO N) (activeMLE N z))
        (circleAverage (activePopulation N) 0) (activeO N) a z)) z - 2/25)

/-- Congruence of design probabilities under pointwise equivalent events (proved). -/
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

/-- The nodes suffice (proved): instantiate the assumed contract at the active sequence with
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
