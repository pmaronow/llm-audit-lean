import SAP.P022.WH.W1.Support

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P022.WH.W1
open SAP.P022 Filter MeasureTheory
open scoped BigOperators Topology ENNReal NNReal
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- A step CDF cannot hide its unit jump inside a cell of strict mesh at most one.
Choose the first nonnegative knot in the finite ordered extended-real partition.
If it were positive, the preceding negative knot and this knot would violate the
mesh condition. The endpoints exclude an empty crossing. About 60 lines. -/
def T1_L1 : Prop :=
  ∀ P (s : Fin (P + 1) → EReal) η, 0 < η → η ≤ 2 → OriginPartitionMesh P s η →
    ∃ j, s j = 0

/-- The perturbed periodic sequence has the same weak limit as its corners.
For each bounded continuous test function use continuity at the four corners,
the perturbation 1/(i+3) tending to zero, and Cesaro convergence on each residue
class. Count the at most three remaining terms. This is only the weak-limit step;
atom counts and allocations are separate. About 150–250 lines. -/
def T1_L2 : Prop := weakPopulationConvergence perturbedCornerWitness cornerLaw

/-- Bounds, square-tail integrability, and the atom counts for the perturbed witness.
The shift lies in (0,1/3], so the indicators at zero equal the binary zero
indicators and those at one are all one. Use four-period counting, the explicit
corner CDF, and continuity off {0,1}. Bounded outcomes give UI. About 150 lines. -/
def T1_L3 : Prop := PerturbedAtomFacts

/-- At the moving threshold every perturbed population value, and therefore every
observed value, is below it. The threshold lies in (0,1). Evaluate the limiting
CDF there and use le_csSup with the CDF error bounded by one. No random sampling
estimate is involved. About 100 lines. -/
def T1_L4 : Prop := PerturbedThresholdFacts

/-- Endpoint values and limits for the unperturbed periodic marginal CDFs.
Count binary entries by complete four-blocks and a bounded remainder; left-CDF
at one equals CDF at zero. Use corner_law_facts for the limiting CDF. About 80 lines. -/
def T7_L1 : Prop := CornerEndpointFacts

/-- Balanced four-corner moments, marginal multiset equality, and the upper
quantile product integral. Repeat each of the four corner values r+1 times.
For the integral, identify the sorted marginal arrays and integrate their common
zero/one quantile on rank cells using SharpBounds.n1_proof through n4_proof.
Only finite counting and rank-cell integration remain. About 200–300 lines. -/
def T7_L2 : Prop := CornerBalancedMoments

/-- A finite N-scaled tail limsup for every tolerance forces the unscaled
probabilities to zero when N=q+4. A limsup below a finite ENNReal is eventually
below a larger finite bound. Divide by N and squeeze using nonnegativity of the
finite probability. This general varying-design lemma takes about 80 lines. -/
def T7_L3 : Prop :=
  ∀ (S : ExperimentSequence) (X : (q : ℕ) → Assignment (S.design q) → ℝ),
    (∀ η, 0 < η → ∃ K : ℝ, scaledProbabilityLimsup S
      (fun q π => η ≤ |X q π|) ≤ ENNReal.ofReal K) →
    designConvergence S.design X 0

/-- From the exact balanced variance identities and the centered convergence,
derive the one-half limit of the wrongly centered absolute error. The shift
N/[2(N-1)] tends to one half. Apply the varying-design perturbation and continuous
mapping lemmas. For epsilon<1/2 the complement is a deviation event, so its
probability tends to zero; probability eventually exceeds 1/2 and N grows,
giving actual divergence and eventual comparison with every real bound.
The inputs are explicit and have independent sources. About 120–180 lines. -/
def T7_L4 : Prop :=
  CornerBalancedVariances →
    designConvergence cornerWitness.design (centeredUpperError cornerWitness) 0 →
    CornerWrongLimits

/-- The printed shifted grid has total weight 1-2e. Establish the nonempty grid's
endpoints zero and one, then telescope with Finset.sum_range_sub. Cell widths
are irrelevant to this identity. About 60–100 lines. -/
def T9_L1 : Prop := ShiftedWeightSum

/-- Translation of both samples preserves the mathematical sharp estimates.
Sorting commutes with a real translation; on positive ranks order statistics
translate. On the common grid the centered quantiles and sample variances are
unchanged. The zero-rank totalization is irrelevant to the integral. Reuse the
centered overlap-weight formula from appendixB_corrected_proof. About 150 lines. -/
def T9_L2 : Prop := BoundTranslationInvariant ∧
  (∀ {n : ℕ}, 0 < n → ∀ (a : Fin n → ℝ) c r, 1 ≤ r → r ≤ n →
    orderStatistic (fun i => a i + c) r = orderStatistic a r + c)

/-- Uniform CDF convergence passes to the left CDF at every fixed point by
the left-limit inequality. Thus the conditional Lemma 2 domain has atom-left
convergence. Apply Bridge.lemma2_corrected_explicit_proof, retaining its positive
antitone universal integer choice. No atom-left assumption is added to the
target. About 120–180 lines. -/
def T6_L1 : Prop := UniversalCDFRates

/-- Upper last-term limsup with the prescribed universal K. Use the public
finite last-integral sup bound, the vanishing population-to-limit uniform CDF
errors in Lemma2Conclusions, and (N-1)/N tending to one. The strict xi margin
gives eventual inclusion in two fixed limiting-CDF tail events; take the finite
union limsup and UniversalCDFRates. About 150 lines. -/
def T6_L2 : Prop := UniversalCDFRates → UpperLastLimit

/-- Conditional upper seven-event limit assembly with specified last-term rate.
Use the existing finite budget at epsilon1 and the corrected allocation. Bound
the finite-union limsup by the sum of the seven limsups; expand the six grouped
coefficients. The first inequality is event monotonicity. About 100–150 lines. -/
def T6_L3 : Prop := UpperLastLimit → UpperConditionalConclusion

/-- The eight-term constrained minimum, including positivity and an attained
minimizer. For positive cube roots r_i use Holder with exponents 3 and 3/2:
(sum r_i)^3 <= (sum r_i^3/nu_i^2)(sum nu_i)^2. Equality holds at nu_i=s*r_i/sum r.
All canonical coefficients are strictly positive on 0<theta<=1, 0<rho<1.
Real.rpow_mul_natCast verifies the roots. About 150–250 lines. -/
def T6_L4 : Prop := AllocationMinimum

/-- Lower Frechet representation of the raw quantile product. Expand both
sorted arrays onto m*k equal rank cells, reversing the control array. A prefix
and a suffix intersect with mass max(0,G+F-1). GP022B2b_pair_integral then
evaluates the double integral. The upper representation is a source template,
not a lower-endpoint donor. All arrays are nonempty and bounded. About 250 lines. -/
def T6_L5 : Prop := LowerQuantileRepresentation

/-- From the lower raw-product representation obtain its seven-term identity
by the same marginal-variance algebra as the public upper identity. Apply the
seven_term_budget and finite union bound. The map max(0,u+v-1) is Lipschitz with
error at most |delta u|+|delta v|; integrate over the square for the sup bound
and split positive tolerances. Include the C=0 case directly. About 250–350 lines. -/
def T6_L6 : Prop := LowerQuantileRepresentation → LowerFiniteFacts

/-- Lower conditional last-term and full-error limits. Use LowerFiniteFacts
and the strict xi2,xi3 margins to compare with fixed limiting-CDF tail events.
Apply UniversalCDFRates, then the seven-event limsup budget with the first six
conditional rates. The lower allocation sums to epsilon1+epsilon2+epsilon3.
This is a finite union argument, not an invocation of printed Lemma 2.
About 150–220 lines. -/
def T6_L7 : Prop := UniversalCDFRates → LowerFiniteFacts → LowerConditionalConclusion

/-- Moment existence and variance positivity for the corollary. Existing
tb13_square_integrability, compatible-coordinate L2, tb13_limiting_variance_pos,
tb13_true_le_bound, and TailB_proposition1 cover the second moments and limits.
The new third-moment passage uses bounded continuous truncations of |x|^3 and
monotone convergence. Frechet bounds give genuine nonempty bounded covariance
images, rather than totalized extrema. About 200–300 lines including transport. -/
def T17_L1 : Prop := CorollaryMomentFacts

/-- Wald coverage for any nonnegative input whose N-scaled value converges in
design probability, including v=0. Start from tb13_actual_variance_clt and the
positive actual limit; use the varying-design Slutsky argument and squeeze
random symmetric thresholds at continuity points of the normal law. When v=0,
bound by every positive fixed interval and let its radius decrease to zero.
Do not assume W is pointwise positive. About 150–250 lines. -/
def T17_L2 : Prop := WaldInputCoverage

/-- Compatible laws preserve all marginal moments, the compatibility class and
both bound functionals. With L2 marginals the upper covariance supremum is
attained by a compatible coupling (TailB_frechet_covariance_L2). Third absolute
moments transfer by equality of marginal measures. About 150–220 lines. -/
def T17_L3 : Prop :=
  ∀ H θ ρ, LawFunctionalsDefined H → LawThirdMomentsFinite H →
    (∀ J ∈ compatibleLaws H, LawThirdMomentsFinite J ∧
      limitingBound J θ ρ .H = limitingBound H θ ρ .H) ∧
    ∃ J ∈ compatibleLaws H,
      lawCovariance J = sSup (lawCovariance '' compatibleLaws H)

/-- Nonsingular laws approach the sharp upper variance. Mix an attaining
compatible coupling with a positive amount lambda of H. The mixture remains
compatible, inherits the third marginal moments, and is nonsingular because
H is absolutely continuous with respect to it. Its true limiting variance is
(1-lambda)*U+lambda*s_H. Choose lambda small enough that it exceeds v<U.
The covariance supremum need not itself have a nonsingular maximizer.
About 150–220 lines. -/
def T17_L4 : Prop := T17_L3 →
  ∀ H θ ρ, 0 < θ → θ ≤ 1 → 0 < ρ → ρ < 1 →
    LawFunctionalsDefined H → LawThirdMomentsFinite H → NonsingularLaw H →
    ∀ v, 0 ≤ v → v < limitingBound H θ ρ .H →
      ∃ J ∈ compatibleLaws H, LawThirdMomentsFinite J ∧ NonsingularLaw J ∧
        v < limitingTrueVariance J θ ρ

/-- A deterministic path simultaneously satisfies the strong law for countably
many measurable sets and finitely many integrable observables. Use the countable
infinite product of J, iIndepFun_infinitePi and strong_law_ae_real. Intersect the
countably many probability-one events and select one path. This is a standalone
probability lemma; no weak convergence or realization is assumed. About 180 lines. -/
def T17_L5 : Prop :=
  ∀ (J : JointLaw) (C : Set (Set (ℝ × ℝ))), C.Countable →
    (∀ s ∈ C, MeasurableSet s) →
    ∀ F : Fin 2 → (ℝ × ℝ) → ℝ,
      (∀ t, Integrable (F t) (J : Measure (ℝ × ℝ))) →
      ∃ u : ℕ → ℝ × ℝ,
        (∀ s ∈ C, Tendsto (fun n => finiteMean (fun i : Fin (n + 4) =>
          if u i.val ∈ s then (1 : ℝ) else 0)) atTop
          (𝓝 ((J : Measure (ℝ × ℝ)) s).toReal)) ∧
        (∀ t, Tendsto (fun n => finiteMean (fun i : Fin (n + 4) => F t (u i.val)))
          atTop (𝓝 (∫ p, F t p ∂(J : Measure (ℝ × ℝ)))))

/-- Realize any finite-third-moment joint law as nested fixed unit outcomes with
conditions 1–3 and bounded empirical thirds. Apply T17_L5 to a countable basis of
rational rectangles plus all marginal atomic halfspaces, and to the two |x|^3
observables. Portmanteau on the rectangle pi-system gives weak convergence;
atomic counts give condition 3, and convergence bounds the empirical thirds.
For every N=q+4 use m=max 2 (min (N-2) floor(theta*rho*N)) and then a clipped
control count approaching theta*(1-rho)*N. Prove clipping is eventually inactive;
the four-unit initial rows remain valid. About 250–350 lines. -/
def T17_L6 : Prop := T17_L5 →
  ∀ J θ ρ, 0 < θ → θ ≤ 1 → 0 < ρ → ρ < 1 → LawThirdMomentsFinite J →
    ∃ S : ExperimentSequence, Conditions123 S J θ ρ ∧ BoundedThirdMoments S

/-- The standard normal critical value exists and is positive for 0<alpha<1.
Use the continuous strictly increasing normal CDF and its endpoint limits.
For s>0,v>=0 the coverage 2 Phi(z sqrt(v/s))-1 is at least nominal exactly when
s<=v, and is strictly below nominal when v<s. The strict result includes v=0.
Reuse NormalCompletion.normalCritical_cdf and strictMono_normal_cdf.
About 60–100 lines. -/
def T17_L7 : Prop :=
  (∀ α, 0 < α → α < 1 → NormalCriticalDefined α ∧
    0 < normalCritical α ∧ normalCDF (normalCritical α) = 1 - α / 2) ∧
  ∀ α v s, 0 < α → α < 1 → 0 ≤ v → 0 < s →
    (1 - α ≤ gaussianWaldCoverage α v s ↔ s ≤ v) ∧
    (v < s → gaussianWaldCoverage α v s < 1 - α)

theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2) (h3 : T1_L3) (h4 : T1_L4) :
    T1WholeStatement := by
  have hA := Bridge.lemma2_counterexample
  have hAc : CertainCDFError reciprocalWitness originLaw (1 / 2) := by
    apply certain_cdf
    intro t q π
    rw [hA.2.2.1 q t π]
    norm_num
  have hBc : ∀ t q π, (1 / 4 : ℝ) ≤ cdfDistance (lawCDF cornerLaw t)
      (sampledCDF perturbedCornerWitness t q π) := by
    intro t q π
    exact le_trans (by norm_num) ((h4 q t).2.2.2.2.2 π).2
  refine ⟨hA, reciprocal_extras, hAc, ?_, corner_law_facts, ?_, h3, h4,
    certain_cdf _ _ _ hBc, ?_, certain_refutes_lemma2 _ _ _ (by norm_num) (hBc true), ?_⟩
  · intro P s η hη hη2 hs
    obtain ⟨j, hj⟩ := h1 P s η hη hη2 hs
    refine ⟨j, hj, ?_⟩
    intro q t
    have hv := reciprocal_extras.2.2.1 q t
    rw [hv.2.1, hv.2.2.2]
    norm_num
  · have ha := Bridge.proposition2_printed_counterexample_proof.1
    refine ⟨ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1, ?_, ?_, h2, h3.2.2.2.2⟩
    · exact ha.2.2.2.2.1
    · exact ha.2.2.2.2.2.1
  · intro t
    exact scaled_certain _ _ (hBc t)
  · intro K
    constructor <;> ring

theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) (h3 : T7_L3) (h4 : T7_L4) :
    T7WholeStatement := by
  have hbase := Bridge.proposition2_printed_counterexample_proof
  have hvar : CornerBalancedVariances := by
    intro r
    let d := cornerWitness.design (4 * r)
    let a := rowOutcomes cornerWitness true (4 * r)
    let b := rowOutcomes cornerWitness false (4 * r)
    obtain ⟨hm, hk, hma, hmb, hva, hvb, _, hcov, _, hsharp⟩ := h2 r
    have hN : (d.N : ℝ) = 4 * ((r : ℝ) + 1) := by
      simp only [d, cornerWitness, reciprocalWitness, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
      ring
    have hn0 : (d.N : ℝ) - 1 ≠ 0 := by
      have hn : (4 : ℝ) ≤ d.N := by exact_mod_cast d.population_min
      linarith
    have hm0 : ((2 * (r + 1) : ℕ) : ℝ) ≠ 0 := by positivity
    have ht : rowTrueVariance cornerWitness (4 * r) =
        1 / (2 * (rowSize cornerWitness (4 * r) - 1)) := by
      change trueVariance d a b = 1 / (2 * ((d.N : ℝ) - 1))
      rw [(Bridge.sharp_bounds_variance_and_all_couplings d a b).2.1,
        varianceExpression, hva, hvb, hcov, hm, hk]
      field_simp
      push_cast
      rw [hN]
      ring
    have hu : rowBound cornerWitness .H (4 * r) =
        1 / (rowSize cornerWitness (4 * r) - 1) := by
      change populationBound d a b .H = 1 / ((d.N : ℝ) - 1)
      rw [populationBound, varianceExpression, hva, hvb, hsharp, hm, hk]
      field_simp
      push_cast
      rw [hN]
      ring
    refine ⟨ht, hu, ?_⟩
    intro π
    unfold centeredUpperError
    rw [ht, hu]
    field_simp
    <;> ring
  have hrate : CornerBalancedRate := by
    intro r δ hδ hNδ
    let d := cornerWitness.design (4 * r)
    let a := rowOutcomes cornerWitness true (4 * r)
    let b := rowOutcomes cornerWitness false (4 * r)
    have hy : ∀ i, |a i| ≤ 1 ∧ |b i| ≤ 1 := fun i => hbase.2.2.1 i.val
    have hm : (1 / 2 : ℝ) * d.N ≤ d.m := by
      rw [(h2 r).1]
      simp only [d, cornerWitness, reciprocalWitness, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
      linarith
    have hk : (1 / 2 : ℝ) * d.N ≤ d.k := by
      rw [(h2 r).2.1]
      simp only [d, cornerWitness, reciprocalWitness, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat]
      linarith
    obtain ⟨_, _, _, _, _, _, rate⟩ := Bridge.bounded_direct_finite_proof d a b 1 (1 / 2)
      (by norm_num) hy (by norm_num) hm hk (by norm_num; exact_mod_cast d.population_min)
    have hn : 16 * (1 : ℝ) ^ 2 / ((1 / 2) ^ 2 * δ) ≤ (d.N : ℝ) := by
      have he : 16 * (1 : ℝ) ^ 2 / ((1 / 2) ^ 2 * δ) = 64 / δ := by ring
      rw [he]
      exact hNδ
    have hr := rate δ hδ hn .H
    have hc : 16 * (16 / (1 / 2 : ℝ) + 8) ^ 2 * 1 ^ 4 /
        ((1 / 2) * d.N * δ ^ 2) = 51200 / ((d.N : ℝ) * δ ^ 2) := by ring
    rw [hc] at hr
    simpa only [centeredUpperError, rowSize, rowEstimate, rowBound, abs_mul, Nat.abs_cast] using hr
  have hcenter : designConvergence cornerWitness.design (centeredUpperError cornerWitness) 0 := by
    apply h3
    intro η hη
    have ha := hbase.1
    have hr := Bridge.bounded_direct_asymptotic_final cornerWitness 1 (1 / 2) 1
      ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
      ha.2.2.2.2.1 ha.2.2.2.2.2.1 (by norm_num) hbase.2.2.1
      η (1 / 4) hη (by norm_num) (by norm_num) .H
    refine ⟨16 * (16 / (1 / 4 : ℝ) + 8) ^ 2 * 1 ^ 4 / ((1 / 4) * η ^ 2), ?_⟩
    simpa only [centeredUpperError, rowSize, rowEstimate, rowBound, abs_mul, Nat.abs_cast] using hr
  refine ⟨hbase, h1, ⟨by norm_num, by norm_num⟩, ?_, h2, hvar, hrate, hcenter,
    h4 hvar hcenter, ?_⟩
  · intro q
    have hp : designProbability (cornerWitness.design q) (fun π => (1 - 1 : ℝ) ≤
        |lastIntegralTerm (cornerWitness.design q) (rowOutcomes cornerWitness true q)
          (rowOutcomes cornerWitness false q) 1 π|) = 1 := by
      apply probability_certain
      intro π
      simpa only [sub_self] using abs_nonneg (lastIntegralTerm (cornerWitness.design q)
        (rowOutcomes cornerWitness true q) (rowOutcomes cornerWitness false q) 1 π)
    exact ⟨hp, by rw [hp, mul_one]⟩
  · intro R hR
    rw [hbase.2.2.2.1] at hR
    exact ENNReal.ofReal_ne_top (top_le_iff.mp hR)

theorem T9_assembly (h1 : T9_L1) (h2 : T9_L2) : T9WholeStatement := by
  have hinv : BoundTranslationInvariant := h2.1
  have htrans : CodeTranslationFormula := by
    intro N m k hm hk hN hw a b c B
    have hbase := Bridge.appendixB_general_discrepancy_proof hm hk hN a b hw
    have hshift := Bridge.appendixB_general_discrepancy_proof hm hk hN
      (fun i => a i + c) (fun i => b i + c) hw
    have hia := h2.2 (by omega : 0 < m) a c 1 (by omega) (by omega)
    have hib1 := h2.2 (by omega : 0 < k) b c 1 (by omega) (by omega)
    have hibk := h2.2 (by omega : 0 < k) b c k (by omega) (by omega)
    have hi := hinv hm hk hN a b c B
    cases B
    · simp only [ite_true]
      rw [hia, hib1, hi] at hshift
      linear_combination hshift.1 - hbase.1
    · simp only [reduceCtorEq, ite_false]
      rw [hia, hibk, hi] at hshift
      linear_combination hshift.2 - hbase.2
  refine ⟨⟨Bridge.appendixB_counterexample, @Bridge.appendixB_general_discrepancy_proof⟩,
    code_example_details, h1, hinv, htrans, ?_⟩
  intro B
  have hz : printedCodeBound 4 (fun _ : Fin 2 => (0 : ℝ)) (fun _ : Fin 2 => (0 : ℝ)) B = 0 := by
    have ho (r : ℕ) : orderStatistic (fun _ : Fin 2 => (0 : ℝ)) r = 0 := by
      rcases r with (_ | _ | _ | r) <;>
        simp [orderStatistic, sortedOutcomes, List.ofFn_succ, List.mergeSort, List.getD]
    simp [printedCodeBound, empiricalQuantile, ho, finiteMean,
      marginalVarianceEstimate, sampleVariance, varianceExpression]
  refine ⟨hz, ?_⟩
  rw [hz, (Bridge.appendixB_counterexample.2 B).2]
  norm_num

theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) (h3 : T6_L3) (h4 : T6_L4)
    (h5 : T6_L5) (h6 : T6_L6) (h7 : T6_L7) : T6WholeStatement := by
  have hlast : UpperLastLimit := h2 h1
  have hupper : UpperConditionalConclusion := h3 hlast
  have hlower : LowerFiniteFacts := h6 h5
  have hopt : OptimizedUpperConclusion := by
    intro S H θ ρ C h hC hy hLemma ε1 hε1 hearlier
    have hθ := h.1
    have hθ1 := h.2.1
    have hρ := h.2.2.1
    have hρ1 := h.2.2.2.1
    have hmin := h4 θ ρ hθ hθ1 hρ hρ1 (ε1 / 2) (by linarith)
    let ν := optimalAllocation θ ρ (ε1 / 2)
    let ξ := ε1 / (32 * C ^ 2)
    have hξ : 0 < ξ := by dsimp [ξ]; positivity
    have hξlt : ξ < ε1 / (16 * C ^ 2) := by
      dsimp [ξ]
      apply div_lt_div_of_pos_left hε1 (by positivity)
      nlinarith [sq_pos_of_pos hC]
    have hrpos : 0 < rootSum θ ρ := by
      unfold rootSum
      apply Finset.sum_pos
      · intro i _
        exact Real.rpow_pos_of_pos (hmin.1 i) _
      · exact Finset.univ_nonempty
    have hlast0 : 0 ≤ lastTermRate θ ρ C ε1 ξ :=
      add_nonneg (marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 true _)
        (marginal_rate_nonneg θ ρ hθ hθ1 hρ hρ1 false _)
    refine ⟨?_, ?_⟩
    · unfold optimizedUpperRate
      exact add_pos_of_pos_of_nonneg (by positivity)
        (div_nonneg hlast0 (by positivity))
    · intro ε hε
      have hb := hupper S H θ ρ C h hC hy hLemma ε1 ξ ν hε1 hξ hξlt
        hmin.2.1 hmin.2.2.1 (hearlier ν hmin.2.1 hmin.2.2.1) ε hε
      refine hb.1.trans (hb.2.trans_eq ?_)
      congr 1
      rw [hmin.2.2.2.1]
      unfold optimizedUpperRate
      have hC4 : C ^ 4 ≠ 0 := pow_ne_zero _ hC.ne'
      dsimp [ξ]
      field_simp
      <;> ring
  refine ⟨retained_T6, h1, hlast, hupper, h4, hopt, hlower, ?_, h7 h1 hlower, ?_⟩
  · intro ν ε1 ε2 ε3 hν
    simp [Fin.sum_univ_succ] at hν
    simp [Fin.sum_univ_succ, lowerAllocation, correctedAllocation]
    linarith
  · intro d y1 y0 π
    simp [lastIntegralTerm, lowerLastIntegralTerm]

theorem T17_assembly (h1 : T17_L1) (h2 : T17_L2) (h3 : T17_L3) (h4 : T17_L4)
    (h5 : T17_L5) (h6 : T17_L6) (h7 : T17_L7) : T17WholeStatement := by
  have hcore : CorollaryCore := by
    intro S H θ ρ h hthird hns
    exact Bridge.TailB_corollary1_and_coverage S H θ ρ h hthird hns
  refine ⟨hcore, h1, h2, ?_⟩
  intro S H θ ρ h hthird hns
  have hmoment := h1 S H θ ρ h hthird hns
  have hcompat := h3 H θ ρ hmoment.1 hmoment.2.1
  have hcounter : ∀ v, 0 ≤ v → v < limitingBound H θ ρ .H →
      ∃ (J : JointLaw) (R : ExperimentSequence),
        J ∈ compatibleLaws H ∧ Conditions123 R J θ ρ ∧ BoundedThirdMoments R ∧
        NonsingularLaw J ∧ v < limitingTrueVariance J θ ρ ∧
        ∀ W : (q : ℕ) → Assignment (R.design q) → ℝ,
          (∀ q π, 0 ≤ W q π) →
          designConvergence R.design (fun q π => rowSize R q * W q π) v →
          ∀ α, 0 < α → α < 1 →
            Tendsto (waldCoverage R W α) atTop
              (𝓝 (gaussianWaldCoverage α v (limitingTrueVariance J θ ρ))) ∧
            gaussianWaldCoverage α v (limitingTrueVariance J θ ρ) < 1 - α := by
    intro v hv hvU
    obtain ⟨J, hJ, hJthird, hJns, hvJ⟩ := h4 h3 H θ ρ h.1 h.2.1 h.2.2.1 h.2.2.2.1
      hmoment.1 hmoment.2.1 hns v hv hvU
    obtain ⟨R, hR, hRthird⟩ := h6 h5 J θ ρ h.1 h.2.1 h.2.2.1 h.2.2.2.1 hJthird
    have hspos := (h1 R J θ ρ hR hRthird hJns).2.2.1
    refine ⟨J, R, hJ, hR, hRthird, hJns, hvJ, ?_⟩
    intro W hW hconv α hα hα1
    exact ⟨h2 R J θ ρ hR hRthird hJns W v hW hv hconv α hα hα1,
      (h7.2 α v _ hα hα1 hv hspos).2 hvJ⟩
  refine ⟨?_, hcounter⟩
  intro v hv
  constructor
  · intro hass
    by_contra hUv
    obtain ⟨J, R, hJ, hR, hRthird, hJns, hvJ, hfail⟩ :=
      hcounter v hv (lt_of_not_ge hUv)
    let W : (q : ℕ) → Assignment (R.design q) → ℝ := fun q _ => v / rowSize R q
    have hW : ∀ q π, 0 ≤ W q π := fun q _ => div_nonneg hv (size_pos R q).le
    have hconv : designConvergence R.design (fun q π => rowSize R q * W q π) v := by
      have he : (fun q π => rowSize R q * W q π) = (fun _ _ => v) := by
        funext q π
        dsimp [W]
        field_simp [(size_pos R q).ne']
      rw [he]
      exact convergence_const R.design v
    obtain ⟨c, hc, hcnominal⟩ := hass.2 J hJ R hR hRthird hJns W hW hconv
      (1 / 2) (by norm_num) (by norm_num)
    have hbad := hfail W hW hconv (1 / 2) (by norm_num) (by norm_num)
    have heq := tendsto_nhds_unique hc hbad.1
    rw [heq] at hcnominal
    exact (not_le.mpr hbad.2) hcnominal
  · intro hUv
    refine ⟨hv, ?_⟩
    intro J hJ R hR hRthird hJns W hW hconv α hα hα1
    have hJmoment := h1 R J θ ρ hR hRthird hJns
    have hspos := hJmoment.2.2.1
    have hle : limitingTrueVariance J θ ρ ≤ v := by
      have hb := hJmoment.2.2.2.1
      rw [(hcompat.1 J hJ).2] at hb
      exact hb.trans hUv
    exact ⟨gaussianWaldCoverage α v (limitingTrueVariance J θ ρ),
      h2 R J θ ρ hR hRthird hJns W v hW hv hconv α hα hα1,
      (h7.2 α v _ hα hα1 hv hspos).1.mpr hle⟩

end
end SAP.P022.WH.W1
