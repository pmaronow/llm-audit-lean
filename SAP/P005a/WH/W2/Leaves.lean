import SAP.P005a.WH.W2.Concentration
import SAP.P005a.WH.W2.Elementary
import SAP.P005a.WH.W2.Orders
import SAP.P005a.WH.W2.SpikeGlue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P005a.WH.W2
noncomputable section
open Finset Filter SAP.P005a.Bridge
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

/-- P005-T7(ii): exact maximum leverage. Bound ordinary |z_i| by 1/n+1/n²,
compare with z_0=1-1/n, use csSup_le and le_csSup on the finite range,
then substitute InteractedExpansion.n1_proof's formula for q. About 100 lines. -/
def T7_L1 : Prop := spikeLeverageFacts

/-- P005-T7(iii): export the slope estimate proved locally in
AronowAudit.P005.Wave1.InteractedExpansion.n8_proof (its hratio calculation).
For a balanced arm containing unit 0, |1/n-mean(a)| <= 1/n+1/n² <= 7/36;
combine with |mean(v)| <= 1 and |slope| <= 2. About 190 lines. -/
def T7_L2 : Prop := spikeHighFitFacts

/-- P005-T7(iv): export and sharpen the population projection calculation inside
AronowAudit.P005.Wave1.InteractedExpansion.n9_proof. Use n1_proof's exact
moments to compute b; its denominator gives 0 <= b <= 1/12. Normalize with
q>0, bound |z|<=1, then average the residual bound in both arms. About 140 lines. -/
def T7_L3 : Prop := spikeProjectionFacts

/-- P005-T7(v): use kappa_bounds, positivity and the already proved deterministic
remainder lower bound in univariate_endpoint_counterexample_proof. Divide by
the positive rate, prove the lower bound diverges on n=2j, and show the bad-event
filter is the entire nonempty design for all sufficiently large even sizes.
This asserts separate finite-space probability-one events, not a coupling. About 160 lines. -/
def T7_L4 : Prop := spikeTailFacts

/-- P005-T7(vi), n=6: a lower bound at every one of the twenty assignments and
one attaining assignment. Rewrite the normalized estimator using n4_proof into
raw a-coordinates, and use the projection identity from n9_proof to eliminate
square roots. Enumerate the rational remainder and certify it with norm_num.
One may use T7_L3 as a premise, so the export need not be reproved. About 100 lines. -/
def T7_L5 : Prop := T7_L3 → spikeMinimum 6 (4357386/779833)

/-- P005-T7(vi), n=12: the same rational certificate for 924 labelled assignments.
Use reflection of the grid and treatment/control complementation to reduce the
cases, or a generated list with a kernel-checked finite certificate; prove a
lower bound everywhere and exhibit an attaining assignment. No infimum over an
empty set or unchecked evaluation is involved. About 150--300 lines. -/
def T7_L6 : Prop := T7_L3 → spikeMinimum 12 (8690712840/752921287)

/-- P005-T9 concentration foundation: diagonalize a real symmetric matrix using
Matrix.IsHermitian.spectral_theorem, Matrix.exp_conj and Matrix.exp_diagonal.
The exponential is PSD. A Rayleigh quotient above a implies some eigenvalue
above a, and its positive exponential is bounded by their sum. About 180 lines. -/
def T9_L1 : Prop := spectralTraceTest

/-- P005-T9 concentration foundation: Peierls' inequality. Expand a unit vector
in an orthonormal eigenbasis and apply convexOn_exp to the weights |v_j|²,
whose sum is one. Matrix.exp_conj and exp_diagonal identify the right side.
Only real symmetric matrices and finite sums are used. About 180 lines. -/
def T9_L2 : Prop := peierls

/-- P005-T9 concentration foundation: diagonalize tA+(1-t)B, apply scalar
convexity of exp followed by Peierls to A and B on each eigenvector, and sum.
Trace invariance under the orthogonal change of basis gives convexity on the
convex real subspace of symmetric matrices. About 100 lines. -/
def T9_L3 : Prop := peierls → traceExpConvex

/-- P005-T9 Lie product formula, analytic estimate. Bound the tails after the
linear term in each matrix exponential by the absolutely convergent exponential
series (NormedSpace.norm_expSeries_summable'). The linear terms cancel in the
split exponential. Work with Matrix.Norms.Operator, a submultiplicative norm.
This local O(t²) estimate needs no symmetry. About 200 lines. -/
def T9_L4 : Prop :=
  ∀ (k : ℕ) (A B : Matrix (Fin k) (Fin k) ℝ),
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 1 →
      ‖NormedSpace.exp (t • (A+B)) - NormedSpace.exp (t • A)*NormedSpace.exp (t • B)‖ ≤ C*t^2

/-- P005-T9 Lie product formula, passage to the limit. Use the preceding local
estimate at t=2^(-j), telescope U^m-V^m without commuting U and V, and bound
both factors' powers by exp(||A||+||B||). The error is O(2^(-j)); exp_nsmul
identifies the unsplit power with exp(A+B). About 180 lines. -/
def T9_L5 : Prop := T9_L4 →
  ∀ (k : ℕ) (A B : Matrix (Fin k) (Fin k) ℝ),
    Tendsto (fun j : ℕ =>
      (NormedSpace.exp (((2 : ℝ)^j)⁻¹ • A) *
        NormedSpace.exp (((2 : ℝ)^j)⁻¹ • B))^(2^j)) atTop
      (nhds (NormedSpace.exp (A+B)))

/-- P005-T9 Golden--Thompson's finite algebraic step: the dyadic trace inequality
for PSD A,B. Write trace(UᵀV) as the finite Frobenius inner product, prove its
Cauchy--Schwarz inequality with Finset.sum_mul_sq_le_sq_mul_sq, and repeatedly
reflect the two halves of the cyclic word (AB)^(2^j). Induction gives
tr((AB)^(2^j)) <= tr(A^(2^j) B^(2^j)). Include the zero-trace cases rather
than dividing by a trace. This is the hardest algebra leaf, about 250--380 lines;
it is the dyadic case only, not the general Araki--Lieb--Thirring theorem. -/
def T9_L6 : Prop :=
  ∀ (k : ℕ) (A B : Matrix (Fin k) (Fin k) ℝ),
    A.PosSemidef → B.PosSemidef → ∀ j : ℕ,
    Matrix.trace ((A*B)^(2^j)) ≤ Matrix.trace (A^(2^j)*B^(2^j))

/-- P005-T9 Hoeffding coupling, first marginal. For each labelled iid draw f,
its observed label set D has card <= s. Count size-s supersets of D as
choose(N-|D|,s-|D|), which is positive for s<=N. The explicitly defined
samplingWeight is nonnegative and sums over S to 1/N^s. About 140 lines. -/
def T9_L7 : Prop :=
  ∀ (N s : ℕ), 0 < N → s ≤ N →
    (∀ (S : Finset (Fin N)) (f : Fin s → Fin N), 0 ≤ samplingWeight N s S f) ∧
    (∀ f : Fin s → Fin N,
      (∑ S ∈ design N s, samplingWeight N s S f) = 1/(N : ℝ)^s)

/-- P005-T9 Hoeffding coupling, second marginal and barycenter. Permuting the
N labels preserves the explicit weights, so all size-s subsets have equal
mass. Within a fixed S, the expected count of each member is equal, all counts
outside S vanish, and their sum is s. Use the first marginal to normalize;
handle s=0 separately. About 240--350 lines, including the finite permutation
bijections. The statement records coordinate counts, so it works for repeated
row values and every vector-valued population simultaneously. -/
def T9_L8 : Prop := T9_L7 →
  ∀ (N s : ℕ), 0 < N → s ≤ N → ∀ S ∈ design N s,
    (∑ f : Fin s → Fin N, samplingWeight N s S f) = 1/((design N s).card : ℝ) ∧
    ∀ i : Fin N,
      (∑ f : Fin s → Fin N, samplingWeight N s S f *
        ((univ.filter (fun j => f j = i)).card : ℝ)) =
          (if i ∈ S then 1 else 0)/((design N s).card : ℝ)

/-- P005-T9 finite convex comparison. Normalize the coupling weights in each
subset fibre, use the coordinate barycenter and ConvexOn.map_sum_le, and sum
over S. The first marginal gives the iid average. All convex combinations
stay in the symmetric subspace. About 160 lines. -/
def T9_L9 : Prop := T9_L7 → T9_L8 → convexSampling

/-- P005-T9 one-draw MGF: diagonalize 0<=X<=I, apply the scalar chord
exp(theta*x) <= 1+x*(exp(theta)-1) on [0,1] for every real theta, then average.
The scalar mean assumption replaces mean(X) by mu I. Use PSD congruence and
finite sums; no operator-monotonicity assertion about exp is needed. About 180 lines. -/
def T9_L10 : Prop := exponentialChord

/-- P005-T9 independent trace MGF. Induct on the draw length. Apply
Golden--Thompson conditional on the first draws, average the last exponential,
and use the chord's scalar upper bound. Multiplication by a PSD exponential
preserves the trace inequality. The scalar factor is nonnegative for
0<=mu<=1. Fin.sum_univ_succ and finite Fubini finish the induction. About 180 lines. -/
def T9_L11 : Prop := goldenThompson → exponentialChord → independentTraceMGF

/-- P005-T9 fixed Chernoff tails. Apply the trace test to +sum and -sum, finite
Markov, and convex comparison for trace exp(theta*sum). Use the independent
MGF with theta=log 2 for the upper tail and theta=-log 2 for the lower tail.
The scalar exponents are at most -s*mu/8; exp(x)>=1+x gives the conversion
from the MGF factor. Add the two bad-event probabilities, including s=0.
All four premises below are earlier proof steps, not additional claim assumptions.
About 220--320 lines. -/
def T9_L12 : Prop :=
  spectralTraceTest → traceExpConvex → convexSampling → independentTraceMGF → fixedChernoff

/-- P005-T9 row specialization and dimension-uniform threshold. For augmented
orthonormal rows w_i let R=max||w_i||²>0, X_i=w_i w_iᵀ/R and mu=1/(nR).
Then 0<=X_i<=I and mean(X)=mu I; isotropy implies mu<=1. Convert fixedChernoff
to the quadratic bad event used by CondT8T9_bad. Its bound is
2(d+1) exp(-s/(8nR)). Use augmented_row_bound, then choose A so
2k exp(-A log k/8)<epsilon for every k>=2 (the argument of
CondT8T9_chernoff_uniform). About 220--320 lines. -/
def T9_L13 : Prop := fixedChernoff → finiteGramControl

/-- P005-T9 final analytic adapter: replay the proved
corrected_interacted_expansion_max_conditional argument with finiteGramControl
in place of CondT8T9_tropp_finite. Start beyond max(3,n0) and the common
standardization/regularity threshold. The existing score expectation, coercivity,
remainder bound, sample threshold and finite Markov lemmas do all remaining
probability estimates. repaired_log_conditions changes log(2d) to log max(d,2).
This is about 130--180 lines and assumes no literature proposition. -/
def T9_L14 : Prop := finiteGramControl → wholeInteractedExpansion

/-- P005-T9 mixed dimension equivalence. Split d=1 and d>=2 on the eventual
positive-dimension tail, squeeze kappa by kappa*log(d)/log 2 on the second
part, and use Real.log_mul. Conversely the repaired condition bounds each
nonnegative summand and the dimension-one subsequence. About 100 lines. -/
def T9_L15 : Prop := mixedLogEquivalence

/-- No new proof leaf is needed for the finite sign counterexample. -/
theorem T5_assembly : T5WholeStatement := T5_complete

/-- No new proof leaf is needed for the finite weight counterexample. -/
theorem T10_assembly : T10WholeStatement := T10_complete

/-- The two analytic/algebraic foundations give Golden--Thompson by a limit. -/
theorem goldenThompson_of_leaves (h1 : T9_L1) (h4 : T9_L4)
    (h5 : T9_L5) (h6 : T9_L6) : goldenThompson := by
  intro k A B hA hB
  have hp (C : Matrix (Fin k) (Fin k) ℝ) (j : ℕ) :
      (NormedSpace.exp (((2 : ℝ)^j)⁻¹ • C))^(2^j) = NormedSpace.exp C := by
    rw [← Matrix.exp_nsmul]
    congr 1
    simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, Nat.cast_pow, Nat.cast_ofNat,
      mul_inv_cancel₀ (pow_ne_zero j (by norm_num : (2 : ℝ) ≠ 0)), one_smul]
  have hc : Continuous (fun C : Matrix (Fin k) (Fin k) ℝ => Matrix.trace C) := by
    unfold Matrix.trace
    fun_prop
  have hl := (hc.tendsto _).comp (h5 h4 k A B)
  apply le_of_tendsto hl
  apply Filter.Eventually.of_forall
  intro j
  have hAs : (((2 : ℝ)^j)⁻¹ • A).IsHermitian := hA.smul (by unfold IsSelfAdjoint; rfl)
  have hBs : (((2 : ℝ)^j)⁻¹ • B).IsHermitian := hB.smul (by unfold IsSelfAdjoint; rfl)
  have hh := h6 k _ _ (h1 k _ hAs).1 (h1 k _ hBs).1 j
  rw [hp, hp] at hh
  exact hh

/-- The complete expansion has no concentration or literature assumption. -/
theorem T9_assembly (h1 : T9_L1) (h2 : T9_L2) (h3 : T9_L3)
    (h4 : T9_L4) (h5 : T9_L5) (h6 : T9_L6) (h7 : T9_L7)
    (h8 : T9_L8) (h9 : T9_L9) (h10 : T9_L10) (h11 : T9_L11)
    (h12 : T9_L12) (h13 : T9_L13) (h14 : T9_L14) (h15 : T9_L15) :
    T9WholeStatement := by
  have hGT := goldenThompson_of_leaves h1 h4 h5 h6
  have hTail := h12 h1 (h3 h2) (h9 h7 h8) (h11 hGT h10)
  exact ⟨T9_correspondence.mp
    ⟨AronowAudit.P005.repaired_log_bounds, AronowAudit.P005.repaired_log_conditions⟩,
    h14 (h13 hTail), h15⟩

/-- The full arm correction needs only existing finite identities and the
same finite-moment argument after a later starting threshold. -/
theorem T11_assembly : T11WholeStatement := by
  have hb : T11Statement := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n d P S y c hn hS hinv
      exact AronowAudit.P005.treated_arm_cancellation (toPopulation P) S y c hn hS hinv
    · intro n d m P hn hm hmn hx c
      exact AronowAudit.P005.Wave1.treated_arm_expectation_proof
        (toPopulation P) hn hm hmn hx c
    · intro n d m P hn hm hmn hc hx c
      exact AronowAudit.P005.Wave1.control_arm_expectation_proof
        (toPopulation P) hn hm hmn hc hx c
    · intro d m P h t
      exact wholeArmOrder_proof 3 (by norm_num) d m P h t
  refine ⟨hb, ?_, ?_, ?_, ?_, wholeArmOrder_proof⟩
  · intro n s hn hs hsn
    have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
    dsimp only [NTTT]
    field_simp [show (n : ℝ) ≠ 0 by linarith,
      show (s : ℝ) ≠ 0 by linarith, show (n : ℝ)-1 ≠ 0 by linarith,
      show (n : ℝ)-2 ≠ 0 by linarith, show (s : ℝ)-1 ≠ 0 by linarith]
    <;> ring
  · intro n d s P hn hs hsn hx y c
    refine ⟨AronowAudit.P005.Wave1.control_arm_generic_expectation
      (toPopulation P) hn hs hsn.le hx y c,
      AronowAudit.P005.Wave1.control_arm_unbiased_any_size
        (toPopulation P) hn hs hsn.le hx y, ?_, ?_⟩
    · intro hs2
      exact AronowAudit.P005.Wave1.control_arm_coefficient_unique hn hs2 c
    · intro hs1
      subst s
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
      norm_num [armBiasCoefficient, NTTT]
      field_simp [show (n : ℝ)-1 ≠ 0 by linarith, show (n : ℝ)-2 ≠ 0 by linarith]
      <;> ring
  · intro n d m P hn hm hmn hx c
    constructor
    · rw [expectation_control hmn.le
        (fun S => mean S P.yC - dot (xMean P S) (armN P S P.yC) +
          c*sampleCov S (leverage P) P.yC)]
      exact AronowAudit.P005.Wave1.control_arm_generic_expectation (toPopulation P)
        hn (Nat.sub_pos_of_lt hmn) (Nat.sub_le _ _) hx P.yC c
    · rw [expectation_control hmn.le (fun S => armDebiased P S P.yC)]
      exact AronowAudit.P005.Wave1.control_arm_unbiased_any_size (toPopulation P)
        hn (Nat.sub_pos_of_lt hmn) (Nat.sub_le _ _) hx P.yC
  · intro n d P hn hG
    have hk := AronowAudit.P005.kappa_bounds (toPopulation P) hn hG
    exact ⟨hk.1, hk.2, AronowAudit.P005.leverage_le_population_size (toPopulation P) hn hG⟩

/-- Existing endpoint proof plus the six precise new exports give every witness clause. -/
theorem T7_assembly (h1 : T7_L1) (h2 : T7_L2) (h3 : T7_L3)
    (h4 : T7_L4) (h5 : T7_L5) (h6 : T7_L6) : T7WholeStatement := by
  have hb : T7Statement := by
    apply T7_correspondence.mp
    refine ⟨AronowAudit.P005.Wave1.univariate_endpoint_counterexample_proof, ?_, ?_⟩
    · intro n hn
      exact AronowAudit.P005.Wave1.InteractedExpansion.spikeQ_pos_of_S1
        AronowAudit.P005.Wave1.InteractedExpansion.n1_proof n (by omega)
    · intro n _
      exact (AronowAudit.P005.univariate_printed_condition
        (fun q => AronowAudit.P005.kappa (AronowAudit.P005.spikePopulation q))).1 n
  have hcards : ∀ n : ℕ, 6 ≤ n → ∀ S ∈ design n (n/2),
      3 ≤ S.card ∧ 3 ≤ (control S).card := by
    intro n hn S hS
    have hs : S.card = n/2 := (Finset.mem_powersetCard.mp hS).2
    have hc : (control S).card = n-S.card := by
      simp [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
    constructor <;> omega
  have hg : ∀ n : ℕ, 6 ≤ n →
      (∑ i, spikeV n i) = 0 ∧
      (∑ i, spikeV n i^2) = (n : ℝ)*(n-1 : ℝ)/(3*(n-2 : ℝ)) ∧
      popMean (spikeA n) = 1/(n : ℝ) ∧
      spikeQ n = (n-1 : ℝ)/(n : ℝ)^2*(1+1/(3*(n-2 : ℝ)*(n : ℝ)^2)) ∧
      (∀ i, |(spikePopulation n).yT i| = |(spikePopulation n).yC i| ∧
        |(spikePopulation n).yT i| ≤ 1) ∧
      (∀ S ∈ design n (n/2), 3 ≤ S.card ∧ 3 ≤ (control S).card ∧
        0 < firstVariance (spikePopulation n) S ∧
        0 < firstVariance (spikePopulation n) (control S)) := by
    intro n hn
    have hm := AronowAudit.P005.Wave1.InteractedExpansion.n1_proof n (by omega)
    have ha : (∑ i, spikeA n i) = 1 := hm.2.2.2.1
    refine ⟨hm.1, hm.2.1, ?_, hm.2.2.2.2, ?_, ?_⟩
    · simp [popMean, mean, ha]
    · intro i
      exact ⟨rfl, hm.2.2.1 i⟩
    · intro S hS
      have hc := hcards n hn S hS
      exact ⟨hc.1, hc.2, spikeVariance_pos n hn S (by omega),
        spikeVariance_pos n hn (control S) (by omega)⟩
  have hfit : ∀ n : ℕ, 6 ≤ n → ∀ A : Finset (Fin n), 2 ≤ A.card →
      mean A (spikeV n) - dot (xMean (spikePopulation n) A)
        (armBetaHat (spikePopulation n) A (spikeV n)) = spikeFit n A ∧
      ((∀ i ∈ A, i.val ≠ 0) →
        (∀ i ∈ A, spikeV n i = (n : ℝ)^2*spikeA n i) ∧ spikeFit n A = n) := by
    intro n hn A hA
    exact ⟨spikeFit_eq n hn A hA, spikeLowFit n hn A hA⟩
  have hlarge : ∀ n : ℕ, 6 ≤ n → Even n → ∀ S ∈ design n (n/2),
      (n-3 : ℝ) ≤ |interactedATE (spikePopulation n) S| := by
    intro n hn heven S hS
    have hs : S.card = n/2 := (Finset.mem_powersetCard.mp hS).2
    have hc : (control S).card = n/2 := by
      have hcc : (control S).card = n-S.card := by
        simp [control, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      have hmod : n % 2 = 0 := Nat.even_iff.mp heven
      omega
    have hcs := hcards n hn S hS
    have hcalc : interactedATE (spikePopulation n) S = spikeFit n S - spikeFit n (control S) := by
      have ht := spikeFit_eq n hn S (by omega)
      have ht' := spikeFit_eq n hn (control S) (by omega)
      dsimp only [interactedATE]
      change mean S (spikeV n) - mean (control S) (spikeV n) -
        (dot (xMean (spikePopulation n) S) (armBetaHat (spikePopulation n) S (spikeV n)) -
          dot (xMean (spikePopulation n) (control S))
            (armBetaHat (spikePopulation n) (control S) (spikeV n))) = _
      linarith
    rw [hcalc]
    let z : Fin n := ⟨0, by omega⟩
    by_cases hz : z ∈ S
    · have hnC : ∀ i ∈ control S, i.val ≠ 0 := by
        intro i hi hv
        have hiz : i = z := Fin.ext hv
        subst i
        exact (Finset.mem_sdiff.mp hi).2 hz
      rw [(spikeLowFit n hn (control S) (by omega) hnC).2]
      have hh := ((h2 n hn S ⟨z, hz, rfl⟩ (by omega)).2 heven hs)
      have hbound := (abs_le.mp hh).2
      linarith [neg_le_abs (spikeFit n S - (n : ℝ))]
    · have hzC : z ∈ control S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hz⟩
      have hnS : ∀ i ∈ S, i.val ≠ 0 := by
        intro i hi hv
        have hiz : i = z := Fin.ext hv
        exact hz (hiz ▸ hi)
      rw [(spikeLowFit n hn S (by omega) hnS).2]
      have hh := ((h2 n hn (control S) ⟨z, hzC, rfl⟩ (by omega)).2 heven hc)
      have hbound := (abs_le.mp hh).2
      linarith [le_abs_self ((n : ℝ)-spikeFit n (control S))]
  refine ⟨hb, hg, h1, h2, h3, hfit, hlarge, h4, by decide, ?_, ?_, h5 h3,
    by norm_num, by decide, ?_, ?_, h6 h3, by norm_num⟩
  · have hh := (h1 6 (by norm_num)).2.1
    norm_num at hh
    exact hh
  · have hh := (h3 6 (by norm_num)).1
    norm_num at hh
    exact hh
  · have hh := (h1 12 (by norm_num)).2.1
    norm_num at hh
    exact hh
  · have hh := (h3 12 (by norm_num)).1
    norm_num at hh
    exact hh

end
end SAP.P005a.WH.W2
