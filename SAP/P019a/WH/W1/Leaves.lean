import SAP.P019a.WH.W1.Finite
import SAP.P019a.WH.W1.FiniteExtras
import SAP.P019a.WH.W1.Analytic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1
open SAP.P019a SAP.P019a.Bridge Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology
noncomputable section
open Classical
universe u

/-- All-n conditional binomial counts in the explicit sixteen-atom witness.
Use corrected_cell_lemmas_proof for n≥2, check n=0,1 directly, and use the symmetry of the fair
assignment bit for the control count. Positivity follows from one positive-mass sample for every K=k.
Sum the binomial masses with add_pow; pow_pos proves that the omitted mass is never zero.
This is a count calculation only; no conditioning on the impossible occupied event at n<2 occurs. -/
def T3_L1 : Prop := wholeT3Counts

/-- The six occupied-cell moments at n=4. Push samples to three labels (treated negative, control
negative, affirmative). Enumerate 81 label strings, using conditional_sample_factorization for response
products. Reuse the count-pattern method in GP019B4b.lean, not its inaccessible private declarations.
First obtain E[A], E[A²], E[h], E[A²h]; the constant conditional mean b=-2/3 gives the other moments.
The positive occupied-event probability is already supplied by finite_product_counterexample_proof. -/
def T3_L2 : Prop := wholeT3Moments

/-- All-n conditional count law for a general finite population satisfying the four assumptions.
For n≥2 use the count block of corrected_cell_lemmas_proof; treat n=0,1 directly using cell_probability.
A positive-mass sample with k negatives proves positivity for every k≤n. The identities for the actual
positive-count sums follow from the binomial theorem and from N00=K-N10, including k=0. About 250 lines. -/
def T4_L1 : Prop :=
  ∀ (E : Type u) [Fintype E] (S : Study E), S.standing → wholeT4Counts S

/-- Finite population reduction, without a finite-space assumption on the original population.
Bounded V and V=W+XZ almost surely imply bounded W. Push (W,X,Y,Z,V) to the finite box of allowed
coordinates, normalize singleton masses, and enumerate the box by Fin N. integral_map and
integral_fintype give equality for every observable test function. Include zero-mass coordinates;
no atom is assumed positive. This leaf concerns one draw, not products. At most 180 lines. -/
def T4_L2 : Prop :=
  ∀ (E : Type u) [MeasurableSpace E] (G : WholeMeasureStudy E),
    IsProbabilityMeasure G.law.measure → G.measurableData → G.boundedData → G.noLiarsDesign →
    ∃ N : ℕ, 0 < N ∧ ∃ S : Study (Fin N),
      ∀ f : WholeObservation → ℝ,
        G.law.mean (fun ω => f (G.observable ω)) =
          S.law.mean (fun ω => f (S.wholeObservable ω))

/-- Lift an exact one-draw observable representation to all ordered iid samples.
First identify the two probability pushforward laws by indicator tests. Product pushforwards then give
equality for each n, including the empty product. integral_map and finite-support integrability give
the equality for arbitrary real tests of the observation vector. The source sample space need not be
countable: only the observable pushforward is countable and effectively finite. At most 180 lines. -/
def T4_L3 : Prop :=
  ∀ (E : Type u) [MeasurableSpace E] (G : WholeMeasureStudy E)
    (N : ℕ) (S : Study (Fin N)),
    IsProbabilityMeasure G.law.measure → G.measurableData → G.boundedData → G.noLiarsDesign →
    (∀ f : WholeObservation → ℝ,
      G.law.mean (fun ω => f (G.observable ω)) =
        S.law.mean (fun ω => f (S.wholeObservable ω))) → wholeRepresentation G S

/-- Transfer all four standing assumptions to an exact finite observable representation.
Use indicator moments for the almost-sure structural equations, arbitrary f(W,X,Y) moments for
independence, and first/second cell moments for non-degeneracy. A positive finite mass cannot violate
an almost-sure equation. Measurability, boundedness and probability guards justify all integral steps.
Only the population part of wholeRepresentation is needed. About 150 lines. -/
def T4_L4 : Prop :=
  ∀ (E : Type u) [MeasurableSpace E] (G : WholeMeasureStudy E)
    (N : ℕ) (S : Study (Fin N)),
    IsProbabilityMeasure G.law.measure → G.measurableData → G.boundedData → G.standing →
    wholeRepresentation G S → S.standing

/-- Transport the established corrected-cell core to the original space.
Unfold event means, variances and covariances and use the population and sample moment equalities in
wholeRepresentation. For the pointwise pattern block, choose in the finite population one positive-mass
atom for each of the four (Y,Z) labels (standing supplies their positive probabilities), thus realizing
any original label pattern. Counts and pattern events depend only on these labels. Transport the
n+2 covariance sequence pointwise for the rate and limit; treatment-count identities are Boolean sums.
Prove these transport helpers locally, then rewrite each conjunct of wholeT4Core; at most 350 lines. -/
def T4_L5 : Prop :=
  ∀ (E : Type u) [MeasurableSpace E] (G : WholeMeasureStudy E)
    (N : ℕ) (S : Study (Fin N)),
    IsProbabilityMeasure G.law.measure → G.measurableData → G.boundedData → G.standing →
    S.standing → wholeRepresentation G S → wholeT4Core S → wholeT4MeasureCore G

/-- Transport the all-size count laws, auxiliary moments, and unshifted covariance asymptotics.
Rewrite the observable sample integrals with wholeRepresentation. The two deterministic identities
are direct Boolean summation and muHat=1+AB, valid even for observations outside the effective support.
The asymptotic functions agree pointwise, so no separate limiting argument is required. About 180 lines. -/
def T4_L6 : Prop :=
  ∀ (E : Type u) [MeasurableSpace E] (G : WholeMeasureStudy E)
    (N : ℕ) (S : Study (Fin N)),
    IsProbabilityMeasure G.law.measure → G.measurableData → G.boundedData → G.standing →
    S.standing → wholeRepresentation G S → wholeT4Counts S → wholeT4Extras S →
    wholeT4MeasureCounts G ∧ wholeT4MeasureExtras G

/-- The complete 128-atom population table and coordinate-deletion property.
Prove the seven-bit joint law by enumerating bit patterns or a bit-vector equivalence. The baseline
sign has square one, giving W=3/2+UP/2. Deleting assignment j leaves prefix and suffix unchanged,
which proves the whole-triple coordinate property. For the tables, copy the integer-sign computation
from GP019B5b.lean and use prefix_integer_cast; its private table helpers are not available donors.
There are only five lists and four cells. Split j<4 versus j=4. At most 300 lines. -/
def T9_L1 : Prop := wholeT9Finite

/-- Marginal Gaussian summaries, correlations, and marginal uniform p-value limits.
Use frc_normal_margin for HasLaw and Gaussian first/second moments for the summaries. frc_row_dot
and independence of the five coordinate normals give the covariances. Compose the existing joint
weak limit with the continuous coordinate p-value map and identify its law via frc_p_law. The latter
is marginal uniformity, so no joint independence is asserted. At most 200 lines. -/
def T9_L2 : Prop := wholeT9Margins

/-- Conditional-average integrability and the covariance between two of the first four transforms.
Set c=d=1/sqrt(2). Identify wholeFisherH with frc_h c d by pointwise algebra. frc_g_memLp,
frc_h_memLp, Holder and product-integrability give all the moment guards (the inner integral need only
be integrable for almost every t). frc_covariance_common then gives the covariance identity for
j≠k<4, since their correlation is 1/2. At most 150 lines. -/
def T9_L3 : Prop :=
  MemLp wholeFisherG 2 (gaussianReal 0 1) ∧
  MemLp wholeFisherH 2 (gaussianReal 0 1) ∧
  Integrable (fun t => wholeFisherH t*wholeFisherG t) (gaussianReal 0 1) ∧
  (∀ᵐ t ∂gaussianReal 0 1, Integrable (fun a => wholeFisherG ((a+t)/Real.sqrt 2))
    (gaussianReal 0 1)) ∧
  (∀ j k : Fin 5, j.val < 4 → k.val < 4 → j ≠ k →
    wholeCovariance wholeGaussianFive
      (fun e => wholeFisherG (correlatedNormals e j))
      (fun e => wholeFisherG (correlatedNormals e k)) =
        wholeVariance (gaussianReal 0 1) wholeFisherH)

/-- Covariance with the fifth transformed coordinate, the new Fubini step.
For j<4, (E_j,E_5) has the product of two standard normal laws. Integrate their product
 g((a+t)/sqrt(2))*g(t) first in a; the inner expectation is h(t). Subtract the product of means.
Use frc_margin_memLp and frc_h_memLp for integrability of products; frc_pair_eq or the product-coordinate
projection identifies the pair law. This is an equality of genuine L2 moments, not totalized junk.
At most 200 lines. -/
def T9_L4 : Prop :=
  ∀ j : Fin 5, j.val < 4 →
    wholeCovariance wholeGaussianFive
      (fun e => wholeFisherG (correlatedNormals e j))
      (fun e => wholeFisherG (correlatedNormals e 4)) =
        wholeCovariance (gaussianReal 0 1) wholeFisherH wholeFisherG

/-- The five printed statistics are simultaneously defined with probability tending to one.
GP019B3b_cell_ae gives eventual counts at least two in each affirmative cell. frc_variance_consistency
has strictly positive limits 4,4,4,4,2 for n times each variance estimate, hence eventual positivity.
Intersect the finitely many almost-sure eventual events. t19_indicator_transfer converts to finite-sample
probabilities. No sample is assumed occupied for every n. At most 150 lines. -/
def T9_L5 : Prop :=
  Tendsto (fun n : ℕ => ((uniformFin 128 (by norm_num)).iid n).prob
    (fun s => wholeT9Defined s)) atTop (nhds 1)

/-- Completion invariance for bounded-continuous-test weak limits on finite sample laws.
The difference of two test expectations is bounded by 2C times the probability of the exceptional
event. Squeeze to zero and add to the known limit. The Fisher transforms also agree on the same
event, so this argument applies without bounding the statistics or the logarithm. The target is Borel
and Q is a probability law, making bounded continuous tests integrable. All maps on a
finite sample domain are measurable. This general transfer lemma takes at most 120 lines. -/
def T9_L6 : Prop :=
  ∀ (E : Type u) [Fintype E] (P : FiniteLaw E)
    (D : (n : ℕ) → (Fin n → E) → Prop),
    Tendsto (fun n : ℕ => (P.iid n).prob (D n)) atTop (nhds 1) →
    ∀ (F : Type u) [MeasurableSpace F] [TopologicalSpace F] [BorelSpace F]
      (T C : (n : ℕ) → (Fin n → E) → F) (Q : Measure F),
      IsProbabilityMeasure Q →
      (∀ n s, D n s → C n s = T n s) → WeakLimit P T Q → WeakLimit P C Q

/-- Every slice defining h(t) is a genuine expectation, including exceptional fixed t.
The affine image (E+t)/sqrt(2) is N(t/sqrt(2),1/2). Its density relative to N(0,1) is at most
sqrt(2)*exp(t²/2): complete the square in the density ratio. Since g is integrable for N(0,1),
measure domination gives integrability for that affine Gaussian law; pull back by the affine map.
This avoids any need for a new Mills-ratio estimate. At most 220 lines. -/
def T9_L7 : Prop :=
  ∀ t : ℝ, Integrable (fun a => wholeFisherG ((a+t)/Real.sqrt 2)) (gaussianReal 0 1)

 theorem T3_assembly (h1 : T3_L1) (h2 : T3_L2) : T3WholeStatement := by
  refine ⟨restrictedT3, t3_population, t3_singleton, h1, h2, ?_⟩
  let S := finiteSampleWitness
  let P := S.law.iid 4
  have hp : P.prob S.occupied ≠ 0 := by
    have h := AronowAudit.P019.Wave1.finite_product_counterexample_proof.2.1
    change P.prob S.occupied = 1431/2048 at h
    rw [h]; norm_num
  have hpoint : (fun s : Fin 4 → Fin 16 => S.muHat s 0 0) =
      fun s => S.sampleA s*S.sampleB s 0 0+1 := by
    funext s
    have h := AronowAudit.P019.estimator_product_identity (toStudy S) s 0 0
    change S.muHat s 0 0 = 1+S.sampleA s*S.sampleB s 0 0 at h
    linarith only [h]
  change P.cv _ S.occupied = P.cv _ S.occupied
  rw [hpoint]
  exact AronowAudit.P019.conditional_variance_shift (toLaw P) _ S.occupied hp 1

 theorem T4_assembly (h1 : T4_L1.{0}) (h2 : T4_L2.{u}) (h3 : T4_L3.{u})
    (h4 : T4_L4.{u}) (h5 : T4_L5.{u}) (h6 : T4_L6.{u}) : T4WholeStatement.{u} := by
  intro E _ G hp hm hb hs
  obtain ⟨N, _, S, hpop⟩ := h2 E G hp hm hb hs.2.1
  have hr := h3 E G N S hp hm hb hs.2.1 hpop
  have hS := h4 E G N S hp hm hb hs hr
  have hc : wholeT4Core S := restrictedT4 (Fin N) S hS
  have he : wholeT4Extras S := t4_extras S hS
  have hcount := h1 (Fin N) S hS
  exact ⟨h5 E G N S hp hm hb hs hS hr hc,
    h6 E G N S hp hm hb hs hS hr hcount he⟩

 theorem T5_assembly : T5WholeStatement := by
  refine ⟨restrictedT5, t5_data, ?_, ?_, ?_⟩
  · norm_num [Set.disjoint_left]
  · refine ⟨0, ?_⟩
    have h := restrictedT5
    change T5Statement at h
    obtain ⟨_, h0, hplus, _⟩ := h
    rw [h0, hplus]; norm_num
  · intro t
    have h := t5_data
    obtain ⟨_, _, _, _, _, _, _, _, hlaw⟩ := h
    have ht := hlaw t
    refine ⟨ht.1.trans ht.2.2.2.symm, ?_, t5_cdf t⟩
    have he : (fun ω : Fin 8 => if (distributionWitness.V ω : ℝ) = t+1 then (1 : ℝ) else 0) =
        fun ω => if (distributionWitness.V ω : ℝ)-1 = t then 1 else 0 := by
      funext ω
      simp only [sub_eq_iff_eq_add]
    rw [he]
    exact ht.1.trans ht.2.2.2.symm

 theorem T7_assembly : T7WholeStatement := by
  refine ⟨restrictedT7, t7_sixteen, t7_eight, ?_⟩
  have h : wholeDiagnosisEight.beta = 2 := t7_eight.2.2.2.2.2.2.2.2.2.1
  rw [h]; norm_num

 theorem T9_assembly (h1 : T9_L1) (h2 : T9_L2) (h3 : T9_L3)
    (h4 : T9_L4) (h5 : T9_L5) (h6 : T9_L6.{0}) (h7 : T9_L7) : T9WholeStatement := by
  refine ⟨restrictedT9, h1, ?_, t9_linearization, h2, ?_, h7, ?_⟩
  · intro j ω
    exact AronowAudit.P019.placebo_influence_residual (toStudy (sequentialStudy j))
      ((restrictedT9.1 j).1) ω (by norm_num [sequentialStudy, uniformFin, toStudy, toLaw])
  · obtain ⟨hg, hh, hprod, hae, hfirst⟩ := h3
    exact ⟨hg, hh, hprod, hae, t9_fisher_law, t9_variance_formula hfirst h4, t9_chi_moments⟩
  · refine ⟨h5, ?_⟩
    intro C hC
    obtain ⟨_, _, _, _, _, hz, hf, _, _, _, _⟩ := restrictedT9
    have hpG : IsProbabilityMeasure (wholeGaussianFive.map correlatedNormals) := by
      unfold wholeGaussianFive; infer_instance
    have hpF : IsProbabilityMeasure sequentialFisherLimit := by
      rw [sequentialFisherLimit_eq]
      exact AronowAudit.P019.Wave1.frc_T_law.isProbabilityMeasure_iff.mp inferInstance
    constructor
    · apply h6 (Fin 128) (uniformFin 128 (by norm_num))
        (fun _ s => wholeT9Defined s) h5 (Fin 5 → ℝ)
        (fun _ s j => studentized ((sequentialStudy j).betaHat s 0 0) 1
          ((sequentialStudy j).betaVarianceHat s 0)) C
        (wholeGaussianFive.map correlatedNormals) hpG
      · intro n s hs; funext j; exact hC n s hs j
      · exact hz
    · apply h6 (Fin 128) (uniformFin 128 (by norm_num))
        (fun _ s => wholeT9Defined s) h5 ℝ
        (fun _ s => fisherStatistic (fun j =>
          normalPValue ((sequentialStudy j).betaHat s 0 0) 1
            ((sequentialStudy j).betaVarianceHat s 0)))
        (fun n s => fisherStatistic (fun j => 2*normalCDF (-|C n s j|))) sequentialFisherLimit hpF
      · intro n s hs
        apply congrArg fisherStatistic
        funext j
        rw [hC n s hs j]
        rfl
      · exact hf

end
end SAP.P019a.WH.W1
