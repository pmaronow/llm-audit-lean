import SAP.P004a.Defs.WholeW2
import SAP.P004a.Bridge
import AronowAudit.P004.P004_RegressionCompletion
import AronowAudit.P004.Wave1.Gap.GLP0042B5
import AronowAudit.P004.Wave1.Gap.GP0042B2b
import AronowAudit.P004.Wave1.Gap.GLP0042B6
import AronowAudit.P004.Wave1.Gap.GLP0041B1
import AronowAudit.P004.Wave1.Gap.GP0041B1
import AronowAudit.P004.P004_DependencyCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W2

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
set_option maxHeartbeats 1000000

/-- Normalize Student's density for every positive real degree of freedom,
including degrees below one. Substitute u=x²/(ν+x²) on the positive half-line,
evaluate the beta integral, and use Gamma(1/2)=sqrt(pi). Establish absolute
integrability in the same substitution, before using real integrals. -/
def T8_L1 : Prop :=
  ∀ ν : ℝ, 0 < ν → Integrable (studentDensity ν) ∧ (∫ x, studentDensity ν x) = 1

/-- The log density ratio has derivative x(x²-1)/(ν+x²), and its value at
zero is nonpositive. Differentiate the logarithms of the positive densities;
bound the Gamma ratio by t7_gamma_midpoint_sq at ν/2 and ν/2+1. -/
def T8_L2 : Prop :=
  ∀ ν : ℝ, 0 < ν →
    studentDensity ν 0 ≤ gaussianPDFReal 0 1 0 ∧
    ∀ x : ℝ, HasDerivAt
      (fun t => Real.log (studentDensity ν t / gaussianPDFReal 0 1 t))
      (x*(x^2-1)/(ν+x^2)) x

/-- Turn the supplied log-ratio calculus into a single crossing on the
positive half-line. It decreases on (0,1), increases on (1,infinity), and
diverges to infinity: beyond max(2,sqrt(2ν)) its derivative is at least x/4.
Use the mean-value theorem and intermediate values. The premises are exactly
the two conclusions of L2 at this ν; no normalization is needed here. -/
def T8_L3 : Prop :=
  ∀ ν : ℝ, 0 < ν →
    studentDensity ν 0 ≤ gaussianPDFReal 0 1 0 →
    (∀ x : ℝ, HasDerivAt
      (fun t => Real.log (studentDensity ν t / gaussianPDFReal 0 1 t))
      (x*(x^2-1)/(ν+x^2)) x) →
    ∃ ρ : ℝ, 1 < ρ ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ ρ → studentDensity ν x ≤ gaussianPDFReal 0 1 x) ∧
      (∀ x : ℝ, ρ ≤ x → gaussianPDFReal 0 1 x ≤ studentDensity ν x)

/-- CDF facts once normalization is supplied. Positivity and continuity of
the density give a continuous strictly increasing CDF; symmetry gives its
value 1/2 at zero, and integrability gives its limit one at infinity.
Use set-integral continuity and positivity on every nonempty interval. -/
def T8_L4 : Prop :=
  ∀ ν : ℝ, 0 < ν → Integrable (studentDensity ν) → (∫ x, studentDensity ν x) = 1 →
    Continuous (studentCDF ν) ∧ StrictMono (studentCDF ν) ∧
    studentCDF ν 0 = 1/2 ∧ Tendsto (studentCDF ν) atTop (nhds 1)

/-- A normalized symmetric Student density with the supplied crossing has
CDF below the normal CDF on the nonnegative half-line. Below the crossing
integrate the density difference from zero; above it integrate the reversed
difference to infinity. Both half-line masses are 1/2. All integrals are
integrable by the premises and integrable_gaussianPDFReal. -/
def T8_L5 : Prop :=
  ∀ ν : ℝ, 0 < ν → Integrable (studentDensity ν) → (∫ x, studentDensity ν x) = 1 →
    studentCDF ν 0 = 1/2 →
    (∃ ρ : ℝ, 1 < ρ ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ ρ → studentDensity ν x ≤ gaussianPDFReal 0 1 x) ∧
      (∀ x : ℝ, ρ ≤ x → gaussianPDFReal 0 1 x ≤ studentDensity ν x)) →
    ∀ x : ℝ, 0 ≤ x → studentCDF ν x ≤ normalCDF x

/-- The exceptional empty-arm probability is p^N+(1-p)^N for N>0 and
vanishes. A zero count forces the unique all-control or all-treated vector;
evaluate its finite product weight, then use geometric convergence. -/
def T8_L6 : Prop :=
  ∀ p : ℝ, 0 < p ∧ p < 1 →
    (∀ N : ℕ, 0 < N → prob (fun _ => p) (fun z : Assignment N => ¬ ValidArms z) =
      p^N+(1-p)^N) ∧
    Tendsto (fun N => prob (fun _ => p) (fun z : Assignment N => ¬ ValidArms z))
      atTop (nhds 0)

/-- Identify the actual spectral positive part in the repeated-star witness,
for every block count, including zero. On one block the eigenvalues are
-1,1,1,1,3 and the negative projection is ww'/8, w=(2,-1,-1,-1,-1).
A short polynomial route avoids choosing these eigenspaces: verify
(K+I)(K-I)(K-3I)=0 blockwise. Its spectral values belong to {-1,1,3}, where
max(t,0)=(t²+4t+3)/8. Use positiveKernel_data and the spectral theorem to
identify the positive part with (K²+4K+3I)/8, then compute the five-by-five
blocks. Handle m=0 first; blockDiagonal multiplication handles the lift.
This is a matrix identity, with no statistical or spectral-representation premise. -/
def T8_L7 : Prop :=
  ∀ m : ℕ, positiveKernel (starBlockKernel m false) = starBlockKernel m true

/-- Strict scalar likelihood geometry. Differentiate the logistic score,
use its strictly negative derivative for strict concavity, and combine with
t9b6_choice_max to get uniqueness. In the two outer branches, monotonicity
of logit gives the clipped formula; at counts zero and N use the defining
branches. This leaf contains only the strictness and identification missing
from the existing maximality proof. -/
def T9_L1 : Prop :=
  ∀ N : ℕ, 0 < N → ∀ z : Assignment N,
    (∀ t : ℝ, HasDerivAt (fun s => armCount z true - N*logistic s)
      (-(N : ℝ)*Real.exp t/(1+Real.exp t)^2) t ∧
      -(N : ℝ)*Real.exp t/(1+Real.exp t)^2 < 0) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, boundaryLikelihood z t = boundaryLikelihood z (boundaryMLE z) →
      t = boundaryMLE z) ∧
    (armCount z true = N → boundaryMLE z = 1) ∧
    (0 < armCount z true → armCount z true < N → boundaryMLE z =
      min 1 (max 0 (Real.log ((armCount z true / N)/(1-armCount z true / N)))))

/-- Sharp Paley-Zygmund bound and the exact symmetry split. From the donor's
second and fourth moments, the tail contribution of T² is at least 3N/4;
weighted Cauchy-Schwarz bounds its square by (3N²-2N) Pr(tail).
Complement all bits to exchange the two strict signed tails. N>0 makes the
fourth-moment denominator positive and excludes zero from the squared tail. -/
def T9_L2 : Prop :=
  ∀ N : ℕ, 0 < N →
    9*(N : ℝ)^2/(16*(3*(N : ℝ)^2-2*N)) ≤
      prob (fun _ => 1/2) (fun z : Assignment N => (N : ℝ)/4 < (boundarySignSum z)^2) ∧
    prob (fun _ => 1/2) (fun z : Assignment N =>
      boundarySignSum z < 0 ∧ (N : ℝ)/4 < (boundarySignSum z)^2) =
      prob (fun _ => 1/2) (fun z : Assignment N => (N : ℝ)/4 < (boundarySignSum z)^2)/2

/-- The standardized fair-sign sum has the standard normal limit under the
actual finite Bernoulli design. Apply corrected_dependency_clt to the finite
atomic design, singleton neighborhoods and signs 2Z-1: means zero, bound one,
variance N. Use t9b6_moments and the atomicDesign expectation adapter. -/
def T9_L3 : Prop :=
  NormalLimit (fun _ _ => 1/2) (fun N z => boundarySignSum z / Real.sqrt N)

/-- Transfer the sign CLT to both printed limit laws and the limiting atom.
For x>0 and eventually x/sqrt(N)<1, the MLE CDF event is exactly
q<=logistic(x/sqrt(N)); its standardized cutoff tends to x/2, since the
logistic derivative at zero is 1/4. Squeeze moving cutoffs using normal CDF
continuity. For x<0 the probability is zero. The atom is exactly {T<=0}.
The leading term is exactly 2T/N. This avoids differentiating the nonsmooth
positive-part map at zero. -/
def T9_L4 : Prop :=
  NormalLimit (fun _ _ => 1/2) (fun N z => boundarySignSum z / Real.sqrt N) → T9LimitLaws

/-- Realize the one-node atomic design by its actual Euclidean integrals.
The radii are 1,2,2. Integrate the three Dirac measures separately, proving
integrability first. The four masses are 1,2,3,3 and the per-draw means are
0,Z,2Z/3,2Z/3. Measurability is the inverse image of a closed band.
This is the only new finite atomic integration needed by this target. -/
def T14_L1 : Prop :=
  (∀ D ∈ ({({1} : Set ℝ), {2}, Icc 0 2, Icc 1 2} : Set (Set ℝ)),
    WellDefined (oneShellPopulation D) 0) ∧
  (∀ x z, |(oneShellPopulation {1}).outcome x z| < 2) ∧
  (∀ x : Fin 3, nodeDistance (oneShellPopulation {1}) 0 (oneShellAtom x) =
    if x = 0 then 1 else 2) ∧
  (∀ z : Assignment 1,
    circleAverage (oneShellPopulation {1}) 0 0 z = 0 ∧
    circleAverage (oneShellPopulation {2}) 0 0 z = bit (z 0) ∧
    circleAverage (oneShellPopulation (Icc 0 2)) 0 0 z = 2*bit (z 0)/3 ∧
    circleAverage (oneShellPopulation (Icc 1 2)) 0 0 z = 2*bit (z 0)/3) ∧
  shellMass (oneShellPopulation {1}) 0 = 1 ∧
  shellMass (oneShellPopulation {2}) 0 = 2 ∧
  shellMass (oneShellPopulation (Icc 0 2)) 0 = 3 ∧
  shellMass (oneShellPopulation (Icc 1 2)) 0 = 3

/-- Establish the area witness's existence and conditional-mean certificate.
The distance region is a closed annulus. Intersecting with the disk changes
nothing for 0<=a<b<=1; its mass is pi(b²-a²)>0 and finite. Bounded measurable
outcomes are integrable. Enumerate the one-node marginalization to get the
point effect norm(x), so the identity radius function satisfies the defining
conditional-mean moment property and is continuous, even at r=0 and r=1. -/
def T14_L2 : Prop := T14AreaExistence

/-- Transport the area band AME through the normalized radial measure.
Use annulus_radial_measure_proof at center zero after removing the redundant
disk restriction; integral_map and the withDensity integral formula then give
the radial integral. Use the supplied existence certificate to justify the
point-effect integral and its nonzero mass division. -/
def T14_L3 : Prop := T14AreaExistence → T14AreaTransport

theorem positiveKernel_data {N : ℕ} (K : Matrix (Fin N) (Fin N) ℝ) (hK : K.IsSymm) :
    ∃ (values : Fin N → ℝ) (vectors : Matrix (Fin N) (Fin N) ℝ),
      vectors.transpose * vectors = 1 ∧
      spectralKernel values vectors false = K ∧
      spectralKernel values vectors true = positiveKernel K := by
  have hh : K.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hK
  let V : Matrix (Fin N) (Fin N) ℝ := hh.eigenvectorUnitary
  refine ⟨hh.eigenvalues, V, ?_, ?_, ?_⟩
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using Unitary.coe_star_mul_self hh.eigenvectorUnitary
  · have hs := hh.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    apply Eq.trans (b := V * Matrix.diagonal (RCLike.ofReal ∘ hh.eigenvalues) * star V) ?_ hs.symm
    ext i j
    simp only [spectralKernel, Bool.false_eq_true, ↓reduceIte]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
      Matrix.star_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro k _
    change hh.eigenvalues k * V i k * V j k = V i k * hh.eigenvalues k * V j k
    ring
  · simp only [positiveKernel, dite_eq_left hh]
    rfl

theorem boundary_propensity (N : ℕ) (i : Fin N) :
    propensities (boundaryO N) boundaryTheta i = 1/2 := by
  norm_num [propensities, boundaryO, boundaryTheta, dot, Fin.sum_univ_one, logistic]

theorem boundary_overlap : Overlap (fun N => propensities (boundaryO N) boundaryTheta) := by
  refine ⟨1/4, by norm_num, by norm_num, ?_⟩
  intro N i
  dsimp only
  rw [boundary_propensity]
  norm_num

theorem boundary_information (N : ℕ) (hN : 0 < N) :
    information (fun _ => 1/2) (boundaryO N) = (1/4 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  ext i j
  fin_cases i
  fin_cases j
  norm_num [information, boundaryO, hn]

theorem leading_information (N : ℕ) (hN : 0 < N) (z : Assignment N) :
    ((information (fun _ => 1/2) (boundaryO N))⁻¹ *ᵥ
      logisticScore (fun _ => 1/2) (boundaryO N) z) 0 = boundaryLeading z := by
  rw [boundary_information N hN]
  norm_num [Matrix.inv_def, Matrix.adjugate_fin_one, Matrix.det_fin_one,
    Matrix.mulVec, dotProduct, Fin.sum_univ_one, logisticScore, boundaryO,
    boundaryLeading, AronowAudit.P004.Wave1.t9b6_count_eq,
    Finset.sum_sub_distrib, Finset.sum_div]
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hc : armCount z true = ∑ i, bit (z i) := AronowAudit.P004.Wave1.t9b6_count_eq z
  rw [hc]
  field_simp


theorem T8_student (h1 : T8_L1) (h2 : T8_L2) (h3 : T8_L3) (h4 : T8_L4) (h5 : T8_L5) :
    T8StudentComparison := by
  intro ν a hν ha ha1
  obtain ⟨hi, hn⟩ := h1 ν hν
  obtain ⟨hcenter, hderiv⟩ := h2 ν hν
  obtain ⟨hcont, hmono, hhalf, hlim⟩ := h4 ν hν hi hn
  have horder := h5 ν hν hi hn hhalf (h3 ν hν hcenter hderiv)
  have hnon : {x : ℝ | a ≤ studentCDF ν x}.Nonempty := by
    obtain ⟨x, hx⟩ := ((tendsto_order.mp hlim).1 a ha1).exists
    exact ⟨x, hx.le⟩
  have hpos : ∀ x : ℝ, a ≤ studentCDF ν x → 0 ≤ x := by
    intro x hx
    by_contra h
    have hh := hmono.monotone (le_of_lt (lt_of_not_ge h))
    rw [hhalf] at hh
    linarith
  have hbdd : BddBelow {x : ℝ | a ≤ studentCDF ν x} := ⟨0, fun x hx => hpos x hx⟩
  refine ⟨hnon, hbdd, ?_⟩
  apply le_csInf hnon
  intro x hx
  obtain ⟨_, hm, _, _, hq, _, _⟩ := AronowAudit.P004.Wave1.DesignLimits.nf_proof
  have hmLocal : StrictMono normalCDF := hm
  apply hmLocal.le_iff_le.mp
  have hqa : normalCDF (normalQuantile a) = a := hq a (by linarith) ha1
  rw [hqa]
  exact hx.trans (horder x (hpos x hx))

theorem T8_finite (hs : T8StudentComparison) : T8FiniteWhole := by
  intro N K hK z e hz
  obtain ⟨values, vectors, ho, he, hQ⟩ := positiveKernel_data K hK
  have hfinite : T8FiniteStatement := @AronowAudit.P004.capped_pd_interval
  have hdon := hfinite values vectors ho z e hz.1 hz.2
  have hbase := hdon 0 0 0 ⟨le_rfl, le_rfl⟩
  change kernelVariance z e (spectralKernel values vectors true) ≤ _ ∧
    max (kernelVariance z e (spectralKernel values vectors false)) 0 ≤ _ ∧ _ at hbase
  rw [he, hQ] at hbase
  refine ⟨AronowAudit.P004.MatrixCompletion.sandwich_treatment z hz.1 hz.2 e K,
    AronowAudit.P004.MatrixCompletion.sandwich_treatment z hz.1 hz.2 e (positiveKernel K),
    hbase.1, hbase.2.1, ?_, ?_⟩
  · intro α c err hα hc hnon herr
    have hcrit := AronowAudit.P004.Wave1.GP0042B2b_capped_pd_quantile α hα
    have hh := (hdon (normalQuantile (1-α/2)) c err ⟨hcrit.1.le, hc⟩).2.2
    change (0 ≤ kernelVariance z e (spectralKernel values vectors false) → _ → _) at hh
    rw [he, hQ] at hh
    exact hh hnon herr
  · intro α ν err hα hν hnon herr
    have hc := (hs ν (1-α/2) hν (by linarith) (by linarith)).2.2
    have hcrit := AronowAudit.P004.Wave1.GP0042B2b_capped_pd_quantile α hα
    have hh := (hdon (normalQuantile (1-α/2)) (studentQuantile ν (1-α/2)) err
      ⟨hcrit.1.le, hc⟩).2.2
    change (0 ≤ kernelVariance z e (spectralKernel values vectors false) → _ → _) at hh
    rw [he, hQ] at hh
    exact hh hnon herr

theorem uniformKernel_symmetric {N : ℕ} {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (P : SpatialPopulation N X) (h : ℝ) :
    (uniformDistanceKernel (nodeSeparation P) h).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [uniformDistanceKernel, Matrix.of_apply]
  rw [show nodeSeparation P i j = nodeSeparation P j i from
    AronowAudit.P004.CLTCompletion.nodeSeparation_symm (Bridge.toPopulation P) i j]

theorem T8_asymptotic {Space : ℕ → Type*} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (hs : T8StudentComparison) (h6 : T8_L6) :
    T8AsymptoticWhole (Space := Space) := by
  intro P p d h α hp hd hh hα hP hWD hloc hv hhom
  have arbitrary : ∀ c : ∀ N, Assignment N → ℝ,
      (∀ N z, ValidArms z → normalQuantile (1-α/2) ≤ c N z) →
      Conservative (T8Coverage P p d h c) α := by
    intro c hc
    choose values vectors ho he hQ using
      (fun N => positiveKernel_data (uniformDistanceKernel (nodeSeparation (P N)) h)
        (uniformKernel_symmetric (P N) h))
    let cext : ∀ N, Assignment N → ℝ := fun N z =>
      if ValidArms z then c N z else normalQuantile (1-α/2)
    have hcext : ∀ N z, normalQuantile (1-α/2) ≤ cext N z := by
      intro N z
      by_cases hz : ValidArms z
      · simpa only [cext, ite_eq_left hz] using hc N z hz
      · simp only [cext, ite_eq_right hz, le_refl]
    have htotal := AronowAudit.P004.Wave1.capped_pd_coverage_proof
      (Bridge.toSequence P) p d h α hp hd hh hα hP hWD hloc hv values vectors ho he hhom cext hcext
    change Conservative (fun N => prob (fun _ => p) (fun z : Assignment N =>
      |hajek (circleAverage (P N) d) z - ame (fun _ => p) (circleAverage (P N) d)| ≤
        cext N z * Real.sqrt (cappedVariance
          (kernelVariance z (residual (circleAverage (P N) d) z) (spectralKernel (values N) (vectors N) true))
          (adjustmentMu z (spectralKernel (values N) (vectors N) true))))) α at htotal
    simp_rw [hQ] at htotal
    intro ε hε
    have hbad := (tendsto_order.mp (h6 p hp).2).2 (ε/2) (by linarith)
    filter_upwards [htotal (ε/2) (by linarith), hbad] with N htot hbadN
    let A : Assignment N → Prop := fun z =>
      |hajek (circleAverage (P N) d) z - ame (fun _ => p) (circleAverage (P N) d)| ≤
        cext N z * Real.sqrt (cappedVariance
          (kernelVariance z (residual (circleAverage (P N) d) z)
            (positiveKernel (uniformDistanceKernel (nodeSeparation (P N)) h)))
          (adjustmentMu z (positiveKernel (uniformDistanceKernel (nodeSeparation (P N)) h))))
    have hbound := AronowAudit.P004.Wave1.GP0042B2b_capped_pd_prob_difference
      (fun _ : Fin N => p) (fun _ => hp) A (fun z => ¬ ValidArms z) (fun _ => False)
      (fun z => ValidArms z ∧
        |hajek (circleAverage (P N) d) z - ame (fun _ => p) (circleAverage (P N) d)| ≤
          c N z * Real.sqrt (cappedVariance
            (kernelVariance z (residual (circleAverage (P N) d) z)
              (positiveKernel (uniformDistanceKernel (nodeSeparation (P N)) h)))
            (adjustmentMu z (positiveKernel (uniformDistanceKernel (nodeSeparation (P N)) h)))))
      (by
        intro z hA hvalid _
        have hz : ValidArms z := not_not.mp hvalid
        exact ⟨hz, by simpa only [A, cext, ite_eq_left hz] using hA⟩)
    have hf : AronowAudit.P004.prob (fun _ : Fin N => p) (fun _ => False) = 0 := by
      simp [AronowAudit.P004.prob, AronowAudit.P004.expect]
    rw [hf, sub_zero] at hbound
    change prob (fun _ => p) A - prob (fun _ => p) (fun z : Assignment N => ¬ ValidArms z) ≤
      T8Coverage P p d h c N at hbound
    change 1-α-ε ≤ T8Coverage P p d h c N
    change 1-α-ε/2 ≤ prob (fun _ : Fin N => p) A at htot
    linarith
  refine ⟨arbitrary, ?_⟩
  intro ν hν
  apply arbitrary
  intro N z hz
  exact (hs (ν N z) (1-α/2) (hν N z hz) (by linarith) (by linarith)).2.2

theorem star_invalid_limit :
    Tendsto (fun m => prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
      ¬ (ValidArms z ∧ 0 < adjustmentMu z (starBlockKernel m true) ∧
        0 < adjustmentNu z (starBlockKernel m true)))) atTop (nhds 0) := by
  have hbound : ∀ᶠ m in atTop,
      prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
        ¬ (ValidArms z ∧ 0 < adjustmentMu z (starBlockKernel m true) ∧
          0 < adjustmentNu z (starBlockKernel m true))) ≤
      AronowAudit.P004.prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
        ¬ AronowAudit.P004.Wave1.t7_Good m z) +
      prob (fun _ => 1/2) (fun z : Assignment (5*m) =>
        1/5 < |adjustmentMu z (starBlockKernel m true)-6/5|) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    apply AronowAudit.P004.Wave1.GP0042B2b_capped_pd_prob_two_upper _ (fun _ => by norm_num)
    intro z hz
    by_cases hg : AronowAudit.P004.Wave1.t7_Good m z
    · right
      by_contra hbad
      have hμ : 0 < adjustmentMu z (starBlockKernel m true) := by
        have hh := (abs_le.mp (le_of_not_gt hbad)).1
        linarith
      exact hz ⟨AronowAudit.P004.Wave1.t7_good_counts m hm z hg.1, hμ,
        AronowAudit.P004.Wave1.t7_nu_pos m hm z hg.1 hμ.ne'⟩
    · exact Or.inl hg
  have hlim := AronowAudit.P004.Wave1.t7_good_probability.add
    (AronowAudit.P004.Wave1.t7_mu_limit (1/5) (by norm_num))
  simp only [add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall (fun m =>
    AronowAudit.P004.Wave1.GP0042B2b_capped_pd_prob_nonneg _ (fun _ => by norm_num) _)) hbound
  exact hlim


theorem T8_uncapped (h7 : T8_L7) : T8UncappedWhole := by
  have ha := AronowAudit.P004.Wave1.adjusted_pd_asymptotic_counterexample_proof
  have hQ (m : ℕ) :
      positiveKernel (uniformDistanceKernel (nodeSeparation (starPopulation (5*m))) (6/5)) =
        starBlockKernel m true := by
    rw [show uniformDistanceKernel (nodeSeparation (starPopulation (5*m))) (6/5) =
      starBlockKernel m false from AronowAudit.P004.Wave1.t7_star_kernel m]
    exact h7 m
  refine ⟨ha.1, AronowAudit.P004.Wave1.t7_star_wellDefined, ?_, ha.2.2.1, ha.2.2.2.1,
    ?_, ?_, hQ, ?_, ?_, ha.2.2.2.2.2.2.2.2.2.2.2⟩
  · intro N i j hij
    exact AronowAudit.P004.Wave1.t7_star_local N 0 i j (lt_trans (by norm_num) hij)
  · intro m
    funext i z
    exact AronowAudit.P004.Wave1.t7_star_circleAverage (5*m) i z
  · intro m
    change AronowAudit.P004.ame (fun _ => 1/2) (fun i _ =>
      AronowAudit.P004.starY ⟨i.val%5, Nat.mod_lt _ (by omega)⟩) = 0
    simp only [AronowAudit.P004.ame, AronowAudit.P004.nodeEffect,
      AronowAudit.P004.Wave1.t7_fixed_marginal (fun _ : Fin (5*m) => 1/2) (fun _ => by norm_num),
      sub_self, Finset.sum_const_zero, zero_div]
  · simpa only [hQ] using star_invalid_limit
  · intro ε hε
    have ht := (tendsto_order.mp AronowAudit.P004.Wave1.t7_coverage_limit).2
      (2*normalCDF (normalQuantile (39/40)*Real.sqrt (15/16))-1+ε) (lt_add_of_pos_right _ hε)
    filter_upwards [ht] with m hm
    apply lt_of_le_of_lt ?_ hm
    apply AronowAudit.P004.Wave1.GP0042B2b_capped_pd_prob_mono _ (fun _ => by norm_num)
    intro z hz
    rw [hQ] at hz
    exact hz.2.2.2

theorem T8_assembly (h1 : T8_L1) (h2 : T8_L2) (h3 : T8_L3)
    (h4 : T8_L4) (h5 : T8_L5) (h6 : T8_L6) (h7 : T8_L7) :
    T8WholeStatement := by
  have hs := T8_student h1 h2 h3 h4 h5
  refine ⟨hs, T8_finite hs, ?_, T8_uncapped h7⟩
  intro Space _ _
  exact T8_asymptotic hs h6


theorem T9_model : T9ModelWhole := by
  have hlog : LogisticConditions boundaryO boundaryTheta boundaryParameterSet
      (fun _ z _ => boundaryMLE z) := AronowAudit.P004.Wave1.t9b6_conditions
  refine ⟨hlog, boundary_overlap, hlog.1, hlog.2.1, ?_, ?_, ?_⟩
  · intros
    norm_num [boundaryO]
  · intro N i
    rw [boundary_propensity]
    norm_num
  · intro N hN
    refine ⟨?_, boundary_information N hN⟩
    have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    simp [boundaryO, hn]

theorem T9_likelihood (h1 : T9_L1) : T9LikelihoodWhole := by
  intro N hN z
  obtain ⟨hsecond, hunique, hfull, hclip⟩ := h1 N hN z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hfull, hclip⟩
  · intro t
    exact (AronowAudit.P004.Wave1.t9b6_likelihood_sum z t).symm
  · intro t
    exact ⟨AronowAudit.P004.Wave1.t9b6_likelihood_deriv N (armCount z true) t, hsecond t⟩
  · exact AronowAudit.P004.Wave1.t9b6_choice_bounds (armCount z true/N)
  · intro t ht
    exact ⟨AronowAudit.P004.Wave1.t9b6_choice_max N (armCount z true) t
      (Nat.cast_pos.mpr hN) ht, hunique t ht⟩
  · intro hS
    have hq : armCount z true / N ≤ (1/2 : ℝ) :=
      (div_le_iff₀ (Nat.cast_pos.mpr hN : (0 : ℝ) < N)).mpr (by linarith)
    exact ite_eq_left hq
  · intro hS
    simp [boundaryMLE, hS]

theorem T9_algebra : T9AlgebraWhole := by
  intro N hN z
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hs : boundarySignSum z = 2*armCount z true - N :=
    AronowAudit.P004.Wave1.t9b6_signsum_count z
  have hlead : boundaryLeading z = 2*boundarySignSum z/N := by
    rw [hs]
    unfold boundaryLeading
    field_simp
    ring
  refine ⟨hs, leading_information N hN z, hlead, ?_, ?_⟩
  · intro hneg
    have hq : armCount z true / N ≤ (1/2 : ℝ) :=
      (div_le_iff₀ hn).mpr (by linarith)
    simp only [boundaryRemainder, boundaryMLE, ite_eq_left hq, zero_sub, hlead]
    ring
  · exact AronowAudit.P004.Wave1.t9b6_tail_inclusion hN z

theorem T9_tails (h2 : T9_L2) : T9TailsWhole := by
  intro N hN
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hD : 0 < 3*(N : ℝ)^2-2*N := by nlinarith [sq_nonneg ((N : ℝ)-1)]
  obtain ⟨hlower, hsplit⟩ := h2 N hN
  have hinc : prob (fun _ => 1/2) (fun z : Assignment N =>
      boundarySignSum z < 0 ∧ (N : ℝ)/4 < (boundarySignSum z)^2) ≤
      prob (fun _ => 1/2) (fun z : Assignment N => 1 < Real.sqrt N * |boundaryRemainder z|) := by
    exact AronowAudit.P004.Wave1.GP0042B2b_capped_pd_prob_mono _
      (fun _ => by norm_num) _ _ (fun z hz => (T9_algebra N hN z).2.2.2.2 hz)
  refine ⟨(AronowAudit.P004.Wave1.t9b6_moments N).1,
    (AronowAudit.P004.Wave1.t9b6_moments N).2, hD, hlower, hsplit, ?_, ?_⟩
  · rw [hsplit] at hinc
    have hh := div_le_div_of_nonneg_right hlower (by norm_num : (0 : ℝ) ≤ 2)
    have he : (9*(N : ℝ)^2/(16*(3*(N : ℝ)^2-2*N)))/2 =
        9*(N : ℝ)^2/(32*(3*(N : ℝ)^2-2*N)) := by
      rw [div_div, show (16*(3*(N : ℝ)^2-2*N))*2 = 32*(3*(N : ℝ)^2-2*N) by ring]
    rw [he] at hh
    exact hh.trans hinc
  · apply (le_div_iff₀ (by positivity : 0 < 32*(3*(N : ℝ)^2-2*N))).mpr
    nlinarith

theorem T9_assembly (h1 : T9_L1) (h2 : T9_L2) (h3 : T9_L3) (h4 : T9_L4) : T9WholeStatement := by
  have hr := AronowAudit.P004.Wave1.corrected_mle_proof boundaryO boundaryTheta boundaryParameterSet
    (fun _ z _ => boundaryMLE z) T9_model.1 boundary_overlap
  have hp : (fun N => AronowAudit.P004.propensities (boundaryO N) boundaryTheta) =
      (fun _ _ => (1/2 : ℝ)) := by
    funext N i
    exact boundary_propensity N i
  rw [hp] at hr
  refine ⟨T9_model, T9_likelihood h1, T9_algebra, T9_tails h2,
    AronowAudit.P004.Wave1.t9b6_not_littleOp, h4 h3, ?_, ?_⟩
  · change AronowAudit.P004.InProb (fun _ _ => 1/2) (fun _ z => |boundaryMLE z|)
    simpa [boundaryTheta, Pi.sub_def, Real.norm_eq_abs] using hr.1
  · change AronowAudit.P004.BigOp (fun _ _ => 1/2) (fun _ z => |boundaryMLE z|) (fun N => (Real.sqrt N)⁻¹)
    simpa [boundaryTheta, Pi.sub_def, Real.norm_eq_abs] using hr.2.1


theorem assignment_one_univ : (Finset.univ : Finset (Assignment 1)) = {![false], ![true]} := by
  decide

theorem ame_one (R : CircleTable 1) (c : ℝ) (hR : ∀ z, R 0 z = c*bit (z 0)) :
    ame (fun _ => 1/2) R = c := by
  have he : R = fun _ z => c*bit (z 0) := by
    funext i z
    fin_cases i
    exact hR z
  rw [he]
  norm_num [ame, nodeEffect, marginal, expect, designWeight, coin, bit,
    assignment_one_univ, Fin.sum_univ_one]

theorem T14_one (h1 : T14_L1) : T14OneNodeWhole := by
  rcases h1 with ⟨hWD, hb, hdist, htable, hm1, hm2, hm02, hm12⟩
  have hA1 : ame (fun _ => 1/2) (circleAverage (oneShellPopulation {1}) 0) = 0 :=
    ame_one _ 0 (fun z => by simpa using (htable z).1)
  have hA2 : ame (fun _ => 1/2) (circleAverage (oneShellPopulation {2}) 0) = 1 :=
    ame_one _ 1 (fun z => by simpa using (htable z).2.1)
  have hA02 : ame (fun _ => 1/2) (circleAverage (oneShellPopulation (Icc 0 2)) 0) = 2/3 :=
    ame_one _ (2/3) (fun z => by rw [(htable z).2.2.1]; ring)
  have hA12 : ame (fun _ => 1/2) (circleAverage (oneShellPopulation (Icc 1 2)) 0) = 2/3 :=
    ame_one _ (2/3) (fun z => by rw [(htable z).2.2.2]; ring)
  refine ⟨hWD, hb, hdist, hA1, hA2, ?_, hA02, hA12, ?_, ?_, ?_⟩
  · rw [hA1, hA2]
    norm_num
  · rw [hm1, hm12]
  · rw [hm2, hm12]
  · rw [hA1, hA2, hA12]
    norm_num

theorem T14_two : T14TwoNodeWhole := by
  have hbase : T14Statement := AronowAudit.P004.spatial_shell_counterexample
  have ht (D : Set ℝ) (hD : MeasurableSet D) : circleAverage (shellSpatialPopulation D) 0 =
      AronowAudit.P004.shellWitnessTable (fun r => r ∈ D) :=
    AronowAudit.P004.shell_spatial_table D hD
  have hm (D : Set ℝ) (i : Fin 2) : shellMass (shellSpatialPopulation D) i =
      (∑ x : Fin 3, if AronowAudit.P004.shellWitnessDistance i x ∈ D then
        (1 : ENNReal) else 0).toReal :=
    congrArg ENNReal.toReal (AronowAudit.P004.shell_spatial_mass D i)
  refine ⟨hbase, ?_, ?_, ?_⟩
  · intro i x
    exact AronowAudit.P004.shell_atom_distances i x
  · intro i
    have hu3 : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
    rw [ht {4} (measurableSet_singleton 4), ht {5} (measurableSet_singleton 5),
      ht (Icc 4 5) measurableSet_Icc, ht (Icc 0 5) measurableSet_Icc, hm, hm, hm]
    fin_cases i <;>
      norm_num [nodeEffect, marginal, expect, designWeight, coin, bit,
        AronowAudit.P004.assignment_two_univ, AronowAudit.P004.shellWitnessTable,
        AronowAudit.P004.shellWitnessDistance, AronowAudit.P004.shellWitnessOutcome,
        AronowAudit.P004.shellWitnessEffect, AronowAudit.P004.bit, Fin.sum_univ_succ, hu3, Finset.filter_insert, Finset.filter_singleton]
  · intro w4 w5
    rcases hbase with ⟨_, _, _, _, _, h4, h5, _, hdisk, _⟩
    rw [h4, h5, hdisk]
    norm_num

/-- Elementary polynomial integration used by the area witness. -/
theorem radial_values :
    ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      IntegrableOn (fun r : ℝ => r) (Icc a b) ∧
      radialUniform a b = (a+b)/2 ∧
      radialAreaIntegral a b = 2*(b^3-a^3)/(3*(b^2-a^2)) := by
  intro a b ha hab _hb
  have hd : b-a ≠ 0 := (sub_pos.mpr hab).ne'
  have hdelta : b^2-a^2 ≠ 0 := by
    have hsum : 0 < b+a := by linarith
    have hh : b^2-a^2 = (b-a)*(b+a) := by ring
    rw [hh]
    exact mul_ne_zero hd hsum.ne'
  refine ⟨continuous_id.integrableOn_Icc, ?_, ?_⟩
  · rw [radialUniform, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab.le, integral_id]
    field_simp [hd]
    ring
  · have he : (fun r : ℝ => r*(2*r/(b^2-a^2))) =
        (fun r : ℝ => (2/(b^2-a^2))*r^2) := by
      funext r
      ring
    rw [radialAreaIntegral, he, integral_const_mul, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hab.le, integral_pow]
    field_simp [hdelta]
    ring


theorem T14_area (h2 : T14_L2) (h3 : T14_L3) : T14AreaWhole := by
  have h4 := radial_values
  have hT := h3 h2
  have hu01 : radialUniform 0 1 = 1/2 := by
    have hh := (h4 0 1 (by norm_num) (by norm_num) (by norm_num)).2.1
    norm_num at hh
    exact hh
  have ha01 : ame (fun _ => 1/2) (circleAverage (radialAreaPopulation (Icc 0 1)) 0) = 2/3 := by
    rw [(hT 0 1 (by norm_num) (by norm_num) (by norm_num)).2.2,
      (h4 0 1 (by norm_num) (by norm_num) (by norm_num)).2.2]
    norm_num
  have hu12 : radialUniform (1/2) 1 = 3/4 := by
    have hh := (h4 (1/2) 1 (by norm_num) (by norm_num) (by norm_num)).2.1
    norm_num at hh
    exact hh
  have ha12 : ame (fun _ => 1/2) (circleAverage (radialAreaPopulation (Icc (1/2) 1)) 0) = 7/9 := by
    rw [(hT (1/2) 1 (by norm_num) (by norm_num) (by norm_num)).2.2,
      (h4 (1/2) 1 (by norm_num) (by norm_num) (by norm_num)).2.2]
    norm_num
  refine ⟨h2, hT, h4, hu01, ha01, hu12, ha12, ?_, ?_⟩
  · rw [hu01, ha01]
    norm_num
  · rw [hu12, ha12]
    norm_num

theorem T14_assembly (h1 : T14_L1) (h2 : T14_L2) (h3 : T14_L3) :
    T14WholeStatement := by
  exact ⟨T14_one h1, T14_two, T14_area h2 h3⟩

end
end SAP.P004a.WH.W2
