import SAP.P004a.WH.W1.Glue
import AronowAudit.P004.Wave1.ObservationalCoverage
import AronowAudit.P004.Wave1.DesignLimits.DL3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P004a.WH.W1

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix Classical Topology ENNReal NNReal
noncomputable section
universe u v
set_option maxHeartbeats 1000000

/-- Push an integrable signed density through a measurable distance map on a finite band.
Form `(μ.withDensityᵥ δ).map r`, prove absolute continuity with respect to `Measure.map r μ`,
and use SignedMeasure.withDensityᵥ_rnDeriv_eq and integrable_rnDeriv. Evaluate on singletons
to obtain the positive-atom formula. This needs only bandwise finiteness, not global
sigma-finiteness. Expected proof: 150-250 lines. -/
def T15_L1 : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (r : X → ℝ) (δ : X → ℝ), Measurable r → Integrable δ μ →
    ∃ t : ℝ → ℝ, W1RadialDensity μ r δ t

/-- Isolate a node with a bounded indicator profile, cancel the positive node count and
identify finite measures from their values on measurable sets. Conversely, bounded
measurable functions are integrable under probability measures, and integral_finsetSum
proves the identity. Expected proof: 120-220 lines. -/
def T15_L2 : Prop := T15KernelStatement

/-- Compute the density's midpoint CDF and the uniform interval's midpoint CDF. Rewrite
withDensity_apply as an integral on [a,(a+b)/2], use integral_id and intervalIntegral
linearity, and use volume_Icc for the uniform measure. No geometry is needed here.
Expected proof: 100-180 lines. -/
def T15_L3 : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b →
    (volume.withDensity (fun r : ℝ => ENNReal.ofReal
      (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0))) (Set.Iic ((a+b)/2)) =
        ENNReal.ofReal ((((a+b)/2)^2-a^2)/(b^2-a^2)) ∧
    w1UniformRadial a b (Set.Iic ((a+b)/2)) = ENNReal.ofReal (1/2)

/-- Full T15 assembly: finite expectation/integration, finite partitions and the paired
counterexample are proved in Support; only the three displayed analytic leaves are new. -/
theorem T15_assembly (h1 : T15_L1.{u}) (h2 : T15_L2) (h3 : T15_L3) : T15WholeStatement.{u,v} := by
  refine ⟨?_,finite_shells,h2,nonidentification,?_⟩
  · intro N X _ _ P p d _hN _hp hWD hdist
    have hf := forced_band P p d hWD
    refine ⟨hf.1,hf.2,?_,?_,fun hp => forced_agrees p (circleAverage P d) hp⟩
    · simp only [w1ForcedAME,hf.2]
    · intro i
      let μ := P.zeta.restrict (region P i d)
      haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (hWD i).2.2.1.ne
      obtain ⟨t,ht⟩ := h1 μ (nodeDistance P i) (w1ForcedPointEffect P p i) (hdist i) (hf.1 i)
      refine ⟨t,ht,?_⟩
      have he := ht.2.1 Set.univ MeasurableSet.univ
      simp only [setIntegral_univ,Set.preimage_univ] at he
      rw [hf.2 i,he]
  · intro c a b X ha hab hX
    have hsub : {x | a ≤ dist x c ∧ dist x c ≤ b} ⊆ X := by
      intro x hx
      exact hX (Metric.mem_closedBall.mpr hx.2)
    have he : w1AreaRadial c a b X = volume.withDensity (fun r : ℝ =>
        ENNReal.ofReal (if a ≤ r ∧ r ≤ b then 2*r/(b^2-a^2) else 0)) := by
      unfold w1AreaRadial
      rw [Measure.restrict_restrict_of_subset hsub]
      exact AronowAudit.P004.Wave1.annulus_radial_measure_proof c a b ha hab
    have hm := h3 a b ha hab
    have hΔ : 0 < b^2-a^2 := by nlinarith [sq_pos_of_pos (sub_pos.mpr hab)]
    have hfrac : (((a+b)/2)^2-a^2)/(b^2-a^2) < (1/2 : ℝ) := by
      apply (div_lt_iff₀ hΔ).mpr
      nlinarith [sq_pos_of_pos (sub_pos.mpr hab)]
    have hnonneg : 0 ≤ (((a+b)/2)^2-a^2)/(b^2-a^2) := by
      apply div_nonneg _ hΔ.le
      nlinarith
    refine ⟨he,he ▸ hm.1,hm.2,hfrac,?_⟩
    intro hEq
    have hval := congrArg (fun M : Measure ℝ => M (Set.Iic ((a+b)/2))) hEq
    rw [he,hm.1,hm.2] at hval
    have hv := congrArg ENNReal.toReal hval
    rw [ENNReal.toReal_ofReal hnonneg,ENNReal.toReal_ofReal (by norm_num)] at hv
    linarith

/-- The joint law of the three-coin blocks factors into identical block laws. Reindex the
finite product design with Fin (3*K) ≃ Fin K × Fin 3 and distribute the finite sums.
The one-block moments are already proved in three_block_moments. This includes K=0.
Expected proof: 150-250 lines. -/
def T1_L1 : Prop :=
  ∀ K : ℕ, ∀ F : (Fin K → ℝ) → ℝ,
    expect (w1ThreeP (3*K)) (fun z => F (w1ThreeBlock z)) =
      ∑ b : Fin K → Assignment 3, (∏ j, designWeight (w1ThreeP 3) (b j)) *
        F (fun j => w1OneBlock (b j))

/-- Use the product block law, expand the square and fourth power, and discard terms with a
singleton block index because each block has mean zero. Equivalently induct on K, obtaining
K*M4+3*K*(K-1)*M2². Divide by (3K) and (3K)². Reindexing the sum also gives the normalized
A-P identity. Expected proof: 200-350 lines. -/
def T1_L2 : Prop := T1BlockLawStatement →
  ∀ K : ℕ, 0 < K →
    (∀ z, Real.sqrt (3*K : ℕ)*(w1ThreeLinear w1ThreeA (3*K) z-w1ThreeLinear w1ThreeB (3*K) z) = w1ThreeU K z) ∧
    expect (w1ThreeP (3*K)) (fun z => (w1ThreeU K z)^2) = 10369/750000 ∧
    expect (w1ThreeP (3*K)) (fun z => (w1ThreeU K z)^4) =
      (915255049/250000000000)/(9*(K : ℝ)) + 3*((K : ℝ)-1)*(10369/750000)^2/(K : ℝ)

/-- A finite weighted Paley-Zygmund bound at half the second moment. Split E[X²] over the
threshold event, bound its complement by a/2, and apply weighted Cauchy-Schwarz to the event.
All weights are a genuine product Bernoulli probability. Expected proof: 60-120 lines. -/
def T1_L3 : Prop :=
  ∀ {N : ℕ} (p : Fin N → ℝ) (X : Assignment N → ℝ) (a b : ℝ),
    (∀ i, 0 < p i ∧ p i < 1) → 0 < a → 0 < b →
    expect p (fun z => (X z)^2) = a → expect p (fun z => (X z)^4) ≤ b →
    a^2/(4*b) ≤ prob p (fun z => a/2 < (X z)^2)

/-- An order-N⁻¹ fitted remainder is negligible at root-N scale. The exact normalized
coefficient difference is U_K. Its positive uniform tail from W5 excludes convergence to
zero; transfer through the negligible remainder using a two-event union bound. No CLT is
needed for this refutation. Expected proof: 120-220 lines. -/
def T1_L4 : Prop :=
  T1MomentStatement → ∀ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
    T1ExpansionStatement θhat → T1RemainderStatement θhat

/-- Apply corrected_dependency_clt to the fixed A-coordinate summands on all sample sizes,
using own_finiteDependencyGraph; their nonzero bounded coefficients give a uniform variance
floor. Restrict this leading-sum CLT to N=3K, where the exact variance is (3/625)/N. Transfer
the order-N⁻¹ remainder and rescale by the exact printed variance. This avoids requiring an
unproved all-N limit for the sample-dependent score fits. Expected proof: 200-350 lines. -/
def T1_L5 : Prop :=
  ∀ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
    LogisticConditions threeTypeONat threeTypeTheta threeTypeParameterSet θhat →
    T1ExpansionStatement θhat → T1GaussianStatement θhat

/-- Random-radius Slutsky gives coverage from the Gaussian limit and N*Vhat -> V_P>0.
Use normal-CDF symmetry, quantile inversion and strict monotonicity to obtain the formula
and strict deficit for every alpha. Cancel sqrt(N) only eventually, where K>0.
Expected proof: 120-220 lines. -/
def T1_L6 : Prop :=
  ∀ θhat : ∀ N, Assignment N → Fin 2 → ℝ,
    T1GaussianStatement θhat → T1CoverageStatement θhat

/-- Combine the new product block law with the proved eight-draw calculation. -/
theorem three_block_law (h1 : T1_L1) : T1BlockLawStatement := ⟨h1,three_block_moments⟩

/-- The exact moment bound, its arithmetic upper bound and the general tail leaf suffice
for all of W5. -/
theorem three_moments (h1 : T1_L1) (h2 : T1_L2) (h3 : T1_L3) : T1MomentStatement := by
  intro K hK
  obtain ⟨hU,hsecond,hfourth⟩ := h2 (three_block_law h1) K hK
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hkpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hb : expect (w1ThreeP (3*K)) (fun z => (w1ThreeU K z)^4) ≤ 2205448981/2250000000000 := by
    rw [hfourth]
    rw [div_mul_eq_div_div, ← add_div]
    apply (div_le_iff₀ hkpos).mpr
    nlinarith
  refine ⟨hU,hsecond,hfourth,hb,?_⟩
  have hp (i : Fin (3*K)) : 0 < w1ThreeP (3*K) i ∧ w1ThreeP (3*K) i < 1 := by
    have h := three_spatial.2.2.2.2.2.2.1 (3*K) i
    constructor <;> linarith [h.1,h.2]
  have ht := h3 (w1ThreeP (3*K)) (w1ThreeU K) (10369/750000) (2205448981/2250000000000)
    hp (by norm_num) (by norm_num) hsecond hb
  norm_num at ht ⊢
  exact ht

/-- Whole T1, using the actual constrained MLE supplied by the existing existence proof. -/
theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2) (h3 : T1_L3)
    (h4 : T1_L4) (h5 : T1_L5) (h6 : T1_L6) : T1WholeStatement := by
  have hm := three_moments h1 h2 h3
  obtain ⟨θhat,hlog⟩ := AronowAudit.P004.Wave1.DecideP004T1_mle_exists
  have hlog' : LogisticConditions threeTypeONat threeTypeTheta threeTypeParameterSet θhat := hlog
  have he := three_expansion θhat hlog'
  have hg := h5 θhat hlog' he
  exact ⟨three_spatial,three_population,three_linear,three_block_law h1,hm,θhat,hlog',he,h4 hm θhat he,hg,h6 θhat hg⟩

/-- The new off-support disk field agrees with the old atomic field at every measured atom.
Prove disjointness of the unit disks using spacing ten; this proves the pointwise bound,
on-disk value and outside value. Integrate the equality on the counting support to obtain
all-band equality and WellDefined. Expected proof: 200-320 lines. -/
def T3_L1 : Prop :=
  (∀ N x z, |(w1ActiveDiskPopulation N).outcome x z| < 2) ∧
  (∀ N (i : Fin N) x z, dist x (planePoint (10*(i : ℝ)) 0) ≤ 1 →
    (w1ActiveDiskPopulation N).outcome x z = w1ActiveSign N i*bit (z i)) ∧
  (∀ N x z, (∀ i : Fin N, 1 < dist x (planePoint (10*(i : ℝ)) 0)) →
    (w1ActiveDiskPopulation N).outcome x z = 0) ∧
  (∀ N d, 0 ≤ d → WellDefined (w1ActiveDiskPopulation N) d) ∧
  (∀ N d, circleAverage (w1ActiveDiskPopulation N) d = circleAverage (activePopulation N) d)

/-- Export the balanced active-group identities: exactly r positive, r negative and 6r zero
signs. Apply the existing population-beta, fitted-beta, estimator and printed-variance
formulas, then independent Bernoulli first/second moments. The positive actual variance
follows from a positive-weight draw with S=1 and the symmetric draw with S=-1.
Expected proof: 250-380 lines. -/
def T3_L2 : Prop := T3FiniteStatement

/-- Sum each fiber of (number of positive H treatments, negative H treatments, L treatments).
Permute coordinates into three groups, count subsets of each size, and factor the independent
product weights. Each fiber has choose(r,u)*choose(r,v)*choose(6r,j) assignments. This is the
shared bridge for T3 and T4; no enumeration of 2^64 draws is required.
Expected proof: 200-350 lines. -/
def T3_L3 : Prop := T3CountStatement

/-- Identify the N=32 estimator and variance as functions of the three counts, use the fiber
bridge, symmetry for E[IPW]=0, and evaluate the small rational sums. Integrate out the L count
using its first two moments before normalization. Expected proof: 120-250 lines. -/
def T3_L4 : Prop := T3FiniteStatement → T3CountStatement →
  variance (w1ActiveP 32) (w1ActiveIPW 32) = 18239/1505280 ∧
  expect (w1ActiveP 32) (w1ActiveVPrinted 32) = 412940740700292467/161486810505216000000

/-- The same count formula at N=64. The high counts run only from 0 through 8; analytically
sum out the independent low count. The exact rational value certifies the decimal printed
in the claim. Expected proof: 120-250 lines. -/
def T3_L5 : Prop := T3FiniteStatement → T3CountStatement →
  variance (w1ActiveP 64) (w1ActiveIPW 64) = 1710440723/354248294400 ∧
  expect (w1ActiveP 64) (w1ActiveVPrinted 64) =
    17415062510218476553980121318471/12002159705791979639097262080000000

/-- Instantiate T2_ipw_expansion on the saturated active witness. Balanced signs make its
score correction zero. Restrict to N=8r and obtain the stronger order-N⁻¹ remainder.
Expected proof: 80-160 lines. -/
def T3_L6 : Prop := T3FiniteStatement →
  W1BigOp (fun r => 8*r) (fun r => w1ActiveP (8*r))
    (fun r z => w1ActiveIPW (8*r) z-2*w1ActiveS (8*r) z/(8*r : ℕ)) (fun r => ((8*r : ℕ) : ℝ)⁻¹)

/-- Use O10's LLNs and R=K-2*betaHat*S+K*betaHat². Continuous mapping yields Q->1/5,
R/N->1/8 and N*Vprinted->2/25. Combine the proved actual variance limit for the ratio;
the positive limit also makes the nonpositive-variance event negligible.
Expected proof: 180-300 lines. -/
def T3_L7 : Prop := T3FiniteStatement →
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r)) (fun r z => armCount z true/(8*r : ℕ)-1/5) ∧
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r)) (fun r z => w1ActiveR (8*r) z/(8*r : ℕ)-1/8) ∧
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r)) (fun r z => (8*r : ℕ)*w1ActiveVPrinted (8*r) z-2/25) ∧
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
    (fun r z => w1ActiveVPrinted (8*r) z/variance (w1ActiveP (8*r)) (w1ActiveIPW (8*r))-8/25) ∧
  Tendsto (fun r => prob (w1ActiveP (8*r)) (fun z => w1ActiveVPrinted (8*r) z ≤ 0)) atTop (nhds 0)

/-- Apply the random-radius coverage theorem at each positive normal critical value.
Normal quantile inversion and strict CDF monotonicity give the strict deficit because
sqrt(8/25)<1. Removing the negligible zero-variance event proves the guarded standardized
formula as well. Expected proof: 120-220 lines. -/
def T3_L8 : Prop := T3AsymptoticStatement → T3CoverageStatement

/-- The spatial glue uses existing MLE, overlap, line-spacing and locality theorems. -/
theorem active_spatial (h : T3_L1) : T3SpatialStatement := by
  obtain ⟨hbd,hon,hoff,hWD,hC⟩ := h
  have hsep (N : ℕ) : nodeSeparation (w1ActiveDiskPopulation N) = nodeSeparation (activePopulation N) := rfl
  have hbase : SpatialLocalConditions activePopulation := AronowAudit.P004.Wave1.T3_spatial
  have hP : SpatialLocalConditions w1ActiveDiskPopulation := by
    rcases hbase with ⟨_hb,hloc,hspace⟩
    refine ⟨⟨2,by norm_num,Eventually.of_forall hbd⟩,?_,hspace⟩
    simpa only [hC,hsep] using hloc
  refine ⟨AronowAudit.P004.Wave1.ObservationalCoverage.o3_proof,
    AronowAudit.P004.Wave1.T3_interior,hP,hbd,hon,hoff,hWD,hC,?_,?_,?_,?_,?_,?_⟩
  · intro N
    rw [hC]
    exact AronowAudit.P004.Wave1.LinePopulation.n3_proof _
  · intro N d hd
    have hh : LocalAt (circleAverage (activePopulation N) d) (nodeSeparation (activePopulation N)) (2*d+2*0) :=
      AronowAudit.P004.Wave1.LinePopulation.n7_proof (activeTable N) 0 d le_rfl hd
        (AronowAudit.P004.Wave1.ObservationalCoverage.o1_proof.2.1 N)
    rw [hC,hsep]
    intro i j hij
    exact hh i j (by linarith)
  · intro N i
    exact AronowAudit.P004.Wave1.LinePopulation.line_zero_ball (activeTable N) i
  · intro N i r hr
    exact AronowAudit.P004.Wave1.LinePopulation.n6_proof (activeTable N) i r hr
  · intro N i
    have he : w1ActiveP N = fun i => if activeGroup N i then 1/2 else 1/10 :=
      AronowAudit.P004.Wave1.ObservationalCoverage.o4_proof N
    rw [he]
    dsimp only
    split_ifs <;> norm_num
  · intro N i j
    unfold activeO
    split_ifs <;> fin_cases j <;> norm_num

/-- The fitted CLT is already proved; restriction to balanced samples removes its exact AME. -/
theorem active_gaussian (hf : T3FiniteStatement) :
    W1NormalLimit (fun r => 8*r) (fun r => w1ActiveP (8*r))
      (fun r z => Real.sqrt (8*r : ℕ)*w1ActiveIPW (8*r) z/(1/2)) := by
  have hc (N : ℕ) : circleAverage (activePopulation N) 0 = activeTable N :=
    AronowAudit.P004.Wave1.LinePopulation.n3_proof _
  have h : NormalLimit w1ActiveP (fun N z => Real.sqrt N *
      (w1ActiveIPW N z-ame (w1ActiveP N) (activeTable N))/(1/2)) := by
    have hh : NormalLimit w1ActiveP (fun N z => Real.sqrt N *
        (fittedIPW (circleAverage (activePopulation N) 0) (activeO N) (w1ActiveMLE N) z-
          ame (w1ActiveP N) (circleAverage (activePopulation N) 0))/(1/2)) :=
      AronowAudit.P004.Wave1.ObservationalCoverage.o11_proof
    simpa only [hc,w1ActiveIPW] using hh
  intro x
  apply ((h x).comp (multiples_tendsto 8 (by omega))).congr'
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hame := (hf r hr).2.2.2.2.1
  simp only [hame,sub_zero,Function.comp_apply]

/-- Full T3 assembly, including exact arithmetic comparisons and both coverage events. -/
theorem T3_assembly (h1 : T3_L1) (h2 : T3_L2) (h3 : T3_L3) (h4 : T3_L4)
    (h5 : T3_L5) (h6 : T3_L6) (h7 : T3_L7) (h8 : T3_L8) : T3WholeStatement := by
  have h32 := h4 h2 h3
  have h64 := h5 h2 h3
  have hn : T3NumericalStatement := by
    refine ⟨h32.1,h32.2,h64.1,h64.2,?_,?_,?_,?_,?_⟩ <;>
      norm_num [h32.1,h32.2,h64.1,h64.2]
  obtain ⟨hQ,hR,hV,hRatio,hZero⟩ := h7 h2
  have ha : T3AsymptoticStatement :=
    ⟨h6 h2,active_gaussian h2,active_variance_limit,hQ,hR,hV,hRatio,hZero⟩
  exact ⟨active_spatial h1,h2,hn,ha,h8 ha⟩

/-- O10 and the residual expansion give R/N->1/8 and pHatH->1/2. Apply continuous mapping
to the proved raw formula; (1/8)/(1/2)²=1/2. Expected proof: 100-180 lines. -/
def T4_L1 : Prop :=
  W1InProb (fun r => 8*r) (fun r => w1ActiveP (8*r))
    (fun r z => (8*r : ℕ)*w1ActiveVRaw (8*r) z-1/2)

/-- Apply the shared count-fiber formula at r=4 to the proved raw formula and the actual
clipped IPW formula. The L count integrates to one. Evaluate the 25 high-count terms,
using symmetry for the IPW mean. Expected proof: 100-200 lines. -/
def T4_L2 : Prop := T3CountStatement →
  expect (w1ActiveP 32) (w1ActiveVRaw 32) = 493725989/38038425600 ∧
  variance (w1ActiveP 32) (w1ActiveIPW 32) = 18239/1505280

/-- T4 shares only the count-fiber leaf with T3. All general bounds, the raw formula and the
actual variance limit are proved, and the last inequality is exact rational arithmetic. -/
theorem T4_assembly (hbridge : T3_L3) (h1 : T4_L1) (h2 : T4_L2) : T4WholeStatement := by
  obtain ⟨hE,hV⟩ := h2 hbridge
  refine ⟨raw_sah_general,active_raw_formula,h1,active_variance_limit,by norm_num,hE,hV,?_⟩
  rw [hE,hV]
  norm_num

/-- Finite sectors at the two well-separated centers form a binary measurable field.
Transfer the existing bin geometry and masses; use boundedness to prove integrability on
all finite-area regions. Export all of W1AreaGeometry, including the on-bin and outside
field formulas. Expected proof: 220-350 lines. -/
def T5_L1 : Prop :=
  ∀ q : Fin 6 → Bool → ℝ, (∀ j a, 0 ≤ q j a ∧ q j a ≤ 1/2) → W1AreaGeometry q

/-- Integrate the on-bin binary indicator. The existing arbitrary-share disk and annular
sector measure formulas give q times the bin area, for every assignment, including the
central disk. Divide by the positive bin mass. Expected proof: 100-180 lines. -/
def T5_L2 : Prop :=
  ∀ q : Fin 6 → Bool → ℝ, (∀ j a, 0 ≤ q j a ∧ q j a ≤ 1/2) → W1AreaGeometry q →
    ∀ (j : Fin 6) i z, circleAverage (w1AreaPopulation q) j i z = q j (z i)

/-- The central disk and ten half-width annuli are disjoint and cover exactly the same
radius-six disk. Translate distance-to-disk using A1; finite inequalities prove the
partition. Their positive finite areas and the same measurable binary field give all
WellDefined certificates. Expected proof: 180-280 lines. -/
def T5_L3 : Prop := W1AreaGeometry (w1AreaShares 0) →
  (∀ j : Fin 11, WellDefined (w1RefinedArea j) 0) ∧
  (∀ i : Fin 2, region (w1AreaCase 0) i 6 = ⋃ j : Fin 11, region (w1RefinedArea j) i 0) ∧
  (∀ i : Fin 2, Pairwise (fun j k : Fin 11 =>
    Disjoint (region (w1RefinedArea j) i 0) (region (w1RefinedArea k) i 0)))

/-- Case A has constant angular share at every radius. On each refined annulus its same
field is the corresponding sector indicator. Use the arbitrary-radius sector formula,
and the central disk formula at j=0, to divide its integral by the positive refined area.
This is a statement about the original field, not a newly specified table.
Expected proof: 150-250 lines. -/
def T5_L4 : Prop := W1AreaRealization (w1AreaShares 0) →
  ∀ (j : Fin 11) i z, circleAverage (w1RefinedArea j) 0 i z = w1AreaShares 0 0 (z i)

/-- Additivity of the integrals supplies the whole-region means; there is no new analytic
leaf for this already proved partition identity. -/
theorem area_realization (h1 : T5_L1) (h2 : T5_L2) (c : Fin 3) : W1AreaRealization (w1AreaShares c) := by
  have hb : ∀ j a, 0 ≤ w1AreaShares c j a ∧ w1AreaShares c j a ≤ 1/2 := by
    intro j a
    fin_cases c <;> fin_cases j <;> cases a <;> norm_num [w1AreaShares]
  have hg := h1 (w1AreaShares c) hb
  have hm := h2 (w1AreaShares c) hb hg
  refine ⟨hg,hm,?_⟩
  rcases hg with ⟨_hbin,_hmeas,_hon,_hoff,hWD,_hWDall,_hreg,hunion,hdis,hmass,_hwholemass⟩
  intro i z
  change (∫ x in region (w1AreaPopulation (w1AreaShares c)) i 6, (w1AreaPopulation (w1AreaShares c)).outcome x z ∂volume) /
      (volume (region (w1AreaPopulation (w1AreaShares c)) i 6)).toReal = _
  rw [hunion]
  have h := AronowAudit.P004.area_partition_identity volume
    (fun j : Fin 6 => region (w1AreaPopulation (w1AreaShares c)) i j) (fun x => (w1AreaPopulation (w1AreaShares c)).outcome x z)
    (by omega) (fun j => (hWD j i).1) (hdis i)
    (fun j => ⟨(hWD j i).2.1,(hWD j i).2.2.1⟩) (fun j => (hWD j i).2.2.2 z)
  change (∫ x in ⋃ j : Fin 6, region (w1AreaPopulation (w1AreaShares c)) i j, (w1AreaPopulation (w1AreaShares c)).outcome x z ∂volume) / _ = _ at h
  rw [h]
  change (∑ j : Fin 6,
    (volume (region (w1AreaPopulation (w1AreaShares c)) i j)).toReal /
      (∑ l : Fin 6, (volume (region (w1AreaPopulation (w1AreaShares c)) i l)).toReal) *
      circleAverage (w1AreaPopulation (w1AreaShares c)) j i z) = _
  simp_rw [hm]
  have hv (j : Fin 6) : (volume (region (w1AreaPopulation (w1AreaShares c)) i j)).toReal = Real.pi*(2*(j : ℝ)+1) := by
    have hh : volume (region (w1AreaPopulation (w1AreaShares c)) i j) =
        ENNReal.ofReal (Real.pi*(2*(j : ℝ)+1)) := hmass i j
    rw [hh,ENNReal.toReal_ofReal (by positivity)]
  have hs : (∑ j : Fin 6, (volume (region (w1AreaPopulation (w1AreaShares c)) i j)).toReal) = 36*Real.pi := by
    simp only [hv]
    norm_num [Fin.sum_univ_succ]
    ring
  simp_rw [hs,hv]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [Real.pi_ne_zero]

/-- Whole T5: all statistical arithmetic and the grid-change sums are proved here. -/
theorem T5_assembly (h1 : T5_L1) (h2 : T5_L2) (h3 : T5_L3) (h4 : T5_L4) : T5WholeStatement := by
  have hr := area_realization h1 h2
  have hcases := area_cases hr
  obtain ⟨hWD,hunion,hdis⟩ := h3 (hr 0).1
  have hm := h4 (hr 0)
  have ht (j : Fin 11) : circleAverage (w1RefinedArea j) 0 =
      fun i z => w1AreaShares 0 0 (z i) := by funext i z; exact hm j i z
  have he (j : Fin 11) : hajek (circleAverage (w1RefinedArea j) 0) areaWitnessAssignment = -17/3000 ∧
      ame (fun _ => 1/2) (circleAverage (w1RefinedArea j) 0) = -17/3000 := by
    rw [ht]
    convert two_node_effect (w1AreaShares 0 0) using 1 <;> norm_num [w1AreaShares]
  refine ⟨hcases,hWD,hunion,hdis,hm,he,?_,?_,?_⟩
  · simp_rw [(he _).1]
    norm_num
  · simp_rw [(he _).2]
    norm_num
  · exact (hcases.2.2.2.2.2.1 0).2.2.2.1

end
end SAP.P004a.WH.W1
