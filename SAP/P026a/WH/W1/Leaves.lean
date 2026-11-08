import SAP.P026a.Defs.WholeW1
import SAP.P026a.Bridge
import AronowAudit.P023.P023_Audit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.WH.W1
open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-- Full-rank normal equations characterize the unique global real least-squares
minimizer. Expand the loss difference as the sum of squared fitted differences. -/
theorem minimizes_iff {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : ι → κ → ℝ) (y : ι → ℝ) (c : κ → ℝ)
    (hr : w1FullRank A) (hc : w1Normal A y c) (b : κ → ℝ) :
    w1Minimizes A y b ↔ b = c := by
  have hc' : AronowAudit.P023.IsOLS A y c := hc
  have hgap (b : κ → ℝ) : w1Loss A y b = w1Loss A y c +
      ∑ i, (w1Predict A b i - w1Predict A c i)^2 := by
    have hz : AronowAudit.P023.dot (AronowAudit.P023.predict A (fun j => b j-c j))
        (fun i => y i-AronowAudit.P023.predict A c i) = 0 := by
      rw [AronowAudit.P023.dot_predict_left]
      apply sum_eq_zero
      intro j _
      rw [hc' j, mul_zero]
    have hp : ∀ i, AronowAudit.P023.predict A (fun j => b j-c j) i =
        w1Predict A b i - w1Predict A c i := by
      intro i
      simp [AronowAudit.P023.predict, w1Predict, mul_sub, sum_sub_distrib]
    have he (i : ι) : (y i - w1Predict A b i)^2 =
        (y i-w1Predict A c i)^2 + (w1Predict A b i-w1Predict A c i)^2 -
        2*((w1Predict A b i-w1Predict A c i)*(y i-w1Predict A c i)) := by ring
    unfold AronowAudit.P023.dot at hz
    simp_rw [hp] at hz
    unfold w1Loss
    simp_rw [he, sum_sub_distrib, sum_add_distrib]
    rw [← mul_sum]
    change (∑ i, (w1Predict A b i - w1Predict A c i) * (y i - w1Predict A c i)) = 0 at hz
    rw [hz]
    ring
  constructor
  · intro hb
    have hle := hb c
    have hnonneg : 0 ≤ ∑ i, (w1Predict A b i-w1Predict A c i)^2 :=
      sum_nonneg (fun _ _ => sq_nonneg _)
    have hz : (∑ i, (w1Predict A b i-w1Predict A c i)^2) = 0 := by
      have h := hgap b
      change w1Loss A y b ≤ w1Loss A y c at hle
      linarith
    have hp (i : ι) : w1Predict A b i-w1Predict A c i = 0 := by
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (w1Predict A b i-w1Predict A c i))).mp hz i (mem_univ i)
      exact (sq_eq_zero_iff).mp hi
    have hbc := hr (fun j => b j-c j) (fun i => by
      simpa only [w1Predict, mul_sub, sum_sub_distrib] using hp i)
    funext j
    exact sub_eq_zero.mp (congrFun hbc j)
  · intro hb
    subst b
    exact AronowAudit.P023.normal_equations_minimize A y c hc'

/-- Regroup the rational unit-level HT total by the fixed Table 1 cluster map.
No change of coefficient field and no extra assumption is needed. -/
theorem table_unit_total (a : Bool) (y : Fin 16 → ℚ) (w : Fin 6 × Fin 15) :
    htSum paperTableUnitDesign a y w =
      htSum paperTableDesign a (fiberTotal paperTableCluster y) w := by
  symm
  calc
    htSum paperTableDesign a (fiberTotal paperTableCluster y) w =
        ∑ k, ∑ i, if paperTableCluster i = k then
          armIndicator paperTableDesign a w k * y i / inclusion paperTableDesign a k else 0 := by
      unfold htSum fiberTotal
      apply sum_congr rfl
      intro k _
      simp only [mul_sum, sum_div, sum_filter]
      apply sum_congr rfl
      intro i _
      split_ifs <;> simp
    _ = ∑ i, armIndicator paperTableDesign a w (paperTableCluster i) * y i /
        inclusion paperTableDesign a (paperTableCluster i) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      simp
    _ = htSum paperTableUnitDesign a y w := rfl

/-- The paper's unit-level generalized estimator equals the residual cluster HT
contrast whose exact moments the project has already certified. -/
theorem linear_g_eq : w1LinearG =
    htContrast paperTableDesign 16 paperTableLinearResidual paperTableLinearResidual := by
  funext w
  have h := AronowAudit.P026.generalized_residual
    (Bridge.toAuditDesign paperTableUnitDesign) 16 paperTableY paperTableY
    (fun _ => paperTableLinearPrediction) w
  change w1LinearG w = htContrast paperTableUnitDesign 16
    (fun i => paperTableY i-paperTableLinearPrediction i)
    (fun i => paperTableY i-paperTableLinearPrediction i) w at h
  rw [h]
  unfold htContrast
  rw [table_unit_total, table_unit_total]
  rfl

/-- Finite mean squared error is variance plus squared bias. -/
theorem mse_eq {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : AssignmentDesign Ω I ℚ) (hD : isProbability D) (f : Ω → ℚ) (θ : ℚ) :
    mean D (fun w => (f w-θ)^2) = designVariance D f + (mean D f-θ)^2 := by
  let C := Bridge.toAuditDesign D
  have he : (fun w => (f w-θ)^2) = (fun w => f w*f w - f w*(2*θ) + θ^2) := by
    funext w
    ring
  change AronowAudit.P026.expectation C _ = AronowAudit.P026.variance C f +
    (AronowAudit.P026.expectation C f-θ)^2
  rw [he, AronowAudit.P026.expectation_add, AronowAudit.P026.expectation_sub,
    AronowAudit.P026.expectation_mul_const, AronowAudit.P026.expectation_const C hD]
  unfold AronowAudit.P026.variance AronowAudit.P026.covariance
  ring

/-- An unbiased estimator's RMSE equals its standard deviation. -/
theorem rmse_eq_sd {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]
    (D : AssignmentDesign Ω I ℚ) (hD : isProbability D) (f : Ω → ℚ) (θ : ℚ)
    (hm : mean D f = θ) :
    w1RMSE D f θ = Real.sqrt ((designVariance D f : ℚ) : ℝ) := by
  unfold w1RMSE
  rw [mse_eq D hD, hm, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]

/-- A positive rational interval for a square implies the corresponding strict
real square-root interval. This supplies explicit, checkable decimal error bounds. -/
theorem sqrt_approx (v c : ℝ) (hc : 0 < c-1/20000000)
    (hl : (c-1/20000000)^2 < v) (hu : v < (c+1/20000000)^2) :
    w1Approx7 (Real.sqrt v) c := by
  have hv : 0 ≤ v := by nlinarith [sq_nonneg (c-1/20000000)]
  have hs := Real.sq_sqrt hv
  have hn := Real.sqrt_nonneg v
  unfold w1Approx7
  rw [abs_lt]
  constructor <;> nlinarith


/-- T1, six-cluster support certificate: exact marginal vectors, attained
same-arm minima, and the exact disagreement minimum and its locations.
Enumerate the fourteen allocations, first caching the marginal and joint tables;
then use finite cases and exact rational normalization. At most about 100 lines.
Donors: AronowAudit.P026.asymmetricSix_counterexample, Fin.sum_univ_succ. -/
def T1_L1 : Prop := w1SixSupportFacts

/-- T1, six-cluster value certificate: the 00/01/11 groups have sizes 4/6/4,
and HT and equation [35] have the displayed values in each group; HT has mean zero.
Cache the six marginal and 36 joint values before reducing the fourteen variance
formulas. Use finite cases and rational arithmetic; no probability limit argument
is involved. At most about 150 lines.
Donors: AronowAudit.P026.asymmetricSix_counterexample,
AronowAudit.P026.marginal, AronowAudit.P026.joint. -/
def T1_L2 : Prop := w1SixValueFacts

/-- T4: independence of two six-unit treatment coordinates holds exactly when
they belong to different complementary pairs. For the positive direction expand
arbitrary Boolean test functions on the four equiprobable allocations and use ring
normalization. For the negative direction test with indicators of Boolean cells
(or the treatment indicator and its complement). All 36 cases are finite; about
80 lines with shared calculations.
Donors: AronowAudit.P026.xorSix_counterexample, Fin.sum_univ_succ. -/
def T4_L1 : Prop :=
  ∀ i j : Fin 6,
    finiteIndependent xorSixLaw (fun w => xorSixLaw.treatment w i)
      (fun w => xorSixLaw.treatment w j) ↔ i.val / 2 ≠ j.val / 2

/-- T6: real block regression certificates. In each block the intercept/X design
has full column rank and the stated coefficient vector satisfies both normal
equations. Cast table_linear_fits' rational normal equations, using the sum over
block subtypes. For rank, compare two rows with distinct X (units 1 and 2 in
block 1; units 7 and 8 in block 2); alternatively use Gram determinants 93 and
176. Do not restrict competitors to rational coefficients. About 120 lines.
Donors: AronowAudit.P026.table_linear_fits, Finset.sum_attach. -/
def T6_L1 : Prop :=
  ∀ b : Bool, w1FullRank (w1BlockDesign b) ∧
    w1Normal (w1BlockDesign b) (w1BlockY b) (w1BlockCoefficients b)

/-- T6: the real FE design (1,T,block2,X) has full column rank on every one of
the ninety allocations. Within cluster 1, units 1 and 2 force the X coefficient
of a zero fitted vector to vanish. Each block has both treated and control
clusters, forcing the T coefficient and then both block intercepts to vanish.
An alternative is a rational Gram determinant certificate cast to the reals.
About 150 lines; no lower bound on a new population parameter is assumed.
Donors: AronowAudit.P026.table_support, AronowAudit.P026.fe_normal_equations,
AronowAudit.P026.table_treatment_mean_certificate. -/
def T6_L2 : Prop :=
  ∀ w : Fin 6 × Fin 15, w1FullRank (w1FeDesign w)

/-- T6: the explicit four-vector reconstructs the rational fitted values and
satisfies all four real normal equations. Expand the two block intercepts in
w1FeCoefficients; show prediction equals the real cast of paperFeFitted, and
cast fe_normal_equations. For the block dummy convert the filtered sum into a
sum with a 0/1 multiplier. No matrix inversion is needed. About 150 lines.
Donors: AronowAudit.P026.fe_normal_equations, AronowAudit.P026.fe_x_certificate,
AronowAudit.P026.fe_estimate_certificate. -/
def T6_L3 : Prop :=
  ∀ w : Fin 6 × Fin 15,
    w1Normal (w1FeDesign w) (fun i => (paperTableY i : ℝ)) (w1FeCoefficients w)

/-- T6: sharpened rational FE moments. Replace paperFeEstimate by the already
certified 6-by-15 rational coefficient table, expand the two finite means and
the second moment, and normalize exact rational inequalities. Cache the mean
and second moment rather than re-evaluating the original regressions. The
variance interval is deliberately tight enough to imply the seven-decimal
square-root approximation .2788094. About 60 lines.
Donors: AronowAudit.P026.fe_estimate_certificate,
AronowAudit.P026.feCoefficientCertificate, AronowAudit.P026.fe_table_moments. -/
def T6_L4 : Prop :=
  (-13987427/1000000000 : ℚ) < mean paperTableDesign paperFeEstimate ∧
  mean paperTableDesign paperFeEstimate < (-13987425/1000000000 : ℚ) ∧
  (77734705/1000000000 : ℚ) < designVariance paperTableDesign paperFeEstimate ∧
  designVariance paperTableDesign paperFeEstimate < (77734706/1000000000 : ℚ)

/-- The Appendix E refutation needs only short finite calculations in addition
to the existing project certificate, so this assembly has no open leaves. -/
theorem T9_assembly : T9WholeStatement := by
  have hb := Bridge.target9
  obtain ⟨hprob,hpos,hs,hj,hvalues,he,hcov,hpop,hprinted,hvar,hne⟩ := hb.1
  have hm : ∀ i : Fin 4, inclusion twoOfFourLaw true i = 1/2 ∧
      inclusion twoOfFourLaw false i = 1/2 := by decide +kernel
  have hc : ∀ w : Fin 6,
      covarianceWithZeroOmission twoOfFourLaw appendixNullOutcomes appendixNullOutcomes w =
        (![-37,-25,-22,-22,-25,-37] : Fin 6 → ℚ) w := by decide +kernel
  have hv : armPopulationBound twoOfFourLaw true appendixNullOutcomes = 28 := by decide +kernel
  refine ⟨hb, hm, hc, hv, ?_, ?_⟩
  · rw [he, hb.2]
    norm_num
  · rw [he, hv]
    norm_num

/-- Complete the two sharp-null counterexamples, using leaves only for the
larger six-cluster finite tables. Literal-domain failure and all bias arithmetic
are discharged here. -/
theorem T1_assembly (h1 : T1_L1) (h2 : T1_L2) : T1WholeStatement := by
  have hb := Bridge.target1
  obtain ⟨ap,am,asupp,az,ar,an,ah,av,ae,avar,aev,alt,ac,aec,aclt⟩ := hb.1
  obtain ⟨bp,bm,bthree,bsupp,bz,bvar,bev,blt,bc,bec⟩ := hb.2
  have bzero : jointInclusion asymmetricSixLaw true false 0 1 = 0 :=
    (bz 0 1 (by decide)).mpr ⟨rfl,rfl⟩
  refine ⟨hb, ?_, ?_, ?_, ?_, ?_, h1, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro h
    exact h.2 0 1 (by decide) az
  · intro w
    simp [w1PartialRatio, az]
  · intro h
    exact h.2 0 1 (by decide) bzero
  · have hn : ∀ w : Fin 14, armIndicator asymmetricSixLaw true w 0 *
        armIndicator asymmetricSixLaw false w 1 = 0 := by decide +kernel
    intro w
    exact ⟨hn w, by simp [w1PartialRatio, bzero]⟩
  · simp [averageEffect]
  · simp [averageEffect]
  · rw [aev, avar]
    norm_num
  · rw [bev, bvar]
    norm_num
  · rw [aec, ac]
    norm_num
  · rw [bec, bc]
    norm_num

/-- Complete the XOR refutation. The exact independence classification is the
only leaf; the remaining omitted certificates are short finite evaluations or
consequences of the existing witness. -/
theorem T4_assembly (h1 : T4_L1) : T4WholeStatement := by
  classical
  have hb := Bridge.target4
  obtain ⟨ap,am,amarg,aj,atreated,af,ac,ae,aa,ab⟩ := hb.1
  obtain ⟨bp,bm,bj,bf,bc,be,bpc,bpe,ba⟩ := hb.2
  refine ⟨hb, h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    ext j
    simp only [mem_filter, mem_univ, true_and, h1 i j]
    fin_cases i <;> fin_cases j <;> decide
  · decide +kernel
  · intro i
    have hevents : ∀ i : Fin 6,
        mean xorSixLaw (fun w => if xorSixLaw.treatment w i = true ∧ xorSixFit w i = 1 then 1 else 0) = 1/2 ∧
        mean xorSixLaw (fun w => if xorSixLaw.treatment w i = true then 1 else 0) *
          mean xorSixLaw (fun w => if xorSixFit w i = 1 then 1 else 0) = 1/4 := by decide +kernel
    refine ⟨(hevents i).1, (hevents i).2, ?_⟩
    intro hi
    have he := hi (fun t => if t = true then 1 else 0) id
    have hc : designCovariance xorSixLaw (fun w => armIndicator xorSixLaw true w i)
        (fun w => xorSixFit w i) = 0 := sub_eq_zero.mpr he
    rw [ac i] at hc
    norm_num at hc
  · rw [ab]
    simp only [ac, (amarg _).1, (amarg _).2]
    norm_num [Fin.sum_univ_succ]
  · decide +kernel
  · decide +kernel
  · rw [be, ba]
    norm_num
  · rw [bpe, ba]
    norm_num

/-- The mixed-premise unbiasedness extension, vector factorization and scalar
specialization are direct applications of existing composition and zero-bias
lemmas. No open leaf is necessary. -/
theorem T5_assembly : T5WholeStatement := by
  refine ⟨Bridge.target5, ?_, ?_, ?_, ?_⟩
  · intro I _ _ _ E x z J G h
    let D := Bridge.toAuditUnit E
    apply AronowAudit.P026.generalized_unbiased D.design D.probability D.marginals
      (Fintype.card I) Fintype.card_pos x z
      (fun w i => G i (fittingResponses E.assignmentDesign (J i) x z w))
    intro i
    rcases h i with hi | hi
    · exact (AronowAudit.P026.vector_fitting_independence D.design i (J i) x z (G i) id hi).2.2
    · exact (AronowAudit.P026.outcome_vector_fitting_independence D.design i (J i) x z (G i) id hi).2.2
  · intro I Θ _ _ _ E i J x z G P
    refine ⟨fun _ => rfl, ?_⟩
    intro hi
    have h := AronowAudit.P026.vector_fitting_independence
      (Bridge.toAuditDesign E.assignmentDesign) i J x z G P hi
    exact ⟨h.2.1, h.2.2⟩
  · intro I Θ _ _ _ E i j x z G P hi
    let D := Bridge.toAuditDesign E.assignmentDesign
    have hg := AronowAudit.P026.independent_comp D (fun w => w i) (fun w => w j) hi
      (fun t => G (if t then x j else z j))
    have hp := AronowAudit.P026.independent_comp D _ _ hg P
    refine ⟨hg, hp, ?_⟩
    exact sub_eq_zero.mpr (hp (fun t => if t = true then 1 else 0) id)
  · let D : AssignmentDesign (Fin 4) (Fin 3) ℝ :=
      ⟨AronowAudit.P026.Refutations.realXorThree.weight,
        AronowAudit.P026.Refutations.realXorThree.treatment⟩
    refine ⟨D, AronowAudit.P026.Refutations.xorFittingSet,
      AronowAudit.P026.Refutations.xorFit, ?_⟩
    exact AronowAudit.P026.Refutations.printed_pairwise_fitting_refuted

/-- Assemble real least-squares identification, the unit/cluster identity,
existing exact moments, and explicit real decimal and rounding consequences. -/
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) (h3 : T6_L3) (h4 : T6_L4) :
    T6WholeStatement := by
  have hb := Bridge.target6
  have hs := AronowAudit.P026.table_support
  have hg := linear_g_eq
  have hm : mean paperTableDesign w1LinearG = 0 ∧
      designVariance paperTableDesign w1LinearG = 38307/634880 ∧
      mean paperTableDesign w1LinearV = 38307/634880 ∧
      designVariance paperTableDesign w1LinearV = 2400328658503/15687787688755200 := by
    rw [hg]
    exact hb.2.2.1
  rcases h4 with ⟨hml,hmu,hvl,hvu⟩
  have hml' : (-13987427/1000000000 : ℝ) < (mean paperTableDesign paperFeEstimate : ℚ) := by exact_mod_cast hml
  have hmu' : ((mean paperTableDesign paperFeEstimate : ℚ) : ℝ) < -13987425/1000000000 := by exact_mod_cast hmu
  have hvl' : (77734705/1000000000 : ℝ) < (designVariance paperTableDesign paperFeEstimate : ℚ) := by
    convert (Rat.cast_lt (K := ℝ)).mpr hvl using 1
    norm_num
  have hvu' : ((designVariance paperTableDesign paperFeEstimate : ℚ) : ℝ) < 77734706/1000000000 := by
    convert (Rat.cast_lt (K := ℝ)).mpr hvu using 1
    norm_num
  refine ⟨hb, hs.1, hs.2.1, hs.2.2.1, ?_, ?_, ?_, ?_, hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h := hs.2.2.2.1 i j hij
    exact ⟨lt_of_lt_of_le (by norm_num) h.2.1, lt_of_lt_of_le (by norm_num) h.2.2.1⟩
  · simp [averageEffect]
  · intro b β
    exact minimizes_iff _ _ _ (h1 b).1 (h1 b).2 β
  · exact congrFun hg
  · rw [hm.1]
    simp [averageEffect]
  · rw [hm.2.2.1, hm.2.1]
    norm_num
  · exact rmse_eq_sd paperTableDesign hs.1 w1LinearG 0 hm.1
  · exact rmse_eq_sd paperTableDesign hs.1 w1LinearV
      (designVariance paperTableDesign w1LinearG) (hm.2.2.1.trans hm.2.1.symm)
  · intro w β
    exact minimizes_iff _ _ _ (h2 w) (h3 w) β
  · intro w
    rfl
  · rw [hm.2.1]
    norm_num [w1Approx7]
  · rw [hm.2.1]
    apply sqrt_approx <;> norm_num
  · rw [hm.2.2.2]
    apply sqrt_approx <;> norm_num
  · unfold w1Approx7
    rw [abs_lt]
    constructor <;> linarith
  · unfold w1Approx7
    rw [abs_lt]
    constructor <;> linarith
  · apply sqrt_approx
    · norm_num
    · linarith
    · linarith
  · rintro ⟨hl,hu⟩
    linarith [hb.2.2.2.2.1]
  · rintro ⟨hl,hu⟩
    linarith [hb.2.2.2.2.2.2.1]
  · rintro ⟨hl,hu⟩
    linarith [hb.2.2.2.2.2.2.1]

end
end SAP.P026a.WH.W1
