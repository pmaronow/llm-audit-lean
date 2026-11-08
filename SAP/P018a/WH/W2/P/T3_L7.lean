import SAP.P018a.WH.W2.Leaves
import AronowAudit.P018.Wave1.Gap.GLP0181B5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable section
namespace SAP.P018a.WH.W2.P.T3_L7

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory
open scoped BigOperators

local notation "signKernel" => AronowAudit.P018.signKernel
local notation "Dyad" => AronowAudit.P018.Dyad
local notation "Vec" => AronowAudit.P018.Vec
local notation "Mat" => AronowAudit.P018.Mat
local notation "designSigma" => AronowAudit.P018.designSigma
local notation "design" => AronowAudit.P018.design
local notation "epsilon" => AronowAudit.P018.epsilon
local notation "populationResidual" => AronowAudit.P018.populationResidual
local notation "populationBeta" => AronowAudit.P018.populationBeta
local notation "conditionalResidualMean" => AronowAudit.P018.conditionalResidualMean
local notation "conditionalResidualCov" => AronowAudit.P018.conditionalResidualCov
local notation "conditionalTerm" => AronowAudit.P018.conditionalTerm
local notation "unitSampleLaw" => AronowAudit.P018.unitSampleLaw
local notation "scoreSum" => AronowAudit.P018.scoreSum
local notation "score" => AronowAudit.P018.score
local notation "covMat" => AronowAudit.P018.covMat
local notation "varMat" => AronowAudit.P018.varMat
local notation "meanMat" => AronowAudit.P018.meanMat
local notation "printedSigma" => AronowAudit.P018.printedSigma
local notation "members" => AronowAudit.P018.members
local notation "overlap" => AronowAudit.P018.overlap
local notation "firstUnit" => AronowAudit.P018.firstUnit
local notation "secondUnit" => AronowAudit.P018.secondUnit
local notation "outer" => AronowAudit.P018.outer
local notation "dot" => AronowAudit.P018.dot
local notation "signValue" => AronowAudit.P018.signValue

local instance signSampleProbability (N : ℕ) : IsProbabilityMeasure
    (unitSampleLaw signKernel N) :=
  AronowAudit.P018.Wave1.printed_sign_probability N

lemma sign_designSigma_bot (N : ℕ) :
    @AronowAudit.P018.designSigma Bool inferInstance 1 N signKernel = ⊥ := by
  unfold AronowAudit.P018.designSigma
  have h : @AronowAudit.P018.design Bool inferInstance 1 N signKernel =
      fun _ _ => (![ (1 : ℝ) ] : Vec 1) := by
    funext ω d
    simp [AronowAudit.P018.design, AronowAudit.P018.signKernel]
  rw [h]
  exact MeasurableSpace.comap_const _

lemma sign_design_value {N : ℕ} (ω : Fin N → Bool) (d : Dyad N) :
    design signKernel ω d = (![ (1 : ℝ) ] : Vec 1) := rfl

lemma sign_epsilon_formula {N : ℕ} (ω : Fin N → Bool) (d : Dyad N) :
    epsilon signKernel ω d =
      signValue (ω (firstUnit d)) + signValue (ω (secondUnit d)) := by
  unfold AronowAudit.P018.epsilon AronowAudit.P018.populationResidual
  rw [AronowAudit.P018.Wave1.appendixB_populationBeta]
  simp [AronowAudit.P018.signKernel, AronowAudit.P018.dot]

lemma sign_epsilon_mean {N : ℕ} (d : Dyad N) :
    (∫ ω, epsilon signKernel ω d ∂ unitSampleLaw signKernel N) = 0 := by
  simp_rw [sign_epsilon_formula]
  rw [integral_add (AronowAudit.P018.Wave1.printed_finite_integrable _ _)
    (AronowAudit.P018.Wave1.printed_finite_integrable _ _)]
  have h1 := AronowAudit.P018.Wave1.appendixB_coord_mean (N := N) (firstUnit d)
  have h2 := AronowAudit.P018.Wave1.appendixB_coord_mean (N := N) (secondUnit d)
  rw [h1, h2]
  norm_num

lemma sign_conditionalResidualMean {N : ℕ} (d : Dyad N) :
    conditionalResidualMean signKernel d = fun _ => 0 := by
  unfold AronowAudit.P018.conditionalResidualMean
  rw [sign_designSigma_bot, MeasureTheory.condExp_bot]
  rw [sign_epsilon_mean]

lemma sign_epsilon_product {N : ℕ} (d f : Dyad N) :
    (∫ ω, epsilon signKernel ω d * epsilon signKernel ω f
      ∂ unitSampleLaw signKernel N) = ((members d ∩ members f).card : ℝ) := by
  classical
  let a : Fin N → ℝ := fun i => if i ∈ members d then 1 else 0
  let b : Fin N → ℝ := fun i => if i ∈ members f then 1 else 0
  have he (e : Dyad N) :
      (fun ω : Fin N → Bool => epsilon signKernel ω e) =
        fun ω => ∑ i, (if i ∈ members e then (1 : ℝ) else 0) * signValue (ω i) := by
    funext ω
    rw [sign_epsilon_formula]
    simp only [ite_mul, one_mul, zero_mul]
    rw [AronowAudit.P018.Wave1.appendixB_indicator_sum (members e)
      (fun i => signValue (ω i)),
      AronowAudit.P018.Wave1.printed_members_endpoints e,
      Finset.sum_pair (ne_of_lt (AronowAudit.P018.Wave1.printed_endpoints_lt e))]
  have hprod := AronowAudit.P018.Wave1.appendixB_linear_product a b
  have hleft :
      (fun ω : Fin N → Bool => epsilon signKernel ω d * epsilon signKernel ω f) =
        fun ω => (∑ i, a i * signValue (ω i)) * (∑ j, b j * signValue (ω j)) := by
    funext ω
    rw [← congrFun (he d) ω, ← congrFun (he f) ω]
  calc
    _ = ∫ ω, (∑ i, a i * signValue (ω i)) * (∑ j, b j * signValue (ω j))
        ∂ unitSampleLaw signKernel N := by rw [← hleft]
    _ = ∑ i, a i * b i := hprod
    _ = ((members d ∩ members f).card : ℝ) := by
      simp [a, b, Finset.inter_comm]

lemma sign_conditionalResidualCov {N : ℕ} (d f : Dyad N) :
    conditionalResidualCov signKernel d f =
      fun _ => ((members d ∩ members f).card : ℝ) := by
  unfold AronowAudit.P018.conditionalResidualCov
  rw [sign_designSigma_bot, sign_conditionalResidualMean d,
    sign_conditionalResidualMean f]
  simp only [Pi.zero_apply, sub_zero]
  rw [MeasureTheory.condExp_bot]
  funext ω
  exact sign_epsilon_product d f

lemma sign_covMat_card {N : ℕ} (d f : Dyad N) :
    covMat (unitSampleLaw signKernel N)
      (fun ω => score (design signKernel ω d) (epsilon signKernel ω d))
      (fun ω => score (design signKernel ω f) (epsilon signKernel ω f)) =
      !![((members d ∩ members f).card : ℝ)] := by
  letI : IsProbabilityMeasure (unitSampleLaw signKernel N) :=
    AronowAudit.P018.Wave1.printed_sign_probability N
  have hfinite : IsFiniteMeasure (unitSampleLaw signKernel N) := inferInstance
  letI := hfinite
  ext a b
  fin_cases a
  fin_cases b
  simp only [AronowAudit.P018.covMat]
  have hs (e : Dyad N) (ω : Fin N → Bool) :
      (score (design signKernel ω e) (epsilon signKernel ω e)) 0 =
        epsilon signKernel ω e := by
    rw [sign_design_value]
    change epsilon signKernel ω e * 1 = epsilon signKernel ω e
    ring
  have hsd : (fun ω => (score (design signKernel ω d) (epsilon signKernel ω d)) 0) =
      fun ω => epsilon signKernel ω d := funext (hs d)
  have hsf : (fun ω => (score (design signKernel ω f) (epsilon signKernel ω f)) 0) =
      fun ω => epsilon signKernel ω f := funext (hs f)
  change ProbabilityTheory.covariance
      (fun ω => (score (design signKernel ω d) (epsilon signKernel ω d)) 0)
      (fun ω => (score (design signKernel ω f) (epsilon signKernel ω f)) 0)
      (unitSampleLaw signKernel N) = ((members d ∩ members f).card : ℝ)
  rw [hsd, hsf]
  rw [ProbabilityTheory.covariance_eq_sub
    (AronowAudit.P018.Wave1.printed_finite_L2 _ _)
    (AronowAudit.P018.Wave1.printed_finite_L2 _ _)]
  rw [sign_epsilon_mean d, sign_epsilon_mean f]
  simp only [mul_zero, sub_zero]
  exact sign_epsilon_product d f

lemma sign_conditionalTerm_card {N : ℕ} (d f : Dyad N) :
    conditionalTerm signKernel d f = !![((members d ∩ members f).card : ℝ)] := by
  letI : IsProbabilityMeasure (unitSampleLaw signKernel N) :=
    AronowAudit.P018.Wave1.printed_sign_probability N
  ext a b
  fin_cases a
  fin_cases b
  unfold AronowAudit.P018.conditionalTerm AronowAudit.P018.meanMat
  rw [sign_conditionalResidualCov]
  simp_rw [sign_design_value]
  simp only [AronowAudit.P018.outer, Matrix.of_apply, Matrix.smul_apply,
    Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, mul_one]
  change (∫ ω, ((members d ∩ members f).card : ℝ)
      ∂ unitSampleLaw signKernel N) = ((members d ∩ members f).card : ℝ)
  simp [integral_const, probReal_univ]

lemma sign_conditionalTerm_cov {N : ℕ} (d f : Dyad N) :
    conditionalTerm signKernel d f =
      covMat (unitSampleLaw signKernel N)
        (fun ω => score (design signKernel ω d) (epsilon signKernel ω d))
        (fun ω => score (design signKernel ω f) (epsilon signKernel ω f)) := by
  rw [sign_conditionalTerm_card, sign_covMat_card]

lemma sign_disjoint_cov_zero {N : ℕ} (d f : Dyad N) (h : ¬ overlap d f) :
    covMat (unitSampleLaw signKernel N)
      (fun ω => score (design signKernel ω d) (epsilon signKernel ω d))
      (fun ω => score (design signKernel ω f) (epsilon signKernel ω f)) = 0 := by
  have hc : members d ∩ members f = ∅ := by
    by_contra hne
    exact h (Finset.nonempty_iff_ne_empty.mpr hne)
  rw [sign_covMat_card]
  ext a b
  fin_cases a
  fin_cases b
  simp [hc]

theorem sign_printedSigma_eq {N : ℕ} (hN : 4 ≤ N) :
    printedSigma signKernel N = !![(N : ℝ) * ((N : ℝ)-1)^2] := by
  let P := unitSampleLaw signKernel N
  let q : Dyad N → (Fin N → Bool) → Vec 1 := fun d ω =>
    score (design signKernel ω d) (epsilon signKernel ω d)
  have hq : ∀ d a, MemLp (fun ω => q d ω a) 2 P := by
    intro d a
    exact AronowAudit.P018.Wave1.printed_finite_L2 _ _
  have hvar := AronowAudit.P018.variance_sum_identity P q hq
  have hscore : (fun ω => ∑ d : Dyad N, q d ω) = scoreSum signKernel := rfl
  rw [hscore] at hvar
  have hsum : printedSigma signKernel N = ∑ d : Dyad N, ∑ f : Dyad N,
      covMat P (q d) (q f) := by
    unfold AronowAudit.P018.printedSigma
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro f hf
    by_cases hov : overlap d f
    · simp only [if_pos hov]
      change conditionalTerm signKernel d f = covMat P (q d) (q f)
      simpa [q, P] using sign_conditionalTerm_cov d f
    · simp only [if_neg hov]
      change (0 : Mat 1) = covMat P (q d) (q f)
      simpa [q, P] using (sign_disjoint_cov_zero d f hov).symm
  have hv : (varMat P (scoreSum signKernel) 0 0) = (N : ℝ) * ((N : ℝ)-1)^2 := by
    change ProbabilityTheory.covariance
      (fun ω => scoreSum signKernel ω 0) (fun ω => scoreSum signKernel ω 0) P = _
    simp_rw [AronowAudit.P018.Wave1.appendixB_scoreSum]
    rw [covariance_self (measurable_of_countable _).aemeasurable,
      variance_const_mul, AronowAudit.P018.Wave1.printed_S_variance]
    ring
  ext a b
  fin_cases a
  fin_cases b
  rw [hsum, ← hvar]
  exact hv

end SAP.P018a.WH.W2.P.T3_L7

theorem SAP.P018a.WH.W2.T3_L7_proof : SAP.P018a.WH.W2.T3_L7 := by
  intro N hN
  have h := SAP.P018a.WH.W2.P.T3_L7.sign_printedSigma_eq hN
  have hkernel : SAP.P018a.Bridge.toKernel SAP.P018a.signKernel =
      AronowAudit.P018.signKernel := rfl
  have hprinted : SAP.P018a.printedSigma SAP.P018a.signKernel N =
      AronowAudit.P018.printedSigma
        (SAP.P018a.Bridge.toKernel SAP.P018a.signKernel) N := rfl
  rw [hprinted, hkernel]
  exact h
