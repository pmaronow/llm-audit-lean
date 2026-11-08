import AronowAudit.P001.P001_Foundations

/-!
# Conditional assessment for cond-P001b

Statement definitions only. No proof of a held result is used here.
The accepted input is a conditional-independence characterization for arbitrary
sub-sigma-fields. A general extremum-estimator candidate is retained separately;
its application to record 0 is rejected for a missing smoothness premise.
See runs/cond-P001b/REPORT.md for scope, rejected candidates, and source checks.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology
set_option linter.unusedVariables false
set_option pp.universes true

namespace AronowAudit.Literature

/-- Coordinate gradient of an arbitrary real criterion on a finite-dimensional
real parameter space. The sup norm on the coordinates is immaterial in finite dimension. -/
def criterionGradient {d : ℕ} (q : (Fin d → ℝ) → ℝ)
    (t : Fin d → ℝ) : Fin d → ℝ :=
  fun j => fderiv ℝ q t (Pi.single j 1)

/-- Coordinate Hessian of an arbitrary real criterion. -/
def criterionHessian {d : ℕ} (q : (Fin d → ℝ) → ℝ)
    (t : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => fderiv ℝ (fun u => criterionGradient q u j) t (Pi.single k 1)

/-- Newey, Whitney K., and Daniel McFadden (1994), "Large Sample Estimation
and Hypothesis Testing", Handbook of Econometrics, vol. IV, ch. 36,
Theorem 3.1, p. 2143; eq. (1.1), p. 2115; complete proof, section 3.5, p. 2152.
Source: https://users.ssc.wisc.edu/~xshi/Newey_Mcfadden_handbook.pdf

General finite-dimensional random-criterion statement. All probability spaces,
parameter dimensions, criteria, estimators, parameter sets, neighborhoods,
Hessian limits and Gaussian covariance matrices are quantified internally.
Random vectors are represented by a.e. measurable functions. `CP` uses outer
measure for arbitrary events; uniform convergence is expressed by the outer
probability of an epsilon violation somewhere in the neighborhood, avoiding
any finiteness convention for a real supremum. This is equivalent to the
source's uniform convergence in outer probability (footnote 9, pp. 2121-2122).
The source's unspecified finite-dimensional matrix norm is represented by the
coordinate sup norm. `WeakLimit` is the bounded continuous test-function
characterization, with measurability of the score made explicit.
`V.PosSemidef` expresses that V is a Gaussian covariance, including singular V.
The a.e. conditions identify random objects up to null sets; no data model,
iid assumption, statistical score, identification, or information bound occurs.
-/
def NeweyMcFadden1994Theorem31.{u} : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
  ∀ (d : ℕ) (Θ : Set (Fin d → ℝ)) (θ : Fin d → ℝ)
    (Q : ℕ → Ω → (Fin d → ℝ) → ℝ) (that : ℕ → Ω → Fin d → ℝ)
    (N : Set (Fin d → ℝ))
    (H : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ),
  (∀ n, AEMeasurable (that n) μ) →
  (∀ n, ∀ᵐ ω ∂μ, that n ω ∈ Θ ∧
    ∀ t ∈ Θ, Q n ω t ≤ Q n ω (that n ω)) →
  AronowAudit.P001.CP μ that θ →
  θ ∈ interior Θ →
  IsOpen N → θ ∈ N → N ⊆ Θ →
  (∀ n, ∀ᵐ ω ∂μ, ContDiffOn ℝ 2 (Q n ω) N) →
  (∀ n, AEMeasurable (fun ω => criterionGradient (Q n ω) θ) μ) →
  V.PosSemidef →
  AronowAudit.P001.WeakLimit μ
    (fun n ω => Real.sqrt n • criterionGradient (Q n ω) θ)
    (AronowAudit.P001.normalVectorLaw V) →
  ContinuousAt H θ →
  (∀ ε : ℝ, 0 < ε → Tendsto
    (fun n => (μ {ω | ∃ t ∈ N,
      ∃ j k, ε ≤ |criterionHessian (Q n ω) t j k - H t j k|}).toReal)
    atTop (nhds 0)) →
  IsUnit (H θ).det →
  AronowAudit.P001.WeakLimit μ
    (fun n ω => Real.sqrt n • (that n ω - θ))
    (AronowAudit.P001.normalVectorLaw ((H θ)⁻¹ * V * (H θ)⁻¹))

#print NeweyMcFadden1994Theorem31
#check @NeweyMcFadden1994Theorem31
#print axioms NeweyMcFadden1994Theorem31


/-- Conditional independence of three sub-sigma-fields, using exactly the
event factorization in Kallenberg (2002), p. 109. No conditional kernels or
standard-Borel assumption on the underlying probability space are used. -/
def eventConditionalIndependence {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (F G H : MeasurableSpace Ω) : Prop :=
  letI : MeasurableSpace Ω := mΩ
  ∀ A B : Set Ω, MeasurableSet[F] A → MeasurableSet[H] B →
    (μ⟦A ∩ B | G⟧) =ᵐ[μ] fun ω => (μ⟦A | G⟧) ω * (μ⟦B | G⟧) ω

/-- Kallenberg, Olav (2002), Foundations of Modern Probability, 2nd edition,
Springer, Proposition 6.6 (conditional independence, Doob), p. 110, equation (8);
conditional-independence definition on p. 109.
Source transcription and page scans: https://djvu.online/file/t4FlvxuKFFZGW
Publisher: https://doi.org/10.1007/978-1-4757-4015-8

This states the complete equivalence, for arbitrary sub-sigma-fields on any
probability space. It includes every event of H, with a separate almost-sure
equality for each event; it does not strengthen this to a simultaneous version.
All sigma-fields lie below the ambient measurable space. The join F ⊔ G is
the sigma-field generated by F and G. Conditional probabilities are Bochner
conditional expectations of bounded event indicators, hence always integrable.
There is no countable-generation or standard-Borel restriction.
-/
def Kallenberg2002Proposition66.{u} : Prop :=
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω),
  ∀ (μ : @Measure Ω mΩ) [@IsProbabilityMeasure Ω mΩ μ],
  ∀ (F G H : MeasurableSpace Ω),
  letI : MeasurableSpace Ω := mΩ
  F ≤ mΩ → G ≤ mΩ → H ≤ mΩ →
  (eventConditionalIndependence μ F G H ↔
    ∀ B : Set Ω, MeasurableSet[H] B → (μ⟦B | F ⊔ G⟧) =ᵐ[μ] (μ⟦B | G⟧))

set_option pp.explicit true in
#print eventConditionalIndependence
set_option pp.explicit true in
#print Kallenberg2002Proposition66
#check @Kallenberg2002Proposition66
#print axioms Kallenberg2002Proposition66

end AronowAudit.Literature

namespace AronowAudit.P001

/- Record 0 has no accepted conditional proposal: its held observation-0
C2 assumption does not supply the simultaneous observation-law event needed
to transfer smoothness to all observations on an arbitrary probability space.
The general Newey-McFadden definition above is retained as an independently
source-checked candidate, not an accepted application to that record. -/

/-- The complete repair in map-P001b record 16, approved by both ref1-P001b
and ref2-P001b (verdict accept, statement_ok true). Only the general published
sigma-field characterization is added. Binary support and rank already belong
to that approved repair, rather than being added to discharge the literature input. -/
def placebo_linear_cef_correction_supporting_conditional_statement.{u} : Prop :=
  AronowAudit.Literature.Kallenberg2002Proposition66.{u} →
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
   {K L : ℕ} (X : Ω → Fin K → ℝ) (W : Ω → Fin L → ℝ) (D : Ω → ℝ)
   (hX : Measurable X) (hW : Measurable W) (hD : Measurable D)
   (hbinary : ∀ᵐ ω ∂μ, D ω=0 ∨ D ω=1)
   (hSupportD : 0 < prob μ {ω | D ω=1} ∧ prob μ {ω | D ω=1} < 1)
   (hX2 : ∀ k,MemLp (fun ω => X ω k) 2 μ) (hW2 : ∀ k,MemLp (fun ω => W ω k) 2 μ)
   (hCI : CI μ X hX W D) (γ : Fin (K+1) → ℝ) (hcef : IsCEF μ X D (linearPredictor γ))
   (hRank : IsUnit (Matrix.det ((fun j k : Fin (K+L+1) => mean μ (fun ω =>
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) j)*
     (Fin.cases 1 (Fin.addCases (X ω) (W ω)) k))) : Matrix (Fin (K+L+1)) (Fin (K+L+1)) ℝ))),
   IsCEF μ (fun ω => (X ω,W ω)) D (fun xw => linearPredictor γ xw.1) ∧
   (∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2) ≤
       mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)) ∧
   ∀ a : ℝ,∀ b : Fin K → ℝ,∀ c : Fin L → ℝ,
     (mean μ (fun ω => (D ω-(a+(∑ k,b k*X ω k)+(∑ k,c k*W ω k)))^2)=
       mean μ (fun ω => (D ω-linearPredictor γ (X ω))^2)) ↔
       a=γ 0 ∧ (∀ k,b k=γ k.succ) ∧ (∀ k,c k=0)

#print placebo_linear_cef_correction_supporting_conditional_statement
#check @placebo_linear_cef_correction_supporting_conditional_statement
#print axioms placebo_linear_cef_correction_supporting_conditional_statement

end AronowAudit.P001
