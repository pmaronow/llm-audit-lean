import SAP.P011b.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P011b.Bridge

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal

noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

theorem starCore_correspondence :
    starCore  ↔ type_of% (AronowAudit.P011.Wave1.star_counterexample_proof) := Iff.rfl

theorem T16Statement_correspondence (F : Family) (c1 c2 c3 c4 : ℝ) (h : Scaling F c1 c2 c3 c4)
    (p : ℕ) (j : Fin p) (D : ∀ k, Matrix (Fin (F.size k)) (Fin p) ℝ) (b : Fin p → ℝ)
    (hrank : ∀ k, ((D k)ᵀ*D k).det ≠ 0)
    (hmean : ∀ k, MeanModel (F.model k) (D k) b)
    (hθ : ∀ k i, (F.model k).theta i = olsTheta (D k) j i) :
    T16Statement F c1 c2 c3 c4 h p j D b hrank hmean hθ ↔ type_of% (AronowAudit.P011.Wave1.ols_repair_proof (toFamily F) c1 c2 c3 c4 h p j D b hrank hmean hθ) := Iff.rfl

theorem T17Statement_correspondence
    {n : ℕ} (hn : 0 < n) (m : Model n) (i j k l : Fin n) :
    T17Statement hn m i j k l ↔ type_of% (AronowAudit.P011.Wave1.corrected_covariance_expansion_moments hn (toModel m) i j k l) := Iff.rfl

theorem T18Core_correspondence :
    T18Core  ↔ type_of% (AronowAudit.P011.printed_expansion_counterexample) := Iff.rfl

theorem T19Statement_correspondence (F : Family) (c1 c2 c3 c4 : ℝ)
    (h : Scaling F c1 c2 c3 c4) (hs : ∀ k, Homoskedastic (F.model k))
    (hpos : ∀ k, 0 < meanVariance (F.model k)) :
    T19Statement F c1 c2 c3 c4 h hs hpos ↔ type_of% (AronowAudit.P011.auxiliary_corrected_display (toFamily F) c1 c2 c3 c4 h hs hpos) := Iff.rfl

theorem signCertificate_correspondence :
    signCertificate  ↔ type_of% (AronowAudit.P011.Wave1.printed_sign_counterexample_full) := Iff.rfl

theorem correlationIdentity_correspondence {n : ℕ} (hn : 0 < n) (m : Model n)
    (hdep : Dependency m) (hs : Homoskedastic m)
    (hL2 : ∀ i, MemLp (fun y => weighted m y i) 2 m.law) :
    correlationIdentity hn m hdep hs hL2 ↔ type_of% (AronowAudit.P011.pairwise_correlation_repair hn (toModel m) hdep hs hL2) := Iff.rfl

theorem pathCorrelations_correspondence :
    pathCorrelations  ↔ type_of% (AronowAudit.P011.path_correlation_instance) := Iff.rfl

theorem T22Statement_correspondence {n : ℕ} (hn : 0 < n) :
    T22Statement hn ↔ type_of% (AronowAudit.P011.upper_program_equivalence hn) := Iff.rfl

theorem variablesCounterexample_correspondence :
    variablesCounterexample  ↔ type_of% (AronowAudit.P011.printed_variables_counterexample) := Iff.rfl

theorem variablesOptimum_correspondence (A : Graph 3) (hA : Compatible (emptyGraph 3) (fun _ => 1) A) :
    variablesOptimum A hA ↔ type_of% (AronowAudit.P011.printed_variables_optimum A hA) := Iff.rfl

theorem T24Statement_correspondence {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) :
    T24Statement R G d hv ↔ type_of% (AronowAudit.P011.corrected_notation R G d hv) := Iff.rfl

theorem helperDenominators_correspondence {n : ℕ} (hn : 1 < n) (A : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) :
    helperDenominators hn A d x ↔ type_of% (AronowAudit.P011.helper_denominators hn A d x) := Iff.rfl

theorem helperCorrection_correspondence {n : ℕ} (hn : 1 < n) (R : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) :
    helperCorrection hn R d x ↔ type_of% (AronowAudit.P011.helper_correction hn R d x) := Iff.rfl

theorem helperExamples_correspondence :
    helperExamples  ↔ type_of% (AronowAudit.P011.helper_counterexamples) := Iff.rfl

theorem threePointScaling_correspondence :
    threePointScaling  ↔ type_of% (AronowAudit.P011.helper_witness_scaling) := Iff.rfl

theorem threePointWitness_correspondence :
    threePointWitness  ↔ type_of% (AronowAudit.P011.helper_witness_law) := Iff.rfl

theorem integerPrograms_correspondence {n : ℕ} (hn : 0 < n) (R : Graph n) (d : Fin n → ℕ) (x : Fin n → ℝ) :
    integerPrograms hn R d x ↔ type_of% (AronowAudit.P011.integer_program_estimators hn R d x) := Iff.rfl

theorem sharpOracleBound_correspondence {n : ℕ} (R G : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) (f : Graph n → ℝ) :
    sharpOracleBound R G d hv f ↔ type_of% (AronowAudit.P011.oracle_sharp_bound R G d hv f) := Iff.rfl

theorem T28Statement_correspondence {n : ℕ} (hn : 0 < n) (R G A : Graph n) (d : Fin n → ℕ)
    (hv : Compatible R d G) (x : Fin n → ℝ)
    (hm : Maximizes R d (fun B => V2 B x) A) :
    T28Statement hn R G A d hv x hm ↔ type_of% (AronowAudit.P011.lemma_one hn R G A d hv x hm) := Iff.rfl

theorem starRegression_correspondence :
    starRegression ↔ type_of% (AronowAudit.P011.block_ols_representations.2) := Iff.rfl

theorem starRelaxation_correspondence :
    starRelaxation ↔ (∀ upper : Bool, ∀ k : ℕ, ∀ a : Edge (4*(k+1)) → ℝ,
      type_of% (AronowAudit.P011.star_relaxation_singleton upper k a)) := Iff.rfl


end
end SAP.P011b.Bridge
