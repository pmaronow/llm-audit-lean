import AronowAudit.P001.Wave1.SieveRateBlueprint
import AronowAudit.P001.Wave1.PolynomialBlp.N3
import AronowAudit.P001.Wave1.SieveRate.N1
import AronowAudit.P001.Wave1.SieveRate.N2
import AronowAudit.P001.Wave1.SieveRate.N3
import AronowAudit.P001.Wave1.SieveRate.N4
import AronowAudit.P001.Wave1.SieveRate.N5
import AronowAudit.P001.Wave1.SieveRate.N6
import AronowAudit.P001.Wave1.SieveRate.N7
import AronowAudit.P001.Wave1.SieveRate.N8
import AronowAudit.P001.Wave1.SieveRate.N9
import AronowAudit.P001.Wave1.SieveRate.N10
import AronowAudit.P001.Wave1.SieveRate.N11
import AronowAudit.P001.Wave1.SieveRate.N12
import AronowAudit.P001.Wave1.SieveRate.N13
import AronowAudit.P001.Wave1.SieveRate.N14
import AronowAudit.P001.Wave1.SieveRate.N15
import AronowAudit.P001.Wave1.SieveRate.N16
import AronowAudit.P001.Wave1.SieveRate.N17
import AronowAudit.P001.Wave1.SieveRate.N18
import AronowAudit.P001.Wave1.SieveRate.N19
import AronowAudit.P001.Wave1.SieveRate.N20

/-! # Refutation of the printed sieve degree-rate assertion (P001-T119) -/

set_option autoImplicit false

namespace AronowAudit.P001.Wave1

open AronowAudit.P001 MeasureTheory ProbabilityTheory Filter Polynomial
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

theorem printed_sieve_degree_rate_contract_refuted :
    ¬ ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X Y : ℕ → Ω → ℝ), IID μ (fun i ω => (X i ω, Y i ω)) → Integrable (Y 0) μ →
      ∀ (a b : ℝ), a < b → ∀ (f : ℝ → ℝ), HasPDF (μ.map (X 0)) f →
      (∀ x, 0 < f x ↔ x ∈ Set.Icc a b) → ∀ (m : ℝ → ℝ), ContDiff ℝ ⊤ m →
      IsCEF μ (X 0) (Y 0) m → ∀ (J : ℕ → ℕ), Tendsto J atTop atTop →
      Tendsto (fun (n : ℕ) => (J n : ℝ) / (n : ℝ)) atTop (nhds 0) →
      ∀ (fit : ℕ → Ω → Polynomial ℝ), IsSieveLS X Y J fit →
      CP μ (fun n ω => ∫ x, ((fit n ω).eval x - m x) ^ 2 ∂(μ.map (X 0))) 0 := by
  exact AronowAudit.P001.Wave1.SieveRate.assemble
    PolynomialBlp.n3_proof
    SieveRate.n1_proof SieveRate.n2_proof SieveRate.n3_proof SieveRate.n4_proof
    SieveRate.n5_proof SieveRate.n6_proof SieveRate.n7_proof SieveRate.n8_proof
    SieveRate.n9_proof SieveRate.n10_proof SieveRate.n11_proof SieveRate.n12_proof
    SieveRate.n13_proof SieveRate.n14_proof SieveRate.n15_proof SieveRate.n16_proof
    SieveRate.n17_proof SieveRate.n19_proof SieveRate.n18_proof SieveRate.n20_proof

end

end AronowAudit.P001.Wave1
