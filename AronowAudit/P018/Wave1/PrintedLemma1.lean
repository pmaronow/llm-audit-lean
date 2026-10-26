import AronowAudit.P018.Wave1.PrintedLemma1Blueprint
import AronowAudit.P018.Wave1.PrintedLemma1.N1
import AronowAudit.P018.Wave1.PrintedLemma1.N2
import AronowAudit.P018.Wave1.PrintedLemma1.N3
import AronowAudit.P018.Wave1.PrintedLemma1.N4
import AronowAudit.P018.Wave1.PrintedLemma1.N5

set_option autoImplicit false

namespace AronowAudit.P018.Wave1
open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
noncomputable section

theorem lemma1_printed_refuted :
  ¬ ∀ {U : Type} [MeasurableSpace U] {k : ℕ} (K : Kernel U k), Standing K → SampleRank K →
    (∀ N : ℕ, 3 ≤ N → varMat (unitSampleLaw K N) (scoreSum K) = printedSigma K N) ∧
    (∃ ν : Measure (Vec k), weakLimit (unitSampleLaw K)
      (fun N ω => Real.sqrt N • coefficientError K ω) ν ∧
      (∀ a, MemLp (fun x : Vec k => x a) 2 ν) ∧ meanVec ν id = 0 ∧
      Tendsto (trueTarget K) atTop (𝓝 (varMat ν id))) :=
  PrintedLemma1.assemble PrintedLemma1.n1_proof PrintedLemma1.n2_proof PrintedLemma1.n3_proof PrintedLemma1.n4_proof PrintedLemma1.n5_proof

end
end AronowAudit.P018.Wave1
