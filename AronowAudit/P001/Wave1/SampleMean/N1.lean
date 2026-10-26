import AronowAudit.P001.Wave1.SampleMeanBlueprint

/-!
# Sample-mean moments and Chebyshev bound

Combines the three theorems `iid_sample_mean_expectation_integrable`
(L¹ unbiasedness), `iid_sample_mean_finite_moments` (variance `V[X]/n` under L²) and
`iid_sample_mean_chebyshev` (tail bound under L²). The printed positivity guard
`0 < V[X]` of Theorem 3.2.5 is carried but not needed by the proof.
-/

set_option autoImplicit false

universe u

namespace AronowAudit.P001.Wave1.SampleMean

open AronowAudit.P001

theorem n1_proof : N1.{u} := fun μ _ X hiid h1 n hn =>
  ⟨iid_sample_mean_expectation_integrable μ X hiid h1 n hn, fun h2 =>
    ⟨(iid_sample_mean_finite_moments μ X hiid h2 n hn).2, fun _ ε hε =>
      iid_sample_mean_chebyshev μ X hiid h2 n hn ε hε⟩⟩

end AronowAudit.P001.Wave1.SampleMean
