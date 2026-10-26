import AronowAudit.P018.P018_Audit

/-!
# P018-T26: refutation of Lemma 1 as printed

The printed claim states that for every kernel `K` with `Standing K` and
`SampleRank K`, (i) for every `N ≥ 3` the unconditional score variance equals the printed
conditional-covariance sum `printedSigma K N` (equation (2), p. 566; (6), p. 573), and
(ii) an asymptotic-law clause. `Target` negates this conjunction for
`U : Type` (universe 0), which suffices to refute the universal claim.

The witness `nonlinearKernel` has iid `Z ~ Uniform[-1,1]`,
`X = (1, 2+Z_i+Z_j)`, and `Y = (Z_i+Z_j)^2`.
The population residual `(Z_i+Z_j)^2 - 2/3` is a function of the design, so every
conditional covariance and hence `printedSigma` vanishes, whereas at `N = 3` the
intercept entry of the true score variance is `12/5`. Failure of conjunct (i)
at `N = 3` refutes the whole conjunction; conjunct (ii) is not needed.
-/

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.PrintedLemma1

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

noncomputable section

/-- **Target (P018-T26).** Negation of the printed Lemma 1 claim (universe 0). -/
def Target : Prop :=
  ¬ ∀ {U : Type} [MeasurableSpace U] {k : ℕ} (K : Kernel U k), Standing K → SampleRank K →
    (∀ N : ℕ, 3 ≤ N → varMat (unitSampleLaw K N) (scoreSum K) = printedSigma K N) ∧
    (∃ ν : Measure (Vec k), weakLimit (unitSampleLaw K)
      (fun N ω => Real.sqrt N • coefficientError K ω) ν ∧
      (∀ a, MemLp (fun x : Vec k => x a) 2 ν) ∧ meanVec ν id = 0 ∧
      Tendsto (trueTarget K) atTop (𝓝 (varMat ν id)))

/-- Explicit nonlinear-kernel counterexample to the printed Lemma 1 claim. -/
def Witness : Prop :=
  Standing nonlinearKernel ∧ SampleRank nonlinearKernel ∧
    ¬ ((∀ N : ℕ, 3 ≤ N →
      varMat (unitSampleLaw nonlinearKernel N) (scoreSum nonlinearKernel) =
        printedSigma nonlinearKernel N) ∧
      (∃ ν : Measure (Vec 2), weakLimit (unitSampleLaw nonlinearKernel)
        (fun N ω => Real.sqrt N • coefficientError nonlinearKernel ω) ν ∧
        (∀ a, MemLp (fun x : Vec 2 => x a) 2 ν) ∧
        meanVec ν id = 0 ∧ Tendsto (trueTarget nonlinearKernel) atTop
          (𝓝 (varMat ν id))))

/-! ## Component propositions -/

/-- For `N ≥ 3`, distinct sampled values at units `1` and `2` imply that
the sample Gram of the nonlinear design is nonsingular. -/
def N1 : Prop :=
  ∀ (N : ℕ) (hN : 3 ≤ N) (ω : Fin N → ℝ),
    ω ⟨1, by omega⟩ ≠ ω ⟨2, by omega⟩ →
      (sampleGram (design nonlinearKernel ω)).det ≠ 0

/-- Under the iid uniform sample law, the values at units `1` and `2`
agree with probability zero for `N ≥ 3`. -/
def N2 : Prop :=
  ∀ (N : ℕ) (hN : 3 ≤ N),
    (unitSampleLaw nonlinearKernel N) {ω | ω ⟨1, by omega⟩ = ω ⟨2, by omega⟩} = 0

/-- At `N = 3`, the printed conditional-covariance sum for `nonlinearKernel` vanishes. -/
def N3 : Prop := printedSigma nonlinearKernel 3 = 0

/-- At `N = 3`, the `(0,0)` entry of the true score variance equals the
variance of the displayed polynomial under three iid Uniform[-1,1] units. -/
def N4 : Prop :=
  (varMat (unitSampleLaw nonlinearKernel 3) (scoreSum nonlinearKernel)) 0 0 =
    variance (fun ω : Fin 3 → ℝ =>
      (ω 0 + ω 1) ^ 2 + (ω 0 + ω 2) ^ 2 + (ω 1 + ω 2) ^ 2 - 2)
      (Measure.pi (fun _ : Fin 3 => uniformUnitLaw))

/-- The displayed polynomial has variance `12/5` under three iid Uniform[-1,1] units. -/
def N5 : Prop :=
  variance (fun ω : Fin 3 → ℝ =>
      (ω 0 + ω 1) ^ 2 + (ω 0 + ω 2) ^ 2 + (ω 1 + ω 2) ^ 2 - 2)
      (Measure.pi (fun _ : Fin 3 => uniformUnitLaw)) = 12 / 5

/-! ## Assembly -/

/-- `SampleRank` for the witness, from `N1` and `N2` (take `N0 = 3`). -/
theorem sampleRank_of (h1 : N1) (h2 : N2) : SampleRank nonlinearKernel := by
  refine ⟨3, fun N hN => ?_⟩
  rw [ae_iff]
  apply measure_mono_null _ (h2 N hN)
  intro ω hω
  by_contra hne
  exact hω (h1 N hN ω hne)

/-- The five component propositions imply the explicit counterexample. -/
theorem assemble_witness (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) : Witness := by
  refine ⟨nonlinear_model_assumptions, sampleRank_of h1 h2, fun h => ?_⟩
  have h00 := congrFun (congrFun (h.1 3 le_rfl) 0) 0
  rw [h4, h5, h3] at h00
  norm_num at h00

/-- The five component propositions imply the negation of the universal printed claim. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) : Target := by
  intro hall
  obtain ⟨hS, hR, hnot⟩ := assemble_witness h1 h2 h3 h4 h5
  exact hnot (hall nonlinearKernel hS hR)

end

end AronowAudit.P018.Wave1.PrintedLemma1
