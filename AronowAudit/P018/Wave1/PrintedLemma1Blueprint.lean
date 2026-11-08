import AronowAudit.P018.P018_Audit

/-!
# Blueprint: P018-T26, refutation of Lemma 1 as printed

Record: P018-T26 / `AronowAudit.P018.lemma1_printed`; resolution `refute`.

Frozen contract (P018_Audit.lean:1595): for every kernel `K` with `Standing K` and
`SampleRank K`, (i) for every `N ≥ 3` the unconditional score variance equals the printed
conditional-covariance sum `printedSigma K N` (equation (2), p. 566; (6), p. 573), and
(ii) an asymptotic-law clause.  `Target` is the negation of exactly that contract, with
`U : Type` (universe 0); the universe-polymorphic frozen theorem would give its universe-0
instance, so this refutes it.  The `example` checks this by `Iff.rfl`.

Witness (map record 4, accepted by both referees): `nonlinearKernel` — iid
`Z ~ Uniform[-1,1]`, `X = (1, 2+Z_i+Z_j)`, `Y = (Z_i+Z_j)^2`.  `Standing` is already proved
(`nonlinear_model_assumptions`).  The population residual `(Z_i+Z_j)^2 - 2/3` is a function
of the design, so every conditional covariance and hence `printedSigma` vanishes, whereas
at `N = 3` the intercept entry of the true score variance is `12/5`.  Failure of conjunct
(i) at `N = 3` refutes the whole conjunction; conjunct (ii) is not needed.

Nodes `N1`–`N5`.  Writers prove `theorem nk_proof : Nk` in
`AronowAudit/P018/Wave1/PrintedLemma1/Nk.lean`.
Final file: `AronowAudit/P018/Wave1/PrintedLemma1.lean`, theorem
`AronowAudit.P018.Wave1.lemma1_printed_refuted`.
-/

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.PrintedLemma1

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

noncomputable section

/-- **Target (P018-T26).** Exact negation of `lemma1_printed` (universe 0). -/
def Target : Prop :=
  ¬ ∀ {U : Type} [MeasurableSpace U] {k : ℕ} (K : Kernel U k), Standing K → SampleRank K →
    (∀ N : ℕ, 3 ≤ N → varMat (unitSampleLaw K N) (scoreSum K) = printedSigma K N) ∧
    (∃ ν : Measure (Vec k), weakLimit (unitSampleLaw K)
      (fun N ω => Real.sqrt N • coefficientError K ω) ν ∧
      (∀ a, MemLp (fun x : Vec k => x a) 2 ν) ∧ meanVec ν id = 0 ∧
      Tendsto (trueTarget K) atTop (𝓝 (varMat ν id)))

/-- Fidelity check: `Target` is literally `¬` (type of the frozen declaration, universe 0).
Only the frozen theorem's *type* is read; its unfinished draft proof is never used. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P018.lemma1_printed.{0}) := Iff.rfl

/-- The mapper's explicit witness statement (`lemma1_printed_refuted` in the map). -/
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

/-! ## Nodes -/

/-- **Node N1** (map record 4: "two sample rows, X_{0,1} and X_{0,2}, differ in their second
coordinates unless Z_1=Z_2 ... these two rows are linearly independent because their first
coordinates are both 1"). Deterministic rank: for `N ≥ 3`, if the sampled values of units
`1` and `2` differ, the sample Gram of the nonlinear design is nonsingular.
Suggested route: the Gram of vectors `(1, x_d)` has determinant
`D Σ x_d² - (Σ x_d)² = ½ Σ_{d,f} (x_d - x_f)²` (`Matrix.det_fin_two`, Lagrange identity),
which is at least `(x_{01} - x_{02})² > 0`; the two dyads are `{0,1}` and `{0,2}` in
`powersetCard 2`, with `firstUnit`/`secondUnit` their min/max. -/
def N1 : Prop :=
  ∀ (N : ℕ) (hN : 3 ≤ N) (ω : Fin N → ℝ),
    ω ⟨1, by omega⟩ ≠ ω ⟨2, by omega⟩ →
      (sampleGram (design nonlinearKernel ω)).det ≠ 0

/-- **Node N2** (map record 4: "Independent atomless uniform variables agree with
probability zero"). Ties between two distinct sampled units are null under the product of
the uniform law. Suggested route: push `ω ↦ (ω 1, ω 2)` forward to
`uniformUnitLaw.prod uniformUnitLaw` (`Measure.pi`, `measurePreserving_eval`, iid
coordinates), then the diagonal is null by Fubini (`Measure.prod_apply`) because
`uniformUnitLaw {z} = 0` (`ProbabilityTheory.cond_apply`, `Real.volume_singleton`). -/
def N2 : Prop :=
  ∀ (N : ℕ) (hN : 3 ≤ N),
    (unitSampleLaw nonlinearKernel N) {ω | ω ⟨1, by omega⟩ = ω ⟨2, by omega⟩} = 0

/-- **Node N3** (map record 4: "The population residual is epsilon_ij=(Z_i+Z_j)^2-2/3=
(X_ij,1-2)^2-2/3. Hence it is measurable with respect to the full design sigma algebra
... every conditionalResidualCov is zero, every conditionalTerm is zero, and
printedSigma(N)=0"). At `N = 3` the printed conditional meat vanishes.
Suggested route: `populationBeta nonlinearKernel = ![2/3,0]`
(`nonlinear_population_projection`, proved), so `epsilon K ω d = g (design K ω d)` with
`g x = (x 1 - 2)^2 - 2/3`; `designSigma ≤` the product σ-algebra (comap of a measurable map);
`MeasureTheory.condExp_of_stronglyMeasurable` gives `conditionalResidualMean = epsilon`
a.e., hence the centred product is `0` a.e. and `condExp` of it is `0` a.e.
(`condExp_congr_ae`, `condExp_zero`); `integral_congr_ae` then kills `conditionalTerm`. -/
def N3 : Prop := printedSigma nonlinearKernel 3 = 0

/-- **Node N4** (map record 4: "At N=3 the intercept coordinate of the total score is
S=2(Z_0^2+Z_1^2+Z_2^2-1)+2(Z_0 Z_1+Z_0 Z_2+Z_1 Z_2)"). Deterministic reduction of the
`(0,0)` entry of the true score variance to the variance of an explicit polynomial.
Suggested route: `populationBeta nonlinearKernel = ![2/3,0]`, enumerate `Dyad 3`
(`decide`/`Finset.univ` of `powersetCard 2 (univ : Finset (Fin 3))`), then
`ProbabilityTheory.covariance_self` (the polynomial is continuous, hence AE-measurable). -/
def N4 : Prop :=
  (varMat (unitSampleLaw nonlinearKernel 3) (scoreSum nonlinearKernel)) 0 0 =
    variance (fun ω : Fin 3 → ℝ =>
      (ω 0 + ω 1) ^ 2 + (ω 0 + ω 2) ^ 2 + (ω 1 + ω 2) ^ 2 - 2)
      (Measure.pi (fun _ : Fin 3 => uniformUnitLaw))

/-- **Node N5** (map record 4: "Var(S)=4·3(1/5-1/9)+4·3(1/3)^2=16/15+4/3=12/5"). Exact
polynomial moment under three iid Uniform[-1,1] units. Suggested route:
`variance_def'`/`variance_eq_sub`, expand the polynomial, integrate monomials with
`MeasureTheory.integral_fintype_prod_eq_prod` and `uniform_unit_moment` (proved;
`E Z = E Z³ = 0`, `E Z² = 1/3`, `E Z⁴ = 1/5`). -/
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

/-- **Assembly of the explicit witness.** -/
theorem assemble_witness (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) : Witness := by
  refine ⟨nonlinear_model_assumptions, sampleRank_of h1 h2, fun h => ?_⟩
  have h00 := congrFun (congrFun (h.1 3 le_rfl) 0) 0
  rw [h4, h5, h3] at h00
  norm_num at h00

/-- **Assembly.** The nodes suffice for the refutation of the universal contract. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) : Target := by
  intro hall
  obtain ⟨hS, hR, hnot⟩ := assemble_witness h1 h2 h3 h4 h5
  exact hnot (hall nonlinearKernel hS hR)

end

end AronowAudit.P018.Wave1.PrintedLemma1
