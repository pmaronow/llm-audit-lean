import AronowAudit.P005.P005_Formalization

/-!
Finite row-sampling literature statements and conditional covariance and
regression-expansion statements. The literature results are explicit hypotheses
of the application statements.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false

namespace AronowAudit.Literature

/-- Uniform probability on labelled size-s subsets of Fin N.
This definition has no dependence on a population, estimator, or conclusion. -/
def labelledSubsetProbability (N s : ℕ) (E : Finset (Fin N) → Prop) : ℝ := by
  classical
  exact ((((Finset.univ : Finset (Fin N)).powersetCard s).filter E).card : ℝ) /
    (((Finset.univ : Finset (Fin N)).powersetCard s).card : ℝ)

/-- Uniform average on labelled size-s subsets; arbitrary real marks are integrable
because the support is finite. -/
def labelledSubsetExpectation (N s : ℕ) (f : Finset (Fin N) → ℝ) : ℝ :=
  (∑ S ∈ (Finset.univ : Finset (Fin N)).powersetCard s, f S) /
    (((Finset.univ : Finset (Fin N)).powersetCard s).card : ℝ)

/-- Variance with respect to the same finite uniform law. -/
def labelledSubsetVariance (N s : ℕ) (f : Finset (Fin N) → ℝ) : ℝ :=
  labelledSubsetExpectation N s (fun S => (f S - labelledSubsetExpectation N s f)^2)

/-- Sum of a matrix's entries over the sampled rows and sampled columns. -/
def principalSum (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℝ)
    (S : Finset (Fin N)) : ℝ := ∑ i ∈ S, ∑ j ∈ S, Q i j

/-- Lihua Lei and Peng Ding, "Regression adjustment in completely randomized
experiments with a diverging number of covariates," Biometrika 108(4) (2021),
815-828, Supplementary Material, Lemma A.5. Accessible accepted manuscript:
arXiv:1806.07585v4, dated 1 January 2021, p. 17; proof pp. 25-26.
https://arxiv.org/pdf/1806.07585v4 .

Full lemma: the expectation identity holds for every real matrix, and the variance
bound requires both zero row sums and zero column sums. There is no symmetry or
positive-semidefiniteness assumption. All sample sizes 0 <= s <= N are included.
-/
def LeiDing2021QuadraticSampling : Prop :=
  ∀ (N s : ℕ), 4 ≤ N → s ≤ N →
    ∀ (Q : Matrix (Fin N) (Fin N) ℝ),
      labelledSubsetExpectation N s (principalSum N Q) =
        (s : ℝ)*((N : ℝ)-s)/((N : ℝ)*((N : ℝ)-1)) * (∑ i, Q i i) +
        (s : ℝ)*((s : ℝ)-1)/((N : ℝ)*((N : ℝ)-1)) * (∑ i, ∑ j, Q i j) ∧
      ((∀ i, (∑ j, Q i j) = 0) → (∀ j, (∑ i, Q i j) = 0) →
        labelledSubsetVariance N s (principalSum N Q) ≤
          (s : ℝ)*((N : ℝ)-s)/((N : ℝ)*((N : ℝ)-1)) * (∑ i, ∑ j, (Q i j)^2))

/-- Squared Euclidean norm, in finite real coordinates. -/
def coordinateNormSq (k : ℕ) (v : Fin k → ℝ) : ℝ := ∑ j, (v j)^2

/-- Squared norm after restricting a rectangular matrix to the specified labelled rows. -/
def restrictedNormSq (N k : ℕ) (W : Matrix (Fin N) (Fin k) ℝ)
    (S : Finset (Fin N)) (v : Fin k → ℝ) : ℝ :=
  ∑ i ∈ S, (∑ j, W i j * v j)^2

/-- Full row-sampling lemma of Joel A. Tropp,
"Improved Analysis of the Subsampled Randomized Hadamard Transform,"
Advances in Adaptive Data Analysis 3(1-2) (2011), 115-126, Lemma 3.4.
Accessible accepted manuscript, revised 17 July 2011, pp. 5-6:
https://tropp.caltech.edu/papers/Tro11-Improved-Analysis-preprint.pdf .

Both singular-value bounds and both failure terms are retained. For real matrices,
the simultaneous bounds are written in their equivalent quadratic-form form:
for every unit vector v, (1-delta)s/N <= ||W_S v||^2 <= (1+eta)s/N.
The bad event is the complement, with strict inequalities. M is exactly N times
the maximum squared row norm. Row labels, rather than distinct row values, are sampled.
The ranges of delta and eta are those of Theorem 2.2, used in the lemma's proof.
Everything is quantified inside this proposition; there are no section parameters.
-/
def Tropp2011RowSampling : Prop :=
  ∀ (N k s : ℕ), 0 < N → 0 < k → s ≤ N →
    ∀ (W : Matrix (Fin N) (Fin k) ℝ),
      (∀ a b : Fin k, (∑ i, W i a * W i b) = if a = b then 1 else 0) →
      ∀ (α δ η : ℝ), 0 < α → 0 ≤ δ → δ < 1 → 0 ≤ η →
        let M := (N : ℝ) * sSup (Set.range (fun i : Fin N => ∑ j : Fin k, (W i j)^2))
        α * M * Real.log (k : ℝ) ≤ (s : ℝ) →
        labelledSubsetProbability N s (fun S =>
          ∃ v : Fin k → ℝ, coordinateNormSq k v = 1 ∧
            (restrictedNormSq N k W S v < (1-δ)*(s : ℝ)/(N : ℝ) ∨
             (1+η)*(s : ℝ)/(N : ℝ) < restrictedNormSq N k W S v)) ≤
          (k : ℝ) * Real.rpow
            (Real.exp (-δ) / Real.rpow (1-δ) (1-δ)) (α * Real.log (k : ℝ)) +
          (k : ℝ) * Real.rpow
            (Real.exp η / Real.rpow (1+η) (1+η)) (α * Real.log (k : ℝ))

end AronowAudit.Literature

namespace AronowAudit.P005

/-- P005-T2 statement conditional on the independent quadratic-form lemma. -/
def corrected_covariance_lemma_conditional_statement : Prop :=
  AronowAudit.Literature.LeiDing2021QuadraticSampling →
  ∀ {n m : ℕ} (hn : 4 ≤ n) (hm : 0 < m) (hmn : m < n)
    (t : Arm) (a b : Fin n → ℝ),
    expectation m (fun S => sampleCov (armSet t S) a b) =
      (((armSize n m t : ℕ) : ℝ) - 1) * n /
        ((armSize n m t : ℝ) * (n - 1)) * popCov a b ∧
    variance m (fun S => sampleCov (armSet t S) a b) ≤
      covarianceBound (armSize n m t) (centered a) (centered b)

/-- P005-T8 statement conditional on the published row-sampling lemma. -/
def corrected_interacted_expansion_max_conditional_statement : Prop :=
  AronowAudit.Literature.Tropp2011RowSampling →
  ∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P)
    (hinv : ∀ᶠ n in Filter.atTop, interactedRegular (P n) (m n))
    (hκ : Filter.Tendsto (fun n => kappa (P n) * Real.log (max (d n) 2 : ℕ))
      Filter.atTop (nhds 0)),
    stochasticO m (fun n S => interactedATE (P n) S - ate (P n) - armLeading (P n) S)
      (fun n => Real.sqrt (kappa (P n)*(d n)/n))

/-- P005-T9 statement conditional on the published row-sampling lemma. -/
def corrected_interacted_expansion_two_conditional_statement : Prop :=
  AronowAudit.Literature.Tropp2011RowSampling →
  ∀ (d m : ℕ → ℕ)
    (P : (n : ℕ) → Population n (d n)) (h : standingAssumptions d m P)
    (hinv : ∀ᶠ n in Filter.atTop, interactedRegular (P n) (m n))
    (hκ : Filter.Tendsto (fun n => kappa (P n) * Real.log (2*(d n) : ℕ))
      Filter.atTop (nhds 0)),
    stochasticO m (fun n S => interactedATE (P n) S - ate (P n) - armLeading (P n) S)
      (fun n => Real.sqrt (kappa (P n)*(d n)/n))

end AronowAudit.P005

