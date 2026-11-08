import AronowAudit.P018.P018_Audit

/-!
# Blueprint: P018-T10 (C2), weighted sandwich consistency for one common directed kernel

Record: P018-T10 / `AronowAudit.P018.weighted_consistency_corrected`; resolution
`repair_and_prove`.

Scope repair (mapper record 2, accepted by both referees).  The frozen draft lets every
record `(N, d, t)` carry an arbitrary kernel (`RepeatedStanding` only), which exceeds the
standing model S9 (common functions of the two sampled units, p. 566) and can leave block
scores with non-zero means.  The repaired contract restores *one* measurable ordered-pair
data kernel `(X, Y)`, evaluated in orientation `(u,v)` or `(v,u)` (`dir`), with at most one
record per orientation (`dir` injective); this is the directed-pair reading of p. 567 and
Appendix D, p. 575.  Normalized weights `w/a_N` stay arbitrary, deterministic, positive and
uniformly bounded, and the normalized expected weighted Gram has a positive definite limit
(corrected C2).  The conclusion is the frozen one, verbatim.

Paper proof (map record 2): rescale by `a_N` (`weighted_scale_invariance`, proved); by
iid exchangeability every record has the same `Q = E[XX']`, `r = E[XY]`, so
`H_N = c_N Q`, `Q` is nonsingular and `β_N = Q⁻¹ r =: β` for `N ≥ 2`; hence every weighted
block score is centred.  Local dependence (two-unit supports, `≤ N³` overlapping dyad
pairs, `≤ 12 N⁵` dependent pairs of overlap products) gives `O(1/N)` variances for the
normalized Gram, score and meat; Chebyshev, inverse continuity, the normal equations,
the residual substitution bound and `sandwich_difference` finish.

Structure.  `Target` (the repaired contract) follows from `CoreTarget` (the same statement
for already-normalized weights `v`, bundled in `Setting`) by exact rescaling.  Generic nodes
`G1`–`G8` are reusable probability/counting facts; model nodes `M0`–`M11` are stated as
implications between named intermediate predicates, so `assemble` checks the whole DAG.

Writers prove `theorem gk_proof : Gk` / `theorem mk_proof : Mk` in
`AronowAudit/P018/Wave1/WeightedConsistency/Gk.lean` / `.../Mk.lean`.
Final file: `AronowAudit/P018/Wave1/WeightedConsistency.lean`, theorem
`AronowAudit.P018.Wave1.weighted_consistency_common_directed_kernel`.
-/

set_option autoImplicit false

namespace AronowAudit.P018.Wave1.WeightedConsistency

open AronowAudit.P018 Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal

universe u

noncomputable section

/-! ## Target -/

/-- **Target (P018-T10, corrected C2, common directed kernel).** -/
def Target : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k),
    RepeatedStanding R → (∀ N d, R.T N d ≤ 2) →
    ∀ (X : U → U → Vec k) (Y : U → U → ℝ)
      (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool),
    (∀ N d, Function.Injective (dir N d)) →
    (∀ N d (t : Fin (R.T N d)) u₁ u₂,
      R.X N d t u₁ u₂ = (if dir N d t then X u₂ u₁ else X u₁ u₂) ∧
      R.Y N d t u₁ u₂ = (if dir N d t then Y u₂ u₁ else Y u₁ u₂)) →
    ∀ (w : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (a : ℕ → ℝ), (∀ N, 0 < a N) →
    (∃ C : ℝ, ∀ N d t, 0 < w N d t / a N ∧ w N d t / a N ≤ C) →
    ∀ (H : Mat k), H.PosDef →
    Tendsto (fun N : ℕ => recordWeightedH R (fun d t => w N d t / a N)) atTop (𝓝 H) →
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • recordWeightedVariance R (w N) ω - recordWeightedTarget R (w N))

/-- Fidelity check: the frozen draft's hypotheses plus the common directed kernel
(`X, Y, dir, hdir, hCommon`) give, through `Target`, exactly the frozen draft's conclusion
(same expression, same norm and topology instances).  Only the frozen theorem's *type* is
read; its unfinished draft proof is never used. -/
example (hT : Target.{u}) {U : Type u} [MeasurableSpace U] {k : ℕ}
    (R : RepeatedKernel U k) (hR : RepeatedStanding R) (hDirections : ∀ N d, R.T N d ≤ 2)
    (w : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (a : ℕ → ℝ) (ha : ∀ N : ℕ, 0 < a N)
    (hw : ∃ C : ℝ, ∀ N d t, 0 < w N d t / a N ∧ w N d t / a N ≤ C)
    (H : Mat k) (hH : H.PosDef)
    (hlim : Tendsto (fun N : ℕ => recordWeightedH R (fun d t => w N d t / a N)) atTop (𝓝 H))
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (hdir : ∀ N d, Function.Injective (dir N d))
    (hCommon : ∀ N d (t : Fin (R.T N d)) u₁ u₂,
      R.X N d t u₁ u₂ = (if dir N d t then X u₂ u₁ else X u₁ u₂) ∧
      R.Y N d t u₁ u₂ = (if dir N d t then Y u₂ u₁ else Y u₁ u₂)) :
    type_of% (AronowAudit.P018.weighted_consistency_corrected R hR hDirections w a ha hw H hH
      hlim) :=
  hT R hR hDirections X Y dir hdir hCommon w a ha hw H hH hlim

/-! ## Objects of the normalized problem -/

/-- Hypotheses of the normalized problem (`v = w/a_N`, bound `C`, limit `H`). -/
def Setting {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k) : Prop :=
  RepeatedStanding R ∧ (∀ N d, Function.Injective (dir N d)) ∧
  (∀ N d (t : Fin (R.T N d)) u₁ u₂,
    R.X N d t u₁ u₂ = (if dir N d t then X u₂ u₁ else X u₁ u₂) ∧
    R.Y N d t u₁ u₂ = (if dir N d t then Y u₂ u₁ else Y u₁ u₂)) ∧
  (∀ N d t, 0 < v N d t ∧ v N d t ≤ C) ∧ H.PosDef ∧
  Tendsto (fun N : ℕ => recordWeightedH R (v N)) atTop (𝓝 H)

/-- `Q = E[X(U,V) X(U,V)']` for iid `U, V`. -/
def popQ {U : Type u} [MeasurableSpace U] {k : ℕ} (μ : Measure U) (X : U → U → Vec k) :
    Mat k :=
  meanMat (μ.prod μ) (fun uv => outer (X uv.1 uv.2) (X uv.1 uv.2))

/-- `r = E[X(U,V) Y(U,V)]` for iid `U, V`. -/
def popR {U : Type u} [MeasurableSpace U] {k : ℕ} (μ : Measure U) (X : U → U → Vec k)
    (Y : U → U → ℝ) : Vec k :=
  meanVec (μ.prod μ) (fun uv => score (X uv.1 uv.2) (Y uv.1 uv.2))

/-- The common population coefficient `β = Q⁻¹ r`. -/
def popBeta {U : Type u} [MeasurableSpace U] {k : ℕ} (μ : Measure U) (X : U → U → Vec k)
    (Y : U → U → ℝ) : Vec k :=
  (popQ μ X)⁻¹.mulVec (popR μ X Y)

/-- `c_N = D⁻¹ Σ_{d,t} v_{dt}`, the normalized total weight. -/
def weightMass {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (N : ℕ) : ℝ :=
  (Dreal N)⁻¹ * ∑ d : Dyad N, ∑ t, v N d t

/-- The normalized sample weighted Gram `D⁻¹ X'WX`. -/
def normGram {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (N : ℕ) (ω : Fin N → U) : Mat k :=
  (Dreal N)⁻¹ • recordWeightedGram R (v N) ω

/-- The scaled meat `(N/D²) meat(q(b))` at a coefficient `b`. -/
def scaledMeatAt {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (N : ℕ) (b : Vec k) (ω : Fin N → U) :
    Mat k :=
  ((N : ℝ) / (Dreal N) ^ 2) • meat members (recordWeightedBlockScore R (v N) b ω)

/-- The deterministic scaled score covariance `(N/D²) Var(Σ_d q_d(β))`. -/
def targetMeat {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (N : ℕ) : Mat k :=
  ((N : ℝ) / (Dreal N) ^ 2) •
    varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N, recordWeightedBlockScore R (v N) β ω d)

/-- Unit support of an ordered dyad pair's overlap product (empty if they do not overlap). -/
def pairSupport {N : ℕ} (P : Dyad N × Dyad N) : Finset (Fin N) :=
  if overlap P.1 P.2 then members P.1 ∪ members P.2 else ∅

/-! ## Intermediate predicates -/

/-- Records are measurable and uniformly bounded a.e. under iid sampling. -/
def RecordRegular {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k) : Prop :=
  (∀ N (d : Dyad N) (t : Fin (R.T N d)),
    Measurable (fun ω : Fin N → U => repeatedX R ω d t) ∧
    Measurable (fun ω : Fin N → U => repeatedY R ω d t)) ∧
  ∃ B : ℝ, 0 ≤ B ∧ ∀ N (d : Dyad N) (t : Fin (R.T N d)),
    ∀ᵐ ω ∂(repeatedLaw R N), ‖repeatedX R ω d t‖ ≤ B ∧ |repeatedY R ω d t| ≤ B

/-- The common kernel is measurable, bounded a.e., and has an intercept coordinate. -/
def KernelRegular {U : Type u} [MeasurableSpace U] {k : ℕ} (μ : Measure U)
    (X : U → U → Vec k) (Y : U → U → ℝ) : Prop :=
  Measurable (fun uv : U × U => X uv.1 uv.2) ∧ Measurable (fun uv : U × U => Y uv.1 uv.2) ∧
  (∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ uv ∂(μ.prod μ), ‖X uv.1 uv.2‖ ≤ B ∧ |Y uv.1 uv.2| ≤ B) ∧
  (∃ j : Fin k, ∀ u₁ u₂, X u₁ u₂ j = 1)

/-- Every record has the common moments `Q` and `r`. -/
def RecordMoments {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) : Prop :=
  ∀ N (d : Dyad N) (t : Fin (R.T N d)),
    meanMat (repeatedLaw R N) (fun ω => outer (repeatedX R ω d t) (repeatedX R ω d t)) =
      popQ R.μ X ∧
    meanVec (repeatedLaw R N) (fun ω => score (repeatedX R ω d t) (repeatedY R ω d t)) =
      popR R.μ X Y

/-- Population design: `Q` nonsingular, `H_N = c_N Q` and `β_N = β` for `N ≥ 2`,
`c_N → c > 0` and `H = c Q`. -/
def PopDesign {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ)
    (H : Mat k) : Prop :=
  (popQ R.μ X).det ≠ 0 ∧
  (∀ N, 2 ≤ N → recordWeightedH R (v N) = weightMass R v N • popQ R.μ X ∧
    recordWeightedBeta R (v N) = popBeta R.μ X Y) ∧
  ∃ c : ℝ, 0 < c ∧ H = c • popQ R.μ X ∧ Tendsto (weightMass R v) atTop (𝓝 c)

/-- Every weighted block score at `β` has mean zero. -/
def Centered {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) :
    Prop :=
  ∀ N (d : Dyad N),
    meanVec (repeatedLaw R N) (fun ω => recordWeightedBlockScore R (v N) (popBeta R.μ X Y) ω d)
      = 0

/-- Normalized sample Gram consistency. -/
def GramLLN {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) : Prop :=
  inProbability (repeatedLaw R) (fun N ω => normGram R v N ω - recordWeightedH R (v N))

/-- Normalized score at `β` vanishes in probability. -/
def ScoreLLN {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) : Prop :=
  inProbability (repeatedLaw R)
    (fun N ω => (Dreal N)⁻¹ • ∑ d : Dyad N, recordWeightedBlockScore R (v N) β ω d)

/-- Coefficient consistency. -/
def CoefConsistent {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) : Prop :=
  inProbability (repeatedLaw R) (fun N ω => recordWeightedOLS R (v N) ω - β)

/-- The scaled meat at `β` concentrates around its mean. -/
def MeatLLN {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) : Prop :=
  inProbability (repeatedLaw R) (fun N ω =>
    scaledMeatAt R v N β ω - meanMat (repeatedLaw R N) (scaledMeatAt R v N β))

/-- Replacing `β` by the fitted coefficient changes the scaled meat negligibly. -/
def SubstitutionNull {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) : Prop :=
  inProbability (repeatedLaw R) (fun N ω =>
    scaledMeatAt R v N (recordWeightedOLS R (v N) ω) ω - scaledMeatAt R v N β ω)

/-- The normalized problem: `Target` for already-normalized weights. -/
def CoreTarget : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H →
    inProbability (repeatedLaw R) (fun N ω =>
      (N : ℝ) • recordWeightedVariance R (v N) ω - recordWeightedTarget R (v N))

/-! ## Generic nodes -/

/-- **Node G1** (map record 2: "By invariance of the product law ... every directed record";
Appendix A's iid unit sampling). Two distinct coordinates of an iid product have the
product law. Suggested route: `ProbabilityTheory.iIndepFun_pi`,
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`, `measurePreserving_eval`. -/
def G1 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ}
    (i j : Fin N), i ≠ j →
      (Measure.pi (fun _ : Fin N => μ)).map (fun ω => (ω i, ω j)) = μ.prod μ

/-- **Node G2** (map record 1, "Products with disjoint unit supports are independent";
used by record 2). Functions of disjoint coordinate sets of an iid product are
uncorrelated. Suggested route: factor `Z = Z ∘ ext ∘ restrict_S` (extend by a fixed point
of the nonempty `U`), `ProbabilityTheory.iIndepFun_pi`,
`ProbabilityTheory.iIndepFun.indepFun_finset`, `IndepFun.comp`,
`ProbabilityTheory.IndepFun.covariance_eq_zero`. -/
def G2 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ}
    (S T : Finset (Fin N)) (Z W : (Fin N → U) → ℝ), Disjoint S T →
    Measurable Z → Measurable W →
    (∀ ω ω', (∀ i ∈ S, ω i = ω' i) → Z ω = Z ω') →
    (∀ ω ω', (∀ i ∈ T, ω i = ω' i) → W ω = W ω') →
    MemLp Z 2 (Measure.pi (fun _ : Fin N => μ)) → MemLp W 2 (Measure.pi (fun _ : Fin N => μ)) →
    covariance Z W (Measure.pi (fun _ : Fin N => μ)) = 0

/-- **Node G3** (map record 1: "If |Z|,|W|≤B^2, then |Cov(Z,W)|≤2B^4 ... any sum of bounded
two-unit variables has variance at most a constant times N^3"). Variance of a sum of
bounded, locally dependent variables. Proof: `variance` of the sum is the double sum of
covariances (`ProbabilityTheory.variance_fun_sum`/`covariance_fun_sum_fun_sum`); disjoint
supports give `0` (`G2`; the writer may import its proof), the others are at most
`2B²` in absolute value. -/
def G3 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ] {N : ℕ}
    {E : Type} [Fintype E] (σ : E → Finset (Fin N)) (Z : E → (Fin N → U) → ℝ) (B : ℝ),
    (∀ e, Measurable (Z e)) →
    (∀ e ω ω', (∀ i ∈ σ e, ω i = ω' i) → Z e ω = Z e ω') →
    (∀ e, ∀ᵐ ω ∂(Measure.pi (fun _ : Fin N => μ)), |Z e ω| ≤ B) →
    variance (fun ω => ∑ e, Z e ω) (Measure.pi (fun _ : Fin N => μ)) ≤
      2 * B ^ 2 * ∑ e, ((Finset.univ.filter (fun e' => (σ e ∩ σ e').Nonempty)).card : ℝ)

/-- **Node G4** (map record 1: "|Q|≤N^3 ... at most 3N^2 such canonical triples contain v
... at most 9N^5 ordered pairs of products"). Dependency counts: ordered overlapping dyad
pairs, and dependent pairs of overlap products (support size `≤ 3`, at most `4N²`
overlapping pairs contain a given unit). Suggested route: `intersection_count`,
`members_card`, `number_of_dyads` (all proved; do not use the drafted `dyad_counts`),
and `Finset.card_le_card_of_surjOn`/`card_biUnion_le` over incident units. -/
def G4 : Prop :=
  ∀ N : ℕ,
    (∑ d : Dyad N, ((Finset.univ.filter
        (fun f : Dyad N => (members d ∩ members f).Nonempty)).card : ℝ)) ≤ (N : ℝ) ^ 3 ∧
    (∑ P : Dyad N × Dyad N, ((Finset.univ.filter
        (fun P' : Dyad N × Dyad N => (pairSupport P ∩ pairSupport P').Nonempty)).card : ℝ)) ≤
      12 * (N : ℝ) ^ 5

/-- **Node G5** (map record 1: "Chebyshev and the N^5 count give ... →0 in probability").
Entrywise Chebyshev for matrix- and vector-valued sequences on changing probability
spaces. Suggested route: `ProbabilityTheory.meas_ge_le_variance_div_sq` (or the proved
`AronowAudit.P018.corrected_chebyshev`) per entry, then a finite union over entries for the
elementwise sup norm (`norm_le_pi_norm`, `pi_norm_lt_iff`). -/
def G5 : Prop :=
  ∀ {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)],
    (∀ F : ∀ N, Ω N → Mat k, (∀ N a b, MemLp (fun ω => F N ω a b) 2 (μ N)) →
      (∀ a b, Tendsto (fun N => variance (fun ω => F N ω a b) (μ N)) atTop (𝓝 0)) →
      inProbability μ (fun N ω => F N ω - meanMat (μ N) (F N))) ∧
    (∀ F : ∀ N, Ω N → Vec k, (∀ N a, MemLp (fun ω => F N ω a) 2 (μ N)) →
      (∀ a, Tendsto (fun N => variance (fun ω => F N ω a) (μ N)) atTop (𝓝 0)) →
      inProbability μ (fun N ω => F N ω - meanVec (μ N) (F N)))

/-- **Node G6** (map record 1: "Arbitrary totalized values on singular samples do not affect
this conclusion"; standard in-probability algebra). Sums, deterministic null sequences,
eventual equality, and a convergent random matrix times a null random vector.
Only outer-measure monotonicity and finite subadditivity are needed (no measurability). -/
def G6 : Prop :=
  ∀ {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)],
    (∀ f g : ∀ N, Ω N → Mat k, inProbability μ f → inProbability μ g →
      inProbability μ (fun N ω => f N ω + g N ω)) ∧
    (∀ f g : ∀ N, Ω N → Vec k, inProbability μ f → inProbability μ g →
      inProbability μ (fun N ω => f N ω + g N ω)) ∧
    (∀ A : ℕ → Mat k, Tendsto A atTop (𝓝 0) → inProbability μ (fun N (_ : Ω N) => A N)) ∧
    (∀ f g : ∀ N, Ω N → Mat k, (∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ ω, f N ω = g N ω) →
      inProbability μ f → inProbability μ g) ∧
    (∀ f g : ∀ N, Ω N → Vec k, (∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ ω, f N ω = g N ω) →
      inProbability μ f → inProbability μ g) ∧
    (∀ (A : ∀ N, Ω N → Mat k) (A0 : Mat k) (s : ∀ N, Ω N → Vec k),
      inProbability μ (fun N ω => A N ω - A0) → inProbability μ s →
      inProbability μ (fun N ω => (A N ω).mulVec (s N ω)))

/-- **Node G7** (map record 1: "Continuity of inversion on the open set of invertible
matrices gives its inverse converging to H^(-1)"). Deterministic and in-probability
continuous mapping for the (totalized) matrix inverse at a nonsingular limit.
Suggested route: `Matrix.nonsing_inv_eq_ringInverse`, `NormedRing.inverse_continuousAt`
under a local `Matrix.linftyOpNormedRing` (same topology), or `Matrix.inv_def` with
`Continuous.matrix_det`/adjugate continuity; then an ε-δ argument for `inProbability`. -/
def G7 : Prop :=
  ∀ {k : ℕ} (G0 : Mat k), G0.det ≠ 0 →
    (∀ G : ℕ → Mat k, Tendsto G atTop (𝓝 G0) → Tendsto (fun N => (G N)⁻¹) atTop (𝓝 G0⁻¹)) ∧
    (∀ {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] (μ : ∀ N, Measure (Ω N))
      [∀ N, IsProbabilityMeasure (μ N)] (G : ∀ N, Ω N → Mat k),
      inProbability μ (fun N ω => G N ω - G0) →
      inProbability μ (fun N ω => (G N ω)⁻¹ - G0⁻¹))

/-- **Node G8** (map record 1: "The exact identity B_N M_N B_N-B0_N T_N B0_N = ... makes each
term tend to zero in probability"). Sandwich passage with a random bread converging in
probability, a deterministic bread converging to the same limit, and a bounded
deterministic meat. Suggested route: `AronowAudit.P018.sandwich_difference` (proved), and
`‖A * B‖ ≤ k ‖A‖ ‖B‖` for the elementwise sup norm (entrywise bounds). -/
def G8 : Prop :=
  ∀ {Ω : ℕ → Type u} [∀ N, MeasurableSpace (Ω N)] {k : ℕ}
    (μ : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (μ N)]
    (Bn Mn : ∀ N, Ω N → Mat k) (B0 T : ℕ → Mat k) (B : Mat k),
    inProbability μ (fun N ω => Bn N ω - B) → Tendsto B0 atTop (𝓝 B) →
    (∃ c : ℝ, ∀ N, ‖T N‖ ≤ c) →
    inProbability μ (fun N ω => Mn N ω - T N) →
    inProbability μ (fun N ω => sandwich (Bn N ω) (Mn N ω) - sandwich (B0 N) (T N))

/-! ## Model nodes -/

/-- **Node M0** (map record 2: "The recorded measurability and boundedness transfer"). Record
regularity from `RepeatedStanding`: measurability, and the uniform a.e. bound transferred
from `R.μ.prod R.μ` to the sample law through `G1` (`firstUnit d ≠ secondUnit d`). -/
def M0 : Prop :=
  G1.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k),
    RepeatedStanding R → RecordRegular R

/-- **Node M1** (map record 2: "The recorded measurability and boundedness transfer to the
common kernel by using any actual record and swapping its arguments if necessary"). Use the
single dyad at `N = 2` and a record `t` (counts are positive); for `dir = true` compose with
`Prod.swap` (`Measure.prod_swap`). -/
def M1 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → KernelRegular R.μ X Y

/-- **Node M2** (map record 2: "By invariance of the product law under swapping U,V, every
directed record has these same Q and r"). Push the record forward with `G1`, use
`Measure.prod_swap` for reversed records, and `integral_map`. -/
def M2 : Prop :=
  G1.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → KernelRegular R.μ X Y → RecordMoments R X Y

/-- **Node M3** (map record 2: "H_N=c_N Q ... If it were singular, det(H_N)=c_N^k det(Q) would
vanish ... beta_w,N=(c_N Q)^(-1)c_N r=Q^(-1)r=beta"). Linearity of `meanMat`/`meanVec` over
the finite record sums (integrability from `RecordRegular`) gives `H_N = c_N Q` and the
`XY` analogue; the intercept gives `Q_jj = 1`, so `c_N = (H_N)_jj → H_jj > 0`
(`Matrix.PosDef.diag_pos`), `H = c Q`, `det H = c^k det Q > 0`; then
`matrix_inverse_scale_total` gives `β_N = β`. -/
def M3 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → RecordMoments R X Y → PopDesign R X Y v H

/-- **Node M4** (map record 2: "In particular E[X_dt(Y_dt-X_dt' beta)]=r-Q beta=0 for each
record, for either orientation. Hence every normalized weighted block score q_d ... has mean
zero"). -/
def M4 : Prop :=
  ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → RecordMoments R X Y → PopDesign R X Y v H →
      Centered R X Y v

/-- **Node M5** (map record 2: "Var(G_ab/D)=O(1/N)"). Weighted Gram law of large numbers:
each entry of `D⁻¹ X'WX` is `D⁻¹ Σ_d Z_d` with two-unit supports `members d` and bound
`2CB²`; `G3` and `G4` give variance `≤ 2(2CB²)² N³ / D² → 0`, and `G5` concludes
(its mean is `recordWeightedH` by `meanMat_scale`). -/
def M5 : Prop :=
  G3.{u} → G4 → G5.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → GramLLN R v

/-- **Node M6** (map record 2: "Var(S_a/D)=O(1/N)"). Score law of large numbers at `β`:
centred (`Centered`), bounded two-unit block scores; `G3`, `G4`, `G5`. -/
def M6 : Prop :=
  G3.{u} → G4 → G5.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → Centered R X Y v →
      ScoreLLN R v (popBeta R.μ X Y)

/-- **Node M7** (map record 2: "The inverse normalized sample Gram converges in probability
to H^(-1), sample singularity has vanishing probability, and the exact normal equations
yield beta_hat-beta→0 in probability"). On nonsingular samples
`β̂ - β = (D⁻¹G)⁻¹ (D⁻¹ Σ_d q_d(β))` (as in `ols_score_identity`); `D⁻¹G →p H`
(GramLLN plus `H_N → H`), `G7` for the inverse, `G6` for the product; singular samples
have vanishing probability since `det` is continuous and `det H ≠ 0`. -/
def M7 : Prop :=
  G6.{u} → G7.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → PopDesign R X Y v H → GramLLN R v →
      ScoreLLN R v (popBeta R.μ X Y) → CoefConsistent R v (popBeta R.μ X Y)

/-- **Node M8** (map record 2: "Here E S=0, and individual block means vanish, so
E meat(q)=Var(S) with no deterministic mean-product remainder"). Exact expectation of the
scaled meat at `β`. Suggested route: `AronowAudit.P018.variance_sparse_identity` (proved)
with `s = members`, zero means from `Centered`, disjoint covariances from `G2`; linearity
of `meanMat` over the finite overlap sum; `meanMat_scale`. -/
def M8 : Prop :=
  G2.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → Centered R X Y v →
      ∀ N, 2 ≤ N → meanMat (repeatedLaw R N) (scaledMeatAt R v N (popBeta R.μ X Y)) =
        targetMeat R v (popBeta R.μ X Y) N

/-- **Node M9** (map record 2: "Var((N/D^2) sum_overlap q_d,a q_f,b)=O(1/N)"). Meat law of
large numbers at `β`: each entry is a sum over `Dyad N × Dyad N` of overlap products with
supports `pairSupport` (bounded by `B_q²`); `G3`, the second bound of `G4`
(`N²/D⁴ · 12 N⁵ → 0`), and `G5`. -/
def M9 : Prop :=
  G3.{u} → G4 → G5.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → MeatLLN R v (popBeta R.μ X Y)

/-- **Node M10** (map record 2: "The fitted block-score change is
-sum_t v_dt X_dt X_dt'(beta_hat-beta) ... bounds the normalized fitted-meat change by
C1||beta_hat-beta||+C2||beta_hat-beta||^2, because (N/D^2)|Q_N| stays bounded"). Residual
substitution. Suggested route: `AronowAudit.P018.residual_substitution_bound` (proved),
the first bound of `G4` with `(N/D²) N³ ≤ 16` for `N ≥ 2`, a.e. record bounds from
`RecordRegular` (finite intersection of a.e. sets), and `G6`. -/
def M10 : Prop :=
  G4 → G6.{u} → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R → CoefConsistent R v (popBeta R.μ X Y) →
      SubstitutionNull R v (popBeta R.μ X Y)

/-- **Node M11** (map record 2: "The deterministic normalized score covariance (N/D^2)Var(S)
stays bounded by the N^3 score-covariance count"). Entries of `Var(S)` are bounded by the
diagonal variances (`|cov| ≤ √(Var Var)`), each `≤ 2B_q² N³` by `G3` and `G4`, and
`(N/D²) N³ ≤ 16` for `N ≥ 2` (for `N < 2`, `Dreal N = 0` and `targetMeat = 0`). -/
def M11 : Prop :=
  G3.{u} → G4 → ∀ {U : Type u} [MeasurableSpace U] {k : ℕ} (R : RepeatedKernel U k)
    (X : U → U → Vec k) (Y : U → U → ℝ) (dir : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → Bool)
    (v : ∀ N : ℕ, (d : Dyad N) → Fin (R.T N d) → ℝ) (C : ℝ) (H : Mat k),
    Setting R X Y dir v C H → RecordRegular R →
      ∃ c : ℝ, ∀ N, ‖targetMeat R v (popBeta R.μ X Y) N‖ ≤ c

/-! ## Glue (proved here) -/

theorem Dreal_ne_zero {N : ℕ} (hN : 2 ≤ N) : Dreal N ≠ 0 := by
  unfold Dreal
  have h2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : (N : ℝ) ≠ 0 := by linarith
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  exact div_ne_zero (mul_ne_zero h0 h1) two_ne_zero

/-- Exact rescaling of the fitted sandwich: `N V̂ = (D⁻¹G)⁻¹ ((N/D²) meat) (D⁻¹G)⁻¹`. -/
theorem variance_rescale {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (ω : Fin N → U) (hN : 2 ≤ N) :
    (N : ℝ) • recordWeightedVariance R w ω =
      sandwich ((Dreal N)⁻¹ • recordWeightedGram R w ω)⁻¹
        (((N : ℝ) / (Dreal N) ^ 2) •
          meat members (recordWeightedBlockScore R w (recordWeightedOLS R w ω) ω)) := by
  have hD := Dreal_ne_zero hN
  rw [matrix_inverse_scale_total _ _ (inv_ne_zero hD), inv_inv]
  unfold recordWeightedVariance sandwich
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  field_simp

/-- The corrected target as a sandwich with the scaled score covariance. -/
theorem target_rescale {U : Type u} [MeasurableSpace U] {k N : ℕ} (R : RepeatedKernel U k)
    (w : (d : Dyad N) → Fin (R.T N d) → ℝ) (β : Vec k) (hβ : recordWeightedBeta R w = β) :
    recordWeightedTarget R w =
      sandwich (recordWeightedH R w)⁻¹ (((N : ℝ) / (Dreal N) ^ 2) •
        varMat (repeatedLaw R N) (fun ω => ∑ d : Dyad N, recordWeightedBlockScore R w β ω d)) := by
  unfold recordWeightedTarget sandwich
  rw [hβ]
  simp only [Matrix.smul_mul, Matrix.mul_smul]

/-! ## Assembly -/

/-- **Core assembly.** The nodes give consistency for normalized weights. -/
theorem assemble_core (g1 : G1.{u}) (g2 : G2.{u}) (g3 : G3.{u}) (g4 : G4) (g5 : G5.{u})
    (g6 : G6.{u}) (g7 : G7.{u}) (g8 : G8.{u}) (m0 : M0.{u}) (m1 : M1.{u}) (m2 : M2.{u})
    (m3 : M3.{u}) (m4 : M4.{u}) (m5 : M5.{u}) (m6 : M6.{u}) (m7 : M7.{u}) (m8 : M8.{u})
    (m9 : M9.{u}) (m10 : M10.{u}) (m11 : M11.{u}) : CoreTarget.{u} := by
  intro U _ k R X Y dir v C H hS
  have hP : ∀ N, IsProbabilityMeasure (repeatedLaw R N) := fun N => by
    have := hS.1.1
    unfold repeatedLaw
    infer_instance
  obtain ⟨gAddM, -, gDet, gEqM, -, -⟩ := g6 (repeatedLaw R)
  have hreg := m0 g1 R hS.1
  have hker := m1 R X Y dir v C H hS
  have hmom := m2 g1 R X Y dir v C H hS hker
  have hpop := m3 R X Y dir v C H hS hreg hmom
  have hcent := m4 R X Y dir v C H hS hreg hmom hpop
  have hgram := m5 g3 g4 g5 R X Y dir v C H hS hreg
  have hscore := m6 g3 g4 g5 R X Y dir v C H hS hreg hcent
  have hcoef := m7 g6 g7 R X Y dir v C H hS hpop hgram hscore
  have hsub := m10 g4 g6 R X Y dir v C H hS hreg hcoef
  have hmeat := m9 g3 g4 g5 R X Y dir v C H hS hreg
  have hmeanmeat := m8 g2 R X Y dir v C H hS hreg hcent
  have hTb := m11 g3 g4 R X Y dir v C H hS hreg
  set β := popBeta R.μ X Y with hβdef
  have hHdet : H.det ≠ 0 := hS.2.2.2.2.1.det_pos.ne'
  obtain ⟨gInvDet, gInvProb⟩ := g7 H hHdet
  -- the meat converges to the deterministic target meat
  have hM : inProbability (repeatedLaw R) (fun N ω =>
      scaledMeatAt R v N (recordWeightedOLS R (v N) ω) ω - targetMeat R v β N) := by
    apply gEqM _ _ ⟨2, fun N hN ω => ?_⟩ (gAddM _ _ hsub hmeat)
    rw [hmeanmeat N hN]
    abel
  -- the random bread converges to `H⁻¹`
  have hG : inProbability (repeatedLaw R) (fun N ω => normGram R v N ω - H) := by
    apply gEqM _ _ ⟨0, fun N _ ω => ?_⟩
      (gAddM _ _ hgram (gDet _ (tendsto_sub_nhds_zero_iff.mpr hS.2.2.2.2.2)))
    abel
  have hB := gInvProb (repeatedLaw R) (normGram R v) hG
  have hB0 := gInvDet (fun N => recordWeightedH R (v N)) hS.2.2.2.2.2
  have hsand := g8 (repeatedLaw R) (fun N ω => (normGram R v N ω)⁻¹)
    (fun N ω => scaledMeatAt R v N (recordWeightedOLS R (v N) ω) ω)
    (fun N => (recordWeightedH R (v N))⁻¹) (targetMeat R v β) H⁻¹ hB hB0 hTb hM
  apply gEqM _ _ ⟨2, fun N hN ω => ?_⟩ hsand
  rw [variance_rescale R (v N) ω hN, target_rescale R (v N) β ((hpop.2.1 N hN).2)]
  rfl

/-- **Assembly.** The nodes suffice for the repaired contract: rescale by `a_N`. -/
theorem assemble (g1 : G1.{u}) (g2 : G2.{u}) (g3 : G3.{u}) (g4 : G4) (g5 : G5.{u})
    (g6 : G6.{u}) (g7 : G7.{u}) (g8 : G8.{u}) (m0 : M0.{u}) (m1 : M1.{u}) (m2 : M2.{u})
    (m3 : M3.{u}) (m4 : M4.{u}) (m5 : M5.{u}) (m6 : M6.{u}) (m7 : M7.{u}) (m8 : M8.{u})
    (m9 : M9.{u}) (m10 : M10.{u}) (m11 : M11.{u}) : Target.{u} := by
  intro U _ k R hR _hDir X Y dir hdir hCommon w a ha hw H hH hlim
  obtain ⟨C, hC⟩ := hw
  have hcore := assemble_core g1 g2 g3 g4 g5 g6 g7 g8 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11
    R X Y dir (fun N d t => w N d t / a N) C H ⟨hR, hdir, hCommon, hC, hH, hlim⟩
  have hfun : (fun (N : ℕ) (ω : Fin N → U) =>
      (N : ℝ) • recordWeightedVariance R (w N) ω - recordWeightedTarget R (w N)) =
      (fun (N : ℕ) (ω : Fin N → U) =>
        (N : ℝ) • recordWeightedVariance R (fun d t => w N d t / a N) ω -
        recordWeightedTarget R (fun d t => w N d t / a N)) := by
    funext N ω
    have hv : (fun d t => w N d t / a N) = (fun d t => (a N)⁻¹ * w N d t) := by
      funext d t
      rw [div_eq_inv_mul]
    obtain ⟨-, hvar, htar⟩ := weighted_scale_invariance R (w N) (a N)⁻¹ (inv_pos.mpr (ha N)) ω
    rw [hv, hvar, htar]
  rw [hfun]
  exact hcore

end

end AronowAudit.P018.Wave1.WeightedConsistency
