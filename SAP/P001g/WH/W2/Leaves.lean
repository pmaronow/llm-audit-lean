import SAP.P001g.WH.W2.Elementary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P001g.WH.W2

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

noncomputable section
universe u

/-- Equality for observed probabilities at two disc likelihood maximizers.
Proof: all probabilities are positive by affinePosW2. Take logarithms of the
positive product using Real.log_prod. The log likelihood is concave on the
convex disc. If any observed probability differs at z and v, strict concavity
of log makes the midpoint log likelihood strictly larger than the common
maximum. Use strictConcaveOn_log_Ioi, a finite sum, and the elementary
midpoint-disc inequality. No positive-size assumption is needed: the conclusion
over sample indices is empty at n = 0. Expected size: 120–220 lines. -/
def T121_L1 : Prop :=
  ∀ {n : ℕ} (s : Fin n → Fin 3) (z v : Fin 2 → ℝ),
    z ∈ circleDiscW2 → v ∈ circleDiscW2 →
    IsMaxOn (circleDiscLikeW2 s) circleDiscW2 z →
    IsMaxOn (circleDiscLikeW2 s) circleDiscW2 v →
    ∀ i, circleAffineW2 z (s i) = circleAffineW2 v (s i)

/-- Uniqueness on the disc for a sample containing just one outcome.
Proof: for n > 0 the nth power is strictly increasing on the positive PMF
range, so maximize the affine probability itself. Its nonconstant linear
parts are z₁, z₂-z₁, and -z₂. Their unique maximizing disc points are (1,0),
(-1/√2,1/√2), and (0,-1), respectively. For the middle case use
(z₂-z₁)^2 + (z₁+z₂)^2 = 2(z₁^2+z₂^2), with the equality case; the two other
cases follow from the disc inequality and squares being nonnegative.
affinePosW2 supplies positivity. Expected size: 100–200 lines. -/
def T121_L2 : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (y : Fin 3) (z v : Fin 2 → ℝ),
    z ∈ circleDiscW2 → v ∈ circleDiscW2 →
    IsMaxOn (fun a => circleAffineW2 a y ^ n) circleDiscW2 z →
    IsMaxOn (fun a => circleAffineW2 a y ^ n) circleDiscW2 v → z = v

/-- Explicit derivatives of sample likelihood along both coordinate axes at
the disc origin. Proof: differentiate the finite product of affine factors,
factor out the positive product at zero, and group indices by their outcome
using circleCountW2. The two logarithmic scores are N₀/c₀-N₁/c₁ and
N₁/c₁-N₂/c₂, with the common factor L(0)/10. basePosW2 proves every
denominator nonzero. One can instead differentiate a sum of logarithms and
then exponentiate. This leaf has no maximization premise and applies to
every sample, including all positive sizes. The assembly supplies Fermat's
theorem and the irrationality argument. Expected size: 120–220 lines. -/
def T121_L3 : Prop :=
  ∀ {n : ℕ} (s : Fin n → Fin 3),
    HasDerivAt (fun t : ℝ => circleDiscLikeW2 s (![t, 0] : Fin 2 → ℝ))
      (circleDiscLikeW2 s 0 / 10 *
        ((circleCountW2 s 0 : ℝ) / circleBaseW2 0 -
          (circleCountW2 s 1 : ℝ) / circleBaseW2 1)) 0 ∧
    HasDerivAt (fun t : ℝ => circleDiscLikeW2 s (![0, t] : Fin 2 → ℝ))
      (circleDiscLikeW2 s 0 / 10 *
        ((circleCountW2 s 1 : ℝ) / circleBaseW2 1 -
          (circleCountW2 s 2 : ℝ) / circleBaseW2 2)) 0

/-- Two distinct observed outcomes identify the disc coordinate; if only one
outcome is observed, use the separate affine-functional uniqueness leaf. -/
theorem discMaxUniqueW2 (h1 : T121_L1) (h2 : T121_L2)
    {n : ℕ} (hn : 0 < n) (s : Fin n → Fin 3) (z v : Fin 2 → ℝ)
    (hz : z ∈ circleDiscW2) (hv : v ∈ circleDiscW2)
    (hmz : IsMaxOn (circleDiscLikeW2 s) circleDiscW2 z)
    (hmv : IsMaxOn (circleDiscLikeW2 s) circleDiscW2 v) : z = v := by
  have heq := h1 s z v hz hv hmz hmv
  by_cases htwo : ∃ i j, s i ≠ s j
  · obtain ⟨i, j, hij⟩ := htwo
    exact affineTwoEqualW2 z v (s i) (s j) hij (heq i) (heq j)
  · let i0 : Fin n := ⟨0, hn⟩
    have hs : ∀ i, s i = s i0 := by
      intro i
      by_contra h
      exact htwo ⟨i, i0, h⟩
    have hf : circleDiscLikeW2 s = fun a => circleAffineW2 a (s i0) ^ n := by
      funext a
      simp [circleDiscLikeW2, hs]
    rw [hf] at hmz hmv
    exact h2 n hn (s i0) z v hz hv hmz hmv

/-- The short interior-maximum argument is proved here, leaving only the
explicit finite-product differentiation to the writer. -/
theorem discStationarityW2 (h3 : T121_L3) {n : ℕ} (s : Fin n → Fin 3)
    (hm : IsMaxOn (circleDiscLikeW2 s) circleDiscW2 (0 : Fin 2 → ℝ)) :
    (circleCountW2 s 0 : ℝ) * circleBaseW2 1 =
      (circleCountW2 s 1 : ℝ) * circleBaseW2 0 ∧
    (circleCountW2 s 1 : ℝ) * circleBaseW2 2 =
      (circleCountW2 s 2 : ℝ) * circleBaseW2 1 := by
  have hsmall (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) : t ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith [ht.1] : 0 ≤ t + 1)
      (by linarith [ht.2] : 0 ≤ 1 - t)]
  have hz : (![0, 0] : Fin 2 → ℝ) = 0 := by ext i; fin_cases i <;> rfl
  have hloc0 : IsLocalMax (fun t : ℝ => circleDiscLikeW2 s (![t, 0] : Fin 2 → ℝ)) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0,
      circleDiscLikeW2 s (![t, 0] : Fin 2 → ℝ) ≤ circleDiscLikeW2 s (![0, 0] : Fin 2 → ℝ)
    rw [hz]
    filter_upwards [Ioo_mem_nhds (a := (-1 : ℝ)) (b := 1) (by norm_num) (by norm_num)] with t ht
    exact hm (by simpa [circleDiscW2] using hsmall t ht)
  have hloc1 : IsLocalMax (fun t : ℝ => circleDiscLikeW2 s (![0, t] : Fin 2 → ℝ)) 0 := by
    change ∀ᶠ t : ℝ in 𝓝 0,
      circleDiscLikeW2 s (![0, t] : Fin 2 → ℝ) ≤ circleDiscLikeW2 s (![0, 0] : Fin 2 → ℝ)
    rw [hz]
    filter_upwards [Ioo_mem_nhds (a := (-1 : ℝ)) (b := 1) (by norm_num) (by norm_num)] with t ht
    exact hm (by simpa [circleDiscW2] using hsmall t ht)
  have hpos : 0 < circleDiscLikeW2 s 0 / 10 := by
    apply div_pos _ (by norm_num)
    exact Finset.prod_pos fun i _ => affinePosW2 0 (by norm_num [circleDiscW2]) (s i)
  obtain ⟨hd0, hd1⟩ := h3 s
  have h0 := (mul_eq_zero.mp (hloc0.hasDerivAt_eq_zero hd0)).resolve_left hpos.ne'
  have h1 := (mul_eq_zero.mp (hloc1.hasDerivAt_eq_zero hd1)).resolve_left hpos.ne'
  exact ⟨(div_eq_div_iff (basePosW2 0).ne' (basePosW2 1).ne').mp (sub_eq_zero.mp h0),
    (div_eq_div_iff (basePosW2 1).ne' (basePosW2 2).ne').mp (sub_eq_zero.mp h1)⟩

/-- The origin can never be a disc maximizer at positive sample size. -/
theorem discMaxNonzeroW2 (h3 : T121_L3) {n : ℕ} (hn : 0 < n)
    (s : Fin n → Fin 3) (z : Fin 2 → ℝ)
    (hm : IsMaxOn (circleDiscLikeW2 s) circleDiscW2 z) : z ≠ 0 := by
  intro hz
  subst z
  obtain ⟨h01, h12⟩ := discStationarityW2 h3 s hm
  exact countsNotCriticalW2 (circleCountW2 s) (by rw [countSumW2]; exact hn) h01 h12

/-- Continuous likelihood on the compact disc attains a maximum; its polar
preimage attains the same maximum in the full parameter space. -/
theorem fullAttainmentW2 (n : ℕ) (s : Fin n → Fin 3) :
    ∃ t ∈ circleThetaW2, IsMaxOn (circleLikeW2 s) circleThetaW2 t := by
  obtain ⟨z, hz, hm⟩ := discCompactW2.exists_isMaxOn
    ⟨0, by norm_num [circleDiscW2]⟩ (discLikeContinuousW2 s).continuousOn
  obtain ⟨t, ht, hproj⟩ := projectionSurjectiveW2 z hz
  refine ⟨t, ht, ?_⟩
  intro v hv
  change circleLikeW2 s v ≤ circleLikeW2 s t
  rw [likeProjectionW2, likeProjectionW2, hproj]
  exact hm (projectionMemW2 v hv)

/-- Onto parametrization transfers full-space maximality to the disc. -/
theorem projectedMaxW2 {n : ℕ} (s : Fin n → Fin 3) (t : Fin 3 → ℝ)
    (hm : IsMaxOn (circleLikeW2 s) circleThetaW2 t) :
    IsMaxOn (circleDiscLikeW2 s) circleDiscW2 (circleProjectionW2 t) := by
  intro z hz
  obtain ⟨v, hv, hproj⟩ := projectionSurjectiveW2 z hz
  have h := hm hv
  change circleLikeW2 s v ≤ circleLikeW2 s t at h
  change circleDiscLikeW2 s z ≤ circleDiscLikeW2 s (circleProjectionW2 t)
  simpa only [likeProjectionW2, hproj] using h

/-- The value at n=0 is an arbitrary attained maximum, never a claimed unique
arg max. All positive-size values below will be proved to be unique maxima. -/
def selectedMLEW2 (n : ℕ) (s : Fin n → Fin 3) : Fin 3 → ℝ :=
  Classical.choose (fullAttainmentW2 n s)

theorem selectedMLESpecW2 (n : ℕ) (s : Fin n → Fin 3) :
    selectedMLEW2 n s ∈ circleThetaW2 ∧
      IsMaxOn (circleLikeW2 s) circleThetaW2 (selectedMLEW2 n s) :=
  Classical.choose_spec (fullAttainmentW2 n s)

/-- With the three analytic leaves, the attained maximum is the book's
everywhere unique arg max on every positive-size sample. -/
theorem selectedMLEUniqueW2 (h1 : T121_L1) (h2 : T121_L2) (h3 : T121_L3) :
    CircleMLEW2 selectedMLEW2 := by
  intro n s
  obtain ⟨ht, hm⟩ := selectedMLESpecW2 n s
  refine ⟨ht, hm, ?_⟩
  intro hn v hv heq
  have hmv : IsMaxOn (circleLikeW2 s) circleThetaW2 v := by
    intro w hw
    rw [heq]
    exact hm hw
  have hmt' := projectedMaxW2 s _ hm
  have hmv' := projectedMaxW2 s v hmv
  have hproj := discMaxUniqueW2 h1 h2 hn s _ _
    (projectionMemW2 v hv) (projectionMemW2 _ ht) hmv' hmt'
  exact projectionInjectiveW2 v _ hv ht hproj (discMaxNonzeroW2 h3 hn s _ hmv')

/-- The same i.i.d. law at two distinct true full vectors rules out universal
consistency. The estimator supplied to the asserted theorem is unique on
every sample of every positive size, by the three analytic leaves. -/
theorem T121_assembly (h1 : T121_L1) (h2 : T121_L2) (h3 : T121_L3) :
    T121WholeStatement.{u} := by
  intro h
  let μ := AronowAudit.P001.PrintedConfidence.liftStreamLaw.{u} baseLawW2
  let X : ℕ → (ℕ → ULift.{u} (Fin 3)) → Fin 3 :=
    AronowAudit.P001.PrintedConfidence.streamObservation
  have hiid : IID μ X := (AronowAudit.P001.PrintedConfidence.lift_stream_iid.{u} baseLawW2).1
  have hlaw : μ.map (X 0) = baseLawW2 :=
    (AronowAudit.P001.PrintedConfidence.lift_stream_iid.{u} baseLawW2).2
  have hmle := selectedMLEUniqueW2 h1 h2 h3
  have ha := h μ X hiid (![1, 0] : Fin 2 → ℝ)
    (by norm_num [circleBoundaryW2])
    (by simpa only [mixTrueW2, baseLawW2] using hlaw) selectedMLEW2 hmle
  have hb := h μ X hiid (![-1, 0] : Fin 2 → ℝ)
    (by norm_num [circleBoundaryW2])
    (by simpa only [mixTrueW2, baseLawW2] using hlaw) selectedMLEW2 hmle
  have heq := AronowAudit.P001.probability_limit_unique μ _ _ _ ha hb
  have hc := congrFun heq 1
  norm_num [circleTruthW2] at hc

end
end SAP.P001g.WH.W2
