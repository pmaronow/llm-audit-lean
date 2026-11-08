import SAP.P025b.Defs.WholeW1
import SAP.P025b.WH.W1.Retained
import SAP.P025b.Bridge
import AronowAudit.P025.P025_Interval

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P025b.WH.W1
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

/-- Binary class counts, normalized weight sums, and their pointwise bounds.
Split on each binary outcome to identify filtered sums with sums against y and
1-y. Use normalize_box, ratio_scale_weights, and sum_le_sum. The count identities
follow by taking constant unit weights and multiplying the sample mean by n.
No strict bound on p or on the ratio of probability bounds is needed.
-/
def T20_L1 : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ y : Fin n → ℝ, (∀ i, y i = 0 ∨ y i = 1) →
    ∀ α β : ℝ, 0 < α → α ≤ β → β ≤ 1 →
    let p := populationMean y
    let γ := β/α
    ((Finset.univ.filter (fun i => y i = 1)).card : ℝ) = n*p ∧
    ((Finset.univ.filter (fun i => y i = 0)).card : ℝ) = n*(1-p) ∧
    ∀ w : Fin n → ℝ, weightBox α β w →
      let A := binaryClassSum y w β 1
      let C := binaryClassSum y w β 0
      normBox γ (fun i => β*w i) ∧
      ratio y (fun _ => 1) w = A/(A+C) ∧
      (n*p ≤ A ∧ A ≤ γ*(n*p)) ∧
      (n*(1-p) ≤ C ∧ C ≤ γ*(n*(1-p))) ∧
      (n : ℝ) ≤ A+C ∧ 0 < A+C

/-- Class sums for arbitrary physical weights on the actual pooled pair sample.
Use pair_pooled_ratio to remove unsampled units. Swap the replicate and class
sums and expand the three outcomes to obtain the numerator and denominator.
Sum the pointwise box bounds to bound each A; positivity follows from h>0.
Scaling by 1/h gives the normalized ratio and its feasible class weight vector.
-/
def T14_L1 : Prop :=
  ∀ h : ℕ, 0 < h → ∀ ω : ℕ → Fin 2 × Fin 2 × Fin 2,
    ∀ w : Fin h × (Fin 3 × Fin 2) → ℝ, weightBox (1/4) (1/2) w →
      let A := pairClassWeightSum h ω w
      (∀ j, 2*(h : ℝ) ≤ A j ∧ A j ≤ 4*(h : ℝ)) ∧
      0 < A 0+A 1+A 2 ∧
      ratio (fun ri => threeOutcomes ri.2.1) (pooledIndicator pairDesign h ω) w =
        (2*A 1+3*A 2)/(A 0+A 1+A 2) ∧
      (2*A 1+3*A 2)/(A 0+A 1+A 2) =
        ratio threeOutcomes (fun _ => 1) (fun j => A j/h) ∧
      weightBox (1/4) (1/2) (fun j => A j/h)

/-- Any finite vector of probabilities in [0,1] is realized by a sampling law.
Use independent Bernoulli coordinates on the finite Boolean function space:
the probability of a draw is the product of p or 1-p in each coordinate. The
two-point laws normalize; product_design_coordinate_mean computes each marginal.
The sample contains exactly the coordinates whose Boolean draw is true.
This includes p=0, p=1, and the empty population.
-/
def T15_L1 : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (p : ι → ℝ),
    (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
    ∃ d : FiniteDesign ι (ι → Bool),
      (∀ ω, d.sample ω = Finset.univ.filter (fun i => ω i = true)) ∧
      (∀ ω, d.probability ω = ∏ i, if ω i then p i else 1-p i) ∧
      ∀ i, inclusion d i = p i

/-- With the stated shares and bounds, a compatible population of size three
has exactly one zero and two ones. Unpack Tq compatibility: positivity and the
sum three leave only counts (1,2) and (2,1); the second contradicts the class
bounds on T. The first is witnessed by T=2. Use integer arithmetic on the two
counts and linear real arithmetic on T; no approximation is involved.
-/
def T15_L2 : Prop :=
  ∀ m : Fin 2 → ℕ, (∑ j, m j) = 3 →
    (sharesCompatible (1/2) (3/4) ![1/3,2/3] m ↔ m = ![1,2])

/-- A uniform quota draw is a genuine finite sampling design with marginal s/N.
The draw type is the subtype of subsets of size s, and its probability is the
reciprocal of its finite cardinality. quota_design_valid proves nonemptiness
and normalization; convert its finite-set sums to subtype sums. Then
quota_marginal_eq proves the marginal by counting the subsets containing i.
The positive quota and s≤N ensure the draw type and denominator are nonempty.
-/
def T16_L1 : Prop :=
  ∀ N s : ℕ, 0 < s → s ≤ N →
    ∃ d : FiniteDesign (Fin N) (QuotaDraw N s),
      (∀ ω, d.sample ω = ω.val) ∧
      (∀ ω, d.probability ω = 1/(Fintype.card (QuotaDraw N s) : ℝ)) ∧
      ∀ i, inclusion d i = (s : ℝ)/N

/-- The independent product sampling law preserves each summand's marginals.
Expand sumDesign, inclusion and designExpectation. Membership in the disjoint
union reduces to membership in the appropriate sample. Factor the finite
product sum and use the other law's total probability one. No nonempty
population assumption is needed, and the design structures ensure valid laws.
-/
def T16_L2 : Prop :=
  ∀ {n₀ n₁ : ℕ} {κ κ' : Type} [Fintype κ] [Fintype κ']
    (d : FiniteDesign (Fin n₀) κ) (e : FiniteDesign (Fin n₁) κ'),
    (∀ i, inclusion (sumDesign d e) (Sum.inl i) = inclusion d i) ∧
    (∀ i, inclusion (sumDesign d e) (Sum.inr i) = inclusion e i)

/-- The product replication experiment has precisely the paper's iid law. -/
theorem replications_iid {ι κ : Type*} [Fintype κ] [MeasurableSpace κ]
    (d : FiniteDesign ι κ) : ReplicationsIID d := by
  exact AronowAudit.P025.joint_replications_iid (Bridge.toAudit d)

/-- All missing boundary-example clauses are finite specializations. -/
theorem T12_assembly : T12WholeStatement := by
  have hi : ∀ i : Fin 2, inclusion censusDesign i = 1 := retained_T12.1
  have hc : classTotal censusDesign id = fun _ => 1 := by
    funext j
    classical
    simp only [classTotal, Finset.sum_filter, Fin.sum_univ_two, hi, id_eq]
    fin_cases j <;> norm_num
  have hvec : (![1,1] : Fin 2 → ℝ) = fun _ => 1 := by
    ext i; fin_cases i <;> norm_num
  obtain ⟨hb, hl, hu⟩ := AronowAudit.P025.equal_probability_box_and_endpoints
    (by norm_num : 0 < 2) binaryTwo 1 1 (by norm_num) le_rfl le_rfl (by norm_num)
  have hmean : populationMean binaryTwo = 1/2 := by
    norm_num [populationMean, binaryTwo, Fin.sum_univ_two]
  have hlow : lowerEndpoint binaryTwo (fun _ => 1) 1 1 = 1/2 := hl.trans hmean
  have hhigh : upperEndpoint binaryTwo (fun _ => 1) 1 1 = 1/2 := hu.trans hmean
  refine ⟨retained_T12, ?_, ?_, hmean, ?_, ?_, ?_, ?_, hlow, hhigh,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [hvec]
    simp only [weightBox, one_div_one]
    constructor
    · intro hw; funext i; exact le_antisymm (hw i).2 (hw i).1
    · rintro rfl i; exact ⟨le_rfl, le_rfl⟩
  · have hs := (AronowAudit.P025.ratio_only_and_equal_probabilities
      (by norm_num : 0 < 2) binaryTwo 1 1 1 1 (by norm_num) le_rfl le_rfl
      (by norm_num) le_rfl le_rfl rfl).2 (by norm_num)
    exact hs.trans (congrArg Set.singleton hmean)
  · norm_num [classMean, binaryTwo, Fin.sum_univ_two]
  · intro j; exact congrFun hc j
  · intro j ω
    simp [classCount, censusDesign]
  · intro j; rw [congrFun hc j]; norm_num
  · rw [hc]; exact hlow
  · rw [hc]; exact hhigh
  · ext i; fin_cases i <;> norm_num [upperWeights]
  all_goals norm_num [twoCoordinateMean]

/-- The binary monotonicity arguments have positive denominators even at p=0,1. -/
theorem T20_assembly (h1 : T20_L1) : T20WholeStatement := by
  refine ⟨retained_T20, ?_⟩
  intro n hn y hy α β hα hab hb
  obtain ⟨hc1, hc0, hpoint⟩ := h1 hn y hy α β hα hab hb
  dsimp only
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : 0 ≤ (n : ℝ)*populationMean y := hc1 ▸ Nat.cast_nonneg _
  have hpos (a c : ℝ) (ha : a ∈ Set.Icc ((n : ℝ)*populationMean y)
      ((β/α)*((n : ℝ)*populationMean y)))
      (hc : c ∈ Set.Icc ((n : ℝ)*(1-populationMean y))
        ((β/α)*((n : ℝ)*(1-populationMean y)))) : 0 < a+c := by
    linarith [ha.1, hc.1]
  refine ⟨hc1, hc0, hpoint, hpos, ?_, ?_⟩
  · intro a a' c ha ha' hc haa'
    apply (div_le_div_iff₀ (hpos a c ha hc) (hpos a' c ha' hc)).mpr
    have hc0' : 0 ≤ c := by
      have hz : (0 : ℝ) ≤ n*(1-populationMean y) := hc0 ▸ Nat.cast_nonneg _
      exact hz.trans hc.1
    nlinarith [mul_nonneg hc0' (sub_nonneg.mpr haa')]
  · intro a c c' ha hc hc' hcc'
    exact div_le_div_of_nonneg_left (hp.trans ha.1) (hpos a c ha hc)
      (by linarith)

/-- The displayed polynomial certificates require only ring arithmetic. -/
theorem pair_polynomial_certificates : PairPolynomialCertificates := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro W hW
    dsimp only
    have h0 := hW 0; have h1 := hW 1; have h2 := hW 2
    norm_num at h0 h1 h2
    have hd : 0 < W 0+W 1+W 2 := by linarith
    refine ⟨hd, by ring, by linarith, by ring, by linarith, ?_, ?_⟩
    · apply (le_div_iff₀ hd).mpr; linarith
    · apply (div_le_iff₀ hd).mpr; linarith
  all_goals norm_num [ratio, threeOutcomes, Fin.sum_univ_three]

/-- The remaining pooled clauses are counts and a class-constant right inverse. -/
theorem T14_assembly (h1 : T14_L1) : T14WholeStatement := by
  refine ⟨retained_T14, replications_iid pairDesign, pair_polynomial_certificates, ?_, ?_⟩
  · intro j
    fin_cases j <;> decide
  · intro h hh ω
    refine ⟨?_, h1 h hh ω, ?_⟩
    · intro j
      simp_rw [retained_T14.2.2.1]
      simp
    · intro W hW
      refine ⟨fun ri => W ri.2.1, fun ri => hW ri.2.1, ?_⟩
      intro j
      have hhR : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
      simp [pairClassWeightSum, hhR]

/-- Positive rescaling preserves the entire attainable set. -/
theorem attainable_scale {J : ℕ} (y q : Fin J → ℝ) (α β T : ℝ) (hT : T ≠ 0) :
    attainable y (fun j => T*q j) α β = attainable y q α β := by
  have he (W : Fin J → ℝ) : ratio y (fun j => T*q j) W = ratio y q W :=
    AronowAudit.P025.ratio_scale_masses y q W T hT
  ext v
  constructor
  · rintro ⟨W, hW, hv⟩
    exact ⟨W, hW, (he W).symm.trans hv⟩
  · rintro ⟨W, hW, hv⟩
    exact ⟨W, hW, (he W).trans hv⟩

/-- The compatibility parentheticals follow from the existing density and region results. -/
theorem compatibility_existence : CompatibilityExistence := by
  intro J hJ q hq hsum α β hα hab hb
  have hγ : 1 ≤ β/α := (le_div_iff₀ hα).mpr (by simpa using hab)
  have hregion : proportionRegion q (β/α) q := by
    refine ⟨fun j => (hq j).le, hsum, ?_⟩
    intro j k
    nlinarith [mul_pos (hq j) (hq k)]
  constructor
  · intro hstrict
    have hcone : q ∈ AronowAudit.P025.strictSelectionCone q (β/α) := by
      refine ⟨hq, ?_⟩
      intro j k
      nlinarith [mul_pos (hq j) (hq k)]
    obtain ⟨a, hrat, ha⟩ := AronowAudit.P025.rational_vectors_dense.exists_mem_open
      (AronowAudit.P025.strict_selection_cone_open q (β/α)) ⟨q, hcone⟩
    obtain ⟨m, hm, _⟩ := AronowAudit.P025.rational_cone_mean_compatible
      hJ (fun _ => 0) q a hq α β hα hab ha hrat
    exact ⟨m, hm⟩
  · intro heq
    constructor
    · rintro ⟨m, hm⟩
      obtain ⟨hr, hrat⟩ := AronowAudit.P025.compatible_proportions_necessary
        hJ q hq α β hα hab m hm
      change proportionRegion q (β/α) (classProportions m) at hr
      change rationalVector (classProportions m) at hrat
      have he : classProportions m = q := by
        funext j
        apply le_antisymm
        · have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hr.2.2 j k)
          simpa only [heq, one_mul, ← Finset.mul_sum, ← Finset.sum_mul,
            hsum, hr.2.1, mul_one, one_mul] using hs
        · have hs := Finset.sum_le_sum (s := Finset.univ) (fun k _ => hr.2.2 k j)
          simpa only [heq, one_mul, ← Finset.mul_sum, ← Finset.sum_mul,
            hsum, hr.2.1, mul_one, one_mul] using hs
      rwa [he] at hrat
    · intro hrat
      obtain ⟨m, hm, _⟩ := AronowAudit.P025.rational_region_has_compatible_sizes
        hJ q q hq α β hα hab hregion hrat
      exact ⟨m, hm⟩

end
end SAP.P025b.WH.W1
