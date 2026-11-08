import SAP.P009b.Defs.WholeW1
import SAP.P009b.Bridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators Topology
open Filter

namespace SAP.P009b.WH.W1

universe u
noncomputable section
attribute [local instance] Classical.propDecidable

/-- T27, finite Bernoulli prefixes using only overlap, without outcome moments.
Use BernoulliCompletion.probability_fixed_coordinates on the coordinates with
index less than b; extend a by false outside that prefix. The marginal
partition identity gives the same overlap bounds in the false arm. Bound the
product by the constant products using Finset.prod_le_prod₀ and identify the
coordinate count by Fin.card_filter_val_lt. The empty prefix is included. -/
def T27_L1 : Prop :=
  ∀ {n : ℕ} (E : Experiment n) (k : ℝ) (_hk : 0 < k) (_hBER : Bernoulli E)
    (_hMarg : ∀ i, k⁻¹ ≤ marginal E i true ∧ marginal E i true ≤ 1-k⁻¹)
    (b : ℕ) (hb : b ≤ n) (a : Assignment b),
    k⁻¹^b ≤ prob E.design (fun z => wholePrefix hb z = a) ∧
    prob E.design (fun z => wholePrefix hb z = a) ≤ (1-k⁻¹)^b

/-- T27, normalization, lower bounds and concentration of the explicit heavy law.
Separate the distinguished all-false point in the finite sum; there are 2^b
cube points. The outside mass is (2^b-1)/4^b, between zero and (1/2)^b.
Use 4^b=(2^b)^2 and positivity for the lower bound at the distinguished
point, and squeeze the outside mass to zero by geometric decay. This includes
b=0: the single distinguished point has mass one. -/
def T27_L2 : Prop :=
  (∀ b : ℕ, (∀ z : Assignment b, ((4 : ℝ)^b)⁻¹ ≤ wholeHeavyMass b z) ∧
    (∑ z : Assignment b, wholeHeavyMass b z) = 1) ∧
  Tendsto (fun b => wholeHeavyMass b (fun _ => false)) atTop (nhds 1)

/-- T27, a concentrating atom prevents two disjoint positive limiting masses.
For any real-valued maps (even without the ternary restriction), at least one
of the events f=1 and f=-1 omits the distinguished point. Its probability is
at most one minus that point's mass, by finite_probability_mono and
probability_complement. If both masses tended to c>0, eventually both would
exceed c/2 while the outside mass is less than c/2, a contradiction. -/
def T27_L3 : Prop :=
  ∀ P : (b : ℕ) → Law (Assignment b),
    Tendsto (fun b => (P b).mass (fun _ => false)) atTop (nhds 1) →
    ∀ c : ℝ, 0 < c → ∀ f : (b : ℕ) → Assignment b → ℝ,
    ¬ (Tendsto (fun b => prob (P b) (fun z => f b z = 1)) atTop (nhds c) ∧
       Tendsto (fun b => prob (P b) (fun z => f b z = -1)) atTop (nhds c))

/-- Finite minimization is glue: encode the three values by Fin 3, minimize on
that finite function type, and recode every real-valued ternary competitor. -/
private theorem finite_three_point_minimum {Ω : Type*} [Fintype Ω]
    (objective : (Ω → ℝ) → ℝ) :
    ∃ f : Ω → ℝ, wholeThreeValued f ∧
      ∀ g : Ω → ℝ, wholeThreeValued g → objective f ≤ objective g := by
  obtain ⟨v, hv⟩ := Finite.exists_min
    (fun v : Ω → Fin 3 => objective (fun ω => sharpValue (v ω)))
  have hs : ∀ j : Fin 3, sharpValue j = -1 ∨ sharpValue j = 0 ∨ sharpValue j = 1 := by
    intro j
    fin_cases j <;> simp [sharpValue]
  refine ⟨fun ω => sharpValue (v ω), fun ω => hs (v ω), ?_⟩
  intro g hg
  let w : Ω → Fin 3 := fun ω => if g ω = -1 then 0 else if g ω = 0 then 1 else 2
  have hw : (fun ω => sharpValue (w ω)) = g := by
    funext ω
    rcases hg ω with h | h | h <;> norm_num [w, h, sharpValue]
  simpa only [hw] using hv w

/-- T27 assembly: the existing approximation and minimizer theorems supply the
error and endpoint limits; the new leaves restore the precise finite scope
and the example that explains the correction. -/
theorem T27_assembly (h1 : T27_L1) (h2 : T27_L2) (h3 : T27_L3) :
    T27WholeStatement.{u} := by
  have hmin : ∀ {n b : ℕ} (E : Experiment n) (α : ℝ) (hb : b ≤ n),
      ∃ f : Assignment b → ℝ, wholePrefixMinimizer E α hb f := by
    intro n b E α hb
    exact finite_three_point_minimum
      (fun f => approximationError E.design α (fun z => f (wholePrefix hb z)))
  refine ⟨?_, Bridge.T27Approximation_transport
    (@AronowAudit.P009.three_point_atom_approximation), hmin, ?_, ?_⟩
  · intro n E k hk hBER hMarg b hb
    have hatom := h1 E k hk hBER hMarg b hb
    have hs : {a : Assignment b | 0 < prob E.design (fun z => wholePrefix hb z = a)} =
        Set.univ := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (pow_pos (inv_pos.mpr hk) b).trans_le (hatom a).1
    refine ⟨hatom, hs, ?_⟩
    rw [hs]
    simp [Set.ncard_univ, Nat.card_eq_fintype_card,
      Fintype.card_fin, Fintype.card_bool]
  · intro S k q s α hReg hBER hα b hb hbInfinity
    have hex : ∃ f : (t : ℕ) → Assignment (b t) → ℝ,
        ∀ t, wholePrefixMinimizer (S.experiment t) α (hb t) (f t) := by
      choose f hf using fun t => hmin (S.experiment t) α (hb t)
      exact ⟨f, hf⟩
    have hk := (hReg 0).1
    have hk2 := AronowAudit.P009.BernoulliCompletion.regular_k_ge_two
      (S.positive 0) (Bridge.toExperiment (S.experiment 0)) k q s (hReg 0)
    have hlo : 0 ≤ 1-k⁻¹ := by
      have hi : k⁻¹ ≤ 1 := (inv_le_one₀ hk).mpr (by linarith)
      linarith
    have hhi : 1-k⁻¹ < 1 := by linarith [inv_pos.mpr hk]
    refine ⟨hex, (tendsto_pow_atTop_nhds_zero_of_lt_one hlo hhi).comp hbInfinity, ?_⟩
    intro f hf
    exact (Bridge.T27Minimizer_transport
      (@AronowAudit.P009.corrected_three_point_minimizer))
      S k q s α hReg hBER hα b hb hbInfinity f (fun t => (hf t).1)
        (fun t => (hf t).2)
  · let P : (b : ℕ) → Law (Assignment b) := fun b =>
      { mass := wholeHeavyMass b
        nonneg := fun z => (by positivity : 0 ≤ ((4 : ℝ)^b)⁻¹).trans ((h2.1 b).1 z)
        total := (h2.1 b).2 }
    refine ⟨P, fun _ _ => rfl, fun b => (h2.1 b).1, h2.2, ?_⟩
    intro α hα f _hf
    exact h3 P h2.2 (α/2) (by linarith [hα.1]) f

/-- T18, the missing vector/count ratio identity, including a positive count
probability and r=0. Put H=t18_others E i and t=t18_countOn H w. The count
and vector events depend only on H, and each fixes the same count. Obtain
positivity of the count mass from t18_complete_finset_count and
t18_hypergeom_pos. Apply t18_event_deviation to both events and cancel the
common subtraction of one. t18_masked_congr and t18_masked_count justify the
event hypotheses; t18_countIncoming identifies the package count. No division
by r is used, so the empty incoming-others set needs no separate leaf. -/
def T18_L1 : Prop := wholeVectorCountRatio

/-- The old core already contains every scalar link and the supported-vector
bound. Its first hypergeometric law gives the missing sure zero-count fact. -/
theorem T18_assembly (h1 : T18_L1) : T18WholeStatement := by
  have h : T18CoreStatement := Bridge.T18Core_transport
    (@AronowAudit.P009.Wave1.corrected_hypergeometric_proof)
  refine ⟨h, ?_, h1⟩
  intro n E m hCR i hc hz
  have h0 := (h E m hCR i hc).1 0 (Nat.zero_le _)
  rw [hz] at h0
  simpa [hypergeomMass] using h0

/-- T20, indicator versus witness counts for arbitrary binary arrays. The
pairing map is arbitrary here: involutivity and reflexivity are only needed
by the parent claim, not by this local bound. Split wholeArrayD into zero or
one; when e=1 choose its witness and use Finset.single_le_sum, since every
product is nonnegative. For the second inequality split d again. This is the
array version of the pointwise portion of corrected_pair_dependence. -/
def T20_L1 : Prop :=
  ∀ {n : ℕ} (J : Fin n → Fin n → ℝ)
    (_hJ : ∀ i j, J i j = 0 ∨ J i j = 1) (ρ : Fin n → Fin n),
    (∀ i j, wholeArrayE J ρ i j ≤
      ∑ ℓ, (1-wholeArrayD J i j)*J ℓ i*J (ρ ℓ) j) ∧
    (∀ i j, (∑ ℓ, (1-wholeArrayD J i j)*J ℓ i*J (ρ ℓ) j) ≤
      ∑ ℓ, J ℓ i*J (ρ ℓ) j)

/-- T20 assembly: commute and factor sums, sum the elementary square
inequality, and reindex by the permutation furnished by the involution. -/
theorem T20_assembly (h1 : T20_L1) : T20WholeStatement := by
  have hy : ∀ x y : ℝ, 2*x*y ≤ x^2+y^2 := by
    intro x y
    nlinarith [sq_nonneg (x-y)]
  refine ⟨hy, ?_⟩
  intro n hn J hJ _hdiag ρ hρ
  dsimp only
  let c := wholeArrayC J
  have hp := h1 J hJ ρ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : (∑ i, ∑ j, ∑ ℓ, J ℓ i*J (ρ ℓ) j) = ∑ ℓ, c ℓ*c (ρ ℓ) := by
    calc
      _ = ∑ i, ∑ ℓ, ∑ j, J ℓ i*J (ρ ℓ) j := by
        apply Finset.sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = ∑ ℓ, ∑ i, ∑ j, J ℓ i*J (ρ ℓ) j := Finset.sum_comm
      _ = _ := by simp only [← Finset.mul_sum, ← Finset.sum_mul, c, wholeArrayC]
  have havg : wholeArrayEAvg J ρ ≤
      (∑ i, ∑ j, ∑ ℓ, J ℓ i*J (ρ ℓ) j)/(n : ℝ) := by
    apply div_le_div_of_nonneg_right _ hnR.le
    exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
      (fun j _ => (hp.1 i j).trans (hp.2 i j)))
  have hs : 2*(∑ ℓ, c ℓ*c (ρ ℓ)) ≤ ∑ ℓ, (c ℓ^2+c (ρ ℓ)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ℓ _
    nlinarith [hy (c ℓ) (c (ρ ℓ))]
  have hpair : (∑ ℓ, c ℓ*c (ρ ℓ))/(n : ℝ) ≤
      (∑ ℓ, (c ℓ^2+c (ρ ℓ)^2))/(2*(n : ℝ)) := by
    apply (div_le_div_iff₀ hnR (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hs hnR.le]
  have hsplit : (∑ ℓ, (c ℓ^2+c (ρ ℓ)^2))/(2*(n : ℝ)) =
      (∑ ℓ, c ℓ^2)/(2*(n : ℝ))+(∑ ℓ, c (ρ ℓ)^2)/(2*(n : ℝ)) := by
    rw [Finset.sum_add_distrib, add_div]
  have hperm : (∑ ℓ, c (ρ ℓ)^2) = ∑ ℓ, c ℓ^2 :=
    Equiv.sum_comp hρ.toPerm (fun ℓ => c ℓ^2)
  have hhalf : (∑ ℓ, c ℓ^2)/(2*(n : ℝ))+(∑ ℓ, c (ρ ℓ)^2)/(2*(n : ℝ)) =
      (∑ ℓ, c ℓ^2)/(n : ℝ) := by
    rw [hperm]
    ring
  have hsqrt : (∑ ℓ, c ℓ^2)/(n : ℝ) = wholeArrayC2 J ^ 2 := by
    exact (Real.sq_sqrt (div_nonneg (Finset.sum_nonneg
      (fun ℓ _ => sq_nonneg (c ℓ))) hnR.le)).symm
  refine ⟨hp.1, hp.2, rfl, havg, congrArg (fun x : ℝ => x/(n : ℝ)) ht,
    hpair, hsplit, hperm, hhalf, hsqrt, ?_⟩
  calc
    wholeArrayEAvg J ρ ≤ _ := havg
    _ = (∑ ℓ, c ℓ*c (ρ ℓ))/(n : ℝ) := congrArg (fun x : ℝ => x/(n : ℝ)) ht
    _ ≤ _ := hpair
    _ = _ := hsplit
    _ = _ := hhalf
    _ = wholeArrayC2 J ^ 2 := hsqrt

/-- The negative-order refutation is a two-point rational computation, so it
needs no unproved leaf. Strict positivity guards all its real powers. -/
theorem T29_assembly : T29WholeStatement := by
  norm_num [T29WholeStatement, wholeReciprocalExperiment, Bernoulli, Regular,
    marginal, prob, cov, mean, potential, fairExperiment, fairLaw,
    AronowAudit.P009.sum_cube_succ, AronowAudit.P009.sum_cube_zero,
    Fintype.sum_bool, Fin.forall_fin_one, Real.rpow_neg_one, Real.rpow_neg]

/-- The diagonal independence refutation uses the explicit regular two-unit
paired law and its fair marginal. No new probability lemma is required. -/
theorem T34_assembly : T34WholeStatement := by
  let E := wholeTwoPairedExperiment
  have hPair : Paired E wholeTwoPairing := by
    refine ⟨by decide, ?_⟩
    intro z
    have hz : z = ![z 0, z 1] := by
      funext i
      fin_cases i <;> rfl
    cases h0 : z 0 <;> cases h1 : z 1 <;>
      simp only [h0, h1] at hz <;> rw [hz] <;>
      norm_num [E, wholeTwoPairedExperiment, wholeTwoPairedLaw,
        wholeTwoPairing, Fin.forall_fin_two, funext_iff]
  have hmarg (i : Fin 2) (b : Bool) : marginal E i b = 1/2 :=
    AronowAudit.P009.PairedCompletion.marginal_half
      (Bridge.toExperiment E) (Bridge.toPairing wholeTwoPairing) hPair i b
  have hReg : Regular E 2 2 1 := by
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      rw [hmarg]
      norm_num
    · intro i
      norm_num [mean, E, wholeTwoPairedExperiment]
    · intro i b
      norm_num [mean, potential, E, wholeTwoPairedExperiment]
  have hjoint : prob E.design (fun z => z 0 = true ∧ z 0 = true) = 1/2 := by
    simpa only [and_self, marginal] using hmarg 0 true
  change Paired E wholeTwoPairing ∧ _
  refine ⟨hPair, hReg, ?_, hmarg 0 true, hjoint, ?_, ?_⟩
  · decide
  · rw [hmarg]
    norm_num
  · rw [hjoint, hmarg]
    norm_num

end
end SAP.P009b.WH.W1
