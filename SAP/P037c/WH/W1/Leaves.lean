import SAP.P037c.Defs.WholeW1
import SAP.P037c.WH.W1.Existing
import SAP.P037c.WH.W1.Algebra
import SAP.P037c.WH.W1.Controls
import SAP.P037c.Bridge
import AronowAudit.P037.P037_Review
import AronowAudit.P037.P037_FiniteDesign

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P037c.WH.W1
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Four-block support cardinality. Prove a bijection between supported flattened sets
and Fin 4 → {s // s ∈ pairedSupport}, taking the fiber at each block and flattening
by disjoint union. Use the existing one-block cardinality and Fintype.card_fun.
Do not enumerate 252^4 sets. This is the only missing combinatorial step for T35. -/
def T35_L1 : Prop := whole35Support.card = 252^4

/-- Positive weighted least squares has a unique fitted vector, even with aliased
columns. Apply minimality to the midpoint of two minimizers; the quadratic identity
forces sum_i w_i (H a_i - H b_i)^2 = 0, and positivity forces coordinatewise equality.
No coefficient-rank assumption or existence premise beyond the two minimizers is needed. -/
def T34_L1 : Prop :=
  ∀ (n p : ℕ) (H : Matrix (Fin n) (Fin p) ℝ) (w y : Fin n → ℝ),
    (∀ i, 0 < w i) → ∀ a b,
      regressionMinimum w H y a → regressionMinimum w H y b → H.mulVec a = H.mulVec b

/-- Every finite real design space admits a full-rank matrix basis, including the
zero-dimensional space. Use Module.finBasis for LinearMap.range H.mulVecLin,
include its basis vectors into the ambient coordinate space, and use linear
independence and spanning to show injectivity and equality of column spaces. -/
def T34_L2 : Prop :=
  ∀ (n p : ℕ) (H : Matrix (Fin n) (Fin p) ℝ),
    ∃ (q : ℕ) (B : Matrix (Fin n) (Fin q) ℝ),
      Function.Injective B.mulVec ∧ wholeColumnSpace B = wholeColumnSpace H

private theorem whole35_frozen_outcomes :
    whole35Outcome (whole35Side false) =
      (fun i : Whole35Student => if i.2.2 = false then (1:ℝ) else 0) := by
  funext ⟨h,b,t⟩
  cases t <;> simp [whole35Outcome, whole35Side]

private theorem whole35_frozen_stat (z : Finset Whole35Student) :
    whole35Statistic z (whole35Outcome (whole35Side false)) =
      AronowAudit.P037.Wave1.t35r2_four_stat z := by
  rw [whole35_frozen_outcomes]
  rfl

/-- Assembly of the original one-block certificate and the actual normalized four-block law. -/
theorem T35_assembly (h1 : T35_L1) : T35WholeStatement := by
  have hcard : whole35Support.card = 252^4 := h1
  have hc (z : Finset Whole35Student) (hz : z ∈ whole35Support) : z.card = 20 :=
    AronowAudit.P037.Wave1.t35r2_four_supported_card z hz
  have hbound (z : Finset Whole35Student) :
      |whole35Statistic z (whole35Outcome (whole35Side false))| ≤ 1 := by
    rw [whole35_frozen_stat, AronowAudit.P037.Wave1.t35r2_four_stat_card]
    have hu := Finset.card_le_card (s := z ∩ whole35Side true) Finset.inter_subset_right
    have hs : (whole35Side true).card = 20 :=
      AronowAudit.P037.Wave1.t35r2_four_side_card true
    rw [hs] at hu
    have hu' : ((z ∩ whole35Side true).card:ℝ) ≤ 20 := by exact_mod_cast hu
    have hl : (0:ℝ) ≤ (z ∩ whole35Side true).card := Nat.cast_nonneg _
    change |(2 * ((z ∩ whole35Side true).card:ℝ) - 20) / 20| ≤ 1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hobs : whole35Statistic (whole35Side false)
      (whole35Outcome (whole35Side false)) = -1 := by
    rw [whole35_frozen_stat, AronowAudit.P037.Wave1.t35r2_four_stat_card]
    have hd : whole35Side false ∩ whole35Side true = ∅ :=
      AronowAudit.P037.Wave1.t35r2_four_sides_disjoint
    change (2 * ((whole35Side false ∩ whole35Side true).card:ℝ) - 20) / 20 = -1
    rw [hd]
    norm_num
  have htail : (whole35Support.filter (fun z =>
      |whole35Statistic z (whole35Outcome (whole35Side false))| ≥ 1)).card = 2 := by
    simp only [whole35_frozen_stat]
    exact AronowAudit.P037.Wave1.t35r2_four_tail_card
  refine ⟨t35_base, hcard, ?_, ?_,
    AronowAudit.P037.Wave1.t35r2_four_side_supported false, ?_, ?_, hobs,
    fun z _ => hbound z, ?_, ?_⟩
  · simp [whole35Mass, hcard]
  · intro z hz
    exact ⟨by norm_num [whole35Mass, hcard], hc z hz⟩
  · intro z z' i hi
    simp only [whole35Outcome, hi]
  · intro z hz Y
    have hzcard := hc z hz
    simp [nominationStatistic, whole35Outcome, whole35Statistic,
      ite_mul, mul_ite, hzcard, sub_mul, Finset.sum_sub_distrib]
    ring
  · have he : whole35Support.filter (fun z =>
        |whole35Statistic z (whole35Outcome (whole35Side false))| = 1) =
        whole35Support.filter (fun z =>
        |whole35Statistic z (whole35Outcome (whole35Side false))| ≥ 1) := by
      apply Finset.filter_congr
      intro z _
      exact ⟨fun h => h.ge, fun h => le_antisymm (hbound z) h⟩
    rw [he, htail]
  · simp only [hobs, abs_neg, abs_one, whole35Mass]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_boole]
    rw [htail, hcard]
    norm_num

/-- The E1 law factorizes on every prescribed coordinate set, including the empty set. -/
private theorem whole27_cylinders (s : Finset (Fin 4 × Fin 3))
    (a : Whole27Assignment) :
    (∑ d : Whole27Assignment, whole27Mass d *
      (if ∀ i ∈ s, d i = a i then 1 else 0)) = (1/4:ℝ)^s.card := by
  let f := fun (i : Fin 4 × Fin 3) (k : Fin 4) =>
    (1/4:ℝ) * (if i ∈ s then (if k = a i then 1 else 0) else 1)
  have he (d : Whole27Assignment) :
      whole27Mass d * (if ∀ i ∈ s, d i = a i then 1 else 0) = ∏ i, f i (d i) := by
    simp only [f, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin]
    rw [show (∏ i : Fin 4 × Fin 3,
      (if i ∈ s then (if d i = a i then (1:ℝ) else 0) else 1)) =
      if ∀ i ∈ s, d i = a i then 1 else 0 by
        rw [Finset.prod_ite_mem_eq, Finset.prod_boole]
        split_ifs <;> rfl]
    rfl
  simp_rw [he]
  rw [AronowAudit.P037.finite_product_factorization]
  have hf (i : Fin 4 × Fin 3) : (∑ k : Fin 4, f i k) = if i ∈ s then 1/4 else 1 := by
    by_cases hi : i ∈ s
    · simp [f, hi]
    · norm_num [f, hi, Fin.sum_univ_four]
  simp_rw [hf]
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

/-- Assembly of both supported regression comparisons and the complete E1 assignment law. -/
theorem T27_assembly : T27WholeStatement := by
  have hc := whole27_cylinders
  refine ⟨t27_base, ?_, ?_, hc, ?_, ?_, by positivity, fun _ => rfl, ?_, ?_, by norm_num⟩
  · simpa using hc ∅ (fun i => i.1)
  · intro d
    dsimp [whole27Mass]
    positivity
  · intro i k
    have hm : (∑ d : Whole27Assignment, whole27Mass d *
        (if d i = k then 1 else 0)) = 1/4 := by
      simpa using hc {i} (fun _ => k)
    exact ⟨hm, by rw [hm]; norm_num⟩
  · simpa using hc Finset.univ (fun i => i.1)
  · norm_num [Finset.card_powersetCard, Nat.choose]
  · norm_num [Finset.sum_const, Fintype.card_fun, Finset.card_powersetCard,
      Nat.choose]

/-- Assembly of the finite variance certificate and every exposure's full-control mean shift. -/
theorem T33_assembly : T33WholeStatement := by
  have hmean (z : Fin 6 × (Fin 4 → Bool)) (k : Fin 4) :
      whole33Mean z (whole33Imputed z) k =
        whole33Mean z controlResidual k + controlPointMean k := by
    let X := controlFullRow (controlExposure z)
    let L := regressionMap (controlWeight (controlExposure z)) X
    have hleft : L * X = 1 :=
      AronowAudit.P037.RegressionCompletion.weighted_left_inverse _ _
        (Bridge.control_weights_positive _) (Bridge.collapsed_certificate.2.2.2.2.2.1 z)
    have hi : whole33Imputed z = controlResidual + X.mulVec controlPoint := by
      ext i
      change controlY i + controlPointMean (controlExposure z i) -
        controlPointMean (controlObserved i) =
        controlY i - (controlFullRow controlObserved).mulVec controlPoint i +
        (controlFullRow (controlExposure z)).mulVec controlPoint i
      rw [Bridge.control_prediction, Bridge.control_prediction]
      simp only [controlPointMean]
      ring
    have hf : L.mulVec (whole33Imputed z) = L.mulVec controlResidual + controlPoint := by
      rw [hi, Matrix.mulVec_add, Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]
    change L.mulVec (whole33Imputed z) k.castSucc + L.mulVec (whole33Imputed z) 4 / 4 = _
    rw [hf]
    change (L.mulVec controlResidual k.castSucc + controlPoint k.castSucc) +
      (L.mulVec controlResidual 4 + controlPoint 4) / 4 =
      (L.mulVec controlResidual k.castSucc + L.mulVec controlResidual 4 / 4) +
      (controlPoint k.castSucc + controlPoint 4 / 4)
    ring
  refine ⟨t33_base, ?_, hmean, ?_, ?_, ?_, ?_⟩
  · norm_num [controlPiI, pairReferentRate, Fintype.sum_prod_type, Fin.sum_univ_succ]
  · apply (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 305/200)).2
    norm_num [controlCollapsedVarianceCertificate]
  · apply (Real.sqrt_lt' (by norm_num : (0:ℝ) < 307/200)).2
    norm_num [controlCollapsedVarianceCertificate]
  · apply (Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 605/200)).2
    norm_num [controlFullVarianceCertificate]
  · apply (Real.sqrt_lt' (by norm_num : (0:ℝ) < 607/200)).2
    norm_num [controlFullVarianceCertificate]

/-- Assembly of fixed-control identities, the reduced-control obstruction, and the
extension to every estimable functional in an aliased coefficient presentation. -/
theorem T34_assembly (h1 : T34_L1) (h2 : T34_L2) : T34WholeStatement := by
  have halias : ∀ (n p : ℕ) (H : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → ℝ),
      (∀ i, 0 < w i) → ∀ (y : Fin n → ℝ) (theta a b : Fin p → ℝ),
      regressionMinimum w H y a → regressionMinimum w H (y + H.mulVec theta) b →
      H.mulVec b = H.mulVec a + H.mulVec theta ∧
        ∀ ell, wholeEstimable H ell → ell b = ell a + ell theta := by
    intro n p H w hw y theta a b ha hb
    have hf : H.mulVec b = H.mulVec (a + theta) :=
      h1 n p H w _ hw b (a + theta) hb (minimum_shift H w y theta a ha)
    refine ⟨by simpa only [Matrix.mulVec_add] using hf, ?_⟩
    intro ell he
    simpa only [map_add] using estimable_equal_fit H ell he b (a + theta) hf
  refine ⟨fun Ω _ => ⟨Bridge.same_controls, Bridge.same_controls_extra⟩,
    reduced_controls, ?_, ?_, halias, ?_⟩
  · refine ⟨strict_control_space, sum_control_space, two_control_space, omitted_outside, ?_⟩
    have hc := t33_base
    rcases Bridge.collapsed_certificate with ⟨_,_,_,_,_,_,_,_,_,hfull,_,_⟩
    have hi : controlVariance (fun z => controlContrast z true (whole33Imputed z)) =
        controlVariance (fun z => controlContrast z true controlResidual) :=
      hc.2.2.2.1.trans hfull.symm
    rw [hi]
    exact hc.2.1
  · intro n p H w hw
    refine ⟨h2 n p H, ?_⟩
    intro q B hB hspace y
    have hb := inverse_minimum B w y hw hB
    have hm : B.mulVec ((regressionMap w B).mulVec y) ∈ wholeColumnSpace H := by
      rw [← hspace]
      exact ⟨_,rfl⟩
    rcases hm with ⟨a,ha⟩
    change H.mulVec a = B.mulVec ((regressionMap w B).mulVec y) at ha
    have hamin := minimum_transport H B w y hspace.symm.le a _ ha hb
    refine ⟨hb,⟨a,hamin⟩,?_⟩
    intro c
    constructor
    · intro hc
      exact (h1 n p H w y hw c a hc hamin).trans ha
    · intro hc
      exact minimum_transport H B w y hspace.symm.le c _ hc hb
  · intro Ω _ n p H w r theta a b ell prob hw he ha hb _ ht
    have hp (z : Ω) : ell (b z) = ell (a z) + ell theta :=
      (halias n p (H z) (w z) (hw z) (r z) theta (a z) (b z) (ha z) (hb z)).2 ell (he z)
    refine ⟨hp,?_⟩
    unfold wholeVariance
    simp_rw [hp]
    exact AronowAudit.P037.RegressionCompletion.finite_variance_add_const prob _ ht _

/-- Assembly of raw-moment orthogonality, the expected-equation identities and the
nondegenerate four-state certificate. All substantive projection facts already have donors. -/
theorem T43_assembly : T43WholeStatement := by
  refine ⟨fun Ω K _ _ => ⟨Bridge.block_bias, Bridge.common_intercept⟩, ?_, ?_⟩
  · intro Ω K _ _ B d T C X mu lam p hT hTC hspan htt
    let d' := Bridge.toFiniteDesign d
    let t := fun w => blockDemean (T w)
    let z := fun w => blockDemean (fun i => T w i * C w i)
    let V := fun k => blockDemean (X k)
    have ht : ∀ i, AronowAudit.P037.designMean d' (fun w => t w i) = 0 :=
      AronowAudit.P037.ExpectedProjection.demeaned_treatment_mean d' T p hT
    have hz : ∀ i, AronowAudit.P037.designMean d' (fun w => z w i) =
        p * ∑ k, lam k * V k i :=
      AronowAudit.P037.ExpectedProjection.demeaned_composition_mean d' T C X mu lam p
        hTC hspan
    have hn := AronowAudit.P037.ExpectedProjection.residual_nuisance_orthogonal
      d' t z V lam p ht hz htt
    exact ⟨AronowAudit.P037.ExpectedProjection.residual_mean_zero d' t z V lam p ht hz,
      hn.1, hn.2, AronowAudit.P037.ExpectedProjection.residual_composition_moment
        d' t z V lam p ht hz htt⟩
  · have h := AronowAudit.P037.ExpectedProjection.block_model_nondegenerate_instance
    rcases h with ⟨hT,hTC,hs,htt,hK,hN⟩
    refine ⟨hT,hTC,hs,htt,hK,hN,?_,?_,?_,?_,?_,⟩
    · intro w i
      unfold whole43Treatment
      split_ifs <;> simp
    · intro w
      rw [Fintype.sum_prod_type, Fin.sum_univ_one, Fin.sum_univ_four]
      fin_cases w <;> norm_num [whole43Treatment]
    · intro ⟨b,i⟩
      fin_cases i <;> norm_num [whole43Treatment]
    · intro w i
      unfold whole43Composition
      split_ifs <;> simp
    · exact ⟨(0,0),(0,1),by norm_num⟩

end SAP.P037c.WH.W1
