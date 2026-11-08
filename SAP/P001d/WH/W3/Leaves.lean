import SAP.P001d.Defs.WholeW3
import SAP.P001d.Bridge
import AronowAudit.P001.Wave1.Gap.WP001dB1
import AronowAudit.P016.P016_Interference

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

noncomputable section
namespace SAP.P001d.WH.W3

/-- Rank-free normal equations for a least-squares minimizer. No intercept or
invertibility is needed. For each coordinate direction v, the real function
t ↦ olsRSS X Y (b + t • v) has a global minimum at zero. Differentiate its finite
sum of squares using HasDerivAt.fun_sum and HasDerivAt.pow; its derivative is
-2 times the residual cross product with Xv. IsLocalMin.hasDerivAt_eq_zero makes
that cross product zero. Taking v = Pi.single k 1 gives each coordinate of Xᵀe.
An alternative elementary route expands the same quadratic and chooses a small
step of the opposite sign if the cross product is nonzero. -/
def T65_L1 : Prop :=
  ∀ {n K : ℕ} (X : Matrix (Fin n) (Fin (K+1)) ℝ) (Y : Fin n → ℝ)
    (b : Fin (K+1) → ℝ),
    (∀ c, olsRSS X Y b ≤ olsRSS X Y c) →
    X.transpose.mulVec (Y - X.mulVec b) = 0

/-- The correlation recovery and diagonal/off-diagonal count are short algebraic
arguments. The sampling-variance and corrected block-law results are donors. -/
theorem T64_assembly : T64WholeStatement := by
  classical
  constructor
  · intro Ω _ μ _ m hm X hiid h2 l hl s ρ _hρ hvar hdefined hcorr
    have hs : 0 ≤ s := by
      rw [← hvar 0 ⟨0, hm⟩]
      exact variance_nonneg _ _
    have hd (i : ℕ) (j : Fin m) :
        covariance (fun ω => X i ω j) (fun ω => X i ω j) μ = s :=
      (covariance_self (h2 i j).aemeasurable).trans (hvar i j)
    have ho (i : ℕ) (j k : Fin m) (hjk : j ≠ k) :
        covariance (fun ω => X i ω j) (fun ω => X i ω k) μ =
          wholeCorrelation μ (fun ω => X i ω j) (fun ω => X i ω k) *
            Real.sqrt (variance (fun ω => X i ω j) μ) *
            Real.sqrt (variance (fun ω => X i ω k) μ) ∧
        covariance (fun ω => X i ω j) (fun ω => X i ω k) μ = ρ * s := by
      have hp := hdefined i j k hjk
      have hn := ne_of_gt (mul_pos hp.1 hp.2)
      have hc := (div_eq_iff hn).mp (hcorr i j k hjk)
      change covariance _ _ μ = ρ *
        (Real.sqrt (variance (fun ω => X i ω j) μ) *
          Real.sqrt (variance (fun ω => X i ω k) μ)) at hc
      constructor
      · rw [hcorr i j k hjk, mul_assoc]
        exact hc
      · simpa only [hvar, Real.mul_self_sqrt hs] using hc
    have hcount (i : ℕ) :
        (∑ j, ∑ k, covariance (fun ω => X i ω j) (fun ω => X i ω k) μ) =
          (m : ℝ) * s + (m : ℝ) * ((m : ℝ) - 1) * ρ * s := by
      have he (j k : Fin m) :
          covariance (fun ω => X i ω j) (fun ω => X i ω k) μ =
            ρ * s + (if k = j then s - ρ * s else 0) := by
        by_cases hk : k = j
        · subst k
          rw [hd]
          simp
        · rw [(ho i j k (Ne.symm hk)).2]
          simp [hk]
      simp_rw [he]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hv : variance (clusterMean X l) μ =
        (∑ j, ∑ k, covariance (fun ω => X 0 ω j) (fun ω => X 0 ω k) μ) /
          ((l : ℝ) * (m : ℝ)^2) :=
      AronowAudit.P001.cluster_variance_double_covariance_sum μ hm X
        ((Bridge.iid_iff μ X).mp hiid) (h2 0) l hl
    have he : variance (clusterMean X l) μ =
        s / ((l : ℝ) * m) * (1 + ρ * ((m : ℝ) - 1)) :=
      hv.trans (AronowAudit.P001.intracluster_variance_correct_diagonal l m hl hm s ρ
        (fun j k => covariance (fun ω => X 0 ω j) (fun ω => X 0 ω k) μ)
        (hd 0) (fun j k hjk => (ho 0 j k hjk).2))
    refine ⟨hs, hd, ho, hcount, ?_, ?_, he, ?_, ?_⟩
    · intro i
      rw [hcount i, ← hcount 0]
      exact hv
    · rw [← hcount 0]
      exact hv
    · intro hzero
      have hz : variance (clusterMean X l) μ = s / ((l : ℝ) * m) := by
        simpa only [hzero, zero_mul, add_zero, mul_one] using he
      exact ⟨hz, by simpa only [Nat.cast_mul] using hz⟩
    · intro hone
      rw [he, hone]
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hlR : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
      field_simp
      ring
  · intro l m hl _hm x
    have : NeZero l := ⟨Nat.ne_of_gt hl⟩
    have hb := AronowAudit.P001.Wave1.canonical_block_bootstrap_law hl x
    have : IsProbabilityMeasure (wholeBlockLaw l) := hb.1
    refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1,
      hb.2.2.2.2.2, fun _ _ => rfl, ?_, ?_⟩
    · intro B
      have hi : iIndepFun (fun r (a : Fin B → Fin l → Fin l) => a r)
          (wholeBlockReplicateLaw l B) :=
        iIndepFun_pi (fun _ => measurable_id.aemeasurable)
      refine ⟨?_, hi, ?_⟩
      · unfold wholeBlockReplicateLaw
        infer_instance
      · intro T
        exact hi.comp (fun _ => wholeBlockEstimate T x) (fun _ => Measurable.of_discrete)
    · intro T
      exact ⟨MemLp.of_discrete, rfl⟩

/-- The donor gives attainment even for singular designs and the unique
inverse-formula solution for full-rank designs. The only new leaf supplies
normal equations for every minimizer; the intercept and finite sums do the rest. -/
theorem T65_assembly (h1 : T65_L1) : T65WholeStatement := by
  intro n K hn X Y hinter
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnormal (b : Fin (K+1) → ℝ) (h : X.transpose.mulVec (Y - X.mulVec b) = 0) :
      (X.transpose * X).mulVec b = X.transpose.mulVec Y := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b i
    change Y i - (∑ k, X i k * b k) = _
    rw [Fin.sum_univ_succ]
    simp only [hinter, one_mul, mul_comm]
  · intro b
    simp only [olsRSS, dotProduct, Pi.sub_apply, pow_two]
  · intro b
    constructor
    · intro hb c
      exact (div_le_div_iff_of_pos_right hnR).mp (hb c)
    · intro hb c
      exact (div_le_div_iff_of_pos_right hnR).mpr (hb c)
  · obtain ⟨b, hb⟩ := (AronowAudit.P016.least_squares_attained Y X).1
    refine ⟨b, ?_⟩
    intro c
    have hle : AronowAudit.P016.lsRSS Y X ≤ AronowAudit.P016.lsObjective Y X c := by
      apply csInf_le
      · refine ⟨0, ?_⟩
        rintro z ⟨d, rfl⟩
        exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      · exact ⟨c, rfl⟩
    rw [← hb] at hle
    exact hle
  · intro hX
    have h := AronowAudit.P001.ols_correct_rows_solution_residuals X Y hX hinter
    exact ⟨h.1, hnormal _ h.2.1⟩
  · intro b hb
    let e := Y - X.mulVec b
    have hne : X.transpose.mulVec e = 0 := h1 X Y b hb
    have hs : (∑ i, e i) / (n : ℝ) = 0 := by
      have hsum := congrFun hne 0
      change (∑ i, X i 0 * e i) = 0 at hsum
      simp only [hinter, one_mul] at hsum
      rw [hsum, zero_div]
    have hk (k : Fin (K+1)) : (∑ i, e i * X i k) / (n : ℝ) = 0 := by
      have hc := congrFun hne k
      change (∑ i, X i k * e i) = 0 at hc
      have hc' : (∑ i, e i * X i k) = 0 := by simpa only [mul_comm] using hc
      rw [hc', zero_div]
    exact ⟨hne, hnormal b hne, hs, hk,
      fun k => by rw [hk, hs, zero_mul, sub_zero]⟩

end SAP.P001d.WH.W3
