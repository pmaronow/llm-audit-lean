import SAP.P002a.Defs.WholeW3
import SAP.P002a.Bridge
import AronowAudit.P002.Wave1.Gap.GLP0022B3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P002a.WH.W3
noncomputable section
open Filter
open scoped BigOperators Matrix Classical Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Equally spaced grid moments and bounds. Prove the sums of the first three
powers of j by induction using Finset.sum_range_succ, expand the affine grid,
and divide by m. Alternatively pair j with m-1-j for the odd moments. The bound
uses 0 <= j <= m-1, and the two bounds on v are ordered-field arithmetic.
Template: FV_grid_sums, FV_grid_bound, FV_grid_moments, FV_v_bounds in
AronowAudit/P002/Wave1/Gap/GLP0022B3.lean (private source templates only).
Expected proof size: 100-180 lines. -/
def T6_L1 : Prop := ∀ m : ℕ, 4 ≤ m → T6GridFacts m

/-- Moments and pointwise bounds of the two-block even model, from the grid
facts. Split Fin (2*m) into its first and last m entries. Average the two signs
to obtain E[x]=E[y]=0, E[x^2]=1+eta^2*v, E[xy]=eta*v. Expanding y^2 leaves
v+(1/100) E[(t^2-v)^2] >= v, since E[t]=E[t^3]=0. The triangle inequality gives
|x|<=5/4 and |y|<=11/10. The supplied grid facts are exactly T6_L1's conclusion.
Templates: FV_even_sum, FV_even_reduce, FV_grid_extra, FV_even_moments and
FV_even_bounds in GLP0022B3.lean; no fourth-power grid formula is necessary.
Expected proof size: 160-260 lines. -/
def T6_L2 : Prop :=
  ∀ (m : ℕ), 4 ≤ m → T6GridFacts m →
    mean (t6X m) = 0 ∧ mean (t6Y m) = 0 ∧
    mean (fun i => t6X m i ^ 2) = 1 + t6Eta m ^ 2 * t6V m ∧
    mean (fun i => t6X m i * t6Y m i) = t6Eta m * t6V m ∧
    t6V m ≤ mean (fun i => t6Y m i ^ 2) ∧
    (∀ i, |t6X m i| ≤ 5 / 4) ∧ (∀ i, |t6Y m i| ≤ 11 / 10)

/-- Identify the population OLS fit and both potential residual schedules from
the four supplied scalar moments. The population Gram matrix is diag(1,1+eta^2*v),
whose second diagonal entry is positive for m>=4. Verify its two normal equations
for intercept zero and slope gamma, then multiply by the inverse Gram matrix.
Expand residual and the two-coordinate dot product to obtain t6Error.
Templates: FV_scalar_ols and FV_even_population_fit in GLP0022B3.lean; public
donors include AronowAudit.P002.ols_normal_equations and Matrix.nonsing_inv_mul.
The scalar moment hypotheses are supplied by T6_L2. Expected size: 90-150 lines. -/
def T6_L3 : Prop :=
  ∀ (m : ℕ), 4 ≤ m →
    mean (t6X m) = 0 → mean (t6Y m) = 0 →
    mean (fun i => t6X m i ^ 2) = 1 + t6Eta m ^ 2 * t6V m →
    mean (fun i => t6X m i * t6Y m i) = t6Eta m * t6V m →
    ∀ a : Bool,
      psi (nearSingularModel m) a 0 = t6Coef 0 (t6Gamma m) ∧
      residual (nearSingularModel m) a 0 = t6Error m

/-- All even-model scalar covariates are distinct. Inside a sign block cancel
the positive eta and the nonzero grid denominator, then recover the unit index
from its residue modulo m. Across blocks use |t|<=1 and eta<=1/4 to separate
the ranges [3/4,5/4] and [-5/4,-3/4]. The residue in the second block is i-m.
Template: FV_x_injective in GLP0022B3.lean. Expected size: 60-100 lines. -/
def T6_L4 : Prop := ∀ m : ℕ, 4 ≤ m → Function.Injective (t6X m)

/-- The two pure-sign blocks are admissible reassignments; both refitted slopes
are 1/eta, and the positive-block adjusted statistic is -2/eta. Prove that each
block contains the grid once, hence has size m. Its x mean is s, x second moment
is s^2+eta^2*v, y mean is zero and xy mean is eta*v. Verify the scalar normal
equations for intercept -s/eta and slope 1/eta. Subtract the two adjusted arm
means. Grid facts and full rank are supplied by T6_L1 and the public counterexample
theorem, respectively. Templates: FV_block_sums, FV_block_mean,
FV_affine_block_fit and FV_rare_statistic in GLP0022B3.lean.
Expected proof size: 180-300 lines. -/
def T6_L5 : Prop :=
  ∀ (m : ℕ), 4 ≤ m → T6GridFacts m →
    (∀ T ∈ assignments (nearSingularModel m).pop,
      (gram (nearSingularModel m).x T).det ≠ 0 ∧
      (gram (nearSingularModel m).x Tᶜ).det ≠ 0) →
    t6Block m ∈ assignments (nearSingularModel m).pop ∧
    (t6Block m)ᶜ ∈ assignments (nearSingularModel m).pop ∧
    (∀ a : Bool,
      (fitted (nearSingularModel m) (t6Y m) (t6Block m) a) (some 0) = 1 / t6Eta m) ∧
    adjustedTau (nearSingularModel m) (t6Y m) (t6Block m) = -2 / t6Eta m

private theorem mean_add {n : ℕ} (f g : Fin n → ℝ) :
    mean (fun i => f i + g i) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, add_div]

private theorem mean_sub {n : ℕ} (f g : Fin n → ℝ) :
    mean (fun i => f i - g i) = mean f - mean g := by
  simp [mean, Finset.sum_sub_distrib, sub_div]

private theorem mean_mul {n : ℕ} (c : ℝ) (f : Fin n → ℝ) :
    mean (fun i => c * f i) = c * mean f := by
  simp only [mean, ← Finset.mul_sum]
  ring

private theorem eta_bounds (m : ℕ) (hm : 4 ≤ m) : 0 < t6Eta m ∧ t6Eta m ≤ 1 / 5 := by
  have hp : (5 : ℝ) ≤ (2 : ℝ) ^ ((2 * m) ^ 2) := by
    have he : 3 ≤ (2 * m) ^ 2 := by nlinarith
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) he
    norm_num at h ⊢
    linarith
  unfold t6Eta
  exact ⟨by positivity, (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith)⟩

private theorem tau_compl {n k : ℕ} (P : CovPopulation n k) (q : Fin n → ℝ)
    (T : Finset (Fin n)) : adjustedTau P q Tᶜ = -adjustedTau P q T := by
  simp [adjustedTau, adjustedWith, fitted]

private theorem assignment_compl (m : ℕ) (T : Finset (Fin (2 * m)))
    (hT : T ∈ assignments (nearSingularModel m).pop) :
    Tᶜ ∈ assignments (nearSingularModel m).pop := by
  have hc : T.card = m := (Finset.mem_powersetCard.mp hT).2
  apply Finset.mem_powersetCard.mpr
  refine ⟨Finset.subset_univ _, ?_⟩
  change Tᶜ.card = m
  rw [Finset.card_compl, Fintype.card_fin, hc]
  omega

private theorem tau_expectation (m : ℕ) :
    expectation (nearSingularModel m).pop (adjustedTau (nearSingularModel m) (t6Y m)) = 0 := by
  let P := nearSingularModel m
  let f := adjustedTau P (t6Y m)
  have hs : (∑ T ∈ assignments P.pop, f T) = ∑ T ∈ assignments P.pop, f Tᶜ := by
    apply Finset.sum_bij (fun T _ => Tᶜ)
    · intro T hT
      exact assignment_compl m T hT
    · intro S hS T hT he
      simpa using congrArg (fun U : Finset (Fin (2 * m)) => Uᶜ) he
    · intro T hT
      exact ⟨Tᶜ, assignment_compl m T hT, by simp⟩
    · intro T hT
      simp
  have hf (T : Finset (Fin (2 * m))) : f Tᶜ = -f T := tau_compl P (t6Y m) T
  simp only [hf, Finset.sum_neg_distrib] at hs
  have hz : (∑ T ∈ assignments P.pop, f T) = 0 := by linarith
  change (∑ T ∈ assignments P.pop, f T) / _ = 0
  rw [hz, zero_div]

/-- Assembly of the complete counterexample. Only the five explicitly listed
finite mathematical steps remain for leaf writers. -/
theorem T6_assembly (h1 : T6_L1) (h2 : T6_L2) (h3 : T6_L3)
    (h4 : T6_L4) (h5 : T6_L5) : T6WholeStatement := by
  have old : T6Statement := AronowAudit.P002.Wave1.feasible_variance_counterexample_proof
  have heven : ∀ m, 4 ≤ m →
      T6GridFacts m ∧ T6EvenModelFacts m ∧ T6EvenMomentFacts m ∧
      T6EvenRegressionFacts m ∧ T6RareBlockFacts m ∧ T6VarianceFacts m ∧
      T6EstimatorFacts m ∧ T6FailureFacts m := by
    intro m hm
    let P := nearSingularModel m
    let V := t6Variance m
    have hmr : (4 : ℝ) ≤ m := by exact_mod_cast hm
    have hmpos : (0 : ℝ) < m := by linarith
    have hN : (8 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast (show 8 ≤ 2 * m by omega)
    have hg := h1 m hm
    obtain ⟨hXi, hlate, hrank, hold⟩ := old.1 m hm
    obtain ⟨hx, hy, hx2, hxy, hy2, hxb, hyb⟩ := h2 m hm hg
    obtain ⟨heta, hetab⟩ := eta_bounds m hm
    have hv0 : 0 ≤ t6V m := by linarith [hg.2.2.2.2.1]
    have hv1 : t6V m ≤ 1 := hg.2.2.2.2.2
    have hden : 0 < 1 + t6Eta m ^ 2 * t6V m := by positivity
    have hgamma : t6Gamma m * (1 + t6Eta m ^ 2 * t6V m) = t6Eta m * t6V m := by
      unfold t6Gamma
      exact div_mul_cancel₀ _ hden.ne'
    have hg0 : 0 ≤ t6Gamma m := by unfold t6Gamma; positivity
    have hg1 : t6Gamma m ≤ t6Eta m := by
      nlinarith [mul_nonneg hg0 (mul_nonneg (sq_nonneg (t6Eta m)) hv0)]
    have hobs (S : Finset (Fin (2 * m))) : observedW P.pop 0 S = t6Y m := by
      funext i
      simp [observedW, observedY, P, nearSingularModel, t6Y]
    have hcompliers : compliers P.pop = Finset.univ := by
      simp [compliers, P, nearSingularModel]
    have hn0 : controlSize P.pop = (m : ℝ) := by
      simp only [controlSize, P, nearSingularModel, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have hmodel : T6EvenModelFacts m := by
      refine ⟨hXi, hlate, hcompliers, rfl, hn0, ?_, ?_, ?_, hobs⟩
      · change (m : ℝ) / ((2 * m : ℕ) : ℝ) = 1 / 2
        push_cast
        field_simp
      · intro i a
        exact ⟨rfl, rfl⟩
      · intro i
        rfl
    have hsumx : (∑ i, t6X m i) = 0 := by
      have hn : (((2 * m : ℕ) : ℝ)) ≠ 0 := by positivity
      exact (div_eq_zero_iff.mp hx).resolve_right hn
    have hx4 : mean (fun i => t6X m i ^ 4) ≤ 16 := by
      exact hXi.2.2.2.2.2.2.2.2.1 0
    have hxxlow : (1 / 4 : ℝ) ≤ mean (fun i => t6X m i ^ 2) := by
      rw [hx2]
      nlinarith [mul_nonneg (sq_nonneg (t6Eta m)) hv0]
    have hmom : T6EvenMomentFacts m :=
      ⟨hsumx, hx, hy, hxb, hyb, hx4, hx2, hxxlow, hxy⟩
    have hfit := h3 m hm hx hy hx2 hxy
    have hem : mean (t6Error m) = 0 := by
      change mean (fun i => t6Y m i - t6Gamma m * t6X m i) = 0
      rw [mean_sub, mean_mul, hx, hy]
      ring
    have heb (i : Fin (2 * m)) : |t6Error m i| ≤ 27 / 20 := by
      calc
        _ ≤ |t6Y m i| + |t6Gamma m * t6X m i| := by
          simpa only [t6Error, sub_eq_add_neg, abs_neg] using
            abs_add_le (t6Y m i) (-(t6Gamma m * t6X m i))
        _ ≤ 27 / 20 := by
          rw [abs_mul, abs_of_nonneg hg0]
          nlinarith [hyb i, hxb i, mul_nonneg hg0 (sub_nonneg.mpr (hxb i))]
    have he2 : mean (fun i => t6Error m i ^ 2) =
        mean (fun i => t6Y m i ^ 2) - 2 * t6Gamma m * (t6Eta m * t6V m) +
          t6Gamma m ^ 2 * (1 + t6Eta m ^ 2 * t6V m) := by
      have hf : (fun i => t6Error m i ^ 2) =
          (fun i => (t6Y m i ^ 2 - (2 * t6Gamma m) * (t6X m i * t6Y m i)) +
            t6Gamma m ^ 2 * t6X m i ^ 2) := by funext i; unfold t6Error; ring
      rw [hf, mean_add, mean_sub, mean_mul, mean_mul, hxy, hx2]
    have hglow : (1 / 6 : ℝ) ≤ mean (fun i => t6Error m i ^ 2) := by
      have hdle : 1 + t6Eta m ^ 2 * t6V m ≤ 2 := by
        nlinarith [mul_nonneg (sq_nonneg (t6Eta m)) (sub_nonneg.mpr hv1)]
      have hvdiv : (1 / 6 : ℝ) ≤ t6V m / (1 + t6Eta m ^ 2 * t6V m) := by
        apply (le_div_iff₀ hden).mpr
        linarith [hg.2.2.2.2.1]
      have hge : t6V m / (1 + t6Eta m ^ 2 * t6V m) ≤ mean (fun i => t6Error m i ^ 2) := by
        rw [he2]
        have heq : t6V m - 2 * t6Gamma m * (t6Eta m * t6V m) +
            t6Gamma m ^ 2 * (1 + t6Eta m ^ 2 * t6V m) =
            t6V m / (1 + t6Eta m ^ 2 * t6V m) := by
          unfold t6Gamma
          field_simp [hden.ne']
          ring
        linarith
      exact hvdiv.trans hge
    have hcov : 0 ≤ popCov (t6Error m) (t6Error m) := by
      simp only [popCov, ← pow_two]
      apply div_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      linarith
    have hfourth : fourthNorm (t6Error m) ≤ 5 * Real.sqrt (popVar (t6Error m)) := by
      have hh := hXi.2.2.2.2.2.2.1 true
      rw [hlate, (hfit true).2] at hh
      exact hh
    have hreg : T6EvenRegressionFacts m :=
      ⟨hfit, hem, heb, hglow, hcov, hfourth, h4 m hm, hrank⟩
    obtain ⟨hA, hAc, hslopes, htau⟩ := h5 m hm hg hrank
    have htauc : adjustedTau P (t6Y m) (t6Block m)ᶜ = 2 / t6Eta m := by
      rw [tau_compl, htau]
      ring
    have hezero := tau_expectation m
    have hrare : T6RareBlockFacts m :=
      ⟨hA, hAc, hslopes, htau, htauc, tau_compl P (t6Y m), hezero⟩
    have hcard : (assignments P.pop).card = (2 * m).choose m := by
      simp [assignments, P, nearSingularModel]
    have hCpos : (0 : ℝ) < ((2 * m).choose m : ℝ) := by
      rw [← hcard]
      exact_mod_cast Finset.card_pos.mpr ⟨t6Block m, hA⟩
    have hAne : t6Block m ≠ (t6Block m)ᶜ := by
      intro he
      let i : Fin (2 * m) := ⟨0, by omega⟩
      have hi : i ∈ t6Block m := by simp [t6Block, i]; omega
      exact Finset.mem_compl.mp (he ▸ hi) hi
    have hbin : 8 / (((2 * m).choose m : ℝ) * t6Eta m ^ 2) ≤ V := by
      have hs : 8 / t6Eta m ^ 2 ≤ ∑ T ∈ assignments P.pop, (adjustedTau P (t6Y m) T) ^ 2 := by
        calc
          _ = ∑ T ∈ ({t6Block m, (t6Block m)ᶜ} : Finset (Finset (Fin (2 * m)))),
              (adjustedTau P (t6Y m) T) ^ 2 := by
            rw [Finset.sum_pair hAne, htau, htauc]
            field_simp
            ring
          _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
            (by intro T hT; simp only [Finset.mem_insert, Finset.mem_singleton] at hT
                rcases hT with rfl | rfl <;> assumption)
            (fun T _ _ => sq_nonneg _)
      change _ ≤ (∑ T ∈ assignments P.pop,
        (adjustedTau P (t6Y m) T - expectation P.pop (adjustedTau P (t6Y m))) ^ 2) /
          ((assignments P.pop).card : ℝ)
      rw [hezero, hcard]
      simp only [sub_zero]
      simpa only [div_div, mul_comm] using div_le_div_of_nonneg_right hs hCpos.le
    have hcompare : 8 * (2 : ℝ) ^ (2 * (2 * m) ^ 2) / (2 : ℝ) ^ (2 * m) ≤
        8 / (((2 * m).choose m : ℝ) * t6Eta m ^ 2) := by
      have hchoose : ((2 * m).choose m : ℝ) ≤ (2 : ℝ) ^ (2 * m) := by
        exact_mod_cast Nat.choose_le_two_pow (2 * m) m
      have heq : 8 / t6Eta m ^ 2 = 8 * (2 : ℝ) ^ (2 * (2 * m) ^ 2) := by
        rw [show 2 * (2 * m) ^ 2 = (2 * m) ^ 2 * 2 by omega, pow_mul]
        unfold t6Eta
        field_simp
      rw [← heq]
      simpa only [div_div, mul_comm] using
        div_le_div_of_nonneg_left (by positivity : 0 ≤ 8 / t6Eta m ^ 2) hCpos hchoose
    have hVpos : 0 < V := (div_pos (by norm_num) (mul_pos hCpos (sq_pos_of_pos heta))).trans_le hbin
    have hvar : T6VarianceFacts m := ⟨hVpos, hbin, hcompare⟩
    have hsumy : (∑ i, t6Y m i ^ 2) ≤ (2 * (m : ℝ)) * (121 / 100) := by
      calc
        _ ≤ ∑ _i : Fin (2 * m), (121 / 100 : ℝ) := Finset.sum_le_sum (fun i _ => by
          have hh := abs_le.mp (hyb i)
          nlinarith [mul_nonneg (by linarith : 0 ≤ 11 / 10 - t6Y m i)
            (by linarith : 0 ≤ 11 / 10 + t6Y m i)])
        _ = _ := by simp
    have hRSS : ∀ T ∈ assignments P.pop,
        0 ≤ adjustedSigma2 P (t6Y m) T ∧
        adjustedSigma2 P (t6Y m) T ≤ (∑ i, t6Y m i ^ 2) / (m : ℝ) ^ 2 := by
      intro T hT
      have hc : T.card = m := (Finset.mem_powersetCard.mp hT).2
      have hcc : Tᶜ.card = m := by rw [Finset.card_compl, Fintype.card_fin, hc]; omega
      have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
      have hTcne : Tᶜ.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨hgT, hgTc⟩ := hrank T hT
      have hr1 : rss P.x T (t6Y m) (ols P.x T (t6Y m)) ≤ rss P.x T (t6Y m) 0 :=
        AronowAudit.P002.ols_minimizer_fullrank P.x T (t6Y m) hTne hgT 0
      have hr0 : rss P.x Tᶜ (t6Y m) (ols P.x Tᶜ (t6Y m)) ≤ rss P.x Tᶜ (t6Y m) 0 :=
        AronowAudit.P002.ols_minimizer_fullrank P.x Tᶜ (t6Y m) hTcne hgTc 0
      simp only [rss, dotProduct_zero, sub_zero] at hr1 hr0
      constructor
      · unfold adjustedSigma2 rss
        positivity
      · change rss P.x T (t6Y m) (ols P.x T (t6Y m)) / (m : ℝ) ^ 2 +
          rss P.x Tᶜ (t6Y m) (ols P.x Tᶜ (t6Y m)) / (controlSize P.pop) ^ 2 ≤ _
        rw [hn0, ← add_div]
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact (add_le_add hr1 hr0).trans_eq (Finset.sum_add_sum_compl T _)
    have hsharp : (∑ i, t6Y m i ^ 2) / (m : ℝ) ^ 2 ≤ 121 / (25 * ((2 * m : ℕ) : ℝ)) := by
      have hh := div_le_div_of_nonneg_right hsumy (sq_nonneg (m : ℝ))
      have heq : (2 * (m : ℝ)) * (121 / 100) / (m : ℝ) ^ 2 =
          121 / (25 * ((2 * m : ℕ) : ℝ)) := by
        push_cast
        field_simp
        ring
      exact hh.trans_eq heq
    have hstrict : 121 / (25 * ((2 * m : ℕ) : ℝ)) < 5 / ((2 * m : ℕ) : ℝ) := by
      have hnpos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by linarith
      apply (div_lt_div_iff₀ (by positivity) hnpos).mpr
      nlinarith
    have hest : T6EstimatorFacts m := ⟨hRSS, hsharp, hstrict⟩
    have hp : (2 : ℝ) ^ (2 * m) ≤ (2 : ℝ) ^ (2 * (2 * m) ^ 2) := by
      apply pow_le_pow_right₀ (by norm_num)
      nlinarith
    have hsmall : t6RatioBound m < 1 / 2 := by
      unfold t6RatioBound
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) <
        8 * ((2 * m : ℕ) : ℝ) * (2 : ℝ) ^ (2 * (2 * m) ^ 2))).mpr
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (2 * (2 * m) ^ 2)]
    have hbound (T : Finset (Fin (2 * m))) (hT : T ∈ assignments P.pop) :
        0 ≤ adjustedSigma2 P (t6Y m) T / V ∧
        adjustedSigma2 P (t6Y m) T / V ≤ t6RatioBound m := by
      have hs0 := (hRSS T hT).1
      have hs5 : adjustedSigma2 P (t6Y m) T ≤ 5 / ((2 * m : ℕ) : ℝ) :=
        ((hRSS T hT).2.trans hsharp).trans hstrict.le
      have hlower := hcompare.trans hbin
      refine ⟨div_nonneg hs0 hVpos.le, ?_⟩
      have hh := div_le_div₀ (by positivity : (0 : ℝ) ≤ 5 / ((2 * m : ℕ) : ℝ)) hs5 (by positivity : (0 : ℝ) <
        8 * (2 : ℝ) ^ (2 * (2 * m) ^ 2) / (2 : ℝ) ^ (2 * m)) hlower
      have heq : (5 / ((2 * m : ℕ) : ℝ)) /
          (8 * (2 : ℝ) ^ (2 * (2 * m) ^ 2) / (2 : ℝ) ^ (2 * m)) = t6RatioBound m := by
        unfold t6RatioBound
        field_simp
      exact hh.trans_eq heq
    have hfailure : T6FailureFacts m := by
      refine ⟨hsmall, ?_⟩
      intro S hS
      dsimp only
      rw [hlate, hobs]
      refine ⟨hbound, ?_⟩
      simpa only [show observedW (nearSingularModel m).pop 0 S = t6Y m from hobs S]
        using (hold S hS).2.2
    exact ⟨hg, hmodel, hmom, hreg, hrare, hvar, hest, hfailure⟩
  have hodd : ∀ n, 9 ≤ n → Odd n → T6OddFacts n := by
    intro n hn hnodd
    let P := oddNearModel n
    have hnr : (9 : ℝ) ≤ n := by exact_mod_cast hn
    have hden : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    refine ⟨old.2.1 n hn hnodd, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
    · simp [late, groupMean, oddNearModel]
    · simp [compliers, oddNearModel]
    · intro i a
      exact ⟨rfl, rfl⟩
    · intro i
      refine ⟨rfl, ?_⟩
      have hi0 : (0 : ℝ) ≤ i.val := by positivity
      have hi1 : (i.val : ℝ) ≤ (n : ℝ) - 1 := by
        have h : (i.val : ℝ) + 1 ≤ n := by exact_mod_cast i.isLt
        linarith
      change |2 * (i.val : ℝ) / ((n : ℝ) - 1) - 1| ≤ 1
      rw [abs_le]
      constructor
      · have h : 0 ≤ 2 * (i.val : ℝ) / ((n : ℝ) - 1) := by positivity
        linarith
      · have h : 2 * (i.val : ℝ) / ((n : ℝ) - 1) ≤ 2 :=
          (div_le_iff₀ hden).mpr (by linarith)
        linarith
    · intro i j hij
      apply Fin.ext
      change 2 * (i.val : ℝ) / ((n : ℝ) - 1) - 1 =
        2 * (j.val : ℝ) / ((n : ℝ) - 1) - 1 at hij
      have he := (div_left_inj' hden.ne').mp (show
        2 * (i.val : ℝ) / ((n : ℝ) - 1) = 2 * (j.val : ℝ) / ((n : ℝ) - 1) by linarith)
      have hv : (i.val : ℝ) = j.val := by linarith
      exact_mod_cast hv
    · intro i j
      change (2 * (j.val : ℝ) / ((n : ℝ) - 1) - 1) -
        (2 * (i.val : ℝ) / ((n : ℝ) - 1) - 1) = _
      ring
  have hseqeven (m : ℕ) : t6SequenceModel (2 * m) = nearSingularModel m := by
    have transport (a b : ℕ) (hab : a = b) (h : 2 * a = 2 * b) :
        (h ▸ nearSingularModel a) = nearSingularModel b := by
      subst b
      rfl
    unfold t6SequenceModel
    split
    · next h => exact transport _ _ (by omega) h
    · next h => exact False.elim (h (by omega))
  have hseqodd (n : ℕ) (hn : Odd n) : t6SequenceModel n = oddNearModel n := by
    have hne : ¬2 * (n / 2) = n := by
      intro he
      have hnEven : Even n := ⟨n / 2, by omega⟩
      exact (Nat.not_even_iff_odd.mpr hn) hnEven
    simp [t6SequenceModel, hne]
  have hseq : ∀ n, 8 ≤ n → Xi (t6SequenceModel n) 0 (1 / 4) 16 5 (1 / 3) := by
    intro n hn
    by_cases he : Even n
    · obtain ⟨m, hm⟩ := he
      have heq : n = 2 * m := by omega
      rw [heq]
      rw [hseqeven]
      exact (heven m (by omega)).2.1.1
    · have ho : Odd n := Nat.not_even_iff_odd.mp he
      rw [hseqodd n ho]
      have hn9 : 9 ≤ n := by
        obtain ⟨j, hj⟩ := ho
        omega
      exact (hodd n hn9 ho).1
  have hlim : Tendsto t6FailureProbability atTop (nhds 1) := old.2.2
  exact ⟨heven, hodd, hseq, hseqeven, hseqodd, hlim,
    fun hz => by have he : (1 : ℝ) = 0 := tendsto_nhds_unique hlim hz; norm_num at he⟩

end
end SAP.P002a.WH.W3
