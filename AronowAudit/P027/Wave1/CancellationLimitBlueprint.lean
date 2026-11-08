import AronowAudit.P027.Wave1.GaussianMomentsBlueprint
import Mathlib.Probability.ProductMeasure

/-! # Blueprint: refutation of `AronowAudit.P027.cancellation_model_limit_reading` (P027-T7, R2)

Dossier group P027, record 10. The frozen contract (source
`AronowAudit/P027/P027_Audit.lean`, `cancellation_model_limit_reading`, a `sorry` draft)
is the explicitly labelled R2 fixed-fraction reading of supplement p. A4: on a
common probability space, under the calibrated Gaussian generator at `r ∈ {2,10}`
and every `m = n+1`, raw `A` OR its mean-scale bias `A/N²` converges in probability
to zero. Resolution `refute` (map-P027, accepted by both referees without fixes).

Paper proof (map-P027 report, record 10): at `r = 2` (`q = 4`), `ρ = 99/100`, the
countable product `μ = ⊗_ℕ N(0, 1791/100)` with `ε_{n,k}(ξ) = ξ(phaseIndex k)` and
`β_n = (15/2) ρ √((N−1)/N)`, `N = 4(n+1)`, satisfies every hypothesis. Writing
`A_n/N² = −Σ_g (a_{n,g} + R_{n,g})²` (signal plus normalized centered phase noise),
`E[Σ_g R²] = σ²(q−1)/(qN) → 0` gives `Σ_g R² → 0` in probability (Markov), the
square inequality `|B + S| ≤ tS + (1+1/t)T` controls the cross term, and
`S_n = Σ_g a² → 900ρ²/q`; hence `A_n/N² → −900ρ²/q = −88209/400 ≠ 0` in
probability. Uniqueness of limits in measure and `N² ≥ 1` refute both alternatives.

The frozen target is the negation of the exact recorded contract. The final
declaration (writer) is `AronowAudit.P027.Wave1.cancellation_model_limit_counterexample`
in `AronowAudit/P027/Wave1/CancellationLimit.lean`. Never use the false draft
`cancellation_model_limit_reading` as a premise.
-/

namespace AronowAudit.P027.Wave1.CancellationLimit

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

/-- Frozen target: the negation of the exact recorded contract of
`AronowAudit.P027.cancellation_model_limit_reading` (all binders as in the source). -/
def Target : Prop :=
  ¬ (∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
      (r : ℕ) (hr : 0 < r), r = 2 ∨ r = 10 → ∀ (ρ : ℝ), |ρ| ≤ 1 →
      ∀ (β : ℕ → ℝ) (ε : (n : ℕ) → (Σ _ : Fin r × Fin 2, Fin (n+1)) → Ξ → ℝ),
      (∀ n, GaussianNoise μ (ε n) (900*(1-ρ^2))) →
      (∀ n, (β n)^2 =
        900*ρ^2*((((n+1:ℕ):ℝ)*(2*r))-1)/(16*(((n+1:ℕ):ℝ)*(2*r)))) →
      TendstoInMeasure μ (fun n ξ => biasA (phaseOriginal r (n+1) hr)
          (centeredOutcomes phaseSize (β n) (ε n) ξ)) atTop (fun _ => 0) ∨
      TendstoInMeasure μ (fun n ξ => biasA (phaseOriginal r (n+1) hr)
          (centeredOutcomes phaseSize (β n) (ε n) ξ)/(((n+1:ℕ):ℝ)*(2*r))^2)
          atTop (fun _ => 0))

/-- Fidelity check: `Target` is literally the negation of the frozen contract. -/
example : Target ↔ ¬ (type_of% @AronowAudit.P027.cancellation_model_limit_reading) :=
  Iff.rfl

/-- Normalized signal of phase `g`: `a_g = m β (∓4) / N`, `N = m·2r`. -/
def signal (r m : ℕ) (β : ℝ) (g : Fin r × Fin 2) : ℝ :=
  (m:ℝ)*β*(if g.2 = 0 then -4 else 4)/((m:ℝ)*(2*r))

/-- Normalized centered phase noise `R_g = (Σ_k c_{gk} ε_k)/N` with the source
coefficients `phaseNoiseCoeff` (`1 − 1/q` inside `g`, `−1/q` outside). -/
def noise {Ξ : Type} (r m : ℕ) (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (ξ : Ξ)
    (g : Fin r × Fin 2) : ℝ :=
  (∑ k : Σ _ : Fin r × Fin 2, Fin m, phaseNoiseCoeff g k * ε k ξ)/((m:ℝ)*(2*r))

/-- N1 (shared node; map-P027 "Gaussian-to-moment bridge"): proved once as
`AronowAudit.P027.Wave1.gaussian_noise_moments`. -/
def N1 : Prop := GaussianMoments.Target

/-- N2 (paper-proof step "The actual centered phase total divided by N is
a_(n,g)+R_(n,g) ... The negative-square identity for biasA therefore gives
B_n := A_n/N² = −Σg(a_(n,g)+R_(n,g))²"); use `centered_outcomes_zero`,
`periodic_negative_square` and `phase_centered_total_formula`. Pointwise in `ξ`. -/
def N2 : Prop :=
  ∀ (r m : ℕ) (hr : 0 < r), 0 < m → ∀ {Ξ : Type} (β : ℝ)
    (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ) (ξ : Ξ),
    biasA (phaseOriginal r m hr) (centeredOutcomes phaseSize β ε ξ) / ((m:ℝ)*(2*r))^2 =
      -∑ g : Fin r × Fin 2, (signal r m β g + noise r m ε ξ g)^2

/-- N3 (paper-proof step "Its mean is zero and its second moment is σ²m(1−1/q) ...
Hence R_(n,g)² is integrable and E(R_(n,g)²)=σ²m(1−1/q)/N². Put T_n=Σg R_(n,g)². Then
T_n ≥ 0, is integrable and E(T_n)=σ²(q−1)/(qN)"); use `noise_linear_moments` and
`phase_noise_coeff_square_sum`. -/
def N3 : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (r m : ℕ), 0 < r → 0 < m →
    ∀ (σ2 : ℝ) (ε : (Σ _ : Fin r × Fin 2, Fin m) → Ξ → ℝ), NoiseMoments μ ε σ2 →
    Integrable (fun ξ => ∑ g : Fin r × Fin 2, (noise r m ε ξ g)^2) μ ∧
    ∫ ξ, ∑ g : Fin r × Fin 2, (noise r m ε ξ g)^2 ∂μ =
      σ2 * (2*(r:ℝ) - 1) / (2*(r:ℝ) * ((m:ℝ)*(2*r)))

/-- N4 (standard input; paper-proof step "Markov's inequality gives
P(T_n ≥ u) ≤ σ²(q−1)/(qNu) → 0"): nonnegative integrable functions whose integrals
tend to zero tend to zero in measure (Markov; or L¹-convergence implies convergence
in measure, `tendstoInMeasure_of_tendsto_eLpNorm`). -/
def N4 : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) (T : ℕ → Ξ → ℝ),
    (∀ n ξ, 0 ≤ T n ξ) → (∀ n, Integrable (T n) μ) →
    Tendsto (fun n => ∫ ξ, T n ξ ∂μ) atTop (𝓝 0) →
    TendstoInMeasure μ T atTop (fun _ => 0)

/-- N5 (paper-proof step "For every t>0 and real a,R, both inequalities
±2aR ≤ t a²+R²/t follow by expanding (ta∓R)² ≥ 0 ... Summing over g and also using
T_n ≥ 0 yields |B_n+S_n| ≤ t S_n + (1+1/t)T_n"), pointwise and deterministic. -/
def N5 : Prop :=
  ∀ {ι : Type} [Fintype ι] (a R : ι → ℝ) (t : ℝ), 0 < t →
    |(-∑ i, (a i + R i)^2) + ∑ i, (a i)^2| ≤
      t * ∑ i, (a i)^2 + (1 + 1/t) * ∑ i, (R i)^2

/-- N6 (paper-proof step "For δ>0 choose t=δ/[2(M+1)]>0 and u=δ/[2(1+1/t)]>0. If
T_n<u, the right-hand side is strictly less than δ ... Combining this with the
deterministic limit of −S_n proves B_n→−900ρ²/q in probability"), generic. No
measurability or finiteness of `μ` is needed. -/
def N6 : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) (B : ℕ → Ξ → ℝ) (S : ℕ → ℝ)
    (T : ℕ → Ξ → ℝ) (M : ℝ), (∀ n, 0 ≤ S n) → (∀ n ξ, 0 ≤ T n ξ) →
    (∀ t : ℝ, 0 < t → ∀ n ξ, |B n ξ + S n| ≤ t * S n + (1 + 1/t) * T n ξ) →
    Tendsto S atTop (𝓝 M) → TendstoInMeasure μ T atTop (fun _ => 0) →
    TendstoInMeasure μ B atTop (fun _ => -M)

/-- N7 (paper-proof step "Set S_n=Σg a_(n,g)²=16β_n²/q. Calibration implies
0 ≤ S_n ≤ M := 900ρ²/q and S_n → 900ρ²/q"), deterministic. -/
def N7 : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (ρ : ℝ) (β : ℕ → ℝ),
    (∀ n, (β n)^2 =
      900*ρ^2*((((n+1:ℕ):ℝ)*(2*r))-1)/(16*(((n+1:ℕ):ℝ)*(2*r)))) →
    Tendsto (fun n => ∑ g : Fin r × Fin 2, (signal r (n+1) (β n) g)^2) atTop
      (𝓝 (900*ρ^2/(2*r)))

/-- N8 (paper-proof step "For a fixed n this coordinate map is injective: reduce its
index modulo 4 to recover 2i+b, then recover b modulo 2 and i, and finally j"). -/
def N8 : Prop :=
  ∀ (r m : ℕ), Function.Injective (fun k : Σ _ : Fin r × Fin 2, Fin m => phaseIndex k)

/-- N9 (paper-proof step "Therefore the finite errors are measurable, independent,
and each has exactly N(0,σ²) law, so GaussianNoise holds"): coordinates of the
countable Gaussian product along an injective index map. -/
def N9 : Prop :=
  ∀ {K : Type} (f : K → ℕ), Function.Injective f → ∀ (σ2 : ℝ),
    GaussianNoise (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 σ2.toNNReal))
      (fun k (ξ : ℕ → ℝ) => ξ (f k)) σ2

/-- N10 (paper-proof step "A probability limit is unique almost surely ... If raw A_n
converged in probability to zero, then B_n=A_n/N² would too: N²≥1"); use
`tendstoInMeasure_ae_unique` (no measurability needed). -/
def N10 : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (A : ℕ → Ξ → ℝ) (w : ℕ → ℝ) (c : ℝ), (∀ n, 1 ≤ w n) → c ≠ 0 →
    TendstoInMeasure μ (fun n ξ => A n ξ / w n) atTop (fun _ => c) →
    ¬ (TendstoInMeasure μ A atTop (fun _ => 0) ∨
       TendstoInMeasure μ (fun n ξ => A n ξ / w n) atTop (fun _ => 0))

/-- Intermediate statement (map-P027 `periodic_calibrated_bias_in_measure`, a
reusable extension of corrected T2(vi)): for any common probability space and any
arrays with the stated second moments, `A_n/N_n² → −900ρ²/(2r)` in probability. -/
def CalibratedInMeasure : Prop :=
  ∀ {Ξ : Type} [MeasurableSpace Ξ] (μ : Measure Ξ) [IsProbabilityMeasure μ]
    (r : ℕ) (hr : 0 < r) (ρ : ℝ), |ρ| ≤ 1 → ∀ (β : ℕ → ℝ)
    (ε : (n : ℕ) → (Σ _ : Fin r × Fin 2, Fin (n+1)) → Ξ → ℝ),
    (∀ n, NoiseMoments μ (ε n) (900*(1-ρ^2))) →
    (∀ n, (β n)^2 =
      900*ρ^2*((((n+1:ℕ):ℝ)*(2*r))-1)/(16*(((n+1:ℕ):ℝ)*(2*r)))) →
    TendstoInMeasure μ (fun n ξ => biasA (phaseOriginal r (n+1) hr)
        (centeredOutcomes phaseSize (β n) (ε n) ξ)/(((n+1:ℕ):ℝ)*(2*r))^2)
      atTop (fun _ => -900*ρ^2/(2*r))

/-- N2–N7 suffice for the intermediate probability limit. -/
theorem calibrated_in_measure (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6)
    (h7 : N7) : CalibratedInMeasure := by
  intro Ξ _ μ _ r hr ρ _ β ε hε hβ
  have hr' : (r:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hT : TendstoInMeasure μ
      (fun n ξ => ∑ g : Fin r × Fin 2, (noise r (n+1) (ε n) ξ g)^2) atTop (fun _ => 0) := by
    apply h4 μ
    · intro n ξ
      exact Finset.sum_nonneg (fun g _ => sq_nonneg _)
    · intro n
      exact (h3 μ r (n+1) hr n.succ_pos _ (ε n) (hε n)).1
    · have he : (fun n => ∫ ξ, ∑ g : Fin r × Fin 2, (noise r (n+1) (ε n) ξ g)^2 ∂μ) =
          fun n : ℕ => 900*(1-ρ^2)*(2*(r:ℝ)-1)/(2*(r:ℝ)*(((n+1:ℕ):ℝ)*(2*r))) := by
        funext n
        exact (h3 μ r (n+1) hr n.succ_pos _ (ε n) (hε n)).2
      rw [he]
      have hlim := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (900*(1-ρ^2)*(2*(r:ℝ)-1)/(2*(r:ℝ)*(2*r)))
      rw [mul_zero] at hlim
      refine hlim.congr (fun n => ?_)
      have hn : ((n:ℝ)+1) ≠ 0 := by positivity
      push_cast
      field_simp
  have hB := h6 μ
    (fun n ξ => -∑ g : Fin r × Fin 2, (signal r (n+1) (β n) g + noise r (n+1) (ε n) ξ g)^2)
    (fun n => ∑ g : Fin r × Fin 2, (signal r (n+1) (β n) g)^2)
    (fun n ξ => ∑ g : Fin r × Fin 2, (noise r (n+1) (ε n) ξ g)^2) (900*ρ^2/(2*r))
    (fun n => Finset.sum_nonneg (fun g _ => sq_nonneg _))
    (fun n ξ => Finset.sum_nonneg (fun g _ => sq_nonneg _))
    (fun t ht n ξ => h5 _ _ t ht) (h7 r hr ρ β hβ) hT
  have hc : (-(900*ρ^2/(2*(r:ℝ)))) = -900*ρ^2/(2*r) := by ring
  rw [hc] at hB
  refine hB.congr_left (fun n => Filter.Eventually.of_forall (fun ξ => ?_))
  exact (h2 r (n+1) hr n.succ_pos (β n) (ε n) ξ).symm

/-- Witness law: countable product of `N(0, 900(1−ρ²))` at `ρ = 99/100`
(variance `1791/100`). -/
def witnessMeasure : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => gaussianReal 0 (900*(1-(99/100:ℝ)^2)).toNNReal)

instance : IsProbabilityMeasure witnessMeasure := by
  unfold witnessMeasure; infer_instance

/-- Witness errors: `ε_{n,k}(ξ) = ξ(phaseIndex k)` (shared coordinates across `n`
are allowed by the contract). -/
def witnessNoise : (n : ℕ) → (Σ _ : Fin 2 × Fin 2, Fin (n+1)) → (ℕ → ℝ) → ℝ :=
  fun _ k ξ => ξ (phaseIndex k)

/-- Witness slopes `β_n = (15/2) ρ √((N−1)/N)`, `N = 4(n+1)`, `ρ = 99/100`. -/
def witnessBeta (n : ℕ) : ℝ :=
  (15/2 : ℝ) * (99/100) * Real.sqrt ((4 * ((n+1:ℕ):ℝ) - 1) / (4 * ((n+1:ℕ):ℝ)))

/-- The witness slopes satisfy the exact recorded calibration at `r = 2`. -/
theorem witnessBeta_sq (n : ℕ) : (witnessBeta n)^2 =
    900*(99/100:ℝ)^2*((((n+1:ℕ):ℝ)*(2*((2:ℕ):ℝ)))-1)/(16*(((n+1:ℕ):ℝ)*(2*((2:ℕ):ℝ)))) := by
  have h1 : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
  have hnn : (0:ℝ) ≤ (4 * ((n+1:ℕ):ℝ) - 1) / (4 * ((n+1:ℕ):ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  rw [witnessBeta, mul_pow, Real.sq_sqrt hnn]
  have hpos : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
  field_simp
  push_cast
  ring

/-- The nodes suffice. The contract applied to the explicit witness yields the
disjunction; N1 turns the witness's Gaussian noise into `NoiseMoments`, the
intermediate limit gives `A_n/N_n² → −88209/400`, and N10 refutes the disjunction. -/
theorem assemble (h1 : N1) (h2 : N2) (h3 : N3) (h4 : N4) (h5 : N5) (h6 : N6)
    (h7 : N7) (h8 : N8) (h9 : N9) (h10 : N10) : Target := by
  intro hcon
  have hσ : (0:ℝ) ≤ 900*(1-(99/100:ℝ)^2) := by norm_num
  have hρ : |(99/100:ℝ)| ≤ 1 := by rw [abs_le]; constructor <;> norm_num
  have hg : ∀ n, GaussianNoise witnessMeasure (witnessNoise n) (900*(1-(99/100:ℝ)^2)) :=
    fun n => h9 (fun k : Σ _ : Fin 2 × Fin 2, Fin (n+1) => phaseIndex k) (h8 2 (n+1))
      (900*(1-(99/100:ℝ)^2))
  have hdisj := hcon witnessMeasure 2 (by norm_num) (Or.inl rfl) (99/100) hρ witnessBeta
    witnessNoise hg witnessBeta_sq
  have hlim := calibrated_in_measure h2 h3 h4 h5 h6 h7 witnessMeasure 2 (by norm_num)
    (99/100) hρ witnessBeta witnessNoise
    (fun n => h1 witnessMeasure (witnessNoise n) _ hσ (hg n)) witnessBeta_sq
  have hw : ∀ n : ℕ, (1:ℝ) ≤ (((n+1:ℕ):ℝ)*(2*((2:ℕ):ℝ)))^2 := by
    intro n
    have h1n : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
    have h4 : (1:ℝ) ≤ ((n+1:ℕ):ℝ)*(2*((2:ℕ):ℝ)) := by push_cast at h1n ⊢; nlinarith
    nlinarith
  exact h10 witnessMeasure
    (fun n ξ => biasA (phaseOriginal 2 (n+1) (by norm_num))
      (centeredOutcomes phaseSize (witnessBeta n) (witnessNoise n) ξ))
    (fun n => (((n+1:ℕ):ℝ)*(2*((2:ℕ):ℝ)))^2) (-900*(99/100:ℝ)^2/(2*((2:ℕ):ℝ)))
    hw (by norm_num) hlim hdisj

end
end AronowAudit.P027.Wave1.CancellationLimit
