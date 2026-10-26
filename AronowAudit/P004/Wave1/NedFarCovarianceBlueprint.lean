import AronowAudit.P004.Wave1.FiniteConditioningBlueprint
import AronowAudit.P004.P004_VarianceComponentsCompletion

/-! # Corrected far-pair covariance bound (P004-T29(1))

Supplement A Lemma C.9(iii), equation (109), concerns the random rows `v̂_i` of (107)
at distances `d_ij > 3 b_N`. The bound here assumes bounded outcomes, metric node
distances, uniform quadratic spacing `C_b(1+s²)` for `s ≥ 0`, the kernel conditions C5,
and a uniform NED bound. Finding P004-E018 concerns the radius-uniform spacing constant;
P004-E021 concerns the far-pair condition.

The bound is uniform over deterministic fits `μ₁, μ₀` bounded by `M`, with the constant
chosen before the fits. Its second conjunct specializes to the population arm means
`barMu`. Well-definedness and `1 ≤ bandwidth` are needed only eventually.

Project onto disjoint `T`-balls with `T = d_ij/3`. The product error bound is
`||v_i−ṽ_i||₂ ≤ 2LAH S_i/N²`. Covariance Cauchy–Schwarz and `m_i ≤ 2C_b b²` for `b ≥ 1`
give the final constant `8 C_b L² A³ H`.
-/

universe u

namespace AronowAudit.P004.Wave1.NedFarCovariance

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open scoped BigOperators

/-- The bound uniformly over all deterministic fits bounded by `M`
(Lemma C.9 as printed, with the P004-E021 far-pair condition and the P004-E018
uniform spacing), and the `barMu` specialization. -/
def Target : Prop :=
  ∀ {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)] [∀ N, MeasurableSpace (Space N)]
    (P : PopulationSequence Space) (p d : ℝ) (K ψ : ℝ → ℝ) (bandwidth : ℕ → ℝ)
    (_hp : 0 < p ∧ p < 1) (_hb : BoundedOutcomes P) (_hmetric : MetricNodeDistances P)
    (_hspacing : QuadraticSpacing P) (_hK : KernelConditions K)
    (_hψ : ∀ s, 0 ≤ s → 0 ≤ ψ s) (_hψanti : AntitoneOn ψ (Set.Ici 0))
    (_hNED : ∃ G : ℝ, ∀ N i s, 0 ≤ s → l2Norm (fun _ => p)
      (fun z => circleAverage (P N) d i z - conditionOn (fun _ => p)
        (ball (nodeSeparation (P N)) i s) (circleAverage (P N) d i) z) ≤ G*ψ s)
    (_hWD : ∀ᶠ N in atTop, WellDefined (P N) d) (_hband : ∀ᶠ N in atTop, 1 ≤ bandwidth N),
    (∀ M : ℝ, 0 < M → ∃ C : ℝ, ∀ᶠ N in atTop, ∀ μ1 μ0 : ℝ, |μ1| < M → |μ0| < M →
      ∀ i j, 3*bandwidth N < nodeSeparation (P N) i j →
      |cov (fun _ => p)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N) μ1 μ0 i)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N) μ1 μ0 j)| ≤
      C*(bandwidth N)^2/(N : ℝ)^4 * max
        (∑ k ∈ ball (nodeSeparation (P N)) i (bandwidth N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) i k))
        (∑ l ∈ ball (nodeSeparation (P N)) j (bandwidth N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) j l))) ∧
    (∃ C : ℝ, ∀ᶠ N in atTop, ∀ i j, 3*bandwidth N < nodeSeparation (P N) i j →
      |cov (fun _ => p)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N)
          (barMu (fun _ => p) (circleAverage (P N) d) true)
          (barMu (fun _ => p) (circleAverage (P N) d) false) i)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bandwidth N)
          (barMu (fun _ => p) (circleAverage (P N) d) true)
          (barMu (fun _ => p) (circleAverage (P N) d) false) j)| ≤
      C*(bandwidth N)^2/(N : ℝ)^4 * max
        (∑ k ∈ ball (nodeSeparation (P N)) i (bandwidth N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) i k))
        (∑ l ∈ ball (nodeSeparation (P N)) j (bandwidth N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) j l)))

/-- The single-`N` standing hypotheses of the far-pair computation: positive sample size,
interior coin, table bound `B`, fit bound `M`, node distances satisfying the pseudometric
axioms, nonnegative antitone `ψ`, the uniform NED bound with coefficient `G`, kernel bound
`L` on `[0,∞)`, bandwidth `b>0`. -/
structure FarSetting {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ)
    (K ψ : ℝ → ℝ) (B M G L b : ℝ) : Prop where
  hN : 0 < N
  hp : 0 < p ∧ p < 1
  hB : ∀ i z, |R i z| ≤ B
  hB0 : 0 ≤ B
  hM : 0 ≤ M
  hD0 : ∀ i j, 0 ≤ D i j
  hDself : ∀ i, D i i = 0
  hDsymm : ∀ i j, D i j = D j i
  hDtri : ∀ i j k, D i k ≤ D i j + D j k
  hψ : ∀ s, 0 ≤ s → 0 ≤ ψ s
  hψanti : AntitoneOn ψ (Set.Ici 0)
  hNED : ∀ i s, 0 ≤ s → l2Norm (fun _ => p)
    (fun z => R i z - conditionOn (fun _ => p) (ball D i s) (R i) z) ≤ G * ψ s
  hK : ∀ t, 0 ≤ t → |K t| ≤ L
  hb : 0 < b

/-- `ẽ_k = E[ε_k | Z_J]`, the projected epsilon (paper: "Let ẽ_k=E_{B(i,T)}e_k"). -/
def projEps {N : ℕ} (p : ℝ) (R : CircleTable N) (μ1 μ0 : ℝ) (J : Finset (Fin N))
    (k : Fin N) : Assignment N → ℝ :=
  conditionOn (fun _ => p) J (nedEpsilon p R μ1 μ0 k)

/-- `ṽ_i = Σ_{k∈B(i,b)} K(d_ik/b) ẽ_i ẽ_k` with every factor projected onto `J`
(paper: "define ṽ_i=Σ_{k∈B(i,b)} K(d_ik/b)ẽ_i ẽ_k"). -/
def projRow {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ) (K : ℝ → ℝ)
    (b μ1 μ0 : ℝ) (J : Finset (Fin N)) (i : Fin N) (z : Assignment N) : ℝ :=
  ∑ k ∈ ball D i b, projEps p R μ1 μ0 J i z * projEps p R μ1 μ0 J k z * K (D i k / b)

/-- For bounded outcomes and fits, the epsilon magnitude is bounded by
`(B+M)/(qN)`, where `q = min p (1-p)`. For every conditioning set `J` containing `i`,
the epsilon projection error is at most the outcome projection error divided by `qN`. -/
def E1 : Prop :=
  ∀ {N : ℕ} (p : ℝ) (R : CircleTable N) (B M μ1 μ0 : ℝ), 0 < N → 0 < p ∧ p < 1 →
    (∀ i z, |R i z| ≤ B) → |μ1| ≤ M → |μ0| ≤ M →
    (∀ i z, |nedEpsilon p R μ1 μ0 i z| ≤ (B + M) / (min p (1-p) * N)) ∧
    (∀ (i : Fin N) (J : Finset (Fin N)), i ∈ J →
      l2Norm (fun _ => p) (fun z => nedEpsilon p R μ1 μ0 i z -
          conditionOn (fun _ => p) J (nedEpsilon p R μ1 μ0 i) z) ≤
        l2Norm (fun _ => p) (fun z => R i z - conditionOn (fun _ => p) J (R i) z) /
          (min p (1-p) * N))

/-- Under `FarSetting` and bounded fits, projection onto `B(i,T)` for `T > b`
has L² error at most `2LAH S_i/N²`, where `q = min p (1-p)`, `A = (B+M)/q`,
`H = |G|/q`, and `S_i = ∑ k ∈ B(i,b), ψ(T-D i k)`. Both rows have pointwise
magnitude at most `LA² |B(i,b)|/N²`; the projected row depends only on `B(i,T)`. -/
def E2 : Prop :=
  ∀ {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ) (K ψ : ℝ → ℝ)
    (B M G L b μ1 μ0 : ℝ) (i : Fin N) (T : ℝ),
    FarSetting p R D K ψ B M G L b → |μ1| ≤ M → |μ0| ≤ M → b < T →
    l2Norm (fun _ => p) (fun z => nedVRow p R D K b μ1 μ0 i z -
        projRow p R D K b μ1 μ0 (ball D i T) i z) ≤
      2 * L * ((B + M) / min p (1-p)) * (|G| / min p (1-p)) *
        (∑ k ∈ ball D i b, ψ (T - D i k)) / (N : ℝ)^2 ∧
    (∀ z, |nedVRow p R D K b μ1 μ0 i z| ≤
      L * ((B + M) / min p (1-p))^2 * ((ball D i b).card : ℝ) / (N : ℝ)^2) ∧
    (∀ z, |projRow p R D K b μ1 μ0 (ball D i T) i z| ≤
      L * ((B + M) / min p (1-p))^2 * ((ball D i b).card : ℝ) / (N : ℝ)^2) ∧
    DependsOn (projRow p R D K b μ1 μ0 (ball D i T) i) (↑(ball D i T) : Set (Fin N))

/-- Under `FarSetting` and bounded fits, the far-pair covariance bound for
`D i j > 3b` uses the actual `b`-ball counts and the NED-error sums at radius `D i j/3`. -/
def E3 : Prop :=
  ∀ {N : ℕ} (p : ℝ) (R : CircleTable N) (D : Fin N → Fin N → ℝ) (K ψ : ℝ → ℝ)
    (B M G L b μ1 μ0 : ℝ),
    FarSetting p R D K ψ B M G L b → |μ1| ≤ M → |μ0| ≤ M →
    ∀ i j, 3 * b < D i j →
      |cov (fun _ => p) (nedVRow p R D K b μ1 μ0 i) (nedVRow p R D K b μ1 μ0 j)| ≤
        2 * L^2 * ((B + M) / min p (1-p))^3 * (|G| / min p (1-p)) *
          (((ball D j b).card : ℝ) * (∑ k ∈ ball D i b, ψ (D i j / 3 - D i k)) +
            ((ball D i b).card : ℝ) * (∑ l ∈ ball D j b, ψ (D i j / 3 - D j l))) / (N : ℝ)^4

/-- Elementary bound on a population arm mean. -/
theorem barMu_abs_le {N : ℕ} (p : ℝ) (hp : 0 < p ∧ p < 1) (R : CircleTable N) (B : ℝ)
    (hB0 : 0 ≤ B) (hR : ∀ i z, |R i z| ≤ B) (a : Bool) : |barMu (fun _ => p) R a| ≤ B := by
  unfold barMu
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simpa using hB0
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    rw [abs_div, abs_of_pos hN', div_le_iff₀ hN']
    calc |∑ i, marginal (fun _ => p) R i a| ≤ ∑ i : Fin N, |marginal (fun _ => p) R i a| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin N, B := Finset.sum_le_sum fun i _ =>
          ComponentCompletion.marginal_abs_le (fun _ => p) (fun _ => hp) R B hR i a
      _ = B * N := by simp [mul_comm]

/-- Constants from the quadratic ball-count bound: `m ≤ 2C_b b²` and
`m_j S_i + m_i S_j ≤ 4 C_b b² max(S_i,S_j)`. -/
theorem far_algebra (X mi mj Si Sj Cb b : ℝ) (hX : 0 ≤ X) (hSi : 0 ≤ Si) (hSj : 0 ≤ Sj)
    (hmi0 : 0 ≤ mi) (hmj0 : 0 ≤ mj) (hmi : mi ≤ 2 * Cb * b^2) (hmj : mj ≤ 2 * Cb * b^2) :
    X * (mj * Si + mi * Sj) ≤ X * (4 * Cb * b^2) * max Si Sj := by
  have h1 : mj * Si ≤ (2 * Cb * b^2) * max Si Sj :=
    mul_le_mul hmj (le_max_left _ _) hSi (le_trans hmj0 hmj)
  have h2 : mi * Sj ≤ (2 * Cb * b^2) * max Si Sj :=
    mul_le_mul hmi (le_max_right _ _) hSj (le_trans hmi0 hmi)
  have := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hX
  linarith

/-- The component bounds imply the result: eventual bounds from the sequence hypotheses to
`FarSetting`, the finite bound E3, and the constant `C = 8 C_b L² A³ H`; then the `barMu`
clause from the bounded-fit clause with `M = B + 1`. -/
theorem assemble (hE3 : E3) : Target.{u} := by
  intro Space _ _ P p d K ψ bw hp hb hmetric hspacing hK hψ hψanti hNED hWD hband
  obtain ⟨Bo, hBo, hBoev⟩ := hb
  have hbound : ∀ᶠ N in atTop, ∀ i z, |circleAverage (P N) d i z| ≤ Bo := by
    filter_upwards [hBoev, hWD] with N hBN hWDN
    intro i z
    exact CLTCompletion.circleAverage_abs_le (P N) d Bo hWDN (fun x z => (hBN x z).le) i z
  have hgen : ∀ M : ℝ, 0 < M → ∃ C : ℝ, ∀ᶠ N in atTop, ∀ μ1 μ0 : ℝ, |μ1| < M → |μ0| < M →
      ∀ i j, 3*bw N < nodeSeparation (P N) i j →
      |cov (fun _ => p)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bw N) μ1 μ0 i)
        (nedVRow p (circleAverage (P N) d) (nodeSeparation (P N)) K (bw N) μ1 μ0 j)| ≤
      C*(bw N)^2/(N : ℝ)^4 * max
        (∑ k ∈ ball (nodeSeparation (P N)) i (bw N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) i k))
        (∑ l ∈ ball (nodeSeparation (P N)) j (bw N),
          ψ (nodeSeparation (P N) i j/3-nodeSeparation (P N) j l)) := by
    intro M hM
    obtain ⟨Cb, hCb, hsp⟩ := hspacing
    obtain ⟨G, hG⟩ := hNED
    obtain ⟨-, -, ⟨Kmax, hKmax⟩, -⟩ := hK
    have hq : 0 < min p (1-p) := lt_min hp.1 (sub_pos.mpr hp.2)
    have hKm : 0 ≤ Kmax := le_trans (abs_nonneg _) (hKmax 0 le_rfl).le
    have hA : 0 ≤ (Bo + M) / min p (1-p) := div_nonneg (by linarith) hq.le
    have hH : 0 ≤ |G| / min p (1-p) := div_nonneg (abs_nonneg _) hq.le
    refine ⟨8 * Cb * Kmax^2 * ((Bo + M) / min p (1-p))^3 * (|G| / min p (1-p)), ?_⟩
    filter_upwards [hbound, hsp, hband, eventually_gt_atTop 0] with N hRN hspN hbN hN
    intro μ1 μ0 h1 h0 i j hij
    have hset : FarSetting p (circleAverage (P N) d) (nodeSeparation (P N)) K ψ Bo M G Kmax
        (bw N) :=
      { hN := hN, hp := hp, hB := hRN, hB0 := hBo.le, hM := hM.le,
        hD0 := (hmetric N).1,
        hDself := fun i => ((hmetric N).2.1 i i).mpr rfl,
        hDsymm := (hmetric N).2.2.1, hDtri := (hmetric N).2.2.2,
        hψ := hψ, hψanti := hψanti, hNED := fun i s hs => hG N i s hs,
        hK := fun t ht => (hKmax t ht).le, hb := lt_of_lt_of_le one_pos hbN }
    have h3 := hE3 p _ _ K ψ Bo M G Kmax (bw N) μ1 μ0 hset h1.le h0.le i j hij
    refine le_trans h3 ?_
    set D := nodeSeparation (P N)
    have hS : ∀ i' : Fin N, i' = i ∨ i' = j → 0 ≤ ∑ k ∈ ball D i' (bw N), ψ (D i j / 3 - D i' k) := by
      intro i' hi'
      apply Finset.sum_nonneg
      intro k hk
      apply hψ
      have hk' : D i' k ≤ bw N := by
        simpa only [ball, Finset.mem_filter, Finset.mem_univ, true_and] using hk
      linarith
    have hm : ∀ i' : Fin N, ((ball D i' (bw N)).card : ℝ) ≤ 2 * Cb * (bw N)^2 := by
      intro i'
      have h := hspN i' (bw N) (by linarith)
      have hb2 : 1 ≤ (bw N)^2 := by nlinarith
      nlinarith
    have hX : 0 ≤ 2 * Kmax^2 * ((Bo + M) / min p (1-p))^3 * (|G| / min p (1-p)) /
        (N : ℝ)^4 := by positivity
    have key := far_algebra (2 * Kmax^2 * ((Bo + M) / min p (1-p))^3 * (|G| / min p (1-p)) /
        (N : ℝ)^4) _ _ _ _ Cb (bw N) hX (hS i (Or.inl rfl)) (hS j (Or.inr rfl))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) (hm i) (hm j)
    calc 2 * Kmax^2 * ((Bo + M) / min p (1-p))^3 * (|G| / min p (1-p)) *
          (((ball D j (bw N)).card : ℝ) * (∑ k ∈ ball D i (bw N), ψ (D i j / 3 - D i k)) +
            ((ball D i (bw N)).card : ℝ) * (∑ l ∈ ball D j (bw N), ψ (D i j / 3 - D j l))) /
              (N : ℝ)^4
        = 2 * Kmax^2 * ((Bo + M) / min p (1-p))^3 * (|G| / min p (1-p)) / (N : ℝ)^4 *
          (((ball D j (bw N)).card : ℝ) * (∑ k ∈ ball D i (bw N), ψ (D i j / 3 - D i k)) +
            ((ball D i (bw N)).card : ℝ) * (∑ l ∈ ball D j (bw N), ψ (D i j / 3 - D j l))) := by
          ring
      _ ≤ _ := key
      _ = _ := by ring
  refine ⟨hgen, ?_⟩
  obtain ⟨C, hC⟩ := hgen (Bo + 1) (by linarith)
  refine ⟨C, ?_⟩
  filter_upwards [hC, hbound] with N hCN hRN
  intro i j hij
  exact hCN _ _ (lt_of_le_of_lt (barMu_abs_le p hp _ Bo hBo.le hRN true) (by linarith))
    (lt_of_le_of_lt (barMu_abs_le p hp _ Bo hBo.le hRN false) (by linarith)) i j hij

end
end AronowAudit.P004.Wave1.NedFarCovariance
