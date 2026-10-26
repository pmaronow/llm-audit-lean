import AronowAudit.P004.Wave1.NedHeadlineBlueprint
import AronowAudit.P004.Wave1.NedHeadline.ENV
import AronowAudit.P004.Wave1.NedHeadline.COVSUM
import AronowAudit.P004.Wave1.FiniteConditioning.FC8

universe u

namespace AronowAudit.P004.Wave1.NedHeadline

set_option autoImplicit false
noncomputable section
open AronowAudit.P004 MeasureTheory Filter
open AronowAudit.P004.Wave1.DesignLimits
open scoped BigOperators

/-- Constants shared by the HT, arm-residual and centered linear scores. The raw
outcome bound and spacing bound are needed only eventually; the NED bound holds
for every `N`, as required by LOCCLT. -/
structure ScoreEnvelope {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space) (p d : ℝ) where
  B : ℝ
  L : ℝ
  G : ℝ
  Cb : ℝ
  A : ℝ
  e : ℝ
  ψ : ℝ → ℝ
  hB : 0 < B
  hL : 0 < L
  hL1 : 1 / p ≤ L
  hL0 : 1 / (1 - p) ≤ L
  hG : 0 ≤ G
  hCb : 0 < Cb
  hA : 0 ≤ A
  he : 4 < e
  hψ : ∀ s, 0 ≤ s → 0 ≤ ψ s
  hψanti : AntitoneOn ψ (Set.Ici 0)
  henv : ∀ t, 1 ≤ t → ψ t ≤ A * t ^ (-e)
  hmetric : ∀ N, MetricD (nodeSeparation (P N))
  hspacing : ∀ᶠ N in atTop, ∀ i s, 0 ≤ s →
    ((ball (nodeSeparation (P N)) i s).card : ℝ) ≤ Cb * (1 + s^2)
  hbound : ∀ᶠ N in atTop, ∀ i z, |circleAverage (P N) d i z| ≤ B
  hned : ∀ N i t, 0 ≤ t → l2Norm (fun _ => p)
    (fun z => circleAverage (P N) d i z -
      conditionOn (fun _ => p) (ball (nodeSeparation (P N)) i t)
        (circleAverage (P N) d i) z) ≤ G * ψ t

theorem exists_scoreEnvelope {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] (P : PopulationSequence Space) (p d : ℝ)
    (hS : Standing P p d) : Nonempty (ScoreEnvelope P p d) := by
  obtain ⟨B, hB, hBo⟩ := hS.hb
  obtain ⟨Cb, hCb, hsp⟩ := hS.hspacing
  obtain ⟨ψ, g, G, hψ, hanti, hψlim, hexp, hg, hned⟩ := hS.hNED
  obtain ⟨e, he, C, S, hSpos, henv⟩ := hexp
  obtain ⟨A, hA, henvA⟩ := env_proof ψ e C S hψ hanti (by linarith) hSpos henv
  have hp0 : 0 < 1 - p := sub_pos.mpr hS.hp.2
  have hbound : ∀ᶠ N in atTop, ∀ i z, |circleAverage (P N) d i z| ≤ B := by
    filter_upwards [hBo, hS.hWD] with N hBoN hWDN
    intro i z
    exact CLTCompletion.circleAverage_abs_le (P N) d B hWDN
      (fun x z => (hBoN x z).le) i z
  refine ⟨{
    B := B, L := 1 / p + 1 / (1 - p), G := |G|, Cb := Cb, A := A,
    e := e, ψ := ψ, hB := hB,
    hL := add_pos (one_div_pos.mpr hS.hp.1) (one_div_pos.mpr hp0),
    hL1 := by linarith [one_div_pos.mpr hp0],
    hL0 := by linarith [one_div_pos.mpr hS.hp.1],
    hG := abs_nonneg _, hCb := hCb, hA := hA, he := he, hψ := hψ,
    hψanti := hanti, henv := henvA, hmetric := ?_, hspacing := hsp,
    hbound := hbound, hned := ?_ }⟩
  · intro N
    exact ⟨(hS.hmetric N).1, fun i => ((hS.hmetric N).2.1 i i).mpr rfl,
      (hS.hmetric N).2.2.1, (hS.hmetric N).2.2.2⟩
  · intro N i t ht
    exact (hned N i t ht).trans
      (mul_le_mul_of_nonneg_right ((hg N i).2.trans (le_abs_self G)) (hψ t ht))

/-- Own-coin affine scores inherit the raw NED error with constant `L G`. -/
theorem ScoreEnvelope.affine_ned {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] {P : PopulationSequence Space} {p d : ℝ}
    (E : ScoreEnvelope P p d) (hp : 0 < p ∧ p < 1) (N : ℕ)
    (α β : Fin N → Bool → ℝ) (hα : ∀ i a, |α i a| ≤ E.L)
    (i : Fin N) (t : ℝ) (ht : 0 ≤ t) :
    l2Norm (fun _ => p) (fun z =>
      (α i (z i) * circleAverage (P N) d i z + β i (z i)) -
      conditionOn (fun _ => p) (ball (nodeSeparation (P N)) i t)
        (fun z => α i (z i) * circleAverage (P N) d i z + β i (z i)) z) ≤
      (E.L * E.G) * E.ψ t := by
  have hself : i ∈ ball (nodeSeparation (P N)) i t := by
    simp only [ball, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [(E.hmetric N).2.1 i]
    exact ht
  calc
    _ ≤ E.L * l2Norm (fun _ => p) (fun z => circleAverage (P N) d i z -
        conditionOn (fun _ => p) (ball (nodeSeparation (P N)) i t)
          (circleAverage (P N) d i) z) :=
      FiniteConditioning.fc8_proof (fun _ => p) (fun _ => hp) _ i hself
        (circleAverage (P N) d i) (α i) (β i) E.L (hα i)
    _ ≤ E.L * (E.G * E.ψ t) := mul_le_mul_of_nonneg_left (E.hned N i t ht) E.hL.le
    _ = _ := by ring

theorem ScoreEnvelope.affine_family {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] {P : PopulationSequence Space} {p d : ℝ}
    (E : ScoreEnvelope P p d) (hp : 0 < p ∧ p < 1) (N : ℕ)
    (hsp : ∀ i s, 0 ≤ s → ((ball (nodeSeparation (P N)) i s).card : ℝ) ≤
      E.Cb * (1 + s^2))
    (α β : Fin N → Bool → ℝ) (hα : ∀ i a, |α i a| ≤ E.L) :
    LocalFamily p (fun i z => α i (z i) * circleAverage (P N) d i z + β i (z i))
      (nodeSeparation (P N)) E.ψ (E.L * E.G) E.Cb E.A E.e := by
  exact {
    hp := hp, hD := E.hmetric N, hspacing := hsp, hCb := E.hCb,
    hψ := E.hψ, hψanti := E.hψanti, he := E.he, hA := E.hA, henv := E.henv,
    hKc := mul_nonneg E.hL.le E.hG, hNED := E.affine_ned hp N α β hα }

theorem ScoreEnvelope.contrast_coefficient {Space : ℕ → Type u} [∀ N, MetricSpace (Space N)]
    [∀ N, MeasurableSpace (Space N)] {P : PopulationSequence Space} {p d : ℝ}
    (E : ScoreEnvelope P p d) (hp : 0 < p ∧ p < 1) (a : Bool) :
    |bit a / p - (1 - bit a) / (1 - p)| ≤ E.L := by
  have hq : 0 < 1 - p := sub_pos.mpr hp.2
  cases a
  · simpa [bit, abs_div, abs_of_pos hq] using E.hL0
  · simpa [bit, abs_div, abs_of_pos hp.1] using E.hL1

theorem h2_proof : H2.{u} := by
  intro Space _ _ P p d hS
  obtain ⟨E⟩ := exists_scoreEnvelope P p d hS
  let M : ℝ := E.B / p + E.B / (1 - p)
  let V : ℝ := 10 * E.Cb * M^2 +
    74 * E.Cb * M * (E.L * E.G) * E.A / (1 - (2 : ℝ) ^ (2 - E.e))
  have hM : 0 ≤ M := add_nonneg (div_nonneg E.hB.le hS.hp.1.le)
    (div_nonneg E.hB.le (sub_pos.mpr hS.hp.2).le)
  refine Asymptotics.IsBigO.of_bound |V| ?_
  filter_upwards [E.hbound, E.hspacing, eventually_gt_atTop 0] with N hRN hsp hN
  let R := circleAverage (P N) d
  let X : Fin N → Assignment N → ℝ := residualContrast (fun _ => p) R (fun _ _ => 0)
  let α : Fin N → Bool → ℝ := fun _ a => bit a / p - (1 - bit a) / (1 - p)
  have hX : X = fun i z => α i (z i) * R i z + 0 := by
    funext i z
    dsimp [X, α, residualContrast]
    ring
  have hLF : LocalFamily p X (nodeSeparation (P N)) E.ψ (E.L * E.G) E.Cb E.A E.e := by
    rw [hX]
    exact E.affine_family hS.hp N hsp α (fun _ _ => 0)
      (fun _ a => E.contrast_coefficient hS.hp a)
  have hXB : ∀ i z, |X i z| ≤ M :=
    CLTCompletion.raw_contrast_abs_le p E.B R hS.hp E.hB.le hRN
  have hsum : variance (fun _ => p) (fun z => ∑ i, X i z) ≤ N * V :=
    covsum_proof p X (nodeSeparation (P N)) E.ψ (E.L * E.G) E.Cb E.A E.e M hLF hM hXB
  have hht : ht (fun _ => p) R = fun z => (∑ i, X i z) / N := by
    funext z
    simp only [ht, X, residualContrast, sub_zero]
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hv : variance (fun _ => p) (ht (fun _ => p) R) ≤ |V| * (N : ℝ)⁻¹ := by
    rw [hht, variance_div]
    calc
      _ ≤ ((N : ℝ) * V) / (N : ℝ)^2 :=
        div_le_div_of_nonneg_right hsum (sq_nonneg _)
      _ ≤ ((N : ℝ) * |V|) / (N : ℝ)^2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (le_abs_self V) hn.le)
          (sq_nonneg _)
      _ = _ := by field_simp [hn.ne'] <;> ring
  have hnn := variance_nonneg (fun _ => p) (fun _ => hS.hp) (ht (fun _ => p) R)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg hnn, abs_of_nonneg (inv_nonneg.mpr hn.le)]
  exact hv

end
end AronowAudit.P004.Wave1.NedHeadline
