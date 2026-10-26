import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
namespace AronowAudit.P041

/-!
P041-E006: exponential survival laws illustrating proportional hazards.
The paper defines survival time on p. 4/8 and uses a Cox proportional hazard
model. These laws refute the inference from a small absolute contrast to no
relative bias; they are not fitted to the observations.
-/

/-- P041-T1: "λ₊ = -2 log(q)/12".
This is the positive-fact constant removal hazard, per hour. -/
def positiveHazard (q : ℝ) : ℝ := -2 * Real.log q / 12

/-- P041-T1: "λ₋ = -3 log(q)/12".
This is the negative-fact constant removal hazard, per hour. -/
def negativeHazard (q : ℝ) : ℝ := -3 * Real.log q / 12

/-- "S±(t;q) = exp(-λ±(q)t)", P041-T1.
The parameter is a constant removal hazard; t is hours after insertion. -/
def exponentialSurvival (hazard t : ℝ) : ℝ := Real.exp (-hazard * t)

/-- "D(q) = S₊(12;q) - S₋(12;q)", P041-T1. -/
def twelveHourContrast (q : ℝ) : ℝ :=
  exponentialSurvival (positiveHazard q) 12 -
    exponentialSurvival (negativeHazard q) 12

/-- Independent-fact probability of observing k removals among n facts:
"choose(n,k) p^k (1-p)^(n-k)", P041-T1(v).
No independence assertion about the actual experiment is made. -/
def binomialCountProbability (n k : ℕ) (p : ℝ) : ℝ :=
  (n.choose k : ℝ) * p^k * (1-p)^(n-k)

/-- P041-T1(i): all q in (0,1) give positive hazards and the common,
non-null positive/negative hazard ratio 2/3. -/
theorem proportional_hazards (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < positiveHazard q ∧ 0 < negativeHazard q ∧
    positiveHazard q / negativeHazard q = 2/3 ∧
    negativeHazard q / positiveHazard q = 3/2 ∧
    (2/3 : ℝ) ≠ 1 := by
  have hl : Real.log q < 0 := Real.log_neg hq0 hq1
  have hp : 0 < positiveHazard q := by unfold positiveHazard; nlinarith
  have hn : 0 < negativeHazard q := by unfold negativeHazard; nlinarith
  refine ⟨hp, hn, ?_, ?_, by norm_num⟩
  · apply (div_eq_iff (ne_of_gt hn)).2
    unfold positiveHazard negativeHazard
    ring
  · apply (div_eq_iff (ne_of_gt hp)).2
    unfold positiveHazard negativeHazard
    ring

/-- P041-T1(ii): exponential survival at 12 hours equals q² and q³,
and their positive-minus-negative difference is q²(1-q). -/
theorem twelve_hour_survival (q : ℝ) (hq : 0 < q) :
    exponentialSurvival (positiveHazard q) 12 = q^2 ∧
    exponentialSurvival (negativeHazard q) 12 = q^3 ∧
    twelveHourContrast q = q^2 * (1-q) := by
  have hp : exponentialSurvival (positiveHazard q) 12 = q^2 := by
    unfold exponentialSurvival positiveHazard
    have he : -(-2 * Real.log q / 12) * 12 = (2:ℝ) * Real.log q := by ring
    rw [he]
    simpa [Real.exp_log hq] using (Real.exp_nat_mul (Real.log q) 2)
  have hn : exponentialSurvival (negativeHazard q) 12 = q^3 := by
    unfold exponentialSurvival negativeHazard
    have he : -(-3 * Real.log q / 12) * 12 = (3:ℝ) * Real.log q := by ring
    rw [he]
    simpa [Real.exp_log hq] using (Real.exp_nat_mul (Real.log q) 3)
  refine ⟨hp, hn, ?_⟩
  unfold twelveHourContrast
  rw [hp, hn]
  ring

/-- P041-T1 setting: the same exponential survival laws are q^(t/6)
and q^(t/4) at every real time. -/
theorem exponential_survival_power_laws (q t : ℝ) (hq : 0 < q) :
    exponentialSurvival (positiveHazard q) t = q^(t/6) ∧
    exponentialSurvival (negativeHazard q) t = q^(t/4) := by
  rw [Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hq]
  unfold exponentialSurvival positiveHazard negativeHazard
  constructor <;> congr 1 <;> ring

/-- P041-T1(v): if 0 < p < 1 and k ≤ n, each specified removal count
has strictly positive binomial probability. -/
theorem binomial_count_positive (n k : ℕ) (hk : k ≤ n) (p : ℝ)
    (hp0 : 0 < p) (hp1 : p < 1) : 0 < binomialCountProbability n k p := by
  have hc : (0:ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hk
  unfold binomialCountProbability
  positivity

/-- P041-T1(iii)-(v): explicit qA=4/5 and qF=99/100, their exact
12-hour survivals and contrasts, contrast ratio greater than 13, admissible
removal probabilities, and positive probability for all four observed counts.
The hazard ratio is 2/3 in both populations despite unequal absolute contrasts. -/
theorem common_bias_countermodel :
    exponentialSurvival (positiveHazard (4/5)) 12 = 16/25 ∧
    exponentialSurvival (negativeHazard (4/5)) 12 = 64/125 ∧
    twelveHourContrast (4/5) = 16/125 ∧
    exponentialSurvival (positiveHazard (99/100)) 12 = 9801/10000 ∧
    exponentialSurvival (negativeHazard (99/100)) 12 = 970299/1000000 ∧
    twelveHourContrast (99/100) = 9801/1000000 ∧
    twelveHourContrast (4/5) - twelveHourContrast (99/100) = 118199/1000000 ∧
    0 < twelveHourContrast (4/5) - twelveHourContrast (99/100) ∧
    twelveHourContrast (4/5) / twelveHourContrast (99/100) = 128000/9801 ∧
    13 < twelveHourContrast (4/5) / twelveHourContrast (99/100) ∧
    positiveHazard (4/5) / negativeHazard (4/5) = 2/3 ∧
    positiveHazard (99/100) / negativeHazard (99/100) = 2/3 ∧
    (2/3 : ℝ) ≠ 1 ∧
    1 - exponentialSurvival (negativeHazard (4/5)) 12 = 61/125 ∧
    1 - exponentialSurvival (positiveHazard (4/5)) 12 = 9/25 ∧
    1 - exponentialSurvival (negativeHazard (99/100)) 12 = 29701/1000000 ∧
    1 - exponentialSurvival (positiveHazard (99/100)) 12 = 199/10000 ∧
    (0:ℝ) < 61/125 ∧ (61/125 : ℝ) < 1 ∧
    (0:ℝ) < 9/25 ∧ (9/25 : ℝ) < 1 ∧
    (0:ℝ) < 29701/1000000 ∧ (29701/1000000 : ℝ) < 1 ∧
    (0:ℝ) < 199/10000 ∧ (199/10000 : ℝ) < 1 ∧
    0 < binomialCountProbability 150 75 (61/125) ∧
    0 < binomialCountProbability 150 52 (9/25) ∧
    0 < binomialCountProbability 76 1 (29701/1000000) ∧
    0 < binomialCountProbability 75 3 (199/10000) := by
  obtain ⟨hpa, hna, hda⟩ := twelve_hour_survival (4/5) (by norm_num)
  obtain ⟨hpf, hnf, hdf⟩ := twelve_hour_survival (99/100) (by norm_num)
  have hra := (proportional_hazards (4/5) (by norm_num) (by norm_num)).2.2.1
  have hrf := (proportional_hazards (99/100) (by norm_num) (by norm_num)).2.2.1
  have p1 := binomial_count_positive 150 75 (by omega) (61/125)
    (by norm_num) (by norm_num)
  have p2 := binomial_count_positive 150 52 (by omega) (9/25)
    (by norm_num) (by norm_num)
  have p3 := binomial_count_positive 76 1 (by omega) (29701/1000000)
    (by norm_num) (by norm_num)
  have p4 := binomial_count_positive 75 3 (by omega) (199/10000)
    (by norm_num) (by norm_num)
  simp only [hpa, hna, hda, hpf, hnf, hdf, hra, hrf, p1, p2, p3, p4, and_true]
  norm_num

/-- P041-T2(d): the empirical positive-minus-negative survival contrast
from removed counts. nP,nN are the original arm sizes;
rP,rN are removals by the stated horizon. -/
def observedSurvivalContrast (nP nN rP rN : ℝ) : ℝ :=
  (1-rP/nP) - (1-rN/nN)

/-- P041-T2(d): exact early absolute contrasts in active and former samples,
at 12 hours and at 168 hours, with active-minus-former strictly positive.
These identities condition on the recounted deposited counts. -/
theorem observed_early_contrasts :
    observedSurvivalContrast 150 150 52 75 = 23/150 ∧
    observedSurvivalContrast 75 76 3 1 = -51/1900 ∧
    observedSurvivalContrast 150 150 52 75 -
      observedSurvivalContrast 75 76 3 1 = 1027/5700 ∧
    0 < observedSurvivalContrast 150 150 52 75 -
      observedSurvivalContrast 75 76 3 1 ∧
    observedSurvivalContrast 150 150 82 101 = 19/150 ∧
    observedSurvivalContrast 75 76 7 3 = -307/5700 ∧
    observedSurvivalContrast 150 150 82 101 -
      observedSurvivalContrast 75 76 7 3 = 343/1900 ∧
    0 < observedSurvivalContrast 150 150 82 101 -
      observedSurvivalContrast 75 76 7 3 := by
  norm_num [observedSurvivalContrast]

/-- P041-T2(e): smaller absolute contrast does not entail no relative bias.
The witness is the qA,qF law; this says nothing about the true
relative bias on the actual former-senator pages (p. 5/8). -/
theorem smaller_contrast_does_not_exclude_common_bias :
    ∃ qA qF : ℝ, 0 < qA ∧ qA < 1 ∧ 0 < qF ∧ qF < 1 ∧
      positiveHazard qA / negativeHazard qA = 2/3 ∧
      positiveHazard qF / negativeHazard qF = 2/3 ∧
      positiveHazard qF / negativeHazard qF ≠ 1 ∧
      0 < twelveHourContrast qF ∧
      13 * twelveHourContrast qF < twelveHourContrast qA := by
  refine ⟨4/5, 99/100, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  have ha := (proportional_hazards (4/5) (by norm_num) (by norm_num)).2.2.1
  have hf := (proportional_hazards (99/100) (by norm_num) (by norm_num)).2.2.1
  have da := (twelve_hour_survival (4/5) (by norm_num)).2.2
  have df := (twelve_hour_survival (99/100) (by norm_num)).2.2
  rw [ha, hf, da, df]
  norm_num

end AronowAudit.P041

