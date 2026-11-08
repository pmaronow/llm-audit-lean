import SAP.P037a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P037a

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology

def significanceContradiction : Prop :=
  ∀ (p : ℝ),
    ¬ (p < 1/20 ∧ 1/20 ≤ p)

def roundedWaldComparisons : Prop :=
  ∀ (c : ℝ)
      (hc : 19/10 ≤ c ∧ c ≤ 2),
    tableS6Bins (-57/1000) (7/250) ∧
      tableS6Bins (-57/1000) (17/500) ∧
      waldStatistic (-57/1000) (7/250) = 57/28 ∧
      waldStatistic (-57/1000) (17/500) = 57/34 ∧
      waldStatistic (-57/1000) (17/500) < c ∧
      c < waldStatistic (-57/1000) (7/250)

def waldEnvelope : Prop :=
  ∀ (estimate se : ℝ)
      (h : tableS6Bins estimate se),
    11/7 < waldStatistic estimate se ∧ waldStatistic estimate se < 13/5 ∧
      (6/100:ℝ)/(3/100) = 2

def waldAttainable : Prop :=
  ∀ (z : ℝ) (hz : 11/7 < z ∧ z < 13/5),
    ∃ a se : ℝ, 11/200 < a ∧ a < 13/200 ∧
        1/40 < se ∧ se < 7/200 ∧ a / se = z

def T3Statement : Prop := significanceContradiction ∧ roundedWaldComparisons ∧ waldEnvelope ∧ waldAttainable

def uniformWeightsDiffer : Prop :=
  ∀ (n : ℕ),
    (uniformWeightLaw n (ratioEvent n)).toReal = 1/6 ∧
      (simplexLaw (n+1) (ratioEvent n)).toReal = 1/4 ∧
      uniformWeightLaw n ≠ simplexLaw (n+1)

def ratioCancellation : Prop :=
  ∀ (u v total : ℝ)
      (hu : 0 < u) (hv : 0 < v) (ht : 0 < total),
    (u/total)/(u/total+v/total) = u/(u+v) ∧
      (u/(u+v) < 1/4 ↔ u < v/3)

def uniformArea : Prop :=
  (∫ v : ℝ in (0:ℝ)..1, ∫ u : ℝ in (0:ℝ)..(v/3), (1:ℝ)) = 1/6

def exponentialIntegrals : Prop :=
  (∫ v : ℝ in Ioi 0, Real.exp (-v)) = 1 ∧
      (∫ v : ℝ in Ioi 0, Real.exp (-(4/3)*v)) = 3/4 ∧
      (1:ℝ)-3/4 = 1/4 ∧ (1/6:ℝ) ≠ 1/4 ∧ (1/6:ℝ)-1/4 = -1/12

def weightScaling : Prop :=
  ∀ {I K : Type} [Fintype I] [Fintype K]
      [DecidableEq K] (w : I → ℝ) (X : Matrix I K ℝ) (y : I → ℝ) (b : K → ℝ)
      (_hw : ∀ i, 0 < w i) (_hX : Function.Injective X.mulVec)
      (c : ℝ) (hc : 0 < c),
    wlsCoefficient (fun i => c*w i) X y = wlsCoefficient w X y ∧
      (WLS (fun i => c*w i) X y b ↔ WLS w X y b)

def finiteWeightEvents : Prop := ∀ n : ℕ,
  uniformWeightLaw n (ratioEvent n) ≠ ⊤ ∧ simplexLaw (n+1) (ratioEvent n) ≠ ⊤

def normalizationRefit : Prop :=
  ∀ {K : Type} [Fintype K] [DecidableEq K] (n : ℕ)
    (w : Fin (n+2) → ℝ) (X : Matrix (Fin (n+2)) K ℝ) (y : Fin (n+2) → ℝ),
    (∀ i, 0 < w i) → Function.Injective X.mulVec →
    wlsCoefficient (normalizedWeights w) X y = wlsCoefficient w X y

def T4Statement : Prop := uniformWeightsDiffer ∧ ratioCancellation ∧ uniformArea ∧ exponentialIntegrals ∧ weightScaling ∧ finiteWeightEvents ∧ normalizationRefit

def logUniformExponential : Prop :=
  Measure.map (fun v : ℝ => -Real.log v) uniformDraw =
        ProbabilityTheory.expMeasure 1

def gammaNormalization : Prop :=
  ∀ (m : ℕ),
    (∫ t : ℝ in Ioi 0, t^m*Real.exp (-t)) = m.factorial

def T5Statement : Prop := logUniformExponential ∧ gammaNormalization ∧ uniformWeightsDiffer ∧ weightScaling ∧ finiteWeightEvents ∧ normalizationRefit

def totalsReduction : Prop :=
  (2695:ℕ)-2012 = 683 ∧
      reduction 2695 2012 = 683/2695 ∧
      (49/200:ℝ) < 683/2695 ∧ (683/2695:ℝ) < 51/200 ∧
      (683/2695:ℝ) < 59/200 ∧ (683/2695:ℝ) ≠ 3/10 ∧
      (6830:ℕ) ≠ 8085 ∧
      (11/200:ℝ) ≤ 683/11938 ∧ (683/11938:ℝ) < 13/200 ∧
      (9/40:ℝ) < 2695/11938 ∧ (2695/11938:ℝ) < 23/100 ∧
      (3/10:ℝ)-1/4 = 1/20 ∧ (1/20:ℝ)/(3/10) = 1/6

def roundedTotalsReduction : Prop :=
  ∀ (A B : ℝ)
      (ha : 5389/2 ≤ A ∧ A ≤ 5391/2)
      (hb : 4023/2 ≤ B ∧ B ≤ 4025/2),
    1364/5389 ≤ 1-B/A ∧ 1-B/A ≤ 1368/5391 ∧
      (49/200:ℝ) < 1364/5389 ∧ (1368/5391:ℝ) < 51/200

def mixedBasisReduction : Prop :=
  ∀ (e m : ℝ)
      (he : 11/200 ≤ e ∧ e ≤ 13/200)
      (hm : 39/200 ≤ m ∧ m ≤ 41/200),
    (3/50:ℝ)/(1/5) = 3/10 ∧ 11/41 ≤ e/m ∧ (51/200:ℝ) < e/m

def T6Statement : Prop := totalsReduction ∧ roundedTotalsReduction ∧ mixedBasisReduction

def interpolationNoTie : Prop :=
  ∀ (n k : ℤ),
    350*k ≠ 3500 + 6*(n-200) - 175

def eligibleBounds : Prop :=
  (∀ n, 40 ≤ eligibleCount n ∧ eligibleCount n ≤ 64 ∧
        4 ∣ eligibleCount n) ∧
      Monotone eligibleCount

def eligibleCap : Prop :=
  (∀ n, eligibleCount n = 64 ↔ 521 ≤ n) ∧
      (∀ n, 550 ≤ n → eligibleCount n = 64) ∧
      (40+24*((200:ℝ)-200)/350 = 40) ∧
      (40+24*((550:ℝ)-200)/350 = 64) ∧
      eligibleCount 100 = 40 ∧ eligibleCount 200 = 40 ∧
      eligibleCount 375 = 52

def eligibleShares : Prop :=
  (eligibleCount 100:ℝ)/100 = 2/5 ∧
      (eligibleCount 200:ℝ)/200 = 1/5 ∧
      (eligibleCount 375:ℝ)/375 = 52/375 ∧
      (eligibleCount 550:ℝ)/550 = 64/550 ∧
      (eligibleCount 715:ℝ)/715 = 64/715

def T12Statement : Prop := interpolationNoTie ∧ eligibleBounds ∧ eligibleCap ∧ eligibleShares

def compositionArithmetic : Prop :=
  fittedEffect (4/100) (-85/100) (1/5) = -13/100 ∧
      reduction (1/5) (8/100) = 3/5

def compositionIntervals : Prop :=
  ∀ (t b m : ℝ)
      (ht : 35/1000 ≤ t ∧ t ≤ 45/1000)
      (hb : -855/1000 ≤ b ∧ b ≤ -845/1000)
      (hm : 222/1000 ≤ m ∧ m ≤ 223/1000),
    -136/1000 ≤ fittedEffect t b (1/5) ∧
      fittedEffect t b (1/5) ≤ -124/1000 ∧
      86/1000 ≤ m + fittedEffect t b (1/5) ∧
      m + fittedEffect t b (1/5) ≤ 99/1000 ∧
      ¬ (75/1000 ≤ m + fittedEffect t b (1/5) ∧
         m + fittedEffect t b (1/5) ≤ 85/1000) ∧
      (86/1000:ℝ) ≤ 95/1000 ∧ (95/1000:ℝ) ≤ 99/1000 ∧
      124/223 ≤ -fittedEffect t b (1/5)/m ∧
      -fittedEffect t b (1/5)/m ≤ 68/111 ∧
      (124/223:ℝ) ≤ 57/100 ∧ (57/100:ℝ) ≤ 68/111 ∧
      (124/223:ℝ) ≤ 3/5 ∧ (3/5:ℝ) ≤ 68/111

def effectRounding : Prop := ∀ t b : ℝ,
  35/1000 ≤ t ∧ t ≤ 45/1000 → -855/1000 ≤ b ∧ b ≤ -845/1000 →
  -136/1000 ≤ fittedEffect t b (1/5) ∧ fittedEffect t b (1/5) ≤ -124/1000

def T13Statement : Prop := compositionArithmetic ∧ compositionIntervals ∧ effectRounding

end SAP.P037a
