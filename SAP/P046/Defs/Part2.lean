import SAP.P046.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

def unitUniform : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

namespace IntervalExample

def score (w : ℝ) : ℝ := if w ≤ 3/5 then 13/20 else 99/100

def generate (z : ℝ × ℝ) : Unit :=
  (z.1, (decide (z.2 ≤ score z.1), (false, decide (z.1 ≤ 3/5))))

/-- Fully continuous law specified by independent U(0,1) W and assignment U;
Y(1)=1{W<=3/5}, Y(0)=0 and X=1{U<=pi(W)}, target T1. -/
def study : Study := ⟨Measure.map generate (unitUniform.prod unitUniform), score,
  (fun w => if w ≤ 3/5 then 1 else 0), 1/200⟩



def xiK (k : ℕ) : ℝ := (400 * k / 169 + 10000 * (100 - (k : ℝ)) / 9801) / 100

/-- T1's integer multinomial numerator of P(K=k,S=s), denominator 100^100. -/
def massNumerator (k s : ℕ) : ℕ :=
  Nat.choose 100 k * Nat.choose k s * 39^s * 21^(k-s) * 40^(100-k)


def certifiedCut (k s : ℕ) : Bool := decide
  (200 * 7840800 * (if s ≤ 39 then 39-s else s-39)^2 >
    3363 * (3920400*k + 1690000*(100-k)))

/-- T1 exact integer sum of all 1946 failing multinomial count-state masses, denominator 100^100, E001 v1 section 6. -/
def certifiedNumerator : ℕ := ∑ k ∈ Finset.range 101, ∑ s ∈ Finset.range (k+1),
  if certifiedCut k s then massNumerator k s else 0


end IntervalExample

namespace ConditionalExample

def generate (z : ℝ × ℝ) : Unit :=
  (z.1, (decide (z.2 ≤ (9/10 : ℝ)), (false, decide ((1/2 : ℝ) ≤ z.1))))

def study : Study := ⟨Measure.map generate (unitUniform.prod unitUniform), (fun _ => 9/10),
  (fun w => if 1/2 ≤ w then 1 else 0), 1/20⟩

/-- The covariate event E={all W_i<1/2}, T2, E001 v2 section 3. -/
def E : Set (Sample 100) := {a | ∀ i, W (a i) < 1/2}



end ConditionalExample

namespace RegressionExample

def scoreL (l : Bool) : ℝ := if l then 1/4 else 3/4

def score (w : ℝ) : ℝ := scoreL (decide (w ≤ (1/2 : ℝ)))

/-- T4: one unrestricted real parameter, with g_theta=1/2 on the lower
half and theta on the upper half. This family does not include zero. -/
def predictionL (theta : ℝ) (l : Bool) : ℝ := if l then 1/2 else theta
def prediction (theta w : ℝ) : ℝ := predictionL theta (decide (w ≤ (1/2 : ℝ)))

def generate (z : (ℝ × ℝ) × ℝ) : Unit :=
  let l := decide (z.1.1 ≤ (1/2 : ℝ))
  let b := l && decide (z.1.2 ≤ (1/10 : ℝ))
  (z.1.1, (decide (z.2 ≤ score z.1.1), (b, b)))

/-- T4's continuous law: W uniform, Z Bernoulli(1/10) independent of W,
X|W independent of Z, and Y(0)=Y(1)=LZ. -/
def study : Study :=
  ⟨Measure.map generate ((unitUniform.prod unitUniform).prod unitUniform), score,
    (fun w => if w ≤ 1/2 then 1/10 else 0), 1/8⟩


/-- Both folds use the deterministic empirical fit with parameter zero. -/
def fits (n : ℕ) : CrossFit n where
  fold i := decide (n/2 ≤ i.val)
  g _ _ := prediction 0
  measurable_g _ := by
    simpa [prediction, predictionL] using
      (measurable_const.ite (measurableSet_le measurable_snd measurable_const) measurable_const :
        Measurable (fun z : Sample n × ℝ => if z.2 ≤ (1/2 : ℝ) then (1/2 : ℝ) else 0))
  opposite_fold _ _ _ _ := rfl

end RegressionExample

end
end SAP.P046
