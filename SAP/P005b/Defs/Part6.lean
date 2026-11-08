import SAP.P005b.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005b

noncomputable section
open scoped BigOperators Matrix
open Finset Filter

def biasPart11 {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  1/(n-1 : ℝ) *
    ((((n : ℝ)-m)*(n-1)/(((n : ℝ)-m-1)*n)) * sampleCov (control S) (leverage P) P.yC -
      ((m : ℝ)*(n-1)/(((m : ℝ)-1)*n)) * sampleCov S (leverage P) P.yT)

def biasPart12 {n d : ℕ} (P : Population n d) (m : ℕ) (S : Finset (Fin n)) : ℝ :=
  (NTTT n m*(m : ℝ)^2*(n-1)/(((n : ℝ)-m)*((m : ℝ)-1)*n)) *
    sampleCov S (leverage P) P.yT -
  (NTTC n m*(m : ℝ)*(n-1)/(((n : ℝ)-m-1)*n)) *
    sampleCov (control S) (leverage P) P.yC

def T21Statement : Prop :=
  ∀ {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : noninteractedRegular P m),
    expectation m (biasEstimate P m) = expectation m (adjustedATE P m) - ate P ∧
    expectation m (debiasedATE P m) = ate P ∧
    (∀ S ∈ design n m,
      debiasedATE P m S =
        mean S P.yT - mean (control S) P.yC -
          dot (xMean P S - xMean P (control S)) (Nhat P m S) +
          sampleCov S (leverage P) P.yT / (n-2 : ℝ) -
          sampleCov (control S) (leverage P) P.yC / (n-2 : ℝ)) ∧
    expectation m (adjustedATE P m) - ate P =
      expectation m (fun S => dot (xMean P (control S)-xMean P S)
        (nu1 P m S+nu2 P m S+nu3 P m S)) ∧
    (∀ S ∈ design n m,
      dot (xMean P (control S)-xMean P S) (nu2 P m S) =
        dot (xMean P (control S)-xMean P S) (((Lhat P m S)⁻¹-1) *ᵥ Nhat P m S)) ∧
    (2 ≤ m → 2 ≤ n-m →
      expectation m (biasPart11 P m) =
        (leverageCov P P.yC-leverageCov P P.yT)/(n-1 : ℝ) ∧
      expectation m (biasPart12 P m) =
        (pT n m/pC n m)*NTTT n m*leverageCov P P.yT -
          (pT n m/pC n m)*NTTC n m*leverageCov P P.yC ∧
      expectation m (biasPart12 P m) =
        ((n : ℝ)-2*m)/((n-1 : ℝ)*(n-2 : ℝ)*m)*leverageCov P P.yT -
          (2*(m : ℝ)-n)/((n-1 : ℝ)*(n-2 : ℝ)*(n-m))*leverageCov P P.yC ∧
      (∀ S ∈ design n m,
        biasPart11 P m S+biasPart12 P m S =
          sampleCov (control S) (leverage P) P.yC/(n-2 : ℝ) -
            sampleCov S (leverage P) P.yT/(n-2 : ℝ)))

def T22Main : Prop :=
  ∀ {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : interactedRegular P m),
    expectation m (interactedBiasEstimate P m) = expectation m (interactedATE P) - ate P ∧
    expectation m (interactedDebiasedATE P m) = ate P ∧
    expectation m (fun S => armDebiased P S P.yT) = popMean P.yT ∧
    expectation m (fun S => armDebiased P (control S) P.yC) = popMean P.yC ∧
    (∀ S ∈ design n m,
      interactedDebiasedATE P m S =
        (mean S P.yT - dot (xMean P S) (armN P S P.yT) +
          ((n : ℝ)-m) / ((n-2 : ℝ)*m) * sampleCov S (leverage P) P.yT) -
        (mean (control S) P.yC - dot (xMean P (control S)) (armN P (control S) P.yC) +
          (m : ℝ) / ((n-2 : ℝ)*(n-m)) * sampleCov (control S) (leverage P) P.yC))

def T22Statement : Prop :=
  T22Main ∧
  (∀ {n d m : ℕ} (P : Population n d), 3 ≤ n → 2 ≤ m → m < n → xMean P univ = 0 →
    expectation m (fun S => armDebiased P S P.yT) = popMean P.yT) ∧
  (∀ {n d m : ℕ} (P : Population n d), 3 ≤ n → 0 < m → m < n → 2 ≤ n-m →
    xMean P univ = 0 →
    expectation m (fun S => armDebiased P (control S) P.yC) = popMean P.yC)

def T23Statement : Prop :=
  ∀ {n d m : ℕ} (P : Population n d)
    (hn : 3 ≤ n) (hm : 0 < m) (hmn : m < n) (hP : standardized P)
    (hinv : noninteractedRegular P m),
    (∀ S ∈ design n m, betaHat P m S = N P m + nu1 P m S + nu2 P m S + nu3 P m S) ∧
    expectation m (adjustedATE P m) - ate P =
      expectation m (fun S => dot (xMean P (control S) - xMean P S)
        (nu1 P m S + nu2 P m S + nu3 P m S)) ∧
    expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu1 P m S)) =
      (leverageCov P P.yC - leverageCov P P.yT) / (n-1 : ℝ) ∧
    (leverageCov P P.yC - leverageCov P P.yT) / (n-1 : ℝ) =
      -(1/(n-1 : ℝ)) * popMean (fun i => (leverage P i-popMean (leverage P))*(P.yT i-P.yC i)) ∧
    expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu3 P m S)) =
      ((n : ℝ)-2*m)/((n-1 : ℝ)*(n-2 : ℝ)*m)*leverageCov P P.yT -
        (2*(m : ℝ)-n)/((n-1 : ℝ)*(n-2 : ℝ)*(n-m))*leverageCov P P.yC ∧
    ((∃ c : ℝ, ∀ i, P.yT i-P.yC i = c) →
      expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu1 P m S)) = 0) ∧
    (m = n-m → expectation m (fun S => dot (xMean P (control S)-xMean P S) (nu3 P m S)) = 0)

end
end SAP.P005b
