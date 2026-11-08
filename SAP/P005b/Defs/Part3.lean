import SAP.P005b.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P005b

noncomputable section
open scoped BigOperators Matrix
open Finset Filter

def controlCoefficient (t c : ℕ) : ℝ :=
  1 / ((t+c : ℕ)-1 : ℝ) *
    ((c : ℝ)*((t+c : ℕ)-1 : ℝ) / (((c : ℝ)-1)*(t+c : ℕ))) -
  NTTC (t+c) t * ((t : ℝ)*((t+c : ℕ)-1 : ℝ) / (((c : ℝ)-1)*(t+c : ℕ)))

def treatedCoefficient (t c : ℕ) : ℝ :=
  -1 / ((t+c : ℕ)-1 : ℝ) *
    ((t : ℝ)*((t+c : ℕ)-1 : ℝ) / (((t : ℝ)-1)*(t+c : ℕ))) +
  NTTT (t+c) t * ((t : ℝ)^2*((t+c : ℕ)-1 : ℝ) /
    ((c : ℝ)*((t : ℝ)-1)*(t+c : ℕ)))

def covarianceCombination (t c : ℕ) (A B : ℝ) : ℝ :=
  1 / ((t+c : ℕ)-1 : ℝ) *
    ((c : ℝ)*((t+c : ℕ)-1 : ℝ) / (((c : ℝ)-1)*(t+c : ℕ)) * B -
      (t : ℝ)*((t+c : ℕ)-1 : ℝ) / (((t : ℝ)-1)*(t+c : ℕ)) * A) +
  NTTT (t+c) t * ((t : ℝ)^2*((t+c : ℕ)-1 : ℝ) /
    ((c : ℝ)*((t : ℝ)-1)*(t+c : ℕ))) * A -
  NTTC (t+c) t * ((t : ℝ)*((t+c : ℕ)-1 : ℝ) /
    (((c : ℝ)-1)*(t+c : ℕ))) * B

def T15Statement : Prop :=
  ∀ (t c : ℕ), 2 ≤ t → 2 ≤ c →
    controlCoefficient t c = 1 / ((t+c : ℕ)-2 : ℝ) ∧
    treatedCoefficient t c =
      (((t+c : ℕ) : ℝ) - (t : ℝ)*(t+c : ℕ)) /
        (((t+c : ℕ)-2 : ℝ)*((t : ℝ)-1)*(t+c : ℕ)) ∧
    (((t+c : ℕ) : ℝ) - (t : ℝ)*(t+c : ℕ)) /
        (((t+c : ℕ)-2 : ℝ)*((t : ℝ)-1)*(t+c : ℕ)) =
      -1 / ((t+c : ℕ)-2 : ℝ) ∧
    ∀ (d : ℕ) (P : Population (t+c) d) (S : Finset (Fin (t+c))), S ∈ design (t+c) t →
      covarianceCombination t c (sampleCov S (leverage P) P.yT)
        (sampleCov (control S) (leverage P) P.yC) =
      sampleCov (control S) (leverage P) P.yC / ((t+c : ℕ)-2 : ℝ) -
        sampleCov S (leverage P) P.yT / ((t+c : ℕ)-2 : ℝ)

def T16Statement : Prop :=
  ∀ {n m : ℕ} (hn : 3 ≤ n)
    (hm : 0 < m) (hmn : m < n) (a b c : Fin n → ℝ)
    (ha : ∑ i, a i = 0) (hb : ∑ i, b i = 0) (hc : ∑ i, c i = 0),
    (∀ i j : Fin n, i ≠ j → expectation m (fun S => indicator S i * indicator S j) =
      (m : ℝ)*(m-1)/((n : ℝ)*(n-1))) ∧
    (∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k →
      expectation m (fun S => indicator S i*indicator S j*indicator S k) =
        (m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) ∧
    expectation m (fun S => repeatedPair S a b c) =
      ∑ i, ∑ j ∈ univ.erase i,
        expectation m (fun S => indicator S i * indicator S j) * a i * b i * c j ∧
    expectation m (fun S => repeatedPair S a b c) =
      -(m : ℝ)*(m-1)/((n : ℝ)*(n-1)) * ∑ i, a i*b i*c i ∧
    expectation m (fun S => distinctTriple S a b c) =
      2*(m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2)) * ∑ i, a i*b i*c i ∧
    expectation m (fun S => mean S a*mean S b*mean S c) =
      (1/(m : ℝ)^3)*(
        expectation m (fun S => ∑ i, indicator S i*a i*b i*c i) +
        expectation m (fun S => ∑ i, ∑ j ∈ univ.erase i,
          indicator S i*indicator S j*(a i*b i*c j+a i*b j*c i+a j*b i*c i)) +
        expectation m (fun S => distinctTriple S a b c)) ∧
    expectation m (fun S => mean S a * mean S b * mean S c) =
      (1/(m : ℝ)^3) * ((m : ℝ)/n - 3*(m : ℝ)*(m-1)/((n : ℝ)*(n-1)) +
        2*(m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) * ∑ i, a i*b i*c i ∧
    expectation m (fun S => mean S a * mean S b * mean S c) =
      NTTT n m * popMean (fun i => a i*b i*c i) ∧
    expectation m (fun S => mean S a * mean S b * mean (control S) c) =
      NTTC n m * popMean (fun i => a i*b i*c i) ∧
    (1/(m : ℝ)^3) * ((m : ℝ)/n - 3*(m : ℝ)*(m-1)/((n : ℝ)*(n-1)) +
      2*(m : ℝ)*(m-1)*(m-2)/((n : ℝ)*(n-1)*(n-2))) = (1/(n : ℝ))*NTTT n m ∧
    expectation m (fun S => repeatedPair S a b c) =
      ((m : ℝ)*(m-1)/((n : ℝ)*(n-1))) *
        (∑ i, ∑ j ∈ univ.erase i, a i*b i*c j) ∧
    ((m : ℝ)*(m-1)/((n : ℝ)*(n-1))) *
        (∑ i, ∑ j ∈ univ.erase i, a i*b i*c j) =
      ((m : ℝ)*(m-1)/((n : ℝ)*(n-1))) *
        ((∑ i, ∑ j, a i*b i*c j) - ∑ i, a i*b i*c i) ∧
    (1/(n : ℝ))*NTTT n m =
      ((n : ℝ)-m)*(n-2*m : ℝ)/((n : ℝ)*(m : ℝ)^2*(n-1)*(n-2)) ∧
    (∀ S ∈ design n m, mean (control S) c =
      -((m : ℝ)/((n : ℝ)-m))*mean S c) ∧
    NTTC n m = -((m : ℝ)/((n : ℝ)-m))*NTTT n m

end
end SAP.P005b
