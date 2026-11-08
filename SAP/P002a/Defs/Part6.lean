import SAP.P002a.Defs.Part5

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P002a
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Matrix Classical Topology
attribute [local instance] Classical.propDecidable

def T8Statement : Prop :=
  (∀ s, ∑ i, interceptExampleX i s = 0) ∧
    (∀ s, mean (fun i => interceptExampleX i s^4) = 16) ∧
    (∀ b : Fin 1 → ℝ, 2*normSq b ≤ mean (fun i => (dotProduct (interceptExampleX i) b)^2)) ∧
    let v : Option (Fin 1) → ℝ := fun j => if j = none then 1 else 0
    mean (fun i => (dotProduct (augmented interceptExampleX i) v)^2) = 1 ∧
    normSq v = 1 ∧
    mean (fun i => (dotProduct (augmented interceptExampleX i) v)^2) < 2*normSq v

def T9Finite : Prop :=
  ∀ {n k : ℕ} (x : Fin n → Fin k → ℝ)
    (hn : 0 < n) (e : ℝ) (hx : ∀ s, ∑ i, x i s = 0)
    (he : ∀ b : Fin k → ℝ, e*normSq b ≤ mean (fun i => (dotProduct (x i) b)^2)),
  (gram x Finset.univ) none none = 1 ∧
    (∀ s, (gram x Finset.univ) none (some s) = 0 ∧
          (gram x Finset.univ) (some s) none = 0) ∧
    (∀ s t, (gram x Finset.univ) (some s) (some t) = mean (fun i => x i s*x i t)) ∧
    (∀ b : Option (Fin k) → ℝ,
      min 1 e * normSq b ≤ mean (fun i => (dotProduct (augmented x i) b)^2))

def T9Spectral : Prop :=
  ∀ {n k : ℕ} (x : Fin n → Fin k → ℝ)
    (hn : 0 < n) (hk : 0 < k) (hx : ∀ s, ∑ i, x i s=0),
  sInf {t | ∃ b : Option (Fin k) → ℝ, normSq b=1 ∧
      mean (fun i => (dotProduct (augmented x i) b)^2)=t} = min 1 (leastRayleigh x)

def T9Sequence (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (k : ℕ) (P : ∀ n, CovPopulation (sizes n) k)
    (Z : ∀ n, Ω → Finset (Fin (sizes n))) (δ e A B r : ℝ)
    (hk : 0 < k) (hδ : δ < 1) (he : 0 < e) (hA : 0 < A) (hB : 0 < B)
    (hr : 0 < r ∧ r ≤ 1/2) (hP : ∀ n, Xi (P n) δ e A B r)
    (hZ : RandomizationSequence (fun n => (P n).pop) μ Z)
    (hIndependent : ∀ (I : Finset ℕ) (E : ∀ n, Finset (Fin (sizes n)) → Prop),
      μ {ω | ∀ n ∈ I, E n (Z n ω)} = ∏ n ∈ I, μ {ω | E n (Z n ω)})
    (sub : ℕ → ℕ) (hsub : StrictMono sub),
  ∀ᵐ ω ∂μ, ∃ err : ℕ → ℝ, Tendsto err atTop (nhds 0) ∧
      ∀ᶠ j in atTop, ∀ a : Bool,
        let N := sub j
        let S := Z N ω
        let q := observedW (P N).pop (late (P N).pop) S
        let b := fitted (P N) q S a - ols (P N).x Finset.univ q
        (min 1 e + err j) * normSq b ≤
          dotProduct b (gram (P N).x (if a then S else Sᶜ) *ᵥ b)

def T9Statement (Ω : Type*) [MeasurableSpace Ω] : Prop :=
  T9Finite ∧ T9Spectral ∧ T9Sequence Ω

def T10Printed : Prop :=
  Theta centringModel 0 (1/2) 1 ∧ late centringModel = 2 ∧
    let S : Finset (Fin 4) := {0,1}
    S ∈ assignments centringModel ∧
    groupMean S (fun i => (observedW centringModel 2 S i-
      armMean (observedW centringModel 2 S) S true)^2) = 0 ∧
    groupMean S (fun i => v centringModel true 2 i^2) -
      (groupMean S (w centringModel true 2) -
        mean (fun i => centringModel.y i (centringModel.d i true)) -
        2*mean (fun i => binary (centringModel.d i true)))^2 = -24 ∧
    expectation centringModel (fun T => (groupMean T (w centringModel true 2) -
      mean (fun i => centringModel.y i (centringModel.d i true)) -
      2*mean (fun i => binary (centringModel.d i true)))^2) = 49/3 ∧
    controlSize centringModel/(2*4*(4-1))*∑ i, v centringModel true 2 i^2 = 1/3

def T10Corrected : Prop :=
  let P := centringModel
  let S : Finset (Fin 4) := {0,1}
  0 < S2 P 2 true ∧
  S2 P 2 true = 1/12 ∧
  mean (fun i => P.y i (P.d i true)) = 2 ∧
  mean (fun i => binary (P.d i true)) = 1 ∧
  groupMean S (w P true 2) = -1 ∧
  groupMean S (fun i => v P true 2 i^2) = 1 ∧
  groupMean S (w P true 2) - mean (fun i => P.y i (P.d i true)) -
    2*mean (fun i => binary (P.d i true)) = -5 ∧
  groupMean S (w P true 2) - mean (fun i => P.y i (P.d i true)) +
    2*mean (fun i => binary (P.d i true)) = -1 ∧
  groupMean S (fun i => v P true 2 i^2) -
    (groupMean S (w P true 2) - mean (fun i => P.y i (P.d i true)) +
      2*mean (fun i => binary (P.d i true)))^2 = 0 ∧
  expectation P (fun T => (groupMean T (w P true 2) -
    mean (fun i => P.y i (P.d i true)) +
    2*mean (fun i => binary (P.d i true)))^2) = 1/3

def T10Statement : Prop := T10Printed ∧ T10Corrected

def T11Finite : Prop :=
  ∀ {n : ℕ} (P : Population n) (hP : ValidDesign P) (β : ℝ)
    (S : Finset (Fin n)) (hS : S ∈ assignments P),
  groupMean S (fun i => (observedW P β S i-armMean (observedW P β S) S true)^2) =
      groupMean S (fun i => v P true β i ^ 2) -
        (groupMean S (w P true β) - mean (fun i => P.y i (P.d i true)) +
          β*mean (fun i => binary (P.d i true)))^2 ∧
    expectation P (fun T => (groupMean T (w P true β) - mean (fun i => P.y i (P.d i true)) +
        β*mean (fun i => binary (P.d i true)))^2) =
      controlSize P/((P.n1 : ℝ)*(n : ℝ)*((n : ℝ)-1))*∑ i, v P true β i^2

def T11Normalized : Prop :=
  ∀ {n : ℕ} (P : Population n) (_hP : ValidDesign P) (β : ℝ)
    (_hS : 0 < S2 P β true),
  expectation P (fun T => (groupMean T (w P true β) -
    mean (fun i => P.y i (P.d i true)) +
    β*mean (fun i => binary (P.d i true)))^2 / S2 P β true) =
    controlSize P/((P.n1 : ℝ)*(n : ℝ)*((n : ℝ)-1)) *
      (∑ i, v P true β i^2) / S2 P β true

def T11Rate : Prop :=
  ∀ (sizes : ℕ → ℕ) (hsizes : StrictMono sizes)
    (P : ∀ n, Population (sizes n)) (δ r A : ℝ)
    (hδ : δ < 1) (hr : 0 < r ∧ r ≤ 1/2) (hA : 0 < A)
    (hP : ∀ n, Theta (P n) δ r A)
    (hS : ∀ n, 0 < S2 (P n) (late (P n)) true),
    let f : ℕ → ℝ := fun n => expectation (P n) (fun S =>
      (groupMean S (w (P n) true (late (P n))) -
        mean (fun i => (P n).y i ((P n).d i true)) +
        late (P n)*mean (fun i => binary ((P n).d i true)))^2 / S2 (P n) (late (P n)) true)
    Asymptotics.IsBigO atTop f (fun n => controlSize (P n)/((P n).n1*(sizes n : ℝ))) ∧
    Tendsto f atTop (nhds 0)

def T11Statement : Prop := T11Finite ∧ T11Normalized ∧ T11Rate

end
end SAP.P002a
