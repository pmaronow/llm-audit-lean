import Mathlib
import SAP.P013b.Defs.Part7

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false

namespace SAP.P013b
open scoped BigOperators Topology NNReal ENNReal
open Filter Finset
noncomputable section
attribute [local instance] Classical.propDecidable
variable {Ω : Type*} [Fintype Ω]


def T23Statement : Prop :=
  (∀ (world : Fin 3),
    (∀ i d, (twoWearPopulation world).outcome i d = 0 ∨
      (twoWearPopulation world).outcome i d = 1) ∧
    (∀ i d, pi (twoWearPopulation world) i d = 1/2 ∧
      0 < pi (twoWearPopulation world) i d ∧ pi (twoWearPopulation world) i d < 1) ∧
    (∀ z i, observed (recordedPopulation (twoWearPopulation world) twoRecording) z i =
      ∑ d, indicator (twoWearPopulation world).exposure i d z *
        (recordedPopulation (twoWearPopulation world) twoRecording).outcome i d)) ∧
  (∀ (world : Fin 3),
    recordedData (twoWearPopulation world) twoRecording =
      recordedData (twoWearPopulation 0) twoRecording) ∧
  (∀ (world : Fin 3) (z : Fin 2 × Fin 2),
    htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 z =
      (z.1.val : ℝ)) ∧
  (∀ (world : Fin 3),
    expectation twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) = 1/2 ∧
    variance twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) = 1/4 ∧
    causalEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 = 1/2) ∧
  (∀ (world : Fin 3),
    causalEffect (twoWearPopulation world) 1 0 =
      (if world = 0 then 1/2 else if world = 1 then 1 else 0) ∧
    lostMean (twoWearPopulation world) twoRecording 0 =
      (if world = 2 then 1/2 else 0) ∧
    lostMean (twoWearPopulation world) twoRecording 1 =
      (if world = 1 then 1/2 else 0)) ∧
  (∀ (world : Fin 3),
    expectation twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) -
      causalEffect (twoWearPopulation world) 1 0 =
      (if world = 0 then 0 else if world = 1 then -(1/2) else 1/2)) ∧
  (¬ ∃ h : ((Fin 2 × Fin 2) → Fin 2 → Fin 2 × ℝ × Bool) → ℝ,
      ∀ world : Fin 3,
        h (recordedData (twoWearPopulation world) twoRecording) =
          causalEffect (twoWearPopulation world) 1 0) ∧
  (∀ (world : Fin 3),
    (∀ z, htEffect twoRespondentPopulation 1 0 z = 2 * (z.1.val : ℝ)) ∧
    expectation twoReportDesign (htEffect twoRespondentPopulation 1 0) = 1 ∧
    (∀ z, htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0 z =
      (1/2) * htEffect twoRespondentPopulation 1 0 z) ∧
    expectation twoReportDesign (htEffect twoRespondentPopulation 1 0) -
      causalEffect (twoWearPopulation world) 1 0 =
      (if world = 0 then 1/2 else if world = 1 then 0 else 1)) ∧
  (∀ world z i, recordedData (twoWearPopulation world) twoRecording z i =
      ((if i = 0 then z.1 else z.2), (if i = 0 then (z.1.val : ℝ) else 0),
        (if i = 0 then true else false))) ∧
  (∀ world, expectation twoReportDesign
      (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) -
      causalEffect (twoWearPopulation world) 1 0 =
      lostMean (twoWearPopulation world) twoRecording 0 -
        lostMean (twoWearPopulation world) twoRecording 1) ∧
  (∀ world, expectation twoReportDesign (htEffect twoRespondentPopulation 1 0) -
      expectation twoReportDesign
        (htEffect (recordedPopulation (twoWearPopulation world) twoRecording) 1 0) = 1/2)


def T24Statement : Prop :=
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (hN : 0 < N)
    (d e : Fin K) (hne : d ≠ e)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e),
    expectation P (htMean (recordedPopulation F R) d) =
      potentialMean (recordedPopulation F R) d ∧
    expectation P (htEffect (recordedPopulation F R) d e) =
      causalEffect (recordedPopulation F R) d e ∧
    (∀ a, potentialMean (recordedPopulation F R) a = potentialMean F a - lostMean F R a) ∧
    causalEffect (recordedPopulation F R) d e =
      causalEffect F d e - lostMean F R d + lostMean F R e ∧
    expectation P (htEffect (recordedPopulation F R) d e) - causalEffect F d e =
      lostMean F R e - lostMean F R d ∧
    (expectation P (htEffect (recordedPopulation F R) d e) = causalEffect F d e ↔
      lostMean F R d = lostMean F R e) ∧
    (expectation P (htMean (recordedPopulation F R) d) = potentialMean F d ↔
      lostMean F R d = 0) ∧
    (∀ a, (∀ i, 0 ≤ F.outcome i a) → 0 ≤ lostMean F R a ∧
      (lostMean F R a = 0 ↔ ∀ i, R i a = false → F.outcome i a = 0))) ∧
  (∀ {Ω : Type*} [Fintype Ω] {N K : ℕ} {P : Design Ω}
    (F : Population P N K) (R : Recording N K) (hN : 0 < N)
    (d e : Fin K) (hne : d ≠ e)
    (hd : ∀ i, 0 < pi F i d) (he : ∀ i, 0 < pi F i e)
    (hyd : ∀ i, 0 ≤ F.outcome i d) (hye : ∀ i, 0 ≤ F.outcome i e)
    (hzd : ∀ i, R i d = false → F.outcome i d = 0)
    (hze : ∀ i, R i e = false → F.outcome i e = 0),
    expectation P (htEffect (recordedPopulation F R) d e) = causalEffect F d e) ∧
  (∀ {N K : ℕ} (D : Fin N → Fin K)
    (w G : Fin N → ℝ) (S SR : Finset (Fin N)) (hsub : SR ⊆ S)
    (hS : 0 < S.card) (hSR : 0 < SR.card) (_hw : ∀ i ∈ S, 0 < w i)
    (hkeep : ∀ i ∈ S, G i ≠ 0 → i ∈ SR) (d e : Fin K),
    (∀ a, recordedNumerator D w G a SR = recordedNumerator D w G a S) ∧
    recordedNumerator D w G d S / S.card =
      (SR.card : ℝ) / S.card * (recordedNumerator D w G d SR / SR.card) ∧
    (recordedNumerator D w G d S - recordedNumerator D w G e S) / S.card =
      (SR.card : ℝ) / S.card *
        ((recordedNumerator D w G d SR - recordedNumerator D w G e SR) / SR.card) ∧
    (0 < recordedDenominator D w d SR →
      recordedNumerator D w G d S / recordedDenominator D w d S =
        (recordedDenominator D w d SR / recordedDenominator D w d S) *
          (recordedNumerator D w G d SR / recordedDenominator D w d SR))) ∧
  (∀ {N K : ℕ} (D : Fin N → Fin K)
    (w G : Fin N → ℝ) (S item survey : Finset (Fin N))
    (hi : item ⊆ S) (hs : survey ⊆ S) (hS : S.card = 2050)
    (hitem : item.card = 1708) (hsurvey : survey.card = 1899)
    (hw : ∀ i ∈ S, 0 < w i)
    (hki : ∀ i ∈ S, G i ≠ 0 → i ∈ item)
    (hks : ∀ i ∈ S, G i ≠ 0 → i ∈ survey) (d e : Fin K),
    (recordedNumerator D w G d S - recordedNumerator D w G e S)/2050 =
      (854/1025) * ((recordedNumerator D w G d item - recordedNumerator D w G e item)/1708) ∧
    (recordedNumerator D w G d S - recordedNumerator D w G e S)/2050 =
      (1899/2050) * ((recordedNumerator D w G d survey - recordedNumerator D w G e survey)/1899)) ∧
  (let D : Fin 3 → Fin 2 := fun i => if i = 2 then 0 else 1
    let w : Fin 3 → ℝ := fun _ => 2
    let G : Fin 3 → ℝ := fun i => if i = 1 then 0 else 1
    let S : Finset (Fin 3) := univ
    let SR : Finset (Fin 3) := {0,2}
    (∀ i ∈ S, G i ≠ 0 → i ∈ SR) ∧
    recordedDenominator D w 1 SR / recordedDenominator D w 1 S = 1/2 ∧
    recordedDenominator D w 0 SR / recordedDenominator D w 0 S = 1 ∧
    (¬ ∃ c : ℝ,
      recordedNumerator D w G 1 S / recordedDenominator D w 1 S -
        recordedNumerator D w G 0 S / recordedDenominator D w 0 S =
      c * (recordedNumerator D w G 1 SR / recordedDenominator D w 1 SR -
        recordedNumerator D w G 0 SR / recordedDenominator D w 0 SR))) ∧
  (2050 - 342 = (1708 : ℕ) ∧ 2050 - 151 = (1899 : ℕ) ∧
    (1708 : ℝ) / 2050 = 854 / 1025 ∧ (342 : ℝ) / 2050 = 171 / 1025 ∧
    (1899 : ℝ) / 2050 + 151 / 2050 = 1)

end
end SAP.P013b
