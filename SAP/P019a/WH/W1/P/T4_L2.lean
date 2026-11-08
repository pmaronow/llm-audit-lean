import SAP.P019a.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P019a.WH.W1.P.T4_L2

open SAP.P019a SAP.P019a.Bridge MeasureTheory ProbabilityTheory
open scoped BigOperators
open Classical

abbrev Box (M : ℕ) := Fin (M + 1) × Bool × Bool × Bool × Fin (M + 1)

def clip (M x : ℕ) : Fin (M + 1) :=
  ⟨min x M, by omega⟩

def encode {E : Type*} [MeasurableSpace E] (M : ℕ)
    (G : WholeMeasureStudy E) (ω : E) : Box M :=
  (clip M (G.W ω), G.X ω, G.Y ω, G.Z ω, clip M (G.V ω))

def decode {M : ℕ} (b : Box M) : WholeObservation :=
  (b.1.val, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.val)

lemma measurable_encode {E : Type*} [MeasurableSpace E]
    (M : ℕ) (G : WholeMeasureStudy E) (hG : G.measurableData) :
    Measurable (encode M G) := by
  rcases hG with ⟨hW, hX, hY, hZ, hV⟩
  have hc : Measurable (clip M) := measurable_of_countable _
  exact (hc.comp hW).prodMk (hX.prodMk (hY.prodMk (hZ.prodMk (hc.comp hV))))

lemma W_le_V {E : Type*} [MeasurableSpace E]
    (G : WholeMeasureStudy E) (ω : E)
    (h : (G.V ω : ℝ) = (G.W ω : ℝ) + bitVal (G.X ω) * bitVal (G.Z ω)) :
    G.W ω ≤ G.V ω := by
  have hb : 0 ≤ bitVal (G.X ω) * bitVal (G.Z ω) := by
    cases G.X ω <;> cases G.Z ω <;> norm_num [bitVal]
  have hle : (G.W ω : ℝ) ≤ (G.V ω : ℝ) := by rw [h]; linarith
  exact_mod_cast hle

lemma sum_box_singletons {M : ℕ} (μ : Measure (Box M)) [IsProbabilityMeasure μ] :
    (∑ b : Box M, μ.real {b}) = 1 := by
  simp

end SAP.P019a.WH.W1.P.T4_L2

open SAP.P019a.WH.W1.P.T4_L2 SAP.P019a SAP.P019a.Bridge MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem SAP.P019a.WH.W1.T4_L2_proof : SAP.P019a.WH.W1.T4_L2 := by
  intro E hE G hprob hdata hbound hnl
  letI : MeasurableSpace E := hE
  letI : IsProbabilityMeasure G.law.measure := hprob
  obtain ⟨M, hM⟩ := hbound
  let B := Box M
  let e : Fin (Fintype.card B) ≃ B := (Fintype.equivFin B).symm
  let μ : Measure B := G.law.measure.map (encode M G)
  have henc : Measurable (encode M G) := measurable_encode M G hdata
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  letI : IsFiniteMeasure μ := inferInstance
  have hae : ∀ᵐ ω ∂G.law.measure, decode (encode M G ω) = G.observable ω := by
    filter_upwards [hM, hnl] with ω hv hn
    have hwv : G.W ω ≤ G.V ω := W_le_V G ω hn
    have hw : G.W ω ≤ M := hwv.trans hv
    simp [decode, encode, clip, WholeMeasureStudy.observable,
      Nat.min_eq_left hw, Nat.min_eq_left hv]
  have htotal : (∑ i : Fin (Fintype.card B), μ.real {e i}) = 1 := by
    calc
      (∑ i : Fin (Fintype.card B), μ.real {e i}) = ∑ b : B, μ.real {b} :=
        Equiv.sum_comp e (fun b => μ.real {b})
      _ = 1 := sum_box_singletons μ
  let S : Study (Fin (Fintype.card B)) :=
    { law := ⟨(fun i => μ.real {e i}), (fun i => measureReal_nonneg), htotal⟩
      W := fun i => (e i).1.val
      X := fun i => (e i).2.1
      Y := fun i => (e i).2.2.1
      Z := fun i => (e i).2.2.2.1
      V := fun i => (e i).2.2.2.2.val }
  refine ⟨Fintype.card B, Fintype.card_pos_iff.mpr ⟨⟨⟨0, by omega⟩, false, false, false, ⟨0, by omega⟩⟩⟩, S, ?_⟩
  intro f
  have hInt : Integrable (fun b : B => f (decode b)) μ := Integrable.of_finite
  calc
    G.law.mean (fun ω => f (G.observable ω)) =
        ∫ ω, f (decode (encode M G ω)) ∂G.law.measure := by
          unfold WholeMeasureLaw.mean
          have hEq : (fun ω => f (G.observable ω)) =ᵐ[G.law.measure]
              (fun ω => f (decode (encode M G ω))) := by
            filter_upwards [hae] with ω hω
            exact congrArg f hω.symm
          exact integral_congr_ae hEq
    _ = ∫ b, f (decode b) ∂μ :=
      (integral_map henc.aemeasurable hInt.aestronglyMeasurable).symm
    _ = ∑ b : B, μ.real {b} * f (decode b) := by
      rw [integral_fintype hInt]
      simp only [smul_eq_mul]
    _ = ∑ i : Fin (Fintype.card B), μ.real {e i} * f (S.wholeObservable i) := by
      symm
      exact (Fintype.sum_equiv e
        (fun i => μ.real {e i} * f (S.wholeObservable i))
        (fun b => μ.real {b} * f (decode b))
        (by intro i; simp [Study.wholeObservable, decode, S]))
    _ = S.law.mean (fun i => f (S.wholeObservable i)) := by
      rfl

