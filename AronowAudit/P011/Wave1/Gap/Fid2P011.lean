import AronowAudit.P011.P011_CovarianceCompletion

/-! P011-T17: covariance identities on their separate displayed-moment domains. -/
namespace AronowAudit.P011.Wave1
open AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal ProbabilityTheory
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

def rawFourthMoment
    {Ω : Type} (E : (Ω → ℝ) → ℝ) (Y : Fin 4 → Ω → ℝ)
    (B : Ω → ℝ) (θ : Fin 4 → ℝ) : ℝ :=
  θ 0*θ 1*θ 2*θ 3 * E (fun y => Y 0 y*Y 1 y*Y 2 y*Y 3 y) -
  θ 0*θ 1*θ 2 * E (fun y => Y 0 y*Y 1 y*Y 2 y*B y) -
  θ 0*θ 1*θ 3 * E (fun y => Y 0 y*Y 1 y*Y 3 y*B y) -
  θ 0*θ 2*θ 3 * E (fun y => Y 0 y*Y 2 y*Y 3 y*B y) -
  θ 1*θ 2*θ 3 * E (fun y => Y 1 y*Y 2 y*Y 3 y*B y) +
  θ 0*θ 1 * E (fun y => Y 0 y*Y 1 y*(B y)^2) +
  θ 0*θ 2 * E (fun y => Y 0 y*Y 2 y*(B y)^2) +
  θ 0*θ 3 * E (fun y => Y 0 y*Y 3 y*(B y)^2) +
  θ 1*θ 2 * E (fun y => Y 1 y*Y 2 y*(B y)^2) +
  θ 1*θ 3 * E (fun y => Y 1 y*Y 3 y*(B y)^2) +
  θ 2*θ 3 * E (fun y => Y 2 y*Y 3 y*(B y)^2) -
  θ 0 * E (fun y => Y 0 y*(B y)^3) -
  θ 1 * E (fun y => Y 1 y*(B y)^3) -
  θ 2 * E (fun y => Y 2 y*(B y)^3) -
  θ 3 * E (fun y => Y 3 y*(B y)^3) + E (fun y => (B y)^4)

section Generic
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The covariance bridge needs only the two first moments and their mixed moment. -/
lemma fid2_covariance_eq_sub [IsProbabilityMeasure μ] {f g : Ω → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun ω => f ω * g ω) μ) :
    ProbabilityTheory.covariance f g μ =
      (∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * (∫ ω, g ω ∂μ) := by
  unfold ProbabilityTheory.covariance
  simp_rw [sub_mul, mul_sub]
  rw [integral_sub (hfg.sub' (hf.mul_const _))
      ((hg.const_mul _).sub' (integrable_const _)),
    integral_sub hfg (hf.mul_const _),
    integral_sub (hg.const_mul _) (integrable_const _)]
  simp only [integral_mul_const, integral_const_mul, integral_const, probReal_univ,
    one_smul]
  ring

lemma fid2_pair_integrable {a b B : Ω → ℝ}
    (hab : Integrable (fun ω => a ω*b ω) μ)
    (haB : Integrable (fun ω => a ω*B ω) μ)
    (hbB : Integrable (fun ω => b ω*B ω) μ)
    (hB2 : Integrable (fun ω => B ω^2) μ) :
    Integrable (fun ω => (a ω-B ω)*(b ω-B ω)) μ := by
  exact (((hab.sub' haB).sub' hbB).fun_add hB2).congr
    (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply, Pi.sub_apply]; ring)

lemma fid2_pair_expansion {a b B : Ω → ℝ}
    (hab : Integrable (fun ω => a ω*b ω) μ)
    (haB : Integrable (fun ω => a ω*B ω) μ)
    (hbB : Integrable (fun ω => b ω*B ω) μ)
    (hB2 : Integrable (fun ω => B ω^2) μ) :
    (∫ ω, (a ω-B ω)*(b ω-B ω) ∂μ) =
      (∫ ω, a ω*b ω ∂μ) - (∫ ω, a ω*B ω ∂μ) -
      (∫ ω, b ω*B ω ∂μ) + (∫ ω, B ω^2 ∂μ) := by
  calc
    _ = ∫ ω, a ω*b ω-a ω*B ω-b ω*B ω+B ω^2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => by ring)
    _ = _ := by
      rw [integral_add ((hab.sub' haB).sub' hbB) hB2,
        integral_sub (hab.sub' haB) hbB, integral_sub hab haB]

/-- The sixteen slot monomials, written in the order of the fourth polynomial. -/
structure fid2_FourthData (X : Fin 4 → Ω → ℝ) (B : Ω → ℝ) : Prop where
  f0123 : Integrable (fun ω => X 0 ω*X 1 ω*X 2 ω*X 3 ω) μ
  f012 : Integrable (fun ω => X 0 ω*X 1 ω*X 2 ω*B ω) μ
  f013 : Integrable (fun ω => X 0 ω*X 1 ω*X 3 ω*B ω) μ
  f023 : Integrable (fun ω => X 0 ω*X 2 ω*X 3 ω*B ω) μ
  f123 : Integrable (fun ω => X 1 ω*X 2 ω*X 3 ω*B ω) μ
  f01 : Integrable (fun ω => X 0 ω*X 1 ω*(B ω)^2) μ
  f02 : Integrable (fun ω => X 0 ω*X 2 ω*(B ω)^2) μ
  f03 : Integrable (fun ω => X 0 ω*X 3 ω*(B ω)^2) μ
  f12 : Integrable (fun ω => X 1 ω*X 2 ω*(B ω)^2) μ
  f13 : Integrable (fun ω => X 1 ω*X 3 ω*(B ω)^2) μ
  f23 : Integrable (fun ω => X 2 ω*X 3 ω*(B ω)^2) μ
  f0 : Integrable (fun ω => X 0 ω*(B ω)^3) μ
  f1 : Integrable (fun ω => X 1 ω*(B ω)^3) μ
  f2 : Integrable (fun ω => X 2 ω*(B ω)^3) μ
  f3 : Integrable (fun ω => X 3 ω*(B ω)^3) μ
  fempty : Integrable (fun ω => (B ω)^4) μ

lemma fid2_fourth_data {X : Fin 4 → Ω → ℝ} {B : Ω → ℝ}
    (h : ∀ s : Finset (Fin 4),
      Integrable (fun ω => (∏ a ∈ s, X a ω) * (B ω)^(4-s.card)) μ) :
    fid2_FourthData (μ := μ) X B := by
  constructor
  · simpa [mul_assoc] using h ({0, 1, 2, 3} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({0, 1, 2} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({0, 1, 3} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({0, 2, 3} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({1, 2, 3} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({0, 1} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({0, 2} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({0, 3} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({1, 2} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({1, 3} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({2, 3} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({0} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({1} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({2} : Finset (Fin 4))
  · simpa [mul_assoc] using h ({3} : Finset (Fin 4))
  · simpa [mul_assoc] using h (∅ : Finset (Fin 4))

lemma fid2_fourth_groups {X : Fin 4 → Ω → ℝ} {B : Ω → ℝ}
    (h : fid2_FourthData (μ := μ) X B) :
    Integrable (fun ω => B ω*(X 0 ω*X 1 ω*X 2 ω+X 0 ω*X 1 ω*X 3 ω+
      X 0 ω*X 2 ω*X 3 ω+X 1 ω*X 2 ω*X 3 ω)) μ ∧
    Integrable (fun ω => (B ω)^2*(X 0 ω*X 1 ω+X 0 ω*X 2 ω+X 0 ω*X 3 ω+
      X 1 ω*X 2 ω+X 1 ω*X 3 ω+X 2 ω*X 3 ω)) μ ∧
    Integrable (fun ω => (B ω)^3*(X 0 ω+X 1 ω+X 2 ω+X 3 ω)) μ := by
  refine ⟨?_, ?_, ?_⟩
  · exact (((h.f012.fun_add h.f013).fun_add h.f023).fun_add h.f123).congr
      (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply]; ring)
  · exact (((((h.f01.fun_add h.f02).fun_add h.f03).fun_add h.f12).fun_add h.f13).fun_add h.f23).congr
      (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply]; ring)
  · exact (((h.f0.fun_add h.f1).fun_add h.f2).fun_add h.f3).congr
      (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply]; ring)

lemma fid2_fourth_expansion {X : Fin 4 → Ω → ℝ} {B : Ω → ℝ}
    (h : fid2_FourthData (μ := μ) X B) :
    Integrable (fun ω => (X 0 ω-B ω)*(X 1 ω-B ω)*(X 2 ω-B ω)*(X 3 ω-B ω)) μ ∧
    (∫ ω, (X 0 ω-B ω)*(X 1 ω-B ω)*(X 2 ω-B ω)*(X 3 ω-B ω) ∂μ) =
      fourthMoment (fun f => ∫ ω, f ω ∂μ) (X 0) (X 1) (X 2) (X 3) B := by
  obtain ⟨h3, h2, h1⟩ := fid2_fourth_groups h
  have hi := (((h.f0123.sub' h3).fun_add h2).sub' h1).fun_add h.fempty
  constructor
  · exact hi.congr (Eventually.of_forall fun ω => by
      dsimp only [Pi.add_apply, Pi.sub_apply]
      exact (fourth_polynomial _ _ _ _ _).symm)
  · calc
      _ = ∫ ω, X 0 ω*X 1 ω*X 2 ω*X 3 ω-
          B ω*(X 0 ω*X 1 ω*X 2 ω+X 0 ω*X 1 ω*X 3 ω+
            X 0 ω*X 2 ω*X 3 ω+X 1 ω*X 2 ω*X 3 ω)+
          (B ω)^2*(X 0 ω*X 1 ω+X 0 ω*X 2 ω+X 0 ω*X 3 ω+
            X 1 ω*X 2 ω+X 1 ω*X 3 ω+X 2 ω*X 3 ω)-
          (B ω)^3*(X 0 ω+X 1 ω+X 2 ω+X 3 ω)+(B ω)^4 ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => fourth_polynomial _ _ _ _ _)
      _ = _ := by
        unfold fourthMoment
        rw [integral_add (((h.f0123.sub' h3).fun_add h2).sub' h1) h.fempty,
          integral_sub ((h.f0123.sub' h3).fun_add h2) h1,
          integral_add (h.f0123.sub' h3) h2, integral_sub h.f0123 h3]

/-- Separate each grouped integral into its individually integrable monomials. -/
lemma fid2_fourth_flat {X : Fin 4 → Ω → ℝ} {B : Ω → ℝ}
    (h : fid2_FourthData (μ := μ) X B) :
    fourthMoment (fun f => ∫ ω, f ω ∂μ) (X 0) (X 1) (X 2) (X 3) B =
      rawFourthMoment (fun f => ∫ ω, f ω ∂μ) X B (fun _ => 1) := by
  have h3 : (∫ ω, B ω*(X 0 ω*X 1 ω*X 2 ω+X 0 ω*X 1 ω*X 3 ω+X 0 ω*X 2 ω*X 3 ω+X 1 ω*X 2 ω*X 3 ω) ∂μ) = (∫ ω, X 0 ω*X 1 ω*X 2 ω*B ω ∂μ)+(∫ ω, X 0 ω*X 1 ω*X 3 ω*B ω ∂μ)+(∫ ω, X 0 ω*X 2 ω*X 3 ω*B ω ∂μ)+(∫ ω, X 1 ω*X 2 ω*X 3 ω*B ω ∂μ) := by
    calc
      _ = ∫ ω, X 0 ω*X 1 ω*X 2 ω*B ω+X 0 ω*X 1 ω*X 3 ω*B ω+X 0 ω*X 2 ω*X 3 ω*B ω+X 1 ω*X 2 ω*X 3 ω*B ω ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := by
        rw [integral_add ((h.f012.fun_add h.f013).fun_add h.f023) h.f123,
          integral_add (h.f012.fun_add h.f013) h.f023,
          integral_add h.f012 h.f013]
  have h2 : (∫ ω, (B ω)^2*(X 0 ω*X 1 ω+X 0 ω*X 2 ω+X 0 ω*X 3 ω+X 1 ω*X 2 ω+X 1 ω*X 3 ω+X 2 ω*X 3 ω) ∂μ) = (∫ ω, X 0 ω*X 1 ω*(B ω)^2 ∂μ)+(∫ ω, X 0 ω*X 2 ω*(B ω)^2 ∂μ)+(∫ ω, X 0 ω*X 3 ω*(B ω)^2 ∂μ)+(∫ ω, X 1 ω*X 2 ω*(B ω)^2 ∂μ)+(∫ ω, X 1 ω*X 3 ω*(B ω)^2 ∂μ)+(∫ ω, X 2 ω*X 3 ω*(B ω)^2 ∂μ) := by
    calc
      _ = ∫ ω, X 0 ω*X 1 ω*(B ω)^2+X 0 ω*X 2 ω*(B ω)^2+X 0 ω*X 3 ω*(B ω)^2+X 1 ω*X 2 ω*(B ω)^2+X 1 ω*X 3 ω*(B ω)^2+X 2 ω*X 3 ω*(B ω)^2 ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := by
        rw [integral_add ((((h.f01.fun_add h.f02).fun_add h.f03).fun_add h.f12).fun_add h.f13) h.f23,
          integral_add (((h.f01.fun_add h.f02).fun_add h.f03).fun_add h.f12) h.f13,
          integral_add ((h.f01.fun_add h.f02).fun_add h.f03) h.f12,
          integral_add (h.f01.fun_add h.f02) h.f03,
          integral_add h.f01 h.f02]
  have h1 : (∫ ω, (B ω)^3*(X 0 ω+X 1 ω+X 2 ω+X 3 ω) ∂μ) = (∫ ω, X 0 ω*(B ω)^3 ∂μ)+(∫ ω, X 1 ω*(B ω)^3 ∂μ)+(∫ ω, X 2 ω*(B ω)^3 ∂μ)+(∫ ω, X 3 ω*(B ω)^3 ∂μ) := by
    calc
      _ = ∫ ω, X 0 ω*(B ω)^3+X 1 ω*(B ω)^3+X 2 ω*(B ω)^3+X 3 ω*(B ω)^3 ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := by
        rw [integral_add ((h.f0.fun_add h.f1).fun_add h.f2) h.f3,
          integral_add (h.f0.fun_add h.f1) h.f2,
          integral_add h.f0 h.f1]
  unfold fourthMoment rawFourthMoment
  dsimp only
  rw [h3, h2, h1]
  ring

/-- Raw monomials imply weighted monomials by multiplication by deterministic weights. -/
lemma fid2_weighted_fourth {Y : Fin 4 → Ω → ℝ} {B : Ω → ℝ} (θ : Fin 4 → ℝ)
    (h : ∀ s : Finset (Fin 4),
      Integrable (fun ω => (∏ a ∈ s, Y a ω)*(B ω)^(4-s.card)) μ) :
    ∀ s : Finset (Fin 4),
      Integrable (fun ω => (∏ a ∈ s, θ a*Y a ω)*(B ω)^(4-s.card)) μ := by
  intro s
  exact ((h s).const_mul (∏ a ∈ s, θ a)).congr
    (Eventually.of_forall fun ω => by dsimp only; rw [Finset.prod_mul_distrib]; ring)

lemma fid2_raw_fourth {Y : Fin 4 → Ω → ℝ} {B : Ω → ℝ} (θ : Fin 4 → ℝ)
    (h : ∀ s : Finset (Fin 4),
      Integrable (fun ω => (∏ a ∈ s, Y a ω)*(B ω)^(4-s.card)) μ) :
    (∫ ω, (θ 0*Y 0 ω-B ω)*(θ 1*Y 1 ω-B ω)*
      (θ 2*Y 2 ω-B ω)*(θ 3*Y 3 ω-B ω) ∂μ) =
      rawFourthMoment (fun f => ∫ ω, f ω ∂μ) Y B θ := by
  have hd := fid2_fourth_data (fid2_weighted_fourth θ h)
  rw [(fid2_fourth_expansion hd).2, fid2_fourth_flat hd]
  have ef0123 : (∫ ω, (θ 0*Y 0 ω)*(θ 1*Y 1 ω)*(θ 2*Y 2 ω)*(θ 3*Y 3 ω) ∂μ) =
      (θ 0*θ 1*θ 2*θ 3)*(∫ ω, Y 0 ω*Y 1 ω*Y 2 ω*Y 3 ω ∂μ) := by
    calc
      _ = ∫ ω, (θ 0*θ 1*θ 2*θ 3)*(Y 0 ω*Y 1 ω*Y 2 ω*Y 3 ω) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef012 : (∫ ω, (θ 0*Y 0 ω)*(θ 1*Y 1 ω)*(θ 2*Y 2 ω)*B ω ∂μ) =
      (θ 0*θ 1*θ 2)*(∫ ω, Y 0 ω*Y 1 ω*Y 2 ω*B ω ∂μ) := by
    calc
      _ = ∫ ω, (θ 0*θ 1*θ 2)*(Y 0 ω*Y 1 ω*Y 2 ω*B ω) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef013 : (∫ ω, (θ 0*Y 0 ω)*(θ 1*Y 1 ω)*(θ 3*Y 3 ω)*B ω ∂μ) =
      (θ 0*θ 1*θ 3)*(∫ ω, Y 0 ω*Y 1 ω*Y 3 ω*B ω ∂μ) := by
    calc
      _ = ∫ ω, (θ 0*θ 1*θ 3)*(Y 0 ω*Y 1 ω*Y 3 ω*B ω) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef023 : (∫ ω, (θ 0*Y 0 ω)*(θ 2*Y 2 ω)*(θ 3*Y 3 ω)*B ω ∂μ) =
      (θ 0*θ 2*θ 3)*(∫ ω, Y 0 ω*Y 2 ω*Y 3 ω*B ω ∂μ) := by
    calc
      _ = ∫ ω, (θ 0*θ 2*θ 3)*(Y 0 ω*Y 2 ω*Y 3 ω*B ω) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef123 : (∫ ω, (θ 1*Y 1 ω)*(θ 2*Y 2 ω)*(θ 3*Y 3 ω)*B ω ∂μ) =
      (θ 1*θ 2*θ 3)*(∫ ω, Y 1 ω*Y 2 ω*Y 3 ω*B ω ∂μ) := by
    calc
      _ = ∫ ω, (θ 1*θ 2*θ 3)*(Y 1 ω*Y 2 ω*Y 3 ω*B ω) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef01 : (∫ ω, (θ 0*Y 0 ω)*(θ 1*Y 1 ω)*(B ω)^2 ∂μ) =
      (θ 0*θ 1)*(∫ ω, Y 0 ω*Y 1 ω*(B ω)^2 ∂μ) := by
    calc
      _ = ∫ ω, (θ 0*θ 1)*(Y 0 ω*Y 1 ω*(B ω)^2) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef02 : (∫ ω, (θ 0*Y 0 ω)*(θ 2*Y 2 ω)*(B ω)^2 ∂μ) =
      (θ 0*θ 2)*(∫ ω, Y 0 ω*Y 2 ω*(B ω)^2 ∂μ) := by
    calc
      _ = ∫ ω, (θ 0*θ 2)*(Y 0 ω*Y 2 ω*(B ω)^2) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef03 : (∫ ω, (θ 0*Y 0 ω)*(θ 3*Y 3 ω)*(B ω)^2 ∂μ) =
      (θ 0*θ 3)*(∫ ω, Y 0 ω*Y 3 ω*(B ω)^2 ∂μ) := by
    calc
      _ = ∫ ω, (θ 0*θ 3)*(Y 0 ω*Y 3 ω*(B ω)^2) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef12 : (∫ ω, (θ 1*Y 1 ω)*(θ 2*Y 2 ω)*(B ω)^2 ∂μ) =
      (θ 1*θ 2)*(∫ ω, Y 1 ω*Y 2 ω*(B ω)^2 ∂μ) := by
    calc
      _ = ∫ ω, (θ 1*θ 2)*(Y 1 ω*Y 2 ω*(B ω)^2) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef13 : (∫ ω, (θ 1*Y 1 ω)*(θ 3*Y 3 ω)*(B ω)^2 ∂μ) =
      (θ 1*θ 3)*(∫ ω, Y 1 ω*Y 3 ω*(B ω)^2 ∂μ) := by
    calc
      _ = ∫ ω, (θ 1*θ 3)*(Y 1 ω*Y 3 ω*(B ω)^2) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef23 : (∫ ω, (θ 2*Y 2 ω)*(θ 3*Y 3 ω)*(B ω)^2 ∂μ) =
      (θ 2*θ 3)*(∫ ω, Y 2 ω*Y 3 ω*(B ω)^2 ∂μ) := by
    calc
      _ = ∫ ω, (θ 2*θ 3)*(Y 2 ω*Y 3 ω*(B ω)^2) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef0 : (∫ ω, (θ 0*Y 0 ω)*(B ω)^3 ∂μ) =
      (θ 0)*(∫ ω, Y 0 ω*(B ω)^3 ∂μ) := by
    calc
      _ = ∫ ω, (θ 0)*(Y 0 ω*(B ω)^3) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef1 : (∫ ω, (θ 1*Y 1 ω)*(B ω)^3 ∂μ) =
      (θ 1)*(∫ ω, Y 1 ω*(B ω)^3 ∂μ) := by
    calc
      _ = ∫ ω, (θ 1)*(Y 1 ω*(B ω)^3) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef2 : (∫ ω, (θ 2*Y 2 ω)*(B ω)^3 ∂μ) =
      (θ 2)*(∫ ω, Y 2 ω*(B ω)^3 ∂μ) := by
    calc
      _ = ∫ ω, (θ 2)*(Y 2 ω*(B ω)^3) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  have ef3 : (∫ ω, (θ 3*Y 3 ω)*(B ω)^3 ∂μ) =
      (θ 3)*(∫ ω, Y 3 ω*(B ω)^3 ∂μ) := by
    calc
      _ = ∫ ω, (θ 3)*(Y 3 ω*(B ω)^3) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      _ = _ := integral_const_mul _ _
  unfold rawFourthMoment
  dsimp only
  rw [ef0123, ef012, ef013, ef023, ef123, ef01, ef02, ef03, ef12, ef13, ef23, ef0, ef1, ef2, ef3]
  ring

/-- Constant centering uses only the fifteen nonempty selected monomials. -/
lemma fid2_constant_products [IsProbabilityMeasure μ] (X : Fin 4 → Ω → ℝ)
    (h : ∀ s : Finset (Fin 4), s.Nonempty →
      Integrable (fun ω => ∏ a ∈ s, X a ω) μ) (t : ℝ) :
    (let E := fun f : Ω → ℝ => ∫ ω, f ω ∂μ
     let C := fun f g : Ω → ℝ => E (fun ω => f ω*g ω)-E f*E g
     C (fun ω => (X 0 ω-t)*(X 1 ω-t)) (fun ω => (X 2 ω-t)*(X 3 ω-t)) =
       C (fun ω => X 0 ω*X 1 ω) (fun ω => X 2 ω*X 3 ω) -
       t*(C (fun ω => X 0 ω*X 1 ω) (X 2)+
          C (fun ω => X 0 ω*X 1 ω) (X 3)+
          C (X 0) (fun ω => X 2 ω*X 3 ω)+
          C (X 1) (fun ω => X 2 ω*X 3 ω)) +
       t^2*(C (X 0) (X 2)+C (X 0) (X 3)+C (X 1) (X 2)+C (X 1) (X 3))) := by
  have hm : ∀ s : Finset (Fin 4),
      Integrable (fun ω => (∏ a ∈ s, X a ω)*t^(4-s.card)) μ := by
    intro s
    by_cases hs : s = ∅
    · subst s
      simpa using (integrable_const (t^4) : Integrable (fun _ : Ω => t^4) μ)
    · exact (h s (Finset.nonempty_iff_ne_empty.mpr hs)).mul_const _
  have hd := fid2_fourth_data hm
  have hfour := (fid2_fourth_expansion hd).2.trans (fid2_fourth_flat hd)
  have h0 : Integrable (X 0) μ := by simpa using h {0} (by simp)
  have h1 : Integrable (X 1) μ := by simpa using h {1} (by simp)
  have h2 : Integrable (X 2) μ := by simpa using h {2} (by simp)
  have h3 : Integrable (X 3) μ := by simpa using h {3} (by simp)
  have h01 : Integrable (fun ω => X 0 ω*X 1 ω) μ := by
    simpa [mul_assoc] using h {0, 1} (by simp)
  have h23 : Integrable (fun ω => X 2 ω*X 3 ω) μ := by
    simpa [mul_assoc] using h {2, 3} (by simp)
  have hp01 := fid2_pair_expansion (B := fun _ => t)
    h01 (h0.mul_const t) (h1.mul_const t) (integrable_const (t^2))
  have hp23 := fid2_pair_expansion (B := fun _ => t)
    h23 (h2.mul_const t) (h3.mul_const t) (integrable_const (t^2))
  simp only [rawFourthMoment, one_mul, mul_one, integral_mul_const, integral_const,
    probReal_univ, one_smul] at hfour
  simp only [integral_mul_const, integral_const, probReal_univ, one_smul] at hp01 hp23
  dsimp only
  simp only [← mul_assoc] at hfour hp01 hp23 ⊢
  rw [hfour, hp01, hp23]
  ring


end Generic

lemma fid2_covOf_four {n : ℕ} (m : Model n) (a b c d : (Fin n → ℝ) → ℝ) :
    covOf m (fun y => a y*b y) (fun y => c y*d y) =
      expectation m (fun y => a y*b y*c y*d y)-
      expectation m (fun y => a y*b y)*expectation m (fun y => c y*d y) := by
  simp only [covOf, mul_assoc]

lemma fid2_covOf_eq_cov {n : ℕ} (m : Model n) {f g : (Fin n → ℝ) → ℝ}
    (hf : Integrable f m.law) (hg : Integrable g m.law)
    (hfg : Integrable (fun y => f y*g y) m.law) :
    covOf m f g = ProbabilityTheory.covariance f g m.law := by
  let instProbabilityFid2Bridge : IsProbabilityMeasure m.law := m.probability
  exact (fid2_covariance_eq_sub hf hg hfg).symm

lemma fid2_raw_pair {n : ℕ} (m : Model n) (a b : Fin n)
    (h : Integrable (fun y => y a*y b) m.law ∧
      Integrable (fun y => y a*betaHat m y) m.law ∧
      Integrable (fun y => y b*betaHat m y) m.law) :
    Integrable (fun y => weighted m y a*weighted m y b) m.law ∧
    Integrable (fun y => weighted m y a*betaHat m y) m.law ∧
    Integrable (fun y => weighted m y b*betaHat m y) m.law := by
  refine ⟨?_, ?_, ?_⟩
  · exact (h.1.const_mul (m.theta a*m.theta b)).congr
      (Eventually.of_forall fun y => by dsimp only [weighted]; ring)
  · simpa only [weighted, mul_assoc] using h.2.1.const_mul (m.theta a)
  · simpa only [weighted, mul_assoc] using h.2.2.const_mul (m.theta b)

lemma fid2_raw_pair_mean {n : ℕ} (m : Model n) (a b : Fin n) :
    expectation m (fun y => weighted m y a*weighted m y b)-
      expectation m (fun y => weighted m y a*betaHat m y)-
      expectation m (fun y => weighted m y b*betaHat m y)+
      expectation m (fun y => (betaHat m y)^2) =
    pairMoment (expectation m) (fun y => y a) (fun y => y b) (betaHat m)
      (m.theta a) (m.theta b) := by
  have hab : expectation m (fun y => weighted m y a*weighted m y b) =
      m.theta a*m.theta b*expectation m (fun y => y a*y b) := by
    unfold expectation
    calc
      _ = ∫ y, (m.theta a*m.theta b)*(y a*y b) ∂m.law :=
        integral_congr_ae (Eventually.of_forall fun y => by dsimp only [weighted]; ring)
      _ = _ := integral_const_mul _ _
  have haB : expectation m (fun y => weighted m y a*betaHat m y) =
      m.theta a*expectation m (fun y => y a*betaHat m y) := by
    simpa only [expectation, weighted, mul_assoc] using
      (integral_const_mul (μ := m.law) (m.theta a) (fun y => y a*betaHat m y))
  have hbB : expectation m (fun y => weighted m y b*betaHat m y) =
      m.theta b*expectation m (fun y => y b*betaHat m y) := by
    simpa only [expectation, weighted, mul_assoc] using
      (integral_const_mul (μ := m.law) (m.theta b) (fun y => y b*betaHat m y))
  rw [hab, haB, hbB]
  rfl

/-- P011-T17, on the five independent displayed-moment domains. -/
theorem corrected_covariance_expansion_moments
    {n : ℕ} (hn : 0 < n) (m : Model n) (i j k l : Fin n) :
    (let E := expectation m
     let B := betaHat m
     let X : Fin n → (Fin n → ℝ) → ℝ := fun a y => weighted m y a
     let r : Fin n → (Fin n → ℝ) → ℝ := fun a y => X a y - B y
     let Q : Fin n → Fin n → ℝ := fun a b =>
       E (fun y => X a y*X b y) - E (fun y => X a y*B y) -
       E (fun y => X b y*B y) + E (fun y => (B y)^2)
     let v : Fin 4 → Fin n := ![i, j, k, l]
     let Y : Fin 4 → (Fin n → ℝ) → ℝ := fun a y => y (v a)
     let θ : Fin 4 → ℝ := fun a => m.theta (v a)
     let weightedPairs : Prop :=
       Integrable (fun y => (B y)^2) m.law ∧
       ∀ p ∈ ({(i,j), (k,l)} : Finset (Fin n × Fin n)),
         Integrable (fun y => X p.1 y*X p.2 y) m.law ∧
         Integrable (fun y => X p.1 y*B y) m.law ∧
         Integrable (fun y => X p.2 y*B y) m.law
     let weightedFourth : Prop :=
       ∀ s : Finset (Fin 4),
         Integrable (fun y => (∏ a ∈ s, X (v a) y) * (B y)^(4-s.card)) m.law
     let constantMoments : Prop :=
       ∀ s : Finset (Fin 4), s.Nonempty →
         Integrable (fun y => ∏ a ∈ s, X (v a) y) m.law
     let rawPairs : Prop :=
       Integrable (fun y => (B y)^2) m.law ∧
       ∀ p ∈ ({(i,j), (k,l)} : Finset (Fin n × Fin n)),
         Integrable (fun y => y p.1*y p.2) m.law ∧
         Integrable (fun y => y p.1*B y) m.law ∧
         Integrable (fun y => y p.2*B y) m.law
     let rawFourth : Prop :=
       ∀ s : Finset (Fin 4),
         Integrable (fun y => (∏ a ∈ s, Y a y) * (B y)^(4-s.card)) m.law
     (weightedPairs →
       (E (fun y => r i y*r j y) = Q i j ∧
        E (fun y => r k y*r l y) = Q k l)) ∧
     (weightedPairs → weightedFourth →
       (covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
          ProbabilityTheory.covariance (fun y => r i y*r j y)
            (fun y => r k y*r l y) m.law ∧
        covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
          E (fun y => r i y*r j y*r k y*r l y) - Q i j*Q k l ∧
        covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
          fourthMoment E (X i) (X j) (X k) (X l) B - Q i j*Q k l)) ∧
     (constantMoments → ∀ b : ℝ,
       covOf m (fun y => (X i y-b)*(X j y-b))
         (fun y => (X k y-b)*(X l y-b)) =
       covOf m (fun y => X i y*X j y) (fun y => X k y*X l y) -
       b*(covOf m (fun y => X i y*X j y) (X k) +
          covOf m (fun y => X i y*X j y) (X l) +
          covOf m (X i) (fun y => X k y*X l y) +
          covOf m (X j) (fun y => X k y*X l y)) +
       b^2*(covOf m (X i) (X k) + covOf m (X i) (X l) +
            covOf m (X j) (X k) + covOf m (X j) (X l))) ∧
     (rawPairs →
       (Q i j = pairMoment E (fun y => y i) (fun y => y j) B
          (m.theta i) (m.theta j) ∧
        Q k l = pairMoment E (fun y => y k) (fun y => y l) B
          (m.theta k) (m.theta l) ∧
        E (fun y => r i y*r j y) =
          pairMoment E (fun y => y i) (fun y => y j) B (m.theta i) (m.theta j) ∧
        E (fun y => r k y*r l y) =
          pairMoment E (fun y => y k) (fun y => y l) B (m.theta k) (m.theta l))) ∧
     (rawPairs → rawFourth →
       (covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
          ProbabilityTheory.covariance (fun y => r i y*r j y)
            (fun y => r k y*r l y) m.law ∧
        E (fun y => r i y*r j y*r k y*r l y) =
          AronowAudit.P011.Wave1.rawFourthMoment E Y B θ ∧
        covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
          AronowAudit.P011.Wave1.rawFourthMoment E Y B θ -
          pairMoment E (fun y => y i) (fun y => y j) B (m.theta i) (m.theta j) *
          pairMoment E (fun y => y k) (fun y => y l) B (m.theta k) (m.theta l)))) := by
  extract_lets E B X r Q v Y θ weightedPairs weightedFourth constantMoments rawPairs rawFourth
  let instProbabilityFid2 : IsProbabilityMeasure m.law := m.probability
  have pair_mean (hp : weightedPairs) (a b : Fin n)
      (hab : (a, b) ∈ ({(i, j), (k, l)} : Finset (Fin n × Fin n))) :
      E (fun y => r a y*r b y) = Q a b := by
    obtain ⟨hx, ha, hb⟩ := hp.2 (a, b) hab
    exact fid2_pair_expansion hx ha hb hp.1
  have pair_int (hp : weightedPairs) (a b : Fin n)
      (hab : (a, b) ∈ ({(i, j), (k, l)} : Finset (Fin n × Fin n))) :
      Integrable (fun y => r a y*r b y) m.law := by
    obtain ⟨hx, ha, hb⟩ := hp.2 (a, b) hab
    exact fid2_pair_integrable hx ha hb hp.1
  have fourth (hf : weightedFourth) :
      Integrable (fun y => r i y*r j y*r k y*r l y) m.law ∧
      E (fun y => r i y*r j y*r k y*r l y) =
        fourthMoment E (X i) (X j) (X k) (X l) B := by
    unfold E expectation
    simpa [v, r] using fid2_fourth_expansion (fid2_fourth_data hf)
  have weighted_result (hp : weightedPairs) (hf : weightedFourth) :
      covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
        ProbabilityTheory.covariance (fun y => r i y*r j y)
          (fun y => r k y*r l y) m.law ∧
      covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
        E (fun y => r i y*r j y*r k y*r l y)-Q i j*Q k l ∧
      covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
        fourthMoment E (X i) (X j) (X k) (X l) B-Q i j*Q k l := by
    obtain ⟨hi, he⟩ := fourth hf
    have hprod : Integrable (fun y => (r i y*r j y)*(r k y*r l y)) m.law :=
      hi.congr (Eventually.of_forall fun y => by ring)
    have hc := fid2_covOf_four m (r i) (r j) (r k) (r l)
    change covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
      E (fun y => r i y*r j y*r k y*r l y)-
      E (fun y => r i y*r j y)*E (fun y => r k y*r l y) at hc
    rw [pair_mean hp i j (by simp), pair_mean hp k l (by simp)] at hc
    exact ⟨fid2_covOf_eq_cov m (pair_int hp i j (by simp))
      (pair_int hp k l (by simp)) hprod, hc, hc.trans (by rw [he])⟩
  have raw_to_weighted (hp : rawPairs) : weightedPairs := by
    refine ⟨hp.1, ?_⟩
    intro p hmem
    exact fid2_raw_pair m p.1 p.2 (hp.2 p hmem)
  have hqij : Q i j = pairMoment E (fun y => y i) (fun y => y j) B
      (m.theta i) (m.theta j) := fid2_raw_pair_mean m i j
  have hqkl : Q k l = pairMoment E (fun y => y k) (fun y => y l) B
      (m.theta k) (m.theta l) := fid2_raw_pair_mean m k l
  refine ⟨?_, weighted_result, ?_, ?_, ?_⟩
  · intro hp
    exact ⟨pair_mean hp i j (by simp), pair_mean hp k l (by simp)⟩
  · intro hc b
    exact fid2_constant_products (fun a => X (v a)) hc b
  · intro hp
    have hw := raw_to_weighted hp
    exact ⟨hqij, hqkl, (pair_mean hw i j (by simp)).trans hqij,
      (pair_mean hw k l (by simp)).trans hqkl⟩
  · intro hp hf
    have hwf : weightedFourth := fid2_weighted_fourth θ hf
    have hw := weighted_result (raw_to_weighted hp) hwf
    have hraw : E (fun y => r i y*r j y*r k y*r l y) =
        rawFourthMoment E Y B θ := by
      unfold E expectation
      simpa [v, r, X, Y, θ, weighted] using fid2_raw_fourth θ hf
    exact ⟨hw.1, hraw, hw.2.1.trans (by rw [hraw, hqij, hqkl])⟩


end
end AronowAudit.P011.Wave1
