import SAP.P033.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace SAP.P033

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

noncomputable section

/-- Mathematical content packaged for P033-T12. -/
def T12Statement : Prop :=
  (∃! H : ℝ, 0 < H ∧ biasCoverage 1 H = 19/20) ∧
    0 < honestHalfLength 1 ∧ biasCoverage 1 (honestHalfLength 1) = 19/20 ∧
    ((264614554821530/10^14:ℝ) < honestHalfLength 1 ∧
      honestHalfLength 1 < 264614554821540/10^14) ∧
    (∀ θ b : ℝ, |b| ≤ 1 →
      intervalCoverage (biasModelLaw θ b) id θ (honestHalfLength 1) =
        biasCoverage b (honestHalfLength 1) ∧
      19/20 ≤ intervalCoverage (biasModelLaw θ b) id θ (honestHalfLength 1) ∧
      (intervalCoverage (biasModelLaw θ b) id θ (honestHalfLength 1) = 19/20 ↔ |b| = 1)) ∧
    ((195996398454000/10^14:ℝ) < normalCritical ∧ normalCritical < 195996398454010/10^14) ∧
    ((128155156554460/10^14:ℝ) < normalQuantile (9/10) ∧
      normalQuantile (9/10) < 128155156554470/10^14) ∧
    (let C := honestHalfLength 1 * normalQuantile (9/10)/normalCritical;
      (173022157382648/10^14:ℝ) < C ∧ C < 173022157382677/10^14 ∧
      {t | pseudoP t (honestHalfLength 1) ≤ 1/5} = {t | C ≤ |t|} ∧
      (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} =
        normalCDF (1-C)+normalCDF (-1-C)) ∧
    ((23579196727091/10^14:ℝ) <
      (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} ∧
      (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} < 23579196727101/10^14) ∧
    (∃! H : ℝ, 0 < H ∧ biasCoverage (1/2) H = 19/20) ∧
    0 < honestHalfLength (1/2) ∧ biasCoverage (1/2) (honestHalfLength (1/2)) = 19/20 ∧
    ((218147744232810/10^14:ℝ) < honestHalfLength (1/2) ∧
      honestHalfLength (1/2) < 218147744232820/10^14) ∧
    ((20414905632765/10^14:ℝ) <
      (biasModelLaw 0 (1/2)).real {t | pseudoP t (honestHalfLength (1/2)) ≤ 1/5} ∧
      (biasModelLaw 0 (1/2)).real {t | pseudoP t (honestHalfLength (1/2)) ≤ 1/5} < 20414905632774/10^14) ∧
    ¬ ValidBiasP 1 (fun t => pseudoP t (honestHalfLength 1)) ∧
    ¬ ValidBiasP (1/2) (fun t => pseudoP t (honestHalfLength (1/2)))

/-- Mathematical content packaged for P033-T13. -/
def T13Statement : Prop :=
  (∀ t h : ℝ, 0 < h →
      ((|t|/(h/normalCritical)) = normalCritical*|t|/h) ∧
      (pseudoP t h < 1/20 ↔ h < |t|) ∧
      (pseudoP t h < 1/20 ↔ 0 ∉ Icc (t-h) (t+h)) ∧
      (pseudoP t h ≤ 1/20 ↔ h ≤ |t|)) ∧
    (∀ B : ℝ, 0 ≤ B → (∃! H : ℝ, 0 < H ∧ biasCoverage B H = 19/20) ∧
      0 < honestHalfLength B ∧ biasCoverage B (honestHalfLength B) = 19/20 ∧
      (∀ b : ℝ, |b| ≤ B →
        (biasModelLaw 0 b).real {t | pseudoP t (honestHalfLength B) < 1/20} =
          1-biasCoverage b (honestHalfLength B) ∧
        (biasModelLaw 0 b).real {t | pseudoP t (honestHalfLength B) < 1/20} ≤ 1/20 ∧
        ((biasModelLaw 0 b).real {t | pseudoP t (honestHalfLength B) < 1/20} = 1/20 ↔ |b| = B))) ∧
    honestHalfLength 0 = normalCritical ∧
    (∀ t : ℝ, pseudoP t (honestHalfLength 0) = 2*normalCDF (-|t|)) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      (biasModelLaw 0 0).real {t | pseudoP t (honestHalfLength 0) ≤ α} = α) ∧
    (1/5:ℝ) < (biasModelLaw 0 1).real {t | pseudoP t (honestHalfLength 1) ≤ 1/5} ∧
    (∀ B : ℝ, 0 ≤ B →
      biasAwareP B 0 = 1 ∧ Continuous (biasAwareP B) ∧
      StrictAntiOn (biasAwareP B) (Ici 0) ∧
      Tendsto (biasAwareP B) atTop (𝓝 0) ∧ ValidBiasP B (biasAwareP B) ∧
      (∀ b α : ℝ, |b| = B → 0 < α → α < 1 →
        (biasModelLaw 0 b).real {t | biasAwareP B t ≤ α} = α) ∧
      (∀ t : ℝ, (biasAwareP B t ≤ 1/20 ↔ honestHalfLength B ≤ |t|) ∧
        (biasAwareP B t ≤ 1/20 ↔ pseudoP t (honestHalfLength B) ≤ 1/20)))

/-- Mathematical content packaged for P033-T14. -/
def T14Statement : Prop :=
  (∀ q : ℝ, 0 < q →
      upperSE (-3/20) (-101/1000) q = 49/(1000*q) ∧
      widthSE (-213/1000) (-101/1000) q = 7/(125*q) ∧
      widthSE (-213/1000) (-101/1000) q /
        upperSE (-3/20) (-101/1000) q = 8/7) ∧
    ((-101/1000 : ℝ) - (-3/20) = 49/1000 ∧
      (-101/1000 : ℝ) - (-213/1000) = 14/125) ∧
    upperSE (-3/20) (-101/1000) (49/25) = 1/40 ∧
    absoluteT (-3/20) (upperSE (-3/20) (-101/1000) (49/25)) = 6 ∧
    widthSE (-213/1000) (-101/1000) (49/25) = 1/35 ∧
    absoluteT (-3/20) (widthSE (-213/1000) (-101/1000) (49/25)) = 21/4 ∧
    (((-213/1000 : ℝ) + (-101/1000))/2 - (-3/20) = -7/1000) ∧
    (∀ q : ℝ, 0 < q →
      absoluteT (79/1000) (widthSE (27/1000) (132/1000) q) / q = 158/105 ∧
      absoluteT (79/1000) (upperSE (79/1000) (132/1000) q) / q = 79/53) ∧
    ((27/18 : ℝ) < 158/105 ∧ (158/105 : ℝ) < 28/18 ∧
      (26/18 : ℝ) < 79/53 ∧ (79/53 : ℝ) < 27/18)

/-- Mathematical content packaged for P033-T15. -/
def T15Statement : Prop :=
  (∀ α β L U : ℝ, L < U → 0 < normalQuantile (1-α/2) →
      let q := normalQuantile (1-α/2)
      widthSE L U q = (U-L)/(2*q) ∧
      absoluteT β (widthSE L U q) = |β|/widthSE L U q ∧
      reconstructedP β L U q = 2*normalCDF (-absoluteT β (widthSE L U q))) ∧
    normalQuantile (1-(1/10 : ℝ)/2) = normalQuantile (19/20) ∧
    normalQuantile (1-(1/20 : ℝ)/2) = normalCritical ∧
    (∀ β L U q : ℝ, L < U → 0 < q →
      2*q*(widthSE L U q - upperSE β U q) = 2*β-(L+U) ∧
      (widthSE L U q = upperSE β U q ↔ β = (L+U)/2) ∧
      (upperSE β U q < widthSE L U q ↔ (L+U)/2 < β) ∧
      (widthSE L U q < upperSE β U q ↔ β < (L+U)/2)) ∧
    (∀ β q s : ℝ, 0 < q → 0 < s →
      widthSE (β-q*s) (β+q*s) q = s ∧ upperSE β (β+q*s) q = s) ∧
    (∀ q : ℝ, 0 < q →
      widthSE (-213/1000) (-101/1000) q = 7/(125*q) ∧
      absoluteT (-3/20) (widthSE (-213/1000) (-101/1000) q) = 75*q/28) ∧
    (widthSE (-213/1000) (-101/1000) (49/25) = 1/35 ∧
      absoluteT (-3/20) (widthSE (-213/1000) (-101/1000) (49/25)) = 21/4)

/-- Mathematical statement packaged for P033-T1. -/
def T1Statement : Prop :=
  T1CoreStatement ∧ M1Certificate ∧ M1WLSCertificate ∧
    m1Bias = ![-6/5,3/2,3/5,-9/10] ∧
    m1Corrected = ![12/5,-6/5,-4/5,3/5] ∧
    variance (rdEstimator m1Corrected) (rdConditionalLaw m1Treated m1Control) /
      variance (rdEstimator m1Linear) (rdConditionalLaw m1Treated m1Control) = 410/83 ∧
    (1 : ℝ) < 410/83

/-- Mathematical statement packaged for P033-T2. -/
def T2Statement : Prop :=
  T2CoreStatement.{u, v, w} ∧ M2Certificate ∧
    Continuous m1Control ∧ Continuous m1Treated ∧
    (∫ Y, rdEstimator m1Linear Y ∂rdConditionalLaw m2Treated m1Control) = 4 ∧
    HasLaw (fun Y => (rdEstimator m1Linear Y-4)/m1SELinear)
      (gaussianReal 0 1) (rdConditionalLaw m2Treated m1Control) ∧
    (gaussianReal 0 1).real {x : ℝ | (5 : ℝ) ≤ |x|} ≤ 1/25 ∧
    (∀ N : ℕ, 1 ≤ N → ∀ S : Finset (Fin N),
      ∀ (E : Type v) [MeasurableSpace E]
        (F : (Fin N → (Fin 2 × Fin 4) → ℝ) → E),
        Measurable F → (studyDataLaw N S).map F = (studyDataLaw N ∅).map F) ∧
    ((41/5 : ℝ) = 83/50+243/50+42/25)

/-- Mathematical statement packaged for P033-T3. -/
def T3Statement : Prop :=
  T3CoreStatement ∧ ClusterCertificate ∧ ClusterWLSCertificate ∧
    (∀ ω : (Fin 10 ⊕ (Fin 10 × Fin 5)) → Bool, ∀ g : Fin 10,
      (clusterLinear g/5)*(∑ i, nnResidual (noisyClusterOutcome ω g) i) = 0 ∧
      (clusterCorrected g/5)*(∑ i, nnResidual (noisyClusterOutcome ω g) i) = 0) ∧
    (∀ f : ℝ,
      (Finset.univ.filter (fun ω : Fin 10 → Bool =>
        0 ∈ Icc (clusterEstimator clusterLinear ω-normalCritical*Real.sqrt
          (clusterScoreVariance f (fun g => (clusterLinear g/5)*∑ i, nnResidual (clusterOutcome ω g) i)))
          (clusterEstimator clusterLinear ω+normalCritical*Real.sqrt
          (clusterScoreVariance f (fun g => (clusterLinear g/5)*∑ i, nnResidual (clusterOutcome ω g) i))))).card = 112 ∧
      (Finset.univ.filter (fun ω : Fin 10 → Bool =>
        0 ∈ Icc (clusterEstimator clusterCorrected ω-normalCritical*Real.sqrt
          (clusterScoreVariance f (fun g => (clusterCorrected g/5)*∑ i, nnResidual (clusterOutcome ω g) i)))
          (clusterEstimator clusterCorrected ω+normalCritical*Real.sqrt
          (clusterScoreVariance f (fun g => (clusterCorrected g/5)*∑ i, nnResidual (clusterOutcome ω g) i))))).card = 56)

/-- Mathematical statement packaged for P033-T7. -/
def T7Statement : Prop :=
  T7CoreStatement ∧
    binomialTail 19 13 (1/2) = 10949/131072 ∧
    (1/20 : ℝ) < binomialTail 19 13 (1/2) ∧
    binomialTail 19 14 (1/2) < (1/20 : ℝ) ∧
    0 < (caliperDataLaw 19 linearCaliperDensity).real
      {X | caliperCount (caliperCutoff/5) X = 19}

/-- Mathematical statement packaged for P033-T8. -/
def T8Statement : Prop :=
  T8CoreStatement ∧
    (∀ M : ℕ, ∀ h : ℝ, 0 ≤ h → ∀ X : Fin M → ℝ,
      caliperSuccesses h X ≤ caliperCount h X)

/-- Mathematical statement packaged for P033-T9. -/
def T9Statement : Prop :=
  T9CoreStatement.{u, v} ∧
    ((23+46 : ℕ)-57 = 12 ∧ (98+101 : ℕ)-185 = 14 ∧
      (202+226 : ℕ)-278 = 150 ∧ (133+130 : ℕ)-204 = 59) ∧
    ((0 : ℝ) < 19/23 ∧ (19/23 : ℝ) < 1 ∧
      (0 : ℝ) < 185/199 ∧ (185/199 : ℝ) < 1 ∧
      (0 : ℝ) < 139/214 ∧ (139/214 : ℝ) < 1 ∧
      (0 : ℝ) < 204/263 ∧ (204/263 : ℝ) < 1)

/-- Mathematical statement packaged for P033-T10. -/
def T10Statement : Prop :=
  T10CoreStatement ∧
    ((25/49 : ℝ)*(1/2) = 25/98 ∧ (25/98 : ℝ) < 1/2)

/-- Mathematical statement packaged for P033-T11. -/
def T11Statement : Prop :=
  T11CoreStatement ∧ 0 < normalCritical ∧
    (51021/10^5 : ℝ) < 1/normalCritical ∧
    1/normalCritical < (51022/10^5 : ℝ)

end
end SAP.P033
