import SAP.P033.Defs.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

namespace SAP.P033

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

noncomputable section

/-- Mathematical content packaged for P033-T5. -/
def T5Statement : Prop :=
  (∀ eligible treated cell i,
      countToyPotential eligible treated cell i = 0 ∨ countToyPotential eligible treated cell i = 1) ∧
    (∀ eligible i, countToyTreatment eligible i = 0 ∨ countToyTreatment eligible i = 1) ∧
    (∀ i, countToyTreatment false i ≤ countToyTreatment true i) ∧
    (∑ i, countToyTreatment true i) = 50 ∧ (∑ i, countToyTreatment false i) = 0 ∧
    (∀ cell, (∑ i, countToyPotential true false cell i) = (eligibleBaseline cell:ℝ) ∧
      (∑ i, (countToyPotential true true cell i - countToyPotential true false cell i)) = 5) ∧
    (∀ cell, (∑ i, countToyObserved true cell i) = ![(10:ℝ),50] cell ∧
      (∑ i, countToyObserved false cell i) = ![(10:ℝ),40] cell) ∧
    ((5+45 : ℝ)/200 = (10+40)/200) ∧
    waldRatio 30 25 50 0 = 1/10 ∧
    ((10+40 : ℝ)/200 = 1/4) ∧ binaryPopulationVariance (1/4) = 3/16 ∧
    ((1/10 : ℝ)^2/binaryPopulationVariance (1/4) = 4/75) ∧
    sampleVariance ![(10:ℝ),50] = 800 ∧ sampleVariance ![(10:ℝ),40] = 450 ∧
    ((1/10 : ℝ)^2/sampleVariance ![(10:ℝ),50] = 1/80000) ∧
    ((1/80000 : ℝ) ≠ 4/75) ∧
    waldRatio 60 50 100 0 = 1/10 ∧ ((20+80 : ℝ)/400 = 1/4) ∧
    sampleVariance ![(20:ℝ),100] = 3200 ∧
    ((1/10 : ℝ)^2/sampleVariance ![(20:ℝ),100] = 1/320000) ∧
    ((1/320000 : ℝ) = (1/80000)/4) ∧
    (∀ yE yI dE dI sd scale : ℝ, 0 < scale → dE ≠ dI → 0 < sd →
      waldRatio (scale*yE) (scale*yI) (scale*dE) (scale*dI) = waldRatio yE yI dE dI ∧
      waldRatio (scale*yE) (scale*yI) (scale*dE) (scale*dI)/(scale*sd) = (waldRatio yE yI dE dI/sd)/scale) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ y : Fin n → ℝ, ∀ scale : ℝ, 0 < scale →
      sampleSD (fun i => scale*y i) = scale*sampleSD y)

/-- Mathematical content packaged for P033-T6. -/
def T6Statement : Prop :=
  (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Y : Ω → ℝ) (p : ℝ), Measurable Y →
      (∀ᵐ ω ∂μ, Y ω = 0 ∨ Y ω = 1) → μ.real {ω | Y ω = 1} = p →
      variance Y μ = p*(1-p) ∧ variance Y μ = 1/4-(p-1/2)^2 ∧
      variance Y μ ≤ 1/4 ∧ Real.sqrt (variance Y μ) ≤ 1/2) ∧
    (∀ N : ℕ, 2 ≤ N → ∀ Y : Fin N → ℝ,
      (∀ i, Y i = 0 ∨ Y i = 1) →
      sampleVariance Y = (N:ℝ)/((N:ℝ)-1)*sampleMean Y*(1-sampleMean Y) ∧
      sampleVariance Y ≤ (N:ℝ)/(4*((N:ℝ)-1)) ∧
      (1/10:ℝ)*sampleSD Y ≤ (1/20:ℝ)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 1 →
      (1/10:ℝ)*Real.sqrt (binaryPopulationVariance p) ≤ 1/20) ∧
    (∀ p q : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ q → q ≤ 1 → |p-q| ≤ 1) ∧
    (1:ℝ) < 1229/500 ∧ normalPower 0 = 1/20 ∧
    (∀ a : ℝ, 0 < a → HasDerivAt normalPower
      (normalDensity (a-normalCritical)-normalDensity (a+normalCritical)) a ∧
      0 < normalDensity (a-normalCritical)-normalDensity (a+normalCritical) ∧
      normalPower a < normalCDF (a-normalCritical)+1/40) ∧
    StrictMonoOn normalPower (Ici 0) ∧
    (∀ τ : ℝ, |τ| ≤ 1/20 → normalPower (|τ|/binaryStudySE) ≤
      normalPower (1/(20*binaryStudySE)) ∧ normalPower (|τ|/binaryStudySE) < 19/20) ∧
    ((8972619/10^7 : ℝ) < normalPower (1/(20*binaryStudySE)) ∧
      normalPower (1/(20*binaryStudySE)) < (8972620/10^7 : ℝ)) ∧
    (∃ σ60 σ80 σ95 : ℝ,
      normalPower ((1/10)*σ60/binaryStudySE) = 3/5 ∧
      normalPower ((1/10)*σ80/binaryStudySE) = 4/5 ∧
      normalPower ((1/10)*σ95/binaryStudySE) = 19/20 ∧
      (3430295/10^7:ℝ) < σ60 ∧ σ60 < 3430296/10^7 ∧
      (4342101/10^7:ℝ) < σ80 ∧ σ80 < 4342102/10^7 ∧
      (5587016/10^7:ℝ) < σ95 ∧ σ95 < 5587017/10^7 ∧ (1/2:ℝ) < σ95) ∧
    (∀ N : ℕ, 31731 ≤ N →
      (1/2:ℝ)*Real.sqrt ((N:ℝ)/((N:ℝ)-1)) ≤ 5000079/10^7 ∧
      normalPower ((1/20)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))/binaryStudySE) ≤ 8972711/10^7 ∧
      normalPower ((1/20)*Real.sqrt ((N:ℝ)/((N:ℝ)-1))/binaryStudySE) < 19/20) ∧
    (((15/4 : ℝ)-1)/36 = 11/144) ∧ (((11/4 : ℝ)-1)/10 = 7/40) ∧
    (∀ β se σ : ℝ, 0 < σ → 0 < se → (|β|/σ)/(se/σ) = |β|/se)

/-- Mathematical content packaged for P033-T7. -/
def T7CoreStatement : Prop :=
  (∫ x in (0:ℝ)..4, x/8) = 1 ∧
    (∀ r ∈ ({(1/10:ℝ),3/20,1/5} : Finset ℝ),
      let h := caliperCutoff*r;
      0 < h ∧ h < caliperCutoff ∧
      (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), 0 < linearCaliperDensity x) ∧
      caliperAbove linearCaliperDensity h = (2*caliperCutoff*h+h^2)/16 ∧
      caliperBelow linearCaliperDensity h = (2*caliperCutoff*h-h^2)/16 ∧
      caliperProbability linearCaliperDensity h = 1/2+r/4 ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) linearCaliperDensity (Ioo (caliperCutoff-h) (caliperCutoff+h))) ∧
    caliperProbability linearCaliperDensity (caliperCutoff/10) = 21/40 ∧
    caliperProbability linearCaliperDensity (caliperCutoff*3/20) = 43/80 ∧
    caliperProbability linearCaliperDensity (caliperCutoff/5) = 11/20 ∧
    caliperAbove linearCaliperDensity (caliperCutoff/5) = 26411/250000 ∧
    caliperBelow linearCaliperDensity (caliperCutoff/5) = 21609/250000 ∧
    ((caliperCutoff-caliperCutoff/10 = 441/250 ∧ caliperCutoff+caliperCutoff/10 = 539/250) ∧
      (caliperCutoff-caliperCutoff*3/20 = 833/500 ∧ caliperCutoff+caliperCutoff*3/20 = 1127/500) ∧
      (caliperCutoff-caliperCutoff/5 = 196/125 ∧ caliperCutoff+caliperCutoff/5 = 294/125)) ∧
    (∀ k : ℕ, k ≤ 19 → (binomialTail 19 k (1/2) ≤ 1/20 ↔ 14 ≤ k)) ∧
    (∀ M : ℕ, 19 ≤ M →
      let μ := caliperDataLaw M linearCaliperDensity;
      μ.real {X | caliperCount (caliperCutoff/5) X = 19} > 0 →
      μ.real ({X | caliperCount (caliperCutoff/5) X = 19} ∩
        {X | binomialTail 19 (caliperSuccesses (caliperCutoff/5) X) (1/2) ≤ 1/20}) /
        μ.real {X | caliperCount (caliperCutoff/5) X = 19} = binomialTail 19 14 (11/20)) ∧
    (1/20:ℝ) < binomialTail 19 14 (11/20) ∧
    binomialTail 12 9 (1/2) = 299/4096 ∧
    binomialTail 12 9 (21/40) = 336637329302285487/3355443200000000000 ∧
    binomialTail 15 11 (1/2) = 1941/32768 ∧
    binomialTail 15 11 (43/80) = 3589476431322242287677900507/35184372088832000000000000000 ∧
    binomialTail 19 14 (1/2) = 2083/65536 ∧
    binomialTail 19 14 (11/20) = 50930691593528557166389/655360000000000000000000 ∧
    (∀ m : ℕ, 1 ≤ m →
      (∫ x in (0:ℝ)..4, ((m:ℝ)+1)*x^m/4^(m+1)) = 1 ∧
      (∀ h : ℝ, 0 < h → h < caliperCutoff →
        (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), 0 < powerCaliperDensity m x) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (powerCaliperDensity m) (Ioo (caliperCutoff-h) (caliperCutoff+h)) ∧
        caliperProbability (powerCaliperDensity m) h =
          ((caliperCutoff+h)^(m+1)-caliperCutoff^(m+1))/
          ((caliperCutoff+h)^(m+1)-(caliperCutoff-h)^(m+1)))) ∧
    (∀ h : ℝ, 0 < h → h < caliperCutoff →
      Tendsto (fun m : ℕ => caliperProbability (powerCaliperDensity m) h) atTop (𝓝 1)) ∧
    caliperProbability (powerCaliperDensity 9) (49/125) = 4609141/5401600 ∧
    (∀ θ x : ℝ, 0 ≤ x → (gaussianReal θ 1).real {t | |t| ≤ x} = foldedNormalCDF θ x) ∧
    (∀ θ : ℝ, intervalCoverage (gaussianReal θ 1) id θ normalCritical = 19/20) ∧
    ((644747758104/10^12:ℝ) ≤ foldedCaliperProbability (7/2) (49/125) ∧
      foldedCaliperProbability (7/2) (49/125) ≤ 644747758105/10^12) ∧
    ((280413461677/10^12:ℝ) ≤ binomialTail 19 14 (foldedCaliperProbability (7/2) (49/125)) ∧
      binomialTail 19 14 (foldedCaliperProbability (7/2) (49/125)) ≤ 280413461678/10^12) ∧
    ((318944499071/10^12:ℝ) ≤ foldedCaliperProbability 0 (49/125) ∧
      foldedCaliperProbability 0 (49/125) ≤ 318944499072/10^12)

/-- Mathematical content packaged for P033-T8. -/
def T8CoreStatement : Prop :=
  ∀ (f : ℝ → ℝ) (_hf0 : ∀ x, 0 ≤ f x)
    (_hfs : ∀ x, x < 0 → f x = 0) (_hfi : Integrable f volume)
    (_hfn : (∫ x, f x) = 1),
(∀ h : ℝ, 0 < h → h < caliperCutoff → 0 < caliperAbove f h+caliperBelow f h →
      (∀ M n : ℕ, (caliperDataLaw M f).real {X | caliperCount h X = n} > 0 →
        (∀ j : ℕ, j ≤ n →
          (caliperDataLaw M f).real ({X | caliperCount h X = n} ∩ {X | caliperSuccesses h X = j}) /
            (caliperDataLaw M f).real {X | caliperCount h X = n} =
          (n.choose j:ℝ)*caliperProbability f h^j*(1-caliperProbability f h)^(n-j)) ∧
        (∀ k : ℕ, k ≤ n →
          (caliperDataLaw M f).real ({X | caliperCount h X = n} ∩ {X | k ≤ caliperSuccesses h X}) /
            (caliperDataLaw M f).real {X | caliperCount h X = n} =
          binomialTail n k (caliperProbability f h))) ∧
      (caliperProbability f h = 1/2 ↔ caliperAbove f h = caliperBelow f h) ∧
      ((∀ u : ℝ, 0 < u → u < h → f (caliperCutoff+u) = f (caliperCutoff-u)) →
        caliperAbove f h = caliperBelow f h) ∧
      (AntitoneOn f (Icc (caliperCutoff-h) (caliperCutoff+h)) →
        caliperAbove f h ≤ caliperBelow f h ∧ caliperProbability f h ≤ 1/2 ∧
        ∀ n k : ℕ, k ≤ n → binomialTail n k (caliperProbability f h) ≤ binomialTail n k (1/2)) ∧
      (MonotoneOn f (Icc (caliperCutoff-h) (caliperCutoff+h)) →
        caliperBelow f h ≤ caliperAbove f h ∧ 1/2 ≤ caliperProbability f h ∧
        ∀ n k : ℕ, k ≤ n → binomialTail n k (1/2) ≤ binomialTail n k (caliperProbability f h)) ∧
      (∀ a L : ℝ, 0 < a →
        (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h), a ≤ f x) →
        (∀ x ∈ Icc (caliperCutoff-h) (caliperCutoff+h),
          ∀ y ∈ Icc (caliperCutoff-h) (caliperCutoff+h), |f x-f y| ≤ L*|x-y|) →
        |caliperAbove f h-caliperBelow f h| ≤ L*h^2 ∧
        2*h*a ≤ caliperAbove f h+caliperBelow f h ∧
        |caliperProbability f h-1/2| = |caliperAbove f h-caliperBelow f h|/
          (2*(caliperAbove f h+caliperBelow f h)) ∧
        |caliperProbability f h-1/2| ≤ L*h/(4*a))) ∧
    (∀ n k : ℕ, k ≤ n → MonotoneOn (binomialTail n k) (Icc 0 1)) ∧
    (ContinuousAt f caliperCutoff → 0 < f caliperCutoff →
      Tendsto (caliperProbability f) (𝓝[>] (0:ℝ)) (𝓝 (1/2))) ∧
    (∀ f' : ℝ, HasDerivAt f f' caliperCutoff → 0 < f caliperCutoff →
      Asymptotics.IsLittleO (𝓝[>] (0:ℝ))
        (fun h => caliperProbability f h-1/2-h*f'/(4*f caliperCutoff)) (fun h => h)) ∧
    (binomialTail 12 9 (1/2) = 299/4096 ∧ binomialTail 15 11 (1/2) = 1941/32768 ∧
      binomialTail 19 14 (1/2) = 2083/65536)

/-- Mathematical content packaged for P033-T9. -/
def T9CoreStatement : Prop :=
  (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (T : Ω → ℝ) (τ s : ℝ), 0 < s → HasLaw T (gaussianReal (τ/s) 1) μ →
      μ.real {ω | normalCritical < |T ω|} = normalPower (|τ|/s)) ∧
    normalPower 0 = 1/20 ∧
    (∀ a : ℝ, 0 < a → HasDerivAt normalPower
      (normalDensity (a-normalCritical)-normalDensity (a+normalCritical)) a ∧
      0 < normalDensity (a-normalCritical)-normalDensity (a+normalCritical)) ∧
    StrictMonoOn normalPower (Ici 0) ∧
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → 1/20 < normalPower a → normalPower a < 1 →
      normalPower a = normalPower b → a = b) ∧
    (∀ (α : Type*) [DecidableEq α] (L R : Finset α), L.Nonempty → R.Nonempty →
      L.card+R.card = (L ∪ R).card+(L ∩ R).card ∧
      1/2 ≤ clusterCountRatio L R ∧ clusterCountRatio L R ≤ 1 ∧
      (clusterCountRatio L R < 1 ↔ L ∩ R ≠ ∅)) ∧
    (∀ τ s ρ : ℝ, τ ≠ 0 → 0 < s → 0 < ρ → ρ < 1 →
      normalPower (|τ|/s) < normalPower (|τ|/(s*Real.sqrt ρ))) ∧
    ((57/(23+46):ℝ) = 19/23 ∧ (185/(98+101):ℝ) = 185/199 ∧
      (278/(202+226):ℝ) = 139/214 ∧ (204/(133+130):ℝ) = 204/263) ∧
    ((31/48:ℝ)-1/36 = 89/144 ∧ (113/144:ℝ)-1/36 = 109/144 ∧
      (31/48:ℝ)-1/36 = 89/144 ∧ (61/104:ℝ)-1/26 = 57/104 ∧
      (81/104:ℝ)-1/26 = 77/104 ∧ (61/104:ℝ)-1/26 = 57/104)

/-- Mathematical content packaged for P033-T10. -/
def T10CoreStatement : Prop :=
  (0 ≤ (1/2 : ℝ) ∧ (1/2 : ℝ) ≤ 2 ∧ (1/2 : ℝ) ≤ 4/5) ∧
    ((1/2 : ℝ)/(1/2) = 1 ∧ (1 : ℝ) < 49/25) ∧
    ((1/2 : ℝ)/(49/25) = 25/98 ∧ (25/98 : ℝ) < 1/2) ∧
    sampleMean ![(0:ℝ),2,4] = 2 ∧
    sampleVariance ![(0:ℝ),2,4] = 4 ∧
    sampleSD ![(0:ℝ),2,4] = 2 ∧
    funnelPoint 1 (1/2) 2 = (1/2,1/4) ∧
    funnelPoint 1 (1/2) 4 = (1/4,1/8) ∧
    funnelPoint 1 (1/2) 2 ≠ funnelPoint 1 (1/2) 4 ∧
    ((1/2 : ℝ)/(1/4) = 2 ∧ (1/4 : ℝ)/(1/8) = 2)

/-- Mathematical content packaged for P033-T11. -/
def T11CoreStatement : Prop :=
  (∀ β se s : ℝ, s ≠ 0 → se ≠ 0 → (β/s)/(se/s) = β/se) ∧
    (∀ x y ζ : ℝ, y ≠ 0 → ζ ≠ 0 → (x/y = ζ ↔ y = x/ζ)) ∧
    (∀ x y ζ : ℝ, 0 < y → 0 < ζ →
      (ζ ≤ x/y ↔ y ≤ x/ζ) ∧ (y ≤ x/ζ ↔ ζ*y ≤ x)) ∧
    ((1 : ℝ)/(49/25) = 25/49 ∧ (25/49 : ℝ) < 1 ∧ (1 : ℝ) < 49/25) ∧
    (∀ v : ℝ, 0 ≤ v → (Real.sqrt v = v ↔ v = 0 ∨ v = 1)) ∧
    (∀ n k : ℕ, 2 ≤ n → k ≤ n →
      binarySampleVariance n k = (k:ℝ)*((n:ℝ)-k)/((n:ℝ)*((n:ℝ)-1))) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ y : Fin n → ℝ,
      (∀ i, y i = 0 ∨ y i = 1) → ∀ k : ℕ, (∑ i, y i) = (k:ℝ) →
      sampleVariance y = (k:ℝ)*((n:ℝ)-k)/((n:ℝ)*((n:ℝ)-1))) ∧
    binarySampleVariance 568 82 = 123/994 ∧
    ((351770457441169/10^15 - 1/10^14 : ℝ)^2 < 123/994 ∧
      (123/994 : ℝ) < (351770457441169/10^15 + 1/10^14)^2)

end
end SAP.P033
