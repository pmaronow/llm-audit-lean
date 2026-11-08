import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace SAP.P018a
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology BoundedContinuousFunction Matrix.Norms.Elementwise ENNReal
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
abbrev Vec (k : ℕ) := Fin k → ℝ

abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℝ

def outer {k : ℕ} (x y : Vec k) : Mat k := fun a b => x a * y b

def dot {k : ℕ} (x y : Vec k) : ℝ := ∑ a, x a * y a

def dyads (N : ℕ) : Finset (Finset (Fin N)) := univ.powersetCard 2

abbrev Dyad (N : ℕ) := ↥(dyads N)

def members {N : ℕ} (d : Dyad N) : Finset (Fin N) := d.val

theorem members_card {N : ℕ} (d : Dyad N) : (members d).card = 2 := by
  exact (mem_powersetCard.mp d.property).2

def neighbors {N : ℕ} (d : Dyad N) : Finset (Dyad N) :=
  univ.filter (fun q => q ≠ d ∧ (members d ∩ members q).Nonempty)

def overlap {N : ℕ} (d q : Dyad N) : Prop := (members d ∩ members q).Nonempty

instance {N : ℕ} (d q : Dyad N) : Decidable (overlap d q) :=
  inferInstanceAs (Decidable ((members d ∩ members q).Nonempty))

def sandwich {k : ℕ} (P M : Mat k) : Mat k := P * M * P

def score {k : ℕ} (x : Vec k) (r : ℝ) : Vec k := r • x

def meat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) : Mat k :=
  ∑ d, ∑ f, if (s d ∩ s f).Nonempty then outer (q d) (q f) else 0

def unitScore {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (q : E → Vec k) (i : V) : Vec k :=
  ∑ d, if i ∈ s d then q d else 0

def dyadMeat {E : Type*} [Fintype E] {k : ℕ} (q : E → Vec k) : Mat k :=
  ∑ d, outer (q d) (q d)

def expit (t : ℝ) : ℝ := 1 / (1 + Real.exp (-t))

def logisticScore {k : ℕ} (x : Vec k) (y : ℝ) (β : Vec k) : Vec k :=
  score x (y - expit (dot x β))

def logisticBread {E : Type*} [Fintype E] {k : ℕ}
    (X : E → Vec k) (β : Vec k) : Mat k :=
  ∑ d, (expit (dot (X d) β) * (1 - expit (dot (X d) β))) • outer (X d) (X d)

def logisticVariance {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (X : E → Vec k) (Y : E → ℝ) (β : Vec k) : Mat k :=
  sandwich (logisticBread X β)⁻¹ (meat s (fun d => logisticScore (X d) (Y d) β))

def printedLogisticMeat {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (X : E → Vec k) (r : E → ℝ) : Mat k :=
  ∑ d, ∑ f, if (s d ∩ s f).Nonempty then (r d * r f) • outer (X d) (X d) else 0

def sixMembers : Fin 6 → Finset (Fin 4) := ![{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}]

def logitX : Fin 6 → Vec 2 := fun d => ![1, (![0,2,5,5,1,1] : Fin 6 → ℝ) d]

def logitY : Fin 6 → ℝ := ![1,1,1,0,0,0]

def logitR : Fin 6 → ℝ := ![1/2,1/2,1/2,-1/2,-1/2,-1/2]

def logitH : Mat 2 := !![3/2,7/2;7/2,14]

def logitHinv : Mat 2 := !![8/5,-2/5;-2/5,6/35]

def sampleGram {E : Type*} [Fintype E] {k : ℕ} (X : E → Vec k) : Mat k :=
  ∑ d, outer (X d) (X d)

def sampleOLS {E : Type*} [Fintype E] {k : ℕ} (X : E → Vec k) (Y : E → ℝ) : Vec k :=
  (sampleGram X)⁻¹.mulVec (∑ d, score (X d) (Y d))

def fittedResidual {E : Type*} [Fintype E] {k : ℕ}
    (X : E → Vec k) (Y : E → ℝ) (d : E) : ℝ := Y d - dot (X d) (sampleOLS X Y)

def sampleVariance {V E : Type*} [Fintype E] [DecidableEq V]
    (s : E → Finset V) {k : ℕ} (X : E → Vec k) (Y : E → ℝ) : Mat k :=
  sandwich (sampleGram X)⁻¹ (meat s (fun d => score (X d) (fittedResidual X Y d)))

def roleZ1 : Matrix (Fin 3) (Fin 3) ℝ := !![1,0,0;1,0,0;0,1,0]

def roleZ2 : Matrix (Fin 3) (Fin 3) ℝ := !![0,1,0;0,0,1;0,0,1]

def sharedCov3 (τ σ : ℝ) : Mat 3 :=
  τ • ((roleZ1 + roleZ2) * (roleZ1 + roleZ2).transpose) + σ • 1

def twoRoleCov3 (t1 t2 σ : ℝ) : Mat 3 :=
  t1 • (roleZ1 * roleZ1.transpose) + t2 • (roleZ2 * roleZ2.transpose) + σ • 1

def glsF : Matrix (Fin 3) (Fin 2) ℝ := !![1,1;1,3;1,2]

def glsWinv : Mat 3 := (1/21 : ℝ) • !![8,-3,1;-3,9,-3;1,-3,8]

def glsR : Mat 2 := (1/16 : ℝ) • !![71,-27;-27,15]

def glsL : Matrix (Fin 2) (Fin 3) ℝ := !![19/16,-13/16,5/8;-7/16,9/16,-1/8]

def meanVec {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) (f : Ω → Vec k) : Vec k :=
  fun a => ∫ ω, f ω a ∂ μ

def meanMat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) (f : Ω → Mat k) : Mat k :=
  fun a b => ∫ ω, f ω a b ∂ μ

def covMat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (f g : Ω → Vec k) : Mat k :=
  fun a b => ProbabilityTheory.covariance (fun ω => f ω a) (fun ω => g ω b) μ

def varMat {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (μ : Measure Ω) (f : Ω → Vec k) : Mat k :=
  covMat μ f f

def inProbability {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    {E : Type*} [NormedAddCommGroup E] (μ : ∀ N : ℕ, Measure (Ω N))
    (f : ∀ N : ℕ, Ω N → E) : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun N : ℕ => (μ N {ω | ε ≤ ‖f N ω‖}).toReal) atTop (𝓝 0)

def weakLimit {Ω : ℕ → Type*} [∀ N : ℕ, MeasurableSpace (Ω N)]
    {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    (μ : ∀ N : ℕ, Measure (Ω N)) (f : ∀ N : ℕ, Ω N → E) (ν : Measure E) : Prop :=
  (∀ N : ℕ, AEMeasurable (f N) (μ N)) ∧ IsProbabilityMeasure ν ∧
  ∀ g : E →ᵇ ℝ, Tendsto (fun N : ℕ => ∫ ω, g (f N ω) ∂ μ N) atTop (𝓝 (∫ x, g x ∂ ν))

def centeredNormalLaw {k : ℕ} (ν : Measure (Vec k)) (V : Mat k) : Prop :=
  V.PosSemidef ∧ IsProbabilityMeasure ν ∧ ∀ c : Vec k,
    ν.map (fun x => dot c x) = gaussianReal 0 (dot c (V.mulVec c)).toNNReal

structure Kernel (U : Type*) [MeasurableSpace U] (k : ℕ) where
  μ : Measure U
  X : U → U → Vec k
  Y : U → U → ℝ

def unitSampleLaw {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) (N : ℕ) :
    Measure (Fin N → U) := Measure.pi (fun _ => K.μ)

def populationGram {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Mat k :=
  meanMat (K.μ.prod K.μ) (fun uv => outer (K.X uv.1 uv.2) (K.X uv.1 uv.2))

def populationBeta {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Vec k :=
  (populationGram K)⁻¹.mulVec (meanVec (K.μ.prod K.μ) (fun uv => score (K.X uv.1 uv.2) (K.Y uv.1 uv.2)))

def populationResidual {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (u v : U) : ℝ := K.Y u v - dot (K.X u v) (populationBeta K)

def firstUnit {N : ℕ} (d : Dyad N) : Fin N :=
  (members d).min' (Finset.card_pos.mp (by rw [members_card]; omega))

def secondUnit {N : ℕ} (d : Dyad N) : Fin N :=
  (members d).max' (Finset.card_pos.mp (by rw [members_card]; omega))

def design {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (ω : Fin N → U) : Dyad N → Vec k :=
  fun d => K.X (ω (firstUnit d)) (ω (secondUnit d))

def response {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (ω : Fin N → U) : Dyad N → ℝ :=
  fun d => K.Y (ω (firstUnit d)) (ω (secondUnit d))

def epsilon {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k)
    (ω : Fin N → U) (d : Dyad N) : ℝ :=
  populationResidual K (ω (firstUnit d)) (ω (secondUnit d))

def populationScore {U : Type*} [MeasurableSpace U] {k : ℕ}
    (K : Kernel U k) (u v : U) : Vec k := score (K.X u v) (populationResidual K u v)

def scoreSum {U : Type*} [MeasurableSpace U] {k N : ℕ} (K : Kernel U k) (ω : Fin N → U) : Vec k :=
  ∑ d : Dyad N, score (design K ω d) (epsilon K ω d)

def Standing {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Prop :=
  IsProbabilityMeasure K.μ ∧
  Measurable (fun uv : U × U => K.X uv.1 uv.2) ∧
  Measurable (fun uv : U × U => K.Y uv.1 uv.2) ∧
  (∀ u v, K.X u v = K.X v u ∧ K.Y u v = K.Y v u) ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ uv ∂ K.μ.prod K.μ, ‖K.X uv.1 uv.2‖ ≤ C ∧ |K.Y uv.1 uv.2| ≤ C) ∧
  (∃ j : Fin k, ∀ u v, K.X u v j = 1) ∧ (populationGram K).det ≠ 0

def Proposition1Extra {U : Type*} [MeasurableSpace U] {k : ℕ} (K : Kernel U k) : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, ∀ᵐ ω ∂ unitSampleLaw K N,
    ∀ d, |fittedResidual (design K ω) (response K ω) d| ≤ C) ∧
  (∀ a b, (populationGram K) a b ≠ 0) ∧
  (∀ a b, (meanMat (Measure.pi (fun _ : Fin 3 => K.μ)) (fun u =>
    outer (K.X (u 0) (u 1)) (K.X (u 0) (u 2)))) a b ≠ 0) ∧
  (∀ᶠ N : ℕ in atTop,
    (∀ d : Dyad N, (∫ ω, (fittedResidual (design K ω) (response K ω) d)^2
      ∂ unitSampleLaw K N) ≠ 0) ∧
    (∀ d f : Dyad N, f ∈ neighbors d →
      (∫ ω, fittedResidual (design K ω) (response K ω) d *
        fittedResidual (design K ω) (response K ω) f ∂ unitSampleLaw K N) ≠ 0))

end SAP.P018a
