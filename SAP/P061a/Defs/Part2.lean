import SAP.P061a.Defs.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

abbrev BitPair := Fin 2 × Fin 2

def ownBit (i : Fin 2) (z : BitPair) : ℝ :=
  if i = 0 then (z.1.val : ℝ) else (z.2.val : ℝ)

def partnerBit (i : Fin 2) (z : BitPair) : ℝ :=
  if i = 0 then (z.2.val : ℝ) else (z.1.val : ℝ)

def edgeExposure (i : Fin 2) (z : BitPair) : ℝ :=
  ownBit i z + 2 * partnerBit i z

def edgeExposureVector (z : BitPair) : ℝ × ℝ :=
  (edgeExposure 0 z, edgeExposure 1 z)

def inEdgeExposureImage (r : ℝ × ℝ) : Prop := ∃ z : BitPair, edgeExposureVector z = r

def inBitDomain (r : ℝ × ℝ) : Prop :=
  (r.1 = 0 ∨ r.1 = 1) ∧ (r.2 = 0 ∨ r.2 = 1)

noncomputable def geometricMass (k : ℕ) : ℝ := (1/2 : ℝ)^(k+1)

noncomputable def integerExposure : Exposures ℝ 1 := fun _ =>
  Function.extend (fun k : ℕ => (k : ℝ))
    (fun k => if k = 0 then 0 else 1) (fun _ => 0)

def alternatingResponse (k : ℕ) : ℝ :=
  if k = 0 then 0 else (-1 : ℝ)^(k+1) * 2^(k+1)

noncomputable def integerResponse : Responses ℝ 1 := fun _ =>
  Function.extend (fun k : ℕ => (k : ℝ)) alternatingResponse (fun _ => 0)

def coarsenVersion (a : Fin 3) : ℝ := if a = 0 then 0 else 1

def versionExposure {N : ℕ} : Exposures (Fin N → Fin 3) N :=
  fun i z => coarsenVersion (z i)

def versionResponse {N : ℕ} : Responses (Fin N → Fin 3) N :=
  fun i z => ((z i).val : ℝ)

def versionExposureAssignment {N : ℕ} (z : Fin N → Fin 3) : Fin N → Fin 3 :=
  fun i => if z i = 0 then 0 else 1

def samplingSupport (n : ℕ) (z : Fin 4 → Fin 3) : Prop :=
  (Finset.univ.filter (fun i => z i = 2)).card = 1 ∧
    (Finset.univ.filter (fun i => z i ≠ 0)).card = n

noncomputable def samplingResponse : Responses (Fin 4 → Fin 3) 4 :=
  fun i z => ((Finset.univ.filter (fun j => z j ≠ 0)).card : ℝ) *
    (if z i = 2 then 1 else 0)

def pairedOwnBit (K : ℕ) : Exposures (Fin K → BitPair) (K*2) :=
  fun i z => ownBit (finProdFinEquiv.symm i).2 (z (finProdFinEquiv.symm i).1)

def pairedPartnerBit (K : ℕ) : Responses (Fin K → BitPair) (K*2) :=
  fun i z => partnerBit (finProdFinEquiv.symm i).2 (z (finProdFinEquiv.symm i).1)

def pairedEdgeExposure (K : ℕ) : Exposures (Fin K → BitPair) (K*2) :=
  fun i z => pairedOwnBit K i z + 2 * pairedPartnerBit K i z

def inPairedExposureImage (K : ℕ) (r : Fin (K*2) → ℝ) : Prop :=
  ∃ z : Fin K → BitPair, ∀ i, pairedEdgeExposure K i z = r i

def inPairedBitDomain (K : ℕ) (r : Fin (K*2) → ℝ) : Prop :=
  ∀ i, r i = 0 ∨ r i = 1

noncomputable def pairParameter (m : ℕ) : ℝ := if 2 ≤ m then 1/(m : ℝ) else 0

noncomputable def pairResponses (m : ℕ) : Responses (Fin (m^8) → BitPair) (m^8*2) :=
  fun i z => 1 + pairParameter m * pairedPartnerBit (m^8) i z

def replaceOwnBit (i : Fin 2) (e : Fin 2) (z : BitPair) : BitPair :=
  if i = 0 then (e,z.2) else (z.1,e)

def pairedReplacement (K : ℕ) (i : Fin (K*2)) (e : Fin 2) (z : Fin K → BitPair) : Fin K → BitPair :=
  Function.update z (finProdFinEquiv.symm i).1
    (replaceOwnBit (finProdFinEquiv.symm i).2 e (z (finProdFinEquiv.symm i).1))

noncomputable def variancePolynomial (m : ℕ) : ℝ :=
  8 + 16/(m : ℝ) + 14/(m : ℝ)^2 + 2/(m : ℝ)^3 - 4/(m : ℝ)^4

noncomputable def variationDistance {A : Type} [Fintype A] (Q P : A → ℝ) : ℝ :=
  (1/2 : ℝ) * ∑ x, |Q x-P x|

noncomputable def responseRange {A : Type} [Fintype A] (f : A → ℝ) : ℝ :=
  sSup (Set.range f) - sInf (Set.range f)

abbrev Neighborhood {N : ℕ} (A : Type) (H : Finset (Fin N)) := H → A

noncomputable def neighborhoodLaw {A : Type} {N : ℕ} (D : AtomicDesign (Fin N → A))
    (H : Finset (Fin N)) (x : Neighborhood A H) : ℝ :=
  eventProbability D (fun z => ∀ j : H, z j.val=x j)

noncomputable def conditionalNeighborhoodLaw {A : Type} {N : ℕ} (D : AtomicDesign (Fin N → A))
    (i : Fin N) (H : Finset (Fin N)) (e : A) (x : Neighborhood A H) : ℝ :=
  eventProbability D (fun z => z i=e ∧ ∀ j : H, z j.val=x j) /
    eventProbability D (fun z => z i=e)

/-- Exact geometric masses, extended by zero to the full real feasible domain. -/
noncomputable def realIntegerMass : ℝ → ℝ :=
  Function.extend (fun k : ℕ => (k : ℝ)) geometricMass (fun _ => 0)

noncomputable def pairDirectContrast (m : ℕ) (D : AtomicDesign (Fin (m^8) → BitPair)) : ℝ :=
  (m^8*2 : ℝ)⁻¹ * ∑ i, mean D (fun z =>
    pairResponses m i (pairedReplacement (m^8) i 1 z) -
      pairResponses m i (pairedReplacement (m^8) i 0 z))

noncomputable def pairEstimator (m : ℕ) (D : AtomicDesign (Fin (m^8) → BitPair)) :=
  estimateContrast D (pairedOwnBit (m^8)) (pairResponses m) 1 0

noncomputable def pairStandardError (m : ℕ) (D : AtomicDesign (Fin (m^8) → BitPair)) : ℝ :=
  Real.sqrt (designVariance D (pairEstimator m D))


end SAP.P061a
