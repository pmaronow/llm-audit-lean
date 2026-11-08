import SAP.P061a.Defs.Part3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P061a

open scoped BigOperators Topology Classical BoundedContinuousFunction MeasureTheory
open Filter

def EdgeFacts (D : AtomicDesign BitPair) : Prop :=
    ((∀ i : Fin 2, ∀ e : Fin 4,
      exposureProbability D edgeExposure i (e.val : ℝ) = 1/4) ∧
    (∀ i : Fin 2, exposureMean D edgeExposure ownBit i 1 = 1 ∧
      exposureMean D edgeExposure ownBit i 0 = 0) ∧
    populationContrast D edgeExposure ownBit 1 0 = 1 ∧
    globalStability edgeExposure ownBit ∧
    (∀ z : BitPair,
      ¬(inEdgeExposureImage (1,edgeExposure 1 z) ∧
        inEdgeExposureImage (0,edgeExposure 1 z)) ∧
      ¬(inEdgeExposureImage (edgeExposure 0 z,1) ∧
        inEdgeExposureImage (edgeExposure 0 z,0))) ∧
    eventProbability D (fun z =>
      inBitDomain (1,edgeExposure 1 z) ∧
      inBitDomain (0,edgeExposure 1 z)) = 1/2 ∧
    eventProbability D (fun z =>
      inBitDomain (edgeExposure 0 z,1) ∧
      inBitDomain (edgeExposure 0 z,0)) = 1/2) ∧
    (∀ r, inEdgeExposureImage r ↔ r = (0,0) ∨ r = (2,1) ∨ r = (1,2) ∨ r = (3,3)) ∧
    edgeExposureVector (0,0) = (0,0) ∧ edgeExposureVector (0,1) = (2,1) ∧
    edgeExposureVector (1,0) = (1,2) ∧ edgeExposureVector (1,1) = (3,3) ∧
    positiveExposure D edgeExposure 1 ∧ positiveExposure D edgeExposure 0 ∧
    supportStability D edgeExposure ownBit ∧
    (∀ z : BitPair,
      (inBitDomain (1,edgeExposure 1 z) ↔ z.1=0) ∧
      (inBitDomain (0,edgeExposure 1 z) ↔ z.1=0) ∧
      (inBitDomain (edgeExposure 0 z,1) ↔ z.2=0) ∧
      (inBitDomain (edgeExposure 0 z,0) ↔ z.2=0))

def PairedEdgeFacts (K : ℕ) (D : AtomicDesign (Fin K → BitPair)) : Prop :=
    (∀ i : Fin (K*2), ∀ e : Fin 4, exposureProbability D (pairedEdgeExposure K) i e.val = 1/4) ∧
    (∀ i : Fin (K*2), exposureMean D (pairedEdgeExposure K) (pairedOwnBit K) i 1 = 1 ∧
      exposureMean D (pairedEdgeExposure K) (pairedOwnBit K) i 0 = 0) ∧
    populationContrast D (pairedEdgeExposure K) (pairedOwnBit K) 1 0 = 1 ∧
    globalStability (pairedEdgeExposure K) (pairedOwnBit K) ∧
    (∀ i z, ¬(inPairedExposureImage K (Function.update (fun j => pairedEdgeExposure K j z) i 1) ∧
      inPairedExposureImage K (Function.update (fun j => pairedEdgeExposure K j z) i 0))) ∧
    (∀ i, eventProbability D (fun z =>
      inPairedBitDomain K (Function.update (fun j => pairedEdgeExposure K j z) i 1) ∧
      inPairedBitDomain K (Function.update (fun j => pairedEdgeExposure K j z) i 0)) =
        (1/2 : ℝ) * (1/4 : ℝ)^(K-1))

/-- Both raw and exposure-domain failures, including independent copies of the pair. -/
def T2Statement : Prop :=
  (∃ D : AtomicDesign BitPair,
    (∀ z, D.mass z = (Fintype.card BitPair : ℝ)⁻¹) ∧ EdgeFacts D) ∧
  (∀ K, 0 < K → ∃ D : AtomicDesign (Fin K → BitPair),
    (∀ z, D.mass z = ∏ _i : Fin K, (Fintype.card BitPair : ℝ)⁻¹) ∧ PairedEdgeFacts K D)


end SAP.P061a
