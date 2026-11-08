import SAP.P044.Bridge.Part1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P044.Bridge

open Finset MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

@[simp] theorem marginal_lift {Ω K : Type*} {N : ℕ} [Fintype Ω] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → SAP.P044.Exposure) (i : Fin N)
    (a : AronowAudit.P044.Exposure) :
    SAP.P044.marginal p (fun ω i => labels (f ω i)) i a =
      SAP.P044.marginal p f i (labels.symm a) := by
  simp only [SAP.P044.marginal, labels_eq]

@[simp] theorem joint_lift {Ω K : Type*} {N : ℕ} [Fintype Ω] [CommSemiring K]
    (p : Ω → K) (f : Ω → Fin N → SAP.P044.Exposure) (i j : Fin N)
    (a b : AronowAudit.P044.Exposure) :
    SAP.P044.joint p (fun ω i => labels (f ω i)) i j a b =
      SAP.P044.joint p f i j (labels.symm a) (labels.symm b) := by
  simp only [SAP.P044.joint, labels_eq]

@[simp] theorem term_lift {Ω K : Type*} {N : ℕ} [Field K]
    (f : Ω → Fin N → SAP.P044.Exposure) (y w : Fin N → SAP.P044.Exposure → K)
    (a : AronowAudit.P044.Exposure) (ω : Ω) (i : Fin N) :
    SAP.P044.htTerm (fun ω i => labels (f ω i))
      (fun i a => y i (labels.symm a)) (fun i a => w i (labels.symm a)) a ω i =
      SAP.P044.htTerm f y w (labels.symm a) ω i := by
  simp only [SAP.P044.htTerm, labels_eq]

@[simp] theorem mean_lift {Ω K : Type*} {N : ℕ} [Field K]
    (f : Ω → Fin N → SAP.P044.Exposure) (y w : Fin N → SAP.P044.Exposure → K)
    (a : AronowAudit.P044.Exposure) :
    SAP.P044.htMean (fun ω i => labels (f ω i))
      (fun i a => y i (labels.symm a)) (fun i a => w i (labels.symm a)) a =
      SAP.P044.htMean f y w (labels.symm a) := by
  funext ω
  simp only [SAP.P044.htMean, term_lift]

@[simp] theorem contrast_lift {Ω K : Type*} {N : ℕ} [Field K]
    (f : Ω → Fin N → SAP.P044.Exposure) (y w : Fin N → SAP.P044.Exposure → K)
    (a b : AronowAudit.P044.Exposure) :
    SAP.P044.htContrast (fun ω i => labels (f ω i))
      (fun i a => y i (labels.symm a)) (fun i a => w i (labels.symm a)) a b =
      SAP.P044.htContrast f y w (labels.symm a) (labels.symm b) := by
  funext ω
  simp only [SAP.P044.htContrast, mean_lift]

@[simp] theorem tau_lift {K : Type*} {N : ℕ} [Field K]
    (y : Fin N → SAP.P044.Exposure → K) (a b : AronowAudit.P044.Exposure) :
    SAP.P044.tau (fun i a => y i (labels.symm a)) a b =
      SAP.P044.tau y (labels.symm a) (labels.symm b) := rfl

@[simp] theorem variance_lift {Ω K : Type*} {N : ℕ}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (f : Ω → Fin N → SAP.P044.Exposure) (y w : Fin N → SAP.P044.Exposure → K)
    (q : Fin N → Fin N → SAP.P044.Exposure → SAP.P044.Exposure → K)
    (a b : AronowAudit.P044.Exposure) :
    SAP.P044.varianceEstimate (fun ω i => labels (f ω i))
      (fun i a => y i (labels.symm a)) (fun i a => w i (labels.symm a))
      (fun i j a b => q i j (labels.symm a) (labels.symm b)) a b =
      SAP.P044.varianceEstimate f y w q (labels.symm a) (labels.symm b) := by
  funext ω
  simp only [SAP.P044.varianceEstimate, SAP.P044.totalVarianceEstimate,
    SAP.P044.totalCovarianceEstimate, labels_eq]

@[simp] theorem count_lift {R N : ℕ} (f : Fin R → Fin N → SAP.P044.Exposure)
    (i : Fin N) (a : AronowAudit.P044.Exposure) :
    SAP.P044.exposureCount (fun r i => labels (f r i)) i a =
      SAP.P044.exposureCount f i (labels.symm a) := by
  simp only [SAP.P044.exposureCount, labels_eq]

@[simp] theorem jointCount_lift {R N : ℕ} (f : Fin R → Fin N → SAP.P044.Exposure)
    (i j : Fin N) (a b : AronowAudit.P044.Exposure) :
    SAP.P044.jointCount (fun r i => labels (f r i)) i j a b =
      SAP.P044.jointCount f i j (labels.symm a) (labels.symm b) := by
  simp only [SAP.P044.jointCount, labels_eq]

@[simp] theorem weight_lift {K : Type*} [Field K] {R N : ℕ}
    (f : Fin R → Fin N → SAP.P044.Exposure) (i : Fin N) (a : AronowAudit.P044.Exposure) :
    (SAP.P044.smoothedWeight (fun r i => labels (f r i)) i a : K) =
      SAP.P044.smoothedWeight f i (labels.symm a) := by
  simp only [SAP.P044.smoothedWeight, count_lift]

@[simp] theorem joints_lift {K : Type*} [Field K] {R N : ℕ}
    (f : Fin R → Fin N → SAP.P044.Exposure) (i j : Fin N) (a b : AronowAudit.P044.Exposure) :
    (SAP.P044.smoothedJoint (fun r i => labels (f r i)) i j a b : K) =
      SAP.P044.smoothedJoint f i j (labels.symm a) (labels.symm b) := by
  have he : a = b ↔ labels.symm a = labels.symm b := labels.symm.injective.eq_iff.symm
  simp only [SAP.P044.smoothedJoint, jointCount_lift, he]

@[simp] theorem exposure_eq {N : ℕ} (A : SAP.P044.Adjacency N) (z : SAP.P044.Assignment N) :
    AronowAudit.P044.exposure A z = fun i => labels (SAP.P044.exposure A z i) := by
  funext i
  cases h : z i <;> by_cases hp : 0 < SAP.P044.peerCount A z i <;>
    simp [AronowAudit.P044.exposure, SAP.P044.exposure, h, hp]

@[simp] theorem completeProbability_eq (N M : ℕ) (A : SAP.P044.Adjacency N)
    (i : Fin N) (a : AronowAudit.P044.Exposure) :
    AronowAudit.P044.completeProbability N M A i a =
      SAP.P044.completeProbability N M A i (labels.symm a) := by
  simp only [AronowAudit.P044.completeProbability, SAP.P044.completeProbability,
    completeProfiles_eq, exposure_eq, labels_eq]

@[simp] theorem starA_eq : AronowAudit.P044.starA =
    fun i a => SAP.P044.starA i (labels.symm a) := rfl

@[simp] theorem starB_eq : AronowAudit.P044.starB =
    fun i a => SAP.P044.starB i (labels.symm a) := by
  funext i a; cases a <;> simp [AronowAudit.P044.starB, SAP.P044.starB]

@[simp] theorem cycle8Y_eq : AronowAudit.P044.cycle8Y =
    fun i a => SAP.P044.cycle8Y i (labels.symm a) := by
  funext i a; cases a <;> rfl

@[simp] theorem dilatedOutcomes_eq {N : ℕ} (B : Fin N → ℝ) :
    AronowAudit.P044.dilatedOutcomes B = fun i a => SAP.P044.dilatedOutcomes B i (labels.symm a) := by
  funext i a; cases a <;> rfl

end
end SAP.P044.Bridge
