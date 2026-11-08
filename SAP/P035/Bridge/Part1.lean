import SAP.P035.Defs
import AronowAudit.P035.P035_Nonidentification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P035.Bridge

def toYear : Year → AronowAudit.P035.Year
  | .y2012 => .y2012 | .y2014 => .y2014 | .y2015 => .y2015

def fromYear : AronowAudit.P035.Year → Year
  | .y2012 => .y2012 | .y2014 => .y2014 | .y2015 => .y2015

@[simp] theorem to_from (y : AronowAudit.P035.Year) : toYear (fromYear y) = y := by
  cases y <;> rfl

@[simp] theorem from_to (y : Year) : fromYear (toYear y) = y := by
  cases y <;> rfl

def liftOutcome (Y : AronowAudit.P035.PotentialOutcome) : PotentialOutcome :=
  fun y => Y (toYear y)

def lowerOutcome (Y : PotentialOutcome) : AronowAudit.P035.PotentialOutcome :=
  fun y => Y (fromYear y)

@[simp] theorem lower_lift (Y : AronowAudit.P035.PotentialOutcome) :
    lowerOutcome (liftOutcome Y) = Y := by
  funext y
  simp only [lowerOutcome, liftOutcome, to_from]

@[simp] theorem lift_lower (Y : PotentialOutcome) :
    liftOutcome (lowerOutcome Y) = Y := by
  funext y
  simp only [lowerOutcome, liftOutcome, from_to]

def liftLaw (l : AronowAudit.P035.Year → Bool → Bool → ℚ) : Year → Bool → Bool → ℚ :=
  fun y => l (toYear y)

def lowerLaw (l : Year → Bool → Bool → ℚ) : AronowAudit.P035.Year → Bool → Bool → ℚ :=
  fun y => l (fromYear y)

theorem forall_toYear (p : AronowAudit.P035.Year → Prop) :
    (∀ y : Year, p (toYear y)) ↔ ∀ y, p y := by
  constructor
  · intro h y
    simpa only [to_from] using h (fromYear y)
  · intro h y
    exact h (toYear y)

theorem sum_years {M : Type*} [AddCommMonoid M] (f : Year → M) :
    (∑ y ∈ years, f y) = ∑ y ∈ AronowAudit.P035.years, f (fromYear y) := by
  simp [years, AronowAudit.P035.years, fromYear]

@[simp] theorem latentSize_eq (y : Year) :
    latentSize y = AronowAudit.P035.latentSize (toYear y) := by cases y <;> rfl

@[simp] theorem threshold_eq (y : Year) (z : Bool) :
    threshold y z = AronowAudit.P035.threshold (toYear y) z := by
  cases y <;> cases z <;> rfl

@[simp] theorem releasedFrequency_eq (y : Year) (z : Bool) :
    releasedFrequency y z = AronowAudit.P035.releasedFrequency (toYear y) z := by
  cases y <;> cases z <;> rfl

@[simp] theorem reducedDenominator_eq (y : Year) (z : Bool) :
    reducedDenominator y z = AronowAudit.P035.reducedDenominator (toYear y) z := by
  cases y <;> cases z <;> rfl

@[simp] theorem latentPopulation_eq (y : Year) :
    latentPopulation y = AronowAudit.P035.latentPopulation (toYear y) := by
  cases y <;> rfl

@[simp] theorem exactEffect_eq (y : Year) :
    exactEffect y = AronowAudit.P035.exactEffect (toYear y) := by cases y <;> rfl

@[simp] theorem D_eq (y : Year) (z a : Bool) (r : ℕ) :
    D y z a r = AronowAudit.P035.D (toYear y) z a r := by cases y <;> rfl

@[simp] theorem C_eq (y : Year) (z a : Bool) (r : ℕ) :
    C y z a r = AronowAudit.P035.C (toYear y) z a r := by cases y <;> rfl

@[simp] theorem lower_D : lowerOutcome D = AronowAudit.P035.D := by
  funext y
  cases y <;> rfl

@[simp] theorem lower_C : lowerOutcome C = AronowAudit.P035.C := by
  funext y
  cases y <;> rfl

@[simp] theorem outcomeMean_eq (Y : PotentialOutcome) (y : Year) (z a : Bool) :
    outcomeMean Y y z a = AronowAudit.P035.outcomeMean (lowerOutcome Y) (toYear y) z a := by
  cases y <;> rfl

@[simp] theorem successCount_eq (Y : PotentialOutcome) (y : Year) (z : Bool) :
    successCount Y y z = AronowAudit.P035.successCount (lowerOutcome Y) (toYear y) z := by
  cases y <;> rfl

@[simp] theorem campaignDifference_eq (Y : PotentialOutcome) (y : Year) (z : Bool) (r : ℕ) :
    campaignDifference Y y z r =
      AronowAudit.P035.campaignDifference (lowerOutcome Y) (toYear y) z r := by
  cases y <;> rfl

@[simp] theorem campaignMean_eq (Y : PotentialOutcome) (y : Year) (z : Bool) :
    campaignMean Y y z = AronowAudit.P035.campaignMean (lowerOutcome Y) (toYear y) z := by
  cases y <;> rfl

@[simp] theorem yearMass_eq (y : Year) :
    yearMass y = AronowAudit.P035.yearMass (toYear y) := by cases y <;> rfl

@[simp] theorem assignmentMass_eq (y : Year) (z : Bool) :
    assignmentMass y z = AronowAudit.P035.assignmentMass (toYear y) z := by
  cases y <;> cases z <;> rfl

@[simp] theorem conditionalMass_eq (y : Year) (z : Bool) (r : ℕ) :
    conditionalMass y z r = AronowAudit.P035.conditionalMass (toYear y) z r := by
  cases y <;> cases z <;> rfl

@[simp] theorem jointMass_eq (y : Year) (z : Bool) (r : ℕ) :
    jointMass y z r = AronowAudit.P035.jointMass (toYear y) z r := by
  cases y <;> cases z <;> rfl

@[simp] theorem observedLaw_eq (Y : PotentialOutcome) (y : Year) (z b : Bool) :
    observedLaw Y y z b = AronowAudit.P035.observedLaw (lowerOutcome Y) (toYear y) z b := by
  cases y <;> cases z <;> rfl

theorem lowerLaw_observed (Y : PotentialOutcome) :
    lowerLaw (observedLaw Y) = AronowAudit.P035.observedLaw (lowerOutcome Y) := by
  funext y z b
  simp only [lowerLaw, observedLaw_eq, to_from]

theorem observedLaw_lift (Y : AronowAudit.P035.PotentialOutcome) :
    observedLaw (liftOutcome Y) = liftLaw (AronowAudit.P035.observedLaw Y) := by
  funext y z b
  simp only [observedLaw_eq, lower_lift, liftLaw]

theorem observedLaw_eq_iff (U V : PotentialOutcome) :
    observedLaw U = observedLaw V ↔
      AronowAudit.P035.observedLaw (lowerOutcome U) =
        AronowAudit.P035.observedLaw (lowerOutcome V) := by
  constructor
  · intro h
    simpa only [lowerLaw_observed] using congrArg lowerLaw h
  · intro h
    funext y z b
    simpa only [observedLaw_eq] using congrFun (congrFun (congrFun h (toYear y)) z) b

theorem calibrated_iff (Y : PotentialOutcome) :
    Calibrated Y ↔ AronowAudit.P035.Calibrated (lowerOutcome Y) := by
  unfold Calibrated AronowAudit.P035.Calibrated
  simp only [outcomeMean_eq, releasedFrequency_eq]
  exact forall_toYear (fun y => ∀ z,
    AronowAudit.P035.outcomeMean (lowerOutcome Y) y z true =
      AronowAudit.P035.releasedFrequency y z)

theorem calibrated_lift (Y : AronowAudit.P035.PotentialOutcome) :
    Calibrated (liftOutcome Y) ↔ AronowAudit.P035.Calibrated Y := by
  rw [calibrated_iff, lower_lift]

@[simp] theorem overallCampaignEffect_eq (Y : PotentialOutcome) :
    overallCampaignEffect Y = AronowAudit.P035.overallCampaignEffect (lowerOutcome Y) := by
  unfold overallCampaignEffect AronowAudit.P035.overallCampaignEffect
  rw [sum_years]
  simp only [yearMass_eq, assignmentMass_eq, campaignMean_eq, to_from]

theorem identified_iff : CampaignIdentified ↔ AronowAudit.P035.CampaignIdentified := by
  constructor
  · intro h U V hU hV hLaw y
    have hCalU := (calibrated_lift U).mpr hU
    have hCalV := (calibrated_lift V).mpr hV
    have hSame : observedLaw (liftOutcome U) = observedLaw (liftOutcome V) := by
      rw [observedLaw_lift, observedLaw_lift, hLaw]
    have hMean := h (liftOutcome U) (liftOutcome V) hCalU hCalV hSame (fromYear y)
    simpa only [campaignMean_eq, lower_lift, to_from] using hMean
  · intro h U V hU hV hLaw y
    have hMean := h (lowerOutcome U) (lowerOutcome V)
      ((calibrated_iff U).mp hU) ((calibrated_iff V).mp hV)
      ((observedLaw_eq_iff U V).mp hLaw) (toYear y)
    simpa only [campaignMean_eq] using hMean

end SAP.P035.Bridge
