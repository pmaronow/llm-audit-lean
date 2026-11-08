import SAP.P009b.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators
open AronowAudit.P009.Wave1

attribute [local instance] Classical.propDecidable

theorem SAP.P009b.WH.W1.T18_L1_proof : SAP.P009b.WH.W1.T18_L1 := by
  change SAP.P009b.wholeVectorCountRatio
  intro n E m hCR i hc w b hw
  let E' : AronowAudit.P009.Experiment n := SAP.P009b.Bridge.toExperiment E
  have hCR' : AronowAudit.P009.Complete E' m := by
    change AronowAudit.P009.Complete (SAP.P009b.Bridge.toExperiment E) m
    exact hCR
  let H : Finset (Fin n) := t18_others E' i
  have hcard : H.card = AronowAudit.P009.incoming E' i - 1 := by
    exact t18_others_card E' i
  have hcm : AronowAudit.P009.incoming E' i ≤ m := by
    exact hc.trans (Nat.min_le_left m (n-m))
  have hcc : AronowAudit.P009.incoming E' i ≤ n-m := by
    exact hc.trans (Nat.min_le_right m (n-m))
  have hHm : H.card < m := by
    have hm := hCR'.1
    rw [hcard]
    omega
  have hHc : H.card < n-m := by
    have hmn : m < n := hCR'.2.1
    rw [hcard]
    omega
  have hHn : H.card < n := by
    have hm := hCR'.1
    have hmn : m < n := hCR'.2.1
    rw [hcard]
    omega
  have hi : i ∉ H := by
    exact t18_own_not_mem E' i
  have hmask (z : SAP.P009b.Assignment n) :
      SAP.P009b.maskedOthers E i z = AronowAudit.P009.maskedOthers E' i z := by
    rfl
  have htreated (z : SAP.P009b.Assignment n) :
      SAP.P009b.treatedIncoming E i z = AronowAudit.P009.treatedIncoming E' i z := by
    rfl
  let Avec : AronowAudit.P009.Assignment n → Prop :=
    fun z => AronowAudit.P009.maskedOthers E' i z = w
  letI : DecidablePred Avec := Classical.decPred Avec
  let Acount : AronowAudit.P009.Assignment n → Prop :=
    fun z => AronowAudit.P009.treatedIncoming E' i z =
      AronowAudit.P009.treatedIncoming E' i w
  letI : DecidablePred Acount := Classical.decPred Acount
  have hprob_bridge (A : SAP.P009b.Assignment n → Prop) :
      SAP.P009b.prob E.design A = AronowAudit.P009.prob E'.design A := by
    rfl
  have hcmean_bridge (A : SAP.P009b.Assignment n → Prop)
      (X : SAP.P009b.Assignment n → ℝ) :
      SAP.P009b.cmean E.design A X = AronowAudit.P009.cmean E'.design A X := by
    rfl
  have hvec_event :
      (fun z : SAP.P009b.Assignment n => SAP.P009b.maskedOthers E i z = w) =
        (fun z : SAP.P009b.Assignment n => AronowAudit.P009.maskedOthers E' i z = w) := by
    funext z
    rw [hmask z]
  have hcount_event :
      (fun z : SAP.P009b.Assignment n => SAP.P009b.treatedIncoming E i z =
        SAP.P009b.treatedIncoming E i w) =
        (fun z : SAP.P009b.Assignment n => AronowAudit.P009.treatedIncoming E' i z =
          AronowAudit.P009.treatedIncoming E' i w) := by
    funext z
    rw [htreated z, htreated w]
  have hprob_vector :
      SAP.P009b.prob E.design (fun z => SAP.P009b.maskedOthers E i z = w) =
        AronowAudit.P009.prob E'.design Avec := by
    rw [hprob_bridge]
    congr 1
  have hprob_treated :
      SAP.P009b.prob E.design (fun z => SAP.P009b.treatedIncoming E i z =
        SAP.P009b.treatedIncoming E i w) =
        AronowAudit.P009.prob E'.design Acount := by
    rw [hprob_bridge]
    congr 1
  have hX_vector :
      (fun z : SAP.P009b.Assignment n =>
        if SAP.P009b.maskedOthers E i z = w then (1:ℝ) else 0) =
      (fun z : SAP.P009b.Assignment n =>
        if Avec z then (1:ℝ) else 0) := by
    funext z
    by_cases hz : SAP.P009b.maskedOthers E i z = w
    · have hz' : Avec z := by simpa [Avec, hmask z] using hz
      simp [hz, hz']
    · have hz' : ¬ Avec z := by simpa [Avec, hmask z] using hz
      simp [hz, hz']
  have hX_treated :
      (fun z : SAP.P009b.Assignment n =>
        if SAP.P009b.treatedIncoming E i z = SAP.P009b.treatedIncoming E i w
          then (1:ℝ) else 0) =
      (fun z : SAP.P009b.Assignment n =>
        if Acount z then (1:ℝ) else 0) := by
    funext z
    by_cases hz : SAP.P009b.treatedIncoming E i z = SAP.P009b.treatedIncoming E i w
    · have hz' : Acount z := by simpa [Acount, htreated z, htreated w] using hz
      simp [hz, hz']
    · have hz' : ¬ Acount z := by simpa [Acount, htreated z, htreated w] using hz
      simp [hz, hz']
  have hcmean_vector :
      SAP.P009b.cmean E.design (fun z => z i = b)
          (fun z => if SAP.P009b.maskedOthers E i z = w then 1 else 0) =
        AronowAudit.P009.cmean E'.design (fun z => z i = b)
          (fun z => if Avec z then 1 else 0) := by
    calc
      _ = AronowAudit.P009.cmean E'.design (fun z => z i = b)
          (fun z => if SAP.P009b.maskedOthers E i z = w then 1 else 0) :=
        hcmean_bridge _ _
      _ = _ := by rw [hX_vector]
  have hcmean_treated :
      SAP.P009b.cmean E.design (fun z => z i = b)
          (fun z => if SAP.P009b.treatedIncoming E i z = SAP.P009b.treatedIncoming E i w
            then 1 else 0) =
        AronowAudit.P009.cmean E'.design (fun z => z i = b)
          (fun z => if Acount z then 1 else 0) := by
    calc
      _ = AronowAudit.P009.cmean E'.design (fun z => z i = b)
          (fun z => if SAP.P009b.treatedIncoming E i z = SAP.P009b.treatedIncoming E i w
            then 1 else 0) := hcmean_bridge _ _
      _ = _ := by rw [hX_treated]
  let t : ℕ := t18_countOn (fun j => j ∈ H) w
  have ht : t ≤ H.card := by
    exact t18_countOn_le H w
  have hprob_count :
      AronowAudit.P009.prob E'.design
        (fun z => t18_countOn (fun j => j ∈ H) z = t) =
        AronowAudit.P009.hypergeomMass n m H.card t := by
    exact t18_complete_finset_count E' m hCR' H t ht hHm.le hHc.le
  have hpos_count :
      0 < AronowAudit.P009.prob E'.design
        (fun z => t18_countOn (fun j => j ∈ H) z = t) := by
    rw [hprob_count]
    exact t18_hypergeom_pos n m H.card t hCR'.2.1.le hHm.le hHc.le ht
  have hpos_treated :
      0 < AronowAudit.P009.prob E'.design Acount := by
    simpa [Acount, t, t18_countIncoming] using hpos_count
  have hpos_vector :
      0 < AronowAudit.P009.prob E'.design Avec := by
    rw [← hprob_vector]
    exact hw
  have hA_vector :
      DependsOn
        (fun z => if Avec z then (1:ℝ) else 0)
        (H : Set (Fin n)) := by
    dsimp only [Avec]
    intro z z' hz
    have he := t18_masked_congr E' i z z' hz
    simp only [he]
  have hfixed_vector : ∀ z,
      AronowAudit.P009.maskedOthers E' i z = w →
        t18_countOn (fun j => j ∈ H) z = t := by
    intro z hz
    calc
      t18_countOn (fun j => j ∈ H) z =
          t18_countOn (fun j => j ∈ H) (AronowAudit.P009.maskedOthers E' i z) :=
        (t18_masked_count E' i z).symm
      _ = t := by rw [hz]
  have hA_count :
      DependsOn
        (fun z => if Acount z then (1:ℝ) else 0)
        (H : Set (Fin n)) := by
    dsimp only [Acount]
    intro z z' hz
    have hcount := t18_countOn_congr H z z' hz
    have heq : AronowAudit.P009.treatedIncoming E' i z =
        AronowAudit.P009.treatedIncoming E' i z' := by
      simpa only [t18_countIncoming] using hcount
    simp [heq]
  have hfixed_count : ∀ z,
      AronowAudit.P009.treatedIncoming E' i z =
        AronowAudit.P009.treatedIncoming E' i w →
        t18_countOn (fun j => j ∈ H) z = t := by
    intro z hz
    have hz' : t18_countOn (fun j => j ∈ H) z =
        t18_countOn (fun j => j ∈ H) w := by
      simpa only [t18_countIncoming] using hz
    simpa [t] using hz'
  have hdev_vector := t18_event_deviation E' m hCR' H i hi hHn
    Avec t
    hA_vector hfixed_vector hpos_vector b
  have hdev_count := t18_event_deviation E' m hCR' H i hi hHn
    Acount t
    hA_count hfixed_count hpos_treated b
  have hratio :
      AronowAudit.P009.cmean E'.design (fun z => z i = b)
          (fun z => if Avec z then 1 else 0) /
        AronowAudit.P009.prob E'.design Avec =
      AronowAudit.P009.cmean E'.design (fun z => z i = b)
          (fun z => if Acount z then 1 else 0) /
        AronowAudit.P009.prob E'.design Acount := by
    have hdev_vector' := hdev_vector
    have hdev_count' := hdev_count
    linarith [hdev_vector, hdev_count]
  constructor
  · rw [hprob_treated]
    exact hpos_treated
  · have hratio_vector_bridge :
        (SAP.P009b.cmean E.design (fun z => z i = b)
          (fun z => if SAP.P009b.maskedOthers E i z = w then 1 else 0)) /
          SAP.P009b.prob E.design (fun z => SAP.P009b.maskedOthers E i z = w) =
        (AronowAudit.P009.cmean E'.design (fun z => z i = b)
          (fun z => if Avec z then 1 else 0)) /
          AronowAudit.P009.prob E'.design Avec := by
      exact congrArg₂ (fun x y : ℝ => x / y) hcmean_vector hprob_vector
    have hratio_treated_bridge :
        (AronowAudit.P009.cmean E'.design (fun z => z i = b)
          (fun z => if Acount z then 1 else 0)) /
          AronowAudit.P009.prob E'.design Acount =
        (SAP.P009b.cmean E.design (fun z => z i = b)
          (fun z => if SAP.P009b.treatedIncoming E i z =
            SAP.P009b.treatedIncoming E i w then 1 else 0)) /
          SAP.P009b.prob E.design
            (fun z => SAP.P009b.treatedIncoming E i z = SAP.P009b.treatedIncoming E i w) := by
      exact congrArg₂ (fun x y : ℝ => x / y) hcmean_treated.symm hprob_treated.symm
    exact hratio_vector_bridge.trans (hratio.trans hratio_treated_bridge)

