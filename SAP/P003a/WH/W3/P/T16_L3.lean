import SAP.P003a.WH.W3.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P003a.WH.W3.P.T16_L3

open scoped BigOperators
open SAP.P003a
attribute [local instance 0] Classical.propDecidable

private theorem partner_card (n : ℕ) (i : Fin n) :
    Fintype.card (WholePartner n i) = n - 1 := by
  change Fintype.card {j : Fin n // j ≠ i} = n - 1
  rw [Fintype.card_subtype_compl (p := fun j : Fin n => j = i)]
  simp

private def fiberEquiv {n m : ℕ} (i : Fin n)
    (legal : ∀ ω : WholePairSource n m i, (wholePairSample ω).card = m) :
    WholePairSource n m i ≃
      Σ z : Assignment n m, {ω : WholePairSource n m i // wholePairSample ω = z.val} := by
  exact (Equiv.sigmaSubtypeFiberEquiv wholePairSample
    (fun s : Finset (Fin n) => s.card = m) legal).symm

private def eventFiberEquiv {n m : ℕ} (i : Fin n)
    (legal : ∀ ω : WholePairSource n m i, (wholePairSample ω).card = m)
    (E : Finset (Fin n) → Prop) :
    {ω : WholePairSource n m i // E (wholePairSample ω)} ≃
      Σ z : {z : Assignment n m // E z.val},
        {ω : WholePairSource n m i // (⟨wholePairSample ω, legal ω⟩ : Assignment n m) = z.val} := by
  exact (Equiv.sigmaSubtypeFiberEquivSubtype
    (fun ω : WholePairSource n m i => (⟨wholePairSample ω, legal ω⟩ : Assignment n m))
    (p := fun ω : WholePairSource n m i => E (wholePairSample ω))
    (q := fun z : Assignment n m => E z.val) (fun _ => Iff.rfl)).symm

private def typedFiberEquiv {n m : ℕ} (i : Fin n)
    (legal : ∀ ω : WholePairSource n m i, (wholePairSample ω).card = m)
    (z : Assignment n m) :
    {ω : WholePairSource n m i // (⟨wholePairSample ω, legal ω⟩ : Assignment n m) = z} ≃
      {ω : WholePairSource n m i // wholePairSample ω = z.val} where
  toFun ω := ⟨ω.val, congrArg Subtype.val ω.property⟩
  invFun ω := ⟨ω.val, Subtype.ext ω.property⟩
  left_inv := by intro ω; apply Subtype.ext; rfl
  right_inv := by intro ω; apply Subtype.ext; rfl

private noncomputable def rectangleEquiv {n m : ℕ} {i : Fin n}
    (j : WholePartner n i) (E : Bool → Prop)
    (F : WholeResidualAssignment n m i j.val → Prop) :
    ({b : Bool // E b} × {r : WholeResidualAssignment n m i j.val // F r}) ≃
      {ω : WholePairSource n m i // wholePairRectangle j E F ω} :=
  Equiv.ofBijective
    (fun x => ⟨⟨j, (x.1.val, x.2.val)⟩,
      ⟨x.1.val, x.2.val, x.1.property, x.2.property, rfl⟩⟩)
    ⟨by
      intro x y hxy
      have hs := congrArg Subtype.val hxy
      have hpair : (x.1.val, x.2.val) = (y.1.val, y.2.val) := by
        exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
      apply Prod.ext
      · apply Subtype.ext
        exact congrArg Prod.fst hpair
      · apply Subtype.ext
        exact congrArg Prod.snd hpair
    , by
      intro ω
      rcases ω.property with ⟨b, r, hb, hr, heq⟩
      refine ⟨(⟨⟨b, hb⟩, ⟨r, hr⟩⟩ :
        ({b : Bool // E b} × {r : WholeResidualAssignment n m i j.val // F r})), ?_⟩
      apply Subtype.ext
      exact heq.symm⟩

private theorem source_card {n m : ℕ} (i : Fin n)
    (hres : ∀ j : WholePartner n i,
      Fintype.card (WholeResidualAssignment n m i j.val) = (n-2).choose (m-1)) :
    Fintype.card (WholePairSource n m i) =
      (n-1) * 2 * ((n-2).choose (m-1)) := by
  rw [Fintype.card_sigma]
  calc
    (∑ j : WholePartner n i,
        Fintype.card (Bool × WholeResidualAssignment n m i j.val)) =
        ∑ _j : WholePartner n i, 2 * ((n-2).choose (m-1)) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [Fintype.card_prod, hres j]
    _ = Fintype.card (WholePartner n i) * (2 * ((n-2).choose (m-1))) := by simp
    _ = (n-1) * 2 * ((n-2).choose (m-1)) := by rw [partner_card]; ring

private theorem source_card_eq_targets {n m : ℕ} (i : Fin n)
    (legal : ∀ ω : WholePairSource n m i, (wholePairSample ω).card = m)
    (fiber : ∀ z : Assignment n m,
      Fintype.card {ω : WholePairSource n m i // wholePairSample ω = z.val} = m) :
    Fintype.card (WholePairSource n m i) = m * Fintype.card (Assignment n m) := by
  calc
    Fintype.card (WholePairSource n m i) =
        Fintype.card (Σ z : Assignment n m,
          {ω : WholePairSource n m i // wholePairSample ω = z.val}) :=
            Fintype.card_congr (fiberEquiv i legal)
    _ = ∑ z : Assignment n m,
          Fintype.card {ω : WholePairSource n m i // wholePairSample ω = z.val} :=
              Fintype.card_sigma
    _ = ∑ z : Assignment n m, m := by
          apply Finset.sum_congr rfl
          intro z hz
          exact fiber z
    _ = Fintype.card (Assignment n m) * m := by simp
    _ = m * Fintype.card (Assignment n m) := Nat.mul_comm _ _

private theorem event_card_eq_targets {n m : ℕ} (i : Fin n)
    (legal : ∀ ω : WholePairSource n m i, (wholePairSample ω).card = m)
    (fiber : ∀ z : Assignment n m,
      Fintype.card {ω : WholePairSource n m i // wholePairSample ω = z.val} = m)
    (E : Finset (Fin n) → Prop) :
    Fintype.card {ω : WholePairSource n m i // E (wholePairSample ω)} =
      m * Fintype.card {z : Assignment n m // E z.val} := by
  calc
    Fintype.card {ω : WholePairSource n m i // E (wholePairSample ω)} =
        Fintype.card (Σ z : {z : Assignment n m // E z.val},
          {ω : WholePairSource n m i //
            (⟨wholePairSample ω, legal ω⟩ : Assignment n m) = z.val}) :=
            Fintype.card_congr (eventFiberEquiv i legal E)
    _ = ∑ z : {z : Assignment n m // E z.val},
          Fintype.card {ω : WholePairSource n m i //
            (⟨wholePairSample ω, legal ω⟩ : Assignment n m) = z.val} := Fintype.card_sigma
    _ = ∑ z : {z : Assignment n m // E z.val}, m := by
          apply Finset.sum_congr rfl
          intro z hz
          calc
            Fintype.card {ω : WholePairSource n m i //
                (⟨wholePairSample ω, legal ω⟩ : Assignment n m) = z.val} =
              Fintype.card {ω : WholePairSource n m i // wholePairSample ω = z.val} :=
                Fintype.card_congr (typedFiberEquiv i legal z.val)
            _ = m := fiber z.val
    _ = Fintype.card {z : Assignment n m // E z.val} * m := by simp
    _ = m * Fintype.card {z : Assignment n m // E z.val} := Nat.mul_comm _ _
end SAP.P003a.WH.W3.P.T16_L3

open SAP.P003a.WH.W3.P.T16_L3

theorem SAP.P003a.WH.W3.T16_L3_proof : SAP.P003a.WH.W3.T16_L3 := by
  classical
  intro n m hm hn i hres legal fiber
  have hChoose : 0 < (n-2).choose (m-1) := by
    apply Nat.choose_pos
    omega
  have hPartner : 0 < n-1 := by omega
  have hCardSource := source_card i hres
  have hCardTargets := source_card_eq_targets i legal fiber
  have hCardTargetPos : 0 < Fintype.card (Assignment n m) := by
    rw [Fintype.card_finset_len]
    simpa using Nat.choose_pos (show m ≤ n by omega)
  have hCardSourcePos : 0 < Fintype.card (WholePairSource n m i) := by
    rw [hCardSource]
    exact Nat.mul_pos (Nat.mul_pos hPartner (by decide)) hChoose
  have hNReal : ((n-1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hPartner)
  have hMReal : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hChooseReal : ((n-2).choose (m-1) : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.ne_of_gt hChoose)
  have hTargetReal : (Fintype.card (Assignment n m) : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.ne_of_gt hCardTargetPos)
  have hSourceReal : (Fintype.card (WholePairSource n m i) : ℝ) ≠ 0 :=
    by exact_mod_cast (Nat.ne_of_gt hCardSourcePos)
  constructor
  · intro E
    have hCount := event_card_eq_targets i legal fiber E
    have hCountR :
        (Fintype.card {ω : WholePairSource n m i // E (wholePairSample ω)} : ℝ) =
          (m : ℝ) * Fintype.card {z : Assignment n m // E z.val} := by
      exact_mod_cast hCount
    have hTotalR :
        (Fintype.card (WholePairSource n m i) : ℝ) =
          (m : ℝ) * Fintype.card (Assignment n m) := by
      exact_mod_cast hCardTargets
    have hProbSource :
        uniformProb (fun ω : WholePairSource n m i => E (wholePairSample ω)) =
          (Fintype.card {ω : WholePairSource n m i // E (wholePairSample ω)} : ℝ) /
            Fintype.card (WholePairSource n m i) := by
      simp [uniformProb, Fintype.card_subtype]
    have hProbTarget :
        uniformProb (fun z : Assignment n m => E z.val) =
          (Fintype.card {z : Assignment n m // E z.val} : ℝ) /
            Fintype.card (Assignment n m) := by
      simp [uniformProb, Fintype.card_subtype]
    rw [hProbSource, hProbTarget, hCountR, hTotalR]
    field_simp [hMReal, hTargetReal]
    <;> ring
  · intro j E F
    have hRect := rectangleEquiv j E F
    have hRectCard :
        Fintype.card {ω : WholePairSource n m i // wholePairRectangle j E F ω} =
          Fintype.card {b : Bool // E b} *
            Fintype.card {r : WholeResidualAssignment n m i j.val // F r} := by
      calc
        _ = Fintype.card
          ({b : Bool // E b} ×
            {r : WholeResidualAssignment n m i j.val // F r}) :=
              Fintype.card_congr hRect.symm
        _ = _ := by simp only [Fintype.card_prod]
    have hRectCardR :
        (Fintype.card {ω : WholePairSource n m i // wholePairRectangle j E F ω} : ℝ) =
          Fintype.card {b : Bool // E b} *
            Fintype.card {r : WholeResidualAssignment n m i j.val // F r} := by
      exact_mod_cast hRectCard
    have hSourceCardR :
        (Fintype.card (WholePairSource n m i) : ℝ) =
          ((n-1 : ℕ) : ℝ) * 2 * ((n-2).choose (m-1) : ℝ) := by
      exact_mod_cast hCardSource
    have hProbRect :
        uniformProb (wholePairRectangle j E F) =
          (Fintype.card {ω : WholePairSource n m i // wholePairRectangle j E F ω} : ℝ) /
            Fintype.card (WholePairSource n m i) := by
      simp [uniformProb, Fintype.card_subtype]
    have hProbE : uniformProb E = (Fintype.card {b : Bool // E b} : ℝ) / 2 := by
      simp [uniformProb, Fintype.card_subtype]
    have hProbF : uniformProb F =
        (Fintype.card {r : WholeResidualAssignment n m i j.val // F r} : ℝ) /
          ((n-2).choose (m-1) : ℝ) := by
      unfold uniformProb
      rw [← Fintype.card_subtype, hres j]
    rw [hProbRect, hRectCardR, hSourceCardR, hProbE, hProbF]
    field_simp [hNReal, hChooseReal]
    <;> ring
