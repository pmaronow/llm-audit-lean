import AronowAudit.P011.Wave1.PropositionOneBlueprint
import AronowAudit.P011.P011_PathFiniteCompletion

/-!
Disjoint collections of source signs generate independent random variables.
The uncurried source space makes the product-coordinate argument explicit.
-/

set_option autoImplicit false

namespace AronowAudit.P011.Wave1.PropositionOne

open AronowAudit.P011 MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology

noncomputable section

theorem n1_proof : N1 := by
  classical
  intro K β γ _ _ A B hAB f g hf hg
  let I := Fin K × Fin 2
  let e : (I → Bool) ≃ (Fin K → Fin 2 → Bool) := Equiv.curry (Fin K) (Fin 2) Bool
  let μ : Measure (I → Bool) := (PMF.uniformOfFintype (I → Bool)).toMeasure
  have he : Measurable e := measurable_of_finite _
  have hmap : μ.map e = (PMF.uniformOfFintype (Fin K → Fin 2 → Bool)).toMeasure := by
    dsimp only [μ]
    rw [PMF.toMeasure_map e (PMF.uniformOfFintype (I → Bool)) he,
      PathFiniteCompletion.uniform_equiv e]
  have hcoords : iIndepFun (fun p : I => fun u : I → Bool => u p) μ := by
    dsimp only [μ]
    have hp : (PMF.uniformOfFintype (I → Bool)).toMeasure =
        Measure.pi (fun _ : I => (PMF.uniformOfFintype Bool).toMeasure) := by
      apply Measure.ext_of_singleton
      intro u
      simp [Measure.pi_singleton, PMF.toMeasure_apply_singleton,
        PMF.uniformOfFintype_apply, Fintype.card_fun, ENNReal.inv_pow]
    rw [hp]
    exact iIndepFun_pi
      (μ := fun _ : I => (PMF.uniformOfFintype Bool).toMeasure)
      (X := fun _ : I => (id : Bool → Bool)) (fun _ => aemeasurable_id)
  have hrestrict : IndepFun
      (fun u : I → Bool => fun p : A => u p.val)
      (fun u : I → Bool => fun p : B => u p.val) μ :=
    iIndepFun.indepFun_finset A B hAB hcoords (fun p => measurable_pi_apply p)

  -- Complete a partial sign assignment by false off its indicated coordinates.
  -- The dependence assumptions make the choice of these remaining signs irrelevant.
  let fill (S : Finset I) (a : S → Bool) : I → Bool :=
    fun p => if hp : p ∈ S then a ⟨p, hp⟩ else false
  let F : (A → Bool) → β := fun a => f (e (fill A a))
  let G : (B → Bool) → γ := fun b => g (e (fill B b))
  have hF (u : I → Bool) : F (fun p : A => u p.val) = f (e u) := by
    dsimp only [F]
    apply hf
    intro p hp
    change fill A (fun p : A => u p.val) p = u p
    simp only [fill, dif_pos hp]
  have hG (u : I → Bool) : G (fun p : B => u p.val) = g (e u) := by
    dsimp only [G]
    apply hg
    intro p hp
    change fill B (fun p : B => u p.val) p = u p
    simp only [fill, dif_pos hp]
  have hleft : (F ∘ (fun u : I → Bool => fun p : A => u p.val)) = f ∘ e := by
    funext u
    exact hF u
  have hright : (G ∘ (fun u : I → Bool => fun p : B => u p.val)) = g ∘ e := by
    funext u
    exact hG u
  have hflat : IndepFun (f ∘ e) (g ∘ e) μ := by
    have h := hrestrict.comp (measurable_of_finite F) (measurable_of_finite G)
    rw [hleft, hright] at h
    exact h

  -- Transport the two arbitrary codomains along the currying equivalence.
  rw [← hmap]
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hfs : MeasurableSet (f ⁻¹' s) := hs.preimage (measurable_of_finite f)
  have hgt : MeasurableSet (g ⁻¹' t) := ht.preimage (measurable_of_finite g)
  rw [Measure.map_apply he (hfs.inter hgt), Measure.map_apply he hfs,
    Measure.map_apply he hgt]
  simpa only [Set.preimage_inter, Set.preimage_preimage, Function.comp_def] using
    hflat.measure_inter_preimage_eq_mul s t hs ht

end

end AronowAudit.P011.Wave1.PropositionOne
