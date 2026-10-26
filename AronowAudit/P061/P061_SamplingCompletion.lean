import AronowAudit.P061.P061_Foundations

/-! General exposure-pattern SRS. The raw assignment type may record sampling
order and other features; its outcomes need not factor through the sample mask. -/
namespace AronowAudit.P061.SamplingCompletion
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false

def exposureMask {Ω : Type} {N : ℕ} (g : ExposureMapping Ω N) (d : ℝ) (z : Ω) :
    Fin N → Fin 2 := fun i => if g i z=d then 1 else 0

def maskDesign {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (d : ℝ) : Design (Fin N → Fin 2) where
  p := fun b => probability D (fun z => exposureMask g d z=b)
  nonneg := fun b => probability_nonneg D _
  summable := Summable.of_finite
  total := by
    letI : DecidableEq (Fin N → Fin 2) := Classical.decEq _
    simp only [tsum_fintype,probability]
    rw [←Summable.tsum_finsetSum (fun b hb => event_summable D (fun z => exposureMask g d z=b))]
    simpa using D.total

/-- The actual exposed set is uniform among all n-subsets; raw assignments
with the same sampled set are allowed to have different outcomes. -/
def SimpleRandomExposure {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (d : ℝ) (n : ℕ) : Prop :=
  CompleteRandomization (maskDesign D g d) n


theorem mask_pi {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (d : ℝ) (i : Fin N) :
    pi (maskDesign D g d) (fun j b => (b j).val) i 1=pi D g i d := by
  classical
  letI : DecidableEq (Fin N → Fin 2) := Classical.decEq _
  unfold pi probability
  rw [tsum_fintype]
  simp only [maskDesign,probability]
  calc
    _ = ∑ b : Fin N → Fin 2, ∑' z : Ω,
        if exposureMask g d z=b then (if ((b i).val:ℝ)=1 then D.p z else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hi : ((b i).val:ℝ)=1 <;> simp [hi]
    _ = ∑' z : Ω, ∑ b : Fin N → Fin 2,
        if exposureMask g d z=b then (if ((b i).val:ℝ)=1 then D.p z else 0) else 0 := by
      rw [Summable.tsum_finsetSum]
      intro b hb
      by_cases hi : ((b i).val:ℝ)=1
      · simpa only [hi,ite_true] using event_summable D (fun z => exposureMask g d z=b)
      · simp [hi]
    _ = _ := by
      apply tsum_congr
      intro z
      by_cases hg : g i z=d <;> simp [exposureMask,hg]

theorem support_mask {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (d : ℝ) (z : Ω) (hz : Support D z) :
    Support (maskDesign D g d) (exposureMask g d z) := by
  have he : D.p z ≤ (maskDesign D g d).p (exposureMask g d z) := by
    exact event_atom_le D (fun w => exposureMask g d w=exposureMask g d z) z rfl
  exact lt_of_lt_of_le hz he

theorem canonical_treatment_marginal {N : ℕ} (D : Design (Fin N → Fin 2))
    (n : ℕ) (hn : 0<n) (hn' : n≤N) (hd : CompleteRandomization D n) (i : Fin N) :
    pi D (fun j b => (b j).val) i 1=(n:ℝ)/N := by
  classical
  rcases lt_or_eq_of_le hn' with hlt|he
  · exact (complete_randomization_marginals D n hn hlt hd i).1
  · subst n
    have hN : (N:ℝ)≠0 := by exact_mod_cast hn.ne'
    rw [div_self hN]
    unfold pi probability
    conv_rhs => rw [←D.total]
    apply tsum_congr
    intro b
    by_cases hi : ((b i).val:ℝ)=1
    · simp [hi]
    · have hc : (Finset.univ.filter (fun j : Fin N => b j=1)).card≠N := by
        intro hc
        have hh : ∀ j ∈ (Finset.univ : Finset (Fin N)), b j=1 :=
          Finset.card_filter_eq_iff.mp (by simpa using hc)
        have hh' := hh i (Finset.mem_univ i)
        simp [hh'] at hi
      have hp : D.p b=0 := by simp [hd b,hc]
      simp [hi,hp]

theorem SRS_unbiased {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (d : ℝ) (n : ℕ)
    (hn : 0<n) (hn' : n≤N) (hd : SimpleRandomExposure D g d n)
    (hfin : {z : Ω | Support D z}.Finite) :
    (∀ z, Support D z → (Finset.univ.filter (fun i => g i z=d)).card=n) ∧
    (∀ i, pi D g i d=(n:ℝ)/N) ∧
    expectation D (sampleMean g y d n)=aepo D g y d := by
  have hp : ∀ i, pi D g i d=(n:ℝ)/N := by
    intro i
    rw [←mask_pi D g d i]
    exact canonical_treatment_marginal (maskDesign D g d) n hn hn' hd i
  have he : sampleMean g y d n=ht D g y d :=
    funext (fun z => (ht_sample_mean D g y d n (lt_of_lt_of_le hn hn') hn hp z).symm)
  have hu : expectation D (sampleMean g y d n)=aepo D g y d := by
    rw [he]
    exact ht_unbiased D g y d (finite_support_targeted_moment D hfin g y d)
  refine ⟨?_,hp,hu⟩
  intro z hz
  have hs := support_mask D g d z hz
  have hc : (Finset.univ.filter (fun i => exposureMask g d z i=1)).card=n := by
    by_contra hc
    have hp0 : (maskDesign D g d).p (exposureMask g d z)=0 := by simp [hd (exposureMask g d z),hc]
    exact (ne_of_gt hs) hp0
  convert hc using 1
  congr 1
  ext i
  by_cases hg : g i z=d <;> simp [exposureMask,hg]

theorem CR_unbiased {Ω : Type} {N : ℕ} (D : Design Ω)
    (g : ExposureMapping Ω N) (y : OutcomeSchedule Ω N) (n : ℕ)
    (hn : 0<n) (hn' : n<N) (hd : SimpleRandomExposure D g 1 n)
    (hfin : {z : Ω | Support D z}.Finite)
    (hb : ∀ i z, Support D z → g i z=0 ∨ g i z=1) :
    (∀ i, pi D g i 1=(n:ℝ)/N ∧ pi D g i 0=((N-n:ℕ):ℝ)/N) ∧
    expectation D (fun z => sampleMean g y 1 n z-sampleMean g y 0 (N-n) z)=
      aeed D g y 1 0 := by
  have hp := (SRS_unbiased D g y 1 n hn hn'.le hd hfin).2.1
  have hp0 : ∀ i, pi D g i 0=((N-n:ℕ):ℝ)/N := by
    intro i
    have he : pi D g i 0=probability D (fun z => ¬g i z=1) := by
      unfold pi probability
      apply tsum_congr
      intro z
      by_cases hs : Support D z
      · rcases hb i z hs with hz|hz <;> simp [hz]
      · have hz : D.p z=0 := le_antisymm (le_of_not_gt hs) (D.nonneg z)
        simp [hz]
    rw [he,probability_complement]
    change 1-pi D g i 1=_
    rw [hp,Nat.cast_sub hn'.le]
    have hn0 : (N:ℝ)≠0 := by exact_mod_cast (lt_trans hn hn').ne'
    field_simp
  refine ⟨fun i => ⟨hp i,hp0 i⟩,?_⟩
  have he1 : sampleMean g y 1 n=ht D g y 1 :=
    funext (fun z => (ht_sample_mean D g y 1 n (lt_trans hn hn') hn hp z).symm)
  have he0 : sampleMean g y 0 (N-n)=ht D g y 0 :=
    funext (fun z => (ht_sample_mean D g y 0 (N-n) (lt_trans hn hn') (Nat.sub_pos_of_lt hn') hp0 z).symm)
  rw [he1,he0]
  exact ht_contrast_unbiased D g y 1 0
    (finite_support_targeted_moment D hfin g y 1) (finite_support_targeted_moment D hfin g y 0)
    (finite_support_integrable D hfin _) (finite_support_integrable D hfin _)

end
end AronowAudit.P061.SamplingCompletion
