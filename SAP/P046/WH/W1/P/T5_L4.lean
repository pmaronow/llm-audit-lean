import SAP.P046.WH.W1.Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P046.WH.W1.P.T5_L4

noncomputable section
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal

def error (M : Study) (F : ∀ n, CrossFit n) (g : ℝ → ℝ)
    (n : ℕ) (j : Bool) (a : Sample n) : ℝ≥0∞ :=
  wholeL2Sq M (fun w => (F n).g j a w - g w)

theorem error_integrable (M : Study) (f : ℝ → ℝ) (hf : Measurable f)
    (hfin : wholeL2Sq M f ≠ ∞) :
    Integrable (fun o => (f (W o)) ^ 2) M.law := by
  have hmeas : Measurable (fun o : Unit => f (W o)) := hf.comp measurable_fst
  have hsq : Measurable (fun o : Unit => (f (W o)) ^ 2) := hmeas.pow_const 2
  have hnonneg : 0 ≤ᵐ[M.law] fun o : Unit => (f (W o)) ^ 2 :=
    Filter.Eventually.of_forall fun o => sq_nonneg (f (W o))
  apply (lintegral_ofReal_ne_top_iff_integrable hsq.aestronglyMeasurable hnonneg).mp
  simpa [wholeL2Sq] using hfin

theorem wholeL2Sq_bridge (M : Study) (f : ℝ → ℝ) (hf : Measurable f)
    (hfin : wholeL2Sq M f ≠ ∞) :
    ENNReal.ofReal (l2Sq M f) = wholeL2Sq M f := by
  have hmeas : Measurable (fun o : Unit => f (W o)) := hf.comp measurable_fst
  have hsq : Measurable (fun o : Unit => (f (W o)) ^ 2) := hmeas.pow_const 2
  have hint := error_integrable M f hf hfin
  have hbridge := integral_eq_lintegral_of_nonneg_ae
    (μ := M.law)
    (Filter.Eventually.of_forall fun o : Unit => sq_nonneg (f (W o)))
    hsq.aestronglyMeasurable
  change ENNReal.ofReal (∫ o, (f (W o)) ^ 2 ∂M.law) =
    ∫⁻ o, ENNReal.ofReal ((f (W o)) ^ 2) ∂M.law
  rw [hbridge, ENNReal.ofReal_toReal (by simpa [wholeL2Sq] using hfin)]

theorem wholeL2Sq_memLp (M : Study) (f : ℝ → ℝ) (hf : Measurable f)
    (hfin : wholeL2Sq M f ≠ ∞) : MemLp (fun o => f (W o)) 2 M.law := by
  have hmeas : Measurable (fun o : Unit => f (W o)) := hf.comp measurable_fst
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    (error_integrable M f hf hfin)

theorem measurable_error (M : Study) (hM : ValidStudy M)
    (F : ∀ n, CrossFit n) (g : ℝ → ℝ) (hg : Measurable g)
    (n : ℕ) (j : Bool) : Measurable (error M F g n j) := by
  letI := hM.probability
  have hfit : Measurable (fun z : Sample n × Unit => (F n).g j z.1 (W z.2)) := by
    exact ((F n).measurable_g j).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have htarget : Measurable (fun z : Sample n × Unit => g (W z.2)) :=
    hg.comp (measurable_fst.comp measurable_snd)
  have hsq : Measurable (fun z : Sample n × Unit =>
      ((F n).g j z.1 (W z.2) - g (W z.2)) ^ 2) := (hfit.sub htarget).pow_const 2
  have henn : Measurable (fun z : Sample n × Unit =>
      ENNReal.ofReal (((F n).g j z.1 (W z.2) - g (W z.2)) ^ 2)) := by
    exact ENNReal.measurable_ofReal.comp hsq
  change Measurable (fun a : Sample n =>
    ∫⁻ o : Unit, ENNReal.ofReal (((F n).g j a (W o) - g (W o)) ^ 2) ∂M.law)
  exact henn.lintegral_prod_right'

theorem proof : SAP.P046.WH.W1.T5_L4 := by
  classical
  intro M hM F g hg hLg hconv
  letI := hM.probability
  let E : ∀ n, Bool → Sample n → ℝ≥0∞ := error M F g
  have hEmeas : ∀ n j, Measurable (E n j) := by
    intro n j
    exact measurable_error M hM F g hg n j
  let G : ∀ n, CrossFit n := fun n =>
    { fold := (F n).fold
      g := fun j a w => if E n j a ≤ 1 then (F n).g j a w else g w
      measurable_g := by
        intro j
        apply Measurable.ite
        · exact measurableSet_le ((hEmeas n j).comp measurable_fst) measurable_const
        · exact (F n).measurable_g j
        · exact hg.comp measurable_snd
      opposite_fold := by
        intro j a b hab
        have hfit : (F n).g j a = (F n).g j b := (F n).opposite_fold j a b hab
        have he : E n j a = E n j b := by
          simp only [E, error]
          congr 1
          funext w
          simp only [congrFun hfit w]
        change (fun w => if E n j a ≤ 1 then (F n).g j a w else g w) =
          (fun w => if E n j b ≤ 1 then (F n).g j b w else g w)
        rw [he, hfit] }
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro n j
    apply Filter.Eventually.of_forall
    intro a
    by_cases hcut : E n j a ≤ 1
    · have hmeas : Measurable (fun w : ℝ => (F n).g j a w - g w) := by
        exact ((F n).measurable_g j).comp
          (measurable_const.prodMk measurable_id) |>.sub hg
      have hmem := wholeL2Sq_memLp M (fun w => (F n).g j a w - g w) hmeas
        (by
          have ht : E n j a < ∞ := lt_of_le_of_lt hcut (by norm_num)
          simpa [E, error] using ne_of_lt ht)
      have hpred : MemLp (fun o : Unit => (F n).g j a (W o)) 2 M.law := by
        have heq : (fun o : Unit =>
            ((F n).g j a (W o) - g (W o)) + g (W o)) =
            fun o => (F n).g j a (W o) := by
          funext o
          ring
        exact heq ▸ hmem.add hLg
      simpa [G, hcut] using hpred
    · have hG : (fun o : Unit => (G n).g j a (W o)) =
          fun o => g (W o) := by
        funext o
        simp [G, hcut]
      simpa [G, hcut] using hLg
  · intro j eps heps
    have horig := hconv j eps heps
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ)) (h := fun n =>
        (sampleLaw M n {a | ENNReal.ofReal eps < E n j a}).toReal)
    · exact tendsto_const_nhds
    · exact horig
    · intro n
      exact measureReal_nonneg
    · intro n
      apply measureReal_mono (μ := sampleLaw M n) (h₂ := by finiteness)
      intro a ha
      by_cases hcut : E n j a ≤ 1
      · have hmeas : Measurable (fun w : ℝ => (F n).g j a w - g w) := by
          exact ((F n).measurable_g j).comp
            (measurable_const.prodMk measurable_id) |>.sub hg
        have hbridge := wholeL2Sq_bridge M
          (fun w => (F n).g j a w - g w) hmeas
          (by
            have ht : E n j a < ∞ := lt_of_le_of_lt hcut (by norm_num)
            simpa [E, error] using ne_of_lt ht)
        have hsame : (fun w => (G n).g j a w - g w) =
            fun w => (F n).g j a w - g w := by
          funext w
          simp [G, hcut]
        have htarget : l2Sq M (fun w => (G n).g j a w - g w) =
            l2Sq M (fun w => (F n).g j a w - g w) := congrArg (l2Sq M) hsame
        change eps < l2Sq M (fun w => (G n).g j a w - g w) at ha
        rw [htarget] at ha
        have hreal : ENNReal.ofReal (l2Sq M (fun w => (F n).g j a w - g w)) = E n j a := by
          simpa [E, error] using hbridge
        have hlt : ENNReal.ofReal eps <
            ENNReal.ofReal (l2Sq M (fun w => (F n).g j a w - g w)) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (le_of_lt heps)).2 ha
        rw [hreal] at hlt
        exact hlt
      · have hzero : (fun w => (G n).g j a w - g w) = 0 := by
          funext w
          simp [G, hcut]
        change eps < l2Sq M (fun w => (G n).g j a w - g w) at ha
        rw [hzero] at ha
        have hlt : eps < 0 := by simpa [l2Sq] using ha
        exact False.elim (not_lt_of_ge (le_of_lt heps) hlt)
  · have hbad : ∀ n a, adjusted M (F n) a ≠ adjusted M (G n) a →
        a ∈ {a | 1 < E n false a} ∪ {a | 1 < E n true a} := by
      intro n a hneq
      by_contra hnot
      have hn : ¬ (1 < E n false a ∨ 1 < E n true a) := by simpa using hnot
      have hfalse : E n false a ≤ 1 := le_of_not_gt (fun hh => hn (Or.inl hh))
      have htrue : E n true a ≤ 1 := le_of_not_gt (fun hh => hn (Or.inr hh))
      have hterm : ∀ i, adjustedTerm (M.pi (W (a i))) (X (a i)) (Y (a i))
          ((F n).g ((F n).fold i) a (W (a i))) =
        adjustedTerm (M.pi (W (a i))) (X (a i)) (Y (a i))
          ((G n).g ((F n).fold i) a (W (a i))) := by
        intro i
        cases hj : (F n).fold i <;> simp [G, hj, hfalse, htrue]
      apply hneq
      unfold adjusted
      congr 1
      exact Finset.sum_congr rfl (by intro i hi; exact hterm i)
    have hbound (n : ℕ) :
        (sampleLaw M n {a | adjusted M (F n) a ≠ adjusted M (G n) a}).toReal ≤
          (sampleLaw M n {a | 1 < E n false a}).toReal +
            (sampleLaw M n {a | 1 < E n true a}).toReal := by
      exact (measureReal_mono (μ := sampleLaw M n) (fun a ha => hbad n a ha)
        (by finiteness)).trans (measureReal_union_le ..)
    have hfalse := hconv false 1 (by norm_num)
    have htrue := hconv true 1 (by norm_num)
    have hsum : Tendsto (fun n =>
        (sampleLaw M n {a | 1 < E n false a}).toReal +
          (sampleLaw M n {a | 1 < E n true a}).toReal) atTop (nhds 0) := by
      simpa [E, error] using hfalse.add htrue
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun _ : ℕ => (0 : ℝ)) (h := fun n =>
        (sampleLaw M n {a | 1 < E n false a}).toReal +
          (sampleLaw M n {a | 1 < E n true a}).toReal)
    · exact tendsto_const_nhds
    · exact hsum
    · intro n
      exact measureReal_nonneg
    · exact hbound

end
end SAP.P046.WH.W1.P.T5_L4

theorem SAP.P046.WH.W1.T5_L4_proof : SAP.P046.WH.W1.T5_L4 :=
  SAP.P046.WH.W1.P.T5_L4.proof
