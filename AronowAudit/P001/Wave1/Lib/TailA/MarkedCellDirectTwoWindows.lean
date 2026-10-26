import AronowAudit.P001.Wave1.Lib.TailA.MarkedCellDirectWindows

/-! Direct two-window limits for the actual shared original donor locations. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology

namespace AronowAudit.P001.TailA
local instance instDecidableMarkedCellDirectTwoWindows (p : Prop) : Decidable p :=
  Classical.propDecidable p
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000

/-- The overlap and the two exclusive parts partition arbitrary donor windows.
The marked product limit follows from their actual rare-count laws. -/
theorem marked_direct_two_set_retained_limit
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (E F : ℕ → Set MatchUnit) (hE : ∀ n, MeasurableSet (E n))
    (hF : ∀ n, MeasurableSet (F n)) (rates : Fin 3 → ℝ≥0)
    (hr0 : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n ∩ F n)) atTop
      (𝓝 (rates 0 : ℝ)))
    (hr1 : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n \ F n)) atTop
      (𝓝 (rates 1 : ℝ)))
    (hr2 : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (F n \ E n)) atTop
      (𝓝 (rates 2 : ℝ))) (k l : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n) (markedWindowCount (E n) z) k *
        markedRetainedDrawPower (N n) (markedWindowCount (F n) z) l)) atTop
      (𝓝 (matchS^2*Real.exp ((rates 0 : ℝ)*(Real.exp (-2)-1) +
        ((rates 1 : ℝ)+(rates 2 : ℝ))*(Real.exp (-1)-1)))) := by
  let G : ℕ → Fin 3 → Set MatchUnit := fun n i =>
    if i = 0 then E n ∩ F n else if i = 1 then E n \ F n else F n \ E n
  have h0 (n : ℕ) : G n 0 = E n ∩ F n := by simp [G]
  have h1 (n : ℕ) : G n 1 = E n \ F n := by simp [G]
  have h2 (n : ℕ) : G n 2 = F n \ E n := by simp [G]
  have hG (n : ℕ) (i : Fin 3) : MeasurableSet (G n i) := by
    fin_cases i
    · simpa [G] using (hE n).inter (hF n)
    · simpa [G] using (hE n).diff (hF n)
    · simpa [G] using (hF n).diff (hE n)
  have hdis (n : ℕ) (i j : Fin 3) (hij : i ≠ j) : Disjoint (G n i) (G n j) := by
    fin_cases i <;> fin_cases j
    all_goals first
      | exact False.elim (hij rfl)
      | apply Set.disjoint_left.mpr
        intro x hx hy
        simp [G] at hx hy
        tauto
  have hr (i : Fin 3) : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (G n i))
      atTop (𝓝 (rates i : ℝ)) := by
    fin_cases i
    · simpa [G] using hr0
    · simpa [G] using hr1
    · simpa [G] using hr2
  have hunion1 (n : ℕ) : G n 0 ∪ G n 1 = E n := by
    rw [h0,h1]
    ext x
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_diff]
    tauto
  have hunion2 (n : ℕ) : G n 0 ∪ G n 2 = F n := by
    rw [h0,h2]
    ext x
    simp only [Set.mem_union,Set.mem_inter_iff,Set.mem_diff]
    tauto
  have hh := (marked_direct_pair_category_limits m N hm hN G hG hdis rates hr k l).2
  simpa only [hunion1,hunion2] using hh

/-- Nested windows retain the overlap twice in the exponent. -/
theorem marked_direct_nested_retained_limit
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (E F : ℕ → Set MatchUnit) (hE : ∀ n, MeasurableSet (E n))
    (hF : ∀ n, MeasurableSet (F n)) (hsub : ∀ n, E n ⊆ F n)
    (a b : ℝ≥0) (hab : a ≤ b)
    (hrE : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n)) atTop (𝓝 (a : ℝ)))
    (hrF : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (F n)) atTop (𝓝 (b : ℝ)))
    (k l : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n) (markedWindowCount (E n) z) k *
        markedRetainedDrawPower (N n) (markedWindowCount (F n) z) l)) atTop
      (𝓝 (matchS^2*Real.exp ((a : ℝ)*(Real.exp (-2)-1) +
        ((b : ℝ)-(a : ℝ))*(Real.exp (-1)-1)))) := by
  let rates : Fin 3 → ℝ≥0 := ![a,0,b-a]
  have hr0 : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n ∩ F n)) atTop
      (𝓝 (rates 0 : ℝ)) := by
    simpa only [Set.inter_eq_left.mpr (hsub _),show (rates 0 : ℝ) = a from rfl] using hrE
  have hr1 : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n \ F n)) atTop
      (𝓝 (rates 1 : ℝ)) := by
    simp only [Set.sdiff_eq_empty.mpr (hsub _),measureReal_empty,mul_zero]
    exact tendsto_const_nhds
  have hr2 : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (F n \ E n)) atTop
      (𝓝 (rates 2 : ℝ)) := by
    have hd (n : ℕ) : matchingUnitLaw.real (F n \ E n) =
        matchingUnitLaw.real (F n)-matchingUnitLaw.real (E n) :=
      measureReal_sdiff (hsub n) (hE n)
    simpa only [hd,mul_sub,rates,show (rates 2 : ℝ) = (b : ℝ)-(a : ℝ) from
      NNReal.coe_sub hab] using hrF.sub hrE
  have hh := marked_direct_two_set_retained_limit m N hm hN E F hE hF rates hr0 hr1 hr2 k l
  have h0 : (rates 0 : ℝ) = a := rfl
  have h1 : (rates 1 : ℝ) = 0 := rfl
  have h2 : (rates 2 : ℝ) = (b : ℝ)-(a : ℝ) := NNReal.coe_sub hab
  simpa only [h0,h1,h2,zero_add] using hh

/-- Disjoint left/right windows have no overlap category. -/
theorem marked_direct_disjoint_retained_limit
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (E F : ℕ → Set MatchUnit) (hE : ∀ n, MeasurableSet (E n))
    (hF : ∀ n, MeasurableSet (F n)) (hdis : ∀ n, Disjoint (E n) (F n))
    (a b : ℝ≥0)
    (hrE : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n)) atTop (𝓝 (a : ℝ)))
    (hrF : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (F n)) atTop (𝓝 (b : ℝ)))
    (k l : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n) (markedWindowCount (E n) z) k *
        markedRetainedDrawPower (N n) (markedWindowCount (F n) z) l)) atTop
      (𝓝 (matchS^2*Real.exp (-matchS*((a : ℝ)+(b : ℝ))))) := by
  let rates : Fin 3 → ℝ≥0 := ![0,a,b]
  have h0 (n : ℕ) : E n ∩ F n = ∅ := Set.disjoint_iff_inter_eq_empty.mp (hdis n)
  have h1 (n : ℕ) : E n \ F n = E n := by
    ext x
    simp only [Set.mem_diff]
    exact ⟨fun h => h.1,fun h => ⟨h,fun hx => Set.disjoint_left.mp (hdis n) h hx⟩⟩
  have h2 (n : ℕ) : F n \ E n = F n := by
    ext x
    simp only [Set.mem_diff]
    exact ⟨fun h => h.1,fun h => ⟨h,fun hx => Set.disjoint_left.mp (hdis n) hx h⟩⟩
  have hr0 : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n ∩ F n)) atTop
      (𝓝 (rates 0 : ℝ)) := by
    simp only [h0,measureReal_empty,mul_zero]
    exact tendsto_const_nhds
  have hr1 : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (E n \ F n)) atTop
      (𝓝 (rates 1 : ℝ)) := by simpa only [h1,show (rates 1 : ℝ) = a from rfl] using hrE
  have hr2 : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real (F n \ E n)) atTop
      (𝓝 (rates 2 : ℝ)) := by simpa only [h2,show (rates 2 : ℝ) = b from rfl] using hrF
  have hh := marked_direct_two_set_retained_limit m N hm hN E F hE hF rates hr0 hr1 hr2 k l
  have hz0 : (rates 0 : ℝ) = 0 := rfl
  have hz1 : (rates 1 : ℝ) = a := rfl
  have hz2 : (rates 2 : ℝ) = b := rfl
  have he : ((a : ℝ)+(b : ℝ))*(Real.exp (-1)-1) = -matchS*((a : ℝ)+(b : ℝ)) := by
    unfold matchS
    ring
  simpa only [hz0,hz1,hz2,zero_mul,zero_add,he] using hh

theorem marked_closer_donors_nested_right {p x y : ℝ} (hpx : p ≤ x) (hxy : x ≤ y) :
    markedCloserDonors p x ⊆ markedCloserDonors p y := by
  rintro u ⟨hr,hclose⟩
  refine ⟨hr,?_⟩
  rw [marked_closer_right (hpx.trans hxy)]
  rw [marked_closer_right hpx] at hclose
  exact ⟨hclose.1,by linarith [hclose.2]⟩

theorem marked_closer_donors_nested_left {p x y : ℝ} (hxp : x ≤ p) (hyx : y ≤ x) :
    markedCloserDonors p x ⊆ markedCloserDonors p y := by
  rintro u ⟨hr,hclose⟩
  refine ⟨hr,?_⟩
  rw [marked_closer_left (hyx.trans hxp)]
  rw [marked_closer_left hxp] at hclose
  exact ⟨by linarith [hclose.1],hclose.2⟩

theorem marked_closer_donors_opposite {p x y : ℝ} (hxp : x ≤ p) (hpy : p ≤ y) :
    Disjoint (markedCloserDonors p x) (markedCloserDonors p y) := by
  apply Set.disjoint_left.mpr
  rintro u ⟨_,hx⟩ ⟨_,hy⟩
  rw [marked_closer_left hxp] at hx
  rw [marked_closer_right hpy] at hy
  exact (lt_irrefl p) (hy.1.trans hx.2)

/-- Actual two-replica closer-donor kernels for ordered queries to the right.
This includes both central-retention factors and the shared-site overlap. -/
theorem marked_direct_right_recipient_pair_limit (p a b : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (ha : 0 ≤ a) (hab : a ≤ b)
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (k l : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p+a/(m n : ℝ))) z) k *
      markedRetainedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p+b/(m n : ℝ))) z) l)) atTop
      (𝓝 (matchS^2*Real.exp (-(4*p)*(matchS*(a+b)-matchS^2*a)))) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hb : 0 ≤ b := ha.trans hab
  let ra : ℝ≥0 := ⟨4*p*a,by positivity⟩
  let rb : ℝ≥0 := ⟨4*p*b,by positivity⟩
  have hrab : ra ≤ rb := by change 4*p*a ≤ 4*p*b; exact mul_le_mul_of_nonneg_left hab (by positivity)
  have hsub (n : ℕ) : markedCloserDonors p (p+a/(m n : ℝ)) ⊆
      markedCloserDonors p (p+b/(m n : ℝ)) := by
    apply marked_closer_donors_nested_right
    · exact le_add_of_nonneg_right (div_nonneg ha (Nat.cast_nonneg _))
    · exact add_le_add (le_refl p) (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _))
  have hra : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real
      (markedCloserDonors p (p+a/(m n : ℝ)))) atTop (𝓝 (ra : ℝ)) := by
    simpa only [show (ra : ℝ) = 4*p*a from rfl,abs_of_nonneg ha] using marked_closer_donors_rate p a hp m hm
  have hrb : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real
      (markedCloserDonors p (p+b/(m n : ℝ)))) atTop (𝓝 (rb : ℝ)) := by
    simpa only [show (rb : ℝ) = 4*p*b from rfl,abs_of_nonneg hb] using marked_closer_donors_rate p b hp m hm
  have hh := marked_direct_nested_retained_limit m N hm hN _ _
    (fun _ => marked_closer_donors_measurable _ _) (fun _ => marked_closer_donors_measurable _ _)
    hsub ra rb hrab hra hrb k l
  have he : (ra : ℝ)*(Real.exp (-2)-1)+((rb : ℝ)-(ra : ℝ))*(Real.exp (-1)-1) =
      -(4*p)*(matchS*(a+b)-matchS^2*a) := by
    change (4*p*a)*(Real.exp (-2)-1)+(4*p*b-4*p*a)*(Real.exp (-1)-1) = _
    rw [show (-2 : ℝ) = -1+(-1) by norm_num,Real.exp_add]
    unfold matchS
    ring
  simpa only [he] using hh

/-- The same shared-site kernel for ordered queries on the left of the pin. -/
theorem marked_direct_left_recipient_pair_limit (p a b : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (ha : 0 ≤ a) (hab : a ≤ b)
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (k l : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p-a/(m n : ℝ))) z) k *
      markedRetainedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p-b/(m n : ℝ))) z) l)) atTop
      (𝓝 (matchS^2*Real.exp (-(4*p)*(matchS*(a+b)-matchS^2*a)))) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hb : 0 ≤ b := ha.trans hab
  let ra : ℝ≥0 := ⟨4*p*a,by positivity⟩
  let rb : ℝ≥0 := ⟨4*p*b,by positivity⟩
  have hrab : ra ≤ rb := by
    change 4*p*a ≤ 4*p*b
    exact mul_le_mul_of_nonneg_left hab (by positivity)
  have hsub (n : ℕ) : markedCloserDonors p (p-a/(m n : ℝ)) ⊆
      markedCloserDonors p (p-b/(m n : ℝ)) := by
    apply marked_closer_donors_nested_left
    · exact sub_le_self _ (div_nonneg ha (Nat.cast_nonneg _))
    · exact sub_le_sub_left (div_le_div_of_nonneg_right hab (Nat.cast_nonneg _)) p
  have hra : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real
      (markedCloserDonors p (p-a/(m n : ℝ)))) atTop (𝓝 (ra : ℝ)) := by
    simpa only [sub_eq_add_neg,neg_div,abs_neg,abs_of_nonneg ha,
      show (ra : ℝ) = 4*p*a from rfl] using marked_closer_donors_rate p (-a) hp m hm
  have hrb : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real
      (markedCloserDonors p (p-b/(m n : ℝ)))) atTop (𝓝 (rb : ℝ)) := by
    simpa only [sub_eq_add_neg,neg_div,abs_neg,abs_of_nonneg hb,
      show (rb : ℝ) = 4*p*b from rfl] using marked_closer_donors_rate p (-b) hp m hm
  have hh := marked_direct_nested_retained_limit m N hm hN _ _
    (fun _ => marked_closer_donors_measurable _ _) (fun _ => marked_closer_donors_measurable _ _)
    hsub ra rb hrab hra hrb k l
  have he : (ra : ℝ)*(Real.exp (-2)-1)+((rb : ℝ)-(ra : ℝ))*(Real.exp (-1)-1) =
      -(4*p)*(matchS*(a+b)-matchS^2*a) := by
    change (4*p*a)*(Real.exp (-2)-1)+(4*p*b-4*p*a)*(Real.exp (-1)-1) = _
    rw [show (-2 : ℝ) = -1+(-1) by norm_num,Real.exp_add]
    unfold matchS
    ring
  simpa only [he] using hh

/-- Queries on opposite sides have disjoint closer-donor windows.  The two
central-retention factors are still present. -/
theorem marked_direct_opposite_recipient_pair_limit (p a b : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4)) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (k l : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p-a/(m n : ℝ))) z) k *
      markedRetainedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p+b/(m n : ℝ))) z) l)) atTop
      (𝓝 (matchS^2*Real.exp (-4*p*matchS*(a+b)))) := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  let ra : ℝ≥0 := ⟨4*p*a,by positivity⟩
  let rb : ℝ≥0 := ⟨4*p*b,by positivity⟩
  have hdis (n : ℕ) : Disjoint (markedCloserDonors p (p-a/(m n : ℝ)))
      (markedCloserDonors p (p+b/(m n : ℝ))) :=
    marked_closer_donors_opposite (sub_le_self _ (div_nonneg ha (Nat.cast_nonneg _)))
      (le_add_of_nonneg_right (div_nonneg hb (Nat.cast_nonneg _)))
  have hra : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real
      (markedCloserDonors p (p-a/(m n : ℝ)))) atTop (𝓝 (ra : ℝ)) := by
    simpa only [sub_eq_add_neg,neg_div,abs_neg,abs_of_nonneg ha,
      show (ra : ℝ) = 4*p*a from rfl] using marked_closer_donors_rate p (-a) hp m hm
  have hrb : Tendsto (fun n => (m n : ℝ)*matchingUnitLaw.real
      (markedCloserDonors p (p+b/(m n : ℝ)))) atTop (𝓝 (rb : ℝ)) := by
    simpa only [abs_of_nonneg hb,show (rb : ℝ) = 4*p*b from rfl]
      using marked_closer_donors_rate p b hp m hm
  have hh := marked_direct_disjoint_retained_limit m N hm hN _ _
    (fun _ => marked_closer_donors_measurable _ _) (fun _ => marked_closer_donors_measurable _ _)
    hdis ra rb hra hrb k l
  have he : -matchS*((ra : ℝ)+(rb : ℝ)) = -4*p*matchS*(a+b) := by
    change -matchS*(4*p*a+4*p*b) = _
    ring
  simpa only [he] using hh

/-- Product kernels are symmetric only after swapping the complete queries,
including their specified-draw orders. -/
theorem marked_direct_pair_kernel_symm (n N : ℕ) (p t u : ℝ) (k l : ℕ) :
    mean (MatchProduct n) (fun z =>
      markedRetainedDrawPower N (markedWindowCount (markedCloserDonors p (p+t/(n : ℝ))) z) k *
      markedRetainedDrawPower N (markedWindowCount (markedCloserDonors p (p+u/(n : ℝ))) z) l) =
    mean (MatchProduct n) (fun z =>
      markedRetainedDrawPower N (markedWindowCount (markedCloserDonors p (p+u/(n : ℝ))) z) l *
      markedRetainedDrawPower N (markedWindowCount (markedCloserDonors p (p+t/(n : ℝ))) z) k) := by
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => mul_comm _ _)

/-- Length, in one-recipient coordinates, of the common closer-donor window. -/
def markedDirectionalOverlap (t u : ℝ) : ℝ :=
  min (max t 0) (max u 0)+min (max (-t) 0) (max (-u) 0)

/-- The full pointwise two-recipient kernel limit, on all four quadrants.
This is derived from the actual iid donor counts and multinomial formulas. -/
theorem marked_direct_recipient_pair_kernel_limit (p t u : ℝ)
    (hp : p ∈ Set.Ioo (1/4 : ℝ) (3/4))
    (m N : ℕ → ℕ) (hm : Tendsto m atTop atTop) (hN : Tendsto N atTop atTop)
    (k l : ℕ) :
    Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
      markedRetainedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p+t/(m n : ℝ))) z) k *
      markedRetainedDrawPower (N n)
        (markedWindowCount (markedCloserDonors p (p+u/(m n : ℝ))) z) l)) atTop
      (𝓝 (matchS^2*Real.exp (-(4*p)*(matchS*(|t|+|u|)-matchS^2*markedDirectionalOverlap t u)))) := by
  have hright (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k l : ℕ) :
      Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p+a/(m n : ℝ))) z) k *
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p+b/(m n : ℝ))) z) l)) atTop
        (𝓝 (matchS^2*Real.exp (-(4*p)*(matchS*(a+b)-matchS^2*min a b)))) := by
    rcases le_total a b with hab | hba
    · simpa only [min_eq_left hab] using
        marked_direct_right_recipient_pair_limit p a b hp ha hab m N hm hN k l
    · have hh := marked_direct_right_recipient_pair_limit p b a hp hb hba m N hm hN l k
      simpa only [marked_direct_pair_kernel_symm _ _ p a b k l,min_eq_right hba,add_comm a b]
        using hh
  have hleft (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (k l : ℕ) :
      Tendsto (fun n => mean (MatchProduct (m n)) (fun z =>
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p-a/(m n : ℝ))) z) k *
        markedRetainedDrawPower (N n)
          (markedWindowCount (markedCloserDonors p (p-b/(m n : ℝ))) z) l)) atTop
        (𝓝 (matchS^2*Real.exp (-(4*p)*(matchS*(a+b)-matchS^2*min a b)))) := by
    rcases le_total a b with hab | hba
    · simpa only [min_eq_left hab] using
        marked_direct_left_recipient_pair_limit p a b hp ha hab m N hm hN k l
    · have hh := marked_direct_left_recipient_pair_limit p b a hp hb hba m N hm hN l k
      have hswap (n : ℕ) := marked_direct_pair_kernel_symm (m n) (N n) p (-a) (-b) k l
      simp only [neg_div,← sub_eq_add_neg] at hswap
      simpa only [hswap,min_eq_right hba,add_comm a b] using hh
  by_cases ht : 0 ≤ t
  · by_cases hu : 0 ≤ u
    · simpa only [markedDirectionalOverlap,max_eq_left ht,max_eq_left hu,
        max_eq_right (neg_nonpos.mpr ht),max_eq_right (neg_nonpos.mpr hu),min_self,
        add_zero,abs_of_nonneg ht,abs_of_nonneg hu] using hright t u ht hu k l
    · have hu' : u ≤ 0 := le_of_not_ge hu
      have hh := marked_direct_opposite_recipient_pair_limit p (-u) t hp (neg_nonneg.mpr hu') ht
        m N hm hN l k
      simp only [neg_div,sub_neg_eq_add] at hh
      have hswap (n : ℕ) := marked_direct_pair_kernel_symm (m n) (N n) p t u k l
      simpa only [hswap,markedDirectionalOverlap,max_eq_left ht,max_eq_right hu',
        max_eq_right (neg_nonpos.mpr ht),max_eq_left (neg_nonneg.mpr hu'),
        min_eq_right ht,min_eq_left (neg_nonneg.mpr hu'),zero_add,mul_zero,sub_zero,neg_mul,
        abs_of_nonneg ht,abs_of_nonpos hu',add_comm t (-u),mul_assoc] using hh
  · have ht' : t ≤ 0 := le_of_not_ge ht
    by_cases hu : 0 ≤ u
    · have hh := marked_direct_opposite_recipient_pair_limit p (-t) u hp (neg_nonneg.mpr ht') hu
        m N hm hN k l
      simp only [neg_div,sub_neg_eq_add] at hh
      simpa only [markedDirectionalOverlap,max_eq_right ht',max_eq_left hu,
        max_eq_left (neg_nonneg.mpr ht'),max_eq_right (neg_nonpos.mpr hu),
        min_eq_left hu,min_eq_right (neg_nonneg.mpr ht'),zero_add,mul_zero,sub_zero,neg_mul,
        abs_of_nonpos ht',abs_of_nonneg hu,mul_assoc] using hh
    · have hu' : u ≤ 0 := le_of_not_ge hu
      have hh := hleft (-t) (-u) (neg_nonneg.mpr ht') (neg_nonneg.mpr hu') k l
      simp only [neg_div,sub_neg_eq_add] at hh
      simpa only [markedDirectionalOverlap,max_eq_right ht',max_eq_right hu',
        max_eq_left (neg_nonneg.mpr ht'),max_eq_left (neg_nonneg.mpr hu'),min_self,
        zero_add,abs_of_nonpos ht',abs_of_nonpos hu'] using hh

end AronowAudit.P001.TailA
