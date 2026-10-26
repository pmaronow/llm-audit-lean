import AronowAudit.P037.P037_Network
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact finite-support proof of P037-T35 using intersections and histograms. -/
namespace AronowAudit.P037.Wave1
open scoped BigOperators
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- Splitting a fixed-size subset into its intersection and its remainder. -/
lemma t35r2_intersection_count {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (m k : ℕ) (hk : k ≤ m) :
    ((Finset.univ.powersetCard m).filter (fun a => (a ∩ s).card = k)).card =
      (Nat.choose s.card k) * (Nat.choose (Finset.univ \ s).card (m-k)) := by
  rw [← Finset.card_powersetCard, ← Finset.card_powersetCard, ← Finset.card_product]
  apply Finset.card_bij (fun a _ => (a ∩ s, a \ s))
  · intro a ha
    rcases Finset.mem_filter.mp ha with ⟨ha, hak⟩
    have ham := (Finset.mem_powersetCard.mp ha).2
    simp only [Finset.mem_product, Finset.mem_powersetCard]
    refine ⟨⟨Finset.inter_subset_right, hak⟩, ⟨?_, ?_⟩⟩
    · intro x hx
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
    · rw [Finset.card_sdiff, ham, Finset.inter_comm s a, hak]
  · intro a ha b hb hab
    have h₁ := congrArg Prod.fst hab
    have h₂ := congrArg Prod.snd hab
    change a ∩ s = b ∩ s at h₁
    change a \ s = b \ s at h₂
    calc
      a = (a \ s) ∪ (a ∩ s) := (Finset.sdiff_union_inter a s).symm
      _ = (b \ s) ∪ (b ∩ s) := by rw [h₁, h₂]
      _ = b := Finset.sdiff_union_inter b s
  · rintro ⟨u,v⟩ huv
    rcases Finset.mem_product.mp huv with ⟨hu,hv⟩
    rcases Finset.mem_powersetCard.mp hu with ⟨hus,huk⟩
    rcases Finset.mem_powersetCard.mp hv with ⟨hvs,hvk⟩
    have hdis : Disjoint u v := by
      apply Finset.disjoint_left.mpr
      intro x hxu hxv
      exact (Finset.mem_sdiff.mp (hvs hxv)).2 (hus hxu)
    have hinter : (u ∪ v) ∩ s = u := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_union]
      constructor
      · rintro ⟨hxu | hxv, hxs⟩
        · exact hxu
        · exact False.elim ((Finset.mem_sdiff.mp (hvs hxv)).2 hxs)
      · intro hxu
        exact ⟨Or.inl hxu,hus hxu⟩
    have hdiff : (u ∪ v) \ s = v := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨hxu | hxv, hxs⟩
        · exact False.elim (hxs (hus hxu))
        · exact hxv
      · intro hxv
        exact ⟨Or.inr hxv,(Finset.mem_sdiff.mp (hvs hxv)).2⟩
    refine ⟨u ∪ v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, ?_⟩
      · rw [Finset.card_union_of_disjoint hdis, huk, hvk]
        omega
      · rw [hinter,huk]
    · exact Prod.ext hinter hdiff

lemma t35r2_partner_involutive : Function.Involutive partner := by
  rintro ⟨b,t⟩
  cases t <;> rfl

def t35r2_good (z : Finset (Fin 5 × Bool)) : Finset (Fin 5 × Bool) :=
  z.image partner

lemma t35r2_mem_good (z : Finset (Fin 5 × Bool)) (i : Fin 5 × Bool) :
    i ∈ t35r2_good z ↔ partner i ∈ z := by
  constructor
  · intro hi
    obtain ⟨j,hj,hji⟩ := Finset.mem_image.mp hi
    rw [← hji, t35r2_partner_involutive]
    exact hj
  · intro hi
    exact Finset.mem_image.mpr ⟨partner i,hi,t35r2_partner_involutive i⟩

lemma t35r2_good_card (z : Finset (Fin 5 × Bool)) : (t35r2_good z).card = z.card :=
  Finset.card_image_of_injective _ t35r2_partner_involutive.injective

lemma t35r2_stat_card (a z : Finset (Fin 5 × Bool)) (hz : z.card = 5) :
    pairedStatistic a (directOnly z) =
      (2*((a ∩ t35r2_good z).card : ℝ)-5)/5 := by
  have hfilter (s : Finset (Fin 5 × Bool)) :
      s.filter (fun i => partner i ∈ z) = s ∩ t35r2_good z := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_inter,t35r2_mem_good]
  have hdiff : (Finset.univ \ a) ∩ t35r2_good z = t35r2_good z \ a := by
    ext i
    simp only [Finset.mem_inter,Finset.mem_sdiff,Finset.mem_univ,true_and]
    exact and_comm
  have hcard := Finset.card_sdiff_add_card_inter (t35r2_good z) a
  rw [Finset.inter_comm, t35r2_good_card, hz] at hcard
  have hreal : ((t35r2_good z \ a).card : ℝ) + ((a ∩ t35r2_good z).card : ℝ) = 5 := by
    exact_mod_cast hcard
  simp only [pairedStatistic,directOnly,Finset.sum_boole,hfilter,hdiff]
  linarith

lemma t35r2_supported_card (z : Finset (Fin 5 × Bool)) :
    z ∈ pairedSupport ↔ z.card = 5 := by
  simp [pairedSupport]

lemma t35r2_histogram (z : Finset (Fin 5 × Bool)) (hz : z ∈ pairedSupport)
    (k : Fin 6) :
    (pairedSupport.filter (fun a =>
      pairedStatistic a (directOnly z) = ((2*(k.val:ℝ)-5)/5))).card =
      (Nat.choose 5 k.val)^2 := by
  have hzc := t35r2_supported_card z |>.mp hz
  have heq : pairedSupport.filter (fun a =>
      pairedStatistic a (directOnly z) = ((2*(k.val:ℝ)-5)/5)) =
      pairedSupport.filter (fun a => (a ∩ t35r2_good z).card = k.val) := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha,h⟩
      refine ⟨ha, ?_⟩
      rw [t35r2_stat_card a z hzc] at h
      have h' : ((a ∩ t35r2_good z).card : ℝ) = k.val := by linarith
      exact_mod_cast h'
    · rintro ⟨ha,h⟩
      exact ⟨ha,by rw [t35r2_stat_card a z hzc,h]⟩
  rw [heq]
  change ((Finset.univ.powersetCard 5).filter _).card = _
  rw [t35r2_intersection_count _ _ _ (by omega), t35r2_good_card, hzc]
  have hcomp : (Finset.univ \ t35r2_good z).card = 5 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,t35r2_good_card,hzc]
  rw [hcomp, Nat.choose_symm (by omega)]
  ring

/-- The whole permutation tail, obtained by summing the six histogram cells. -/
lemma t35r2_tail_count (z : Finset (Fin 5 × Bool)) (hz : z ∈ pairedSupport) (q : ℝ) :
    (pairedSupport.filter (fun a => |pairedStatistic a (directOnly z)| ≥ q)).card =
      ∑ k : Fin 6, if |(2*(k.val:ℝ)-5)/5| ≥ q then (Nat.choose 5 k.val)^2 else 0 := by
  have hzc := (t35r2_supported_card z).mp hz
  let f (a : Finset (Fin 5 × Bool)) : Fin 6 :=
    ⟨(a ∩ t35r2_good z).card, by
      have h := Finset.card_le_card (s := a ∩ t35r2_good z) Finset.inter_subset_right
      rw [t35r2_good_card,hzc] at h
      omega⟩
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
    (fun a _ => Finset.mem_univ (f a))]
  apply Finset.sum_congr rfl
  intro k _
  have heq :
      (pairedSupport.filter (fun a => |pairedStatistic a (directOnly z)| ≥ q)).filter
        (fun a => f a = k) =
      if |(2*(k.val:ℝ)-5)/5| ≥ q then
        pairedSupport.filter (fun a => pairedStatistic a (directOnly z) =
          (2*(k.val:ℝ)-5)/5) else ∅ := by
    ext a
    have hiff : f a = k ↔ pairedStatistic a (directOnly z) = (2*(k.val:ℝ)-5)/5 := by
      rw [t35r2_stat_card a z hzc]
      constructor
      · intro h
        have h' := congrArg Fin.val h
        change (a ∩ t35r2_good z).card = k.val at h'
        rw [h']
      · intro h
        apply Fin.ext
        change (a ∩ t35r2_good z).card = k.val
        have h' : ((a ∩ t35r2_good z).card : ℝ) = k.val := by linarith
        exact_mod_cast h'
    by_cases hq : |(2*(k.val:ℝ)-5)/5| ≥ q
    · simp only [hq,ite_true,Finset.mem_filter,hiff]
      constructor
      · rintro ⟨⟨ha,_⟩,h⟩
        exact ⟨ha,h⟩
      · rintro ⟨ha,h⟩
        exact ⟨⟨ha,by rw [h]; exact hq⟩,h⟩
    · simp only [hq,ite_false,Finset.mem_filter,Finset.notMem_empty,hiff,iff_false]
      rintro ⟨⟨_,h⟩,h'⟩
      exact hq (by rwa [h'] at h)
  rw [heq]
  split_ifs <;> simp only [t35r2_histogram z hz k,Finset.card_empty]

/-- The self-intersection contains both members of every fully selected pair. -/
lemma t35r2_self_intersection (z : Finset (Fin 5 × Bool)) :
    (z ∩ t35r2_good z).card =
      2 * (Finset.univ.filter (fun b : Fin 5 => (b,false) ∈ z ∧ (b,true) ∈ z)).card := by
  have hf : z ∩ t35r2_good z = Finset.univ.filter
      (fun i : Fin 5 × Bool => i ∈ z ∧ partner i ∈ z) := by
    ext i
    simp [t35r2_mem_good]
  rw [hf]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, partner, Bool.not_true, Bool.not_false]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h0 : (b,false) ∈ z <;> by_cases h1 : (b,true) ∈ z <;> simp [h0,h1]

/-- Empty self-intersection is equivalent to selecting one member of each pair. -/
lemma t35r2_split_iff (z : Finset (Fin 5 × Bool)) (hz : z.card = 5) :
    (∀ b : Fin 5, ((b,false) ∈ z ↔ (b,true) ∉ z)) ↔
      (z ∩ t35r2_good z).card = 0 := by
  constructor
  · intro h
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    rintro ⟨b,t⟩ hi
    rcases Finset.mem_inter.mp hi with ⟨hi,hj⟩
    rw [t35r2_mem_good] at hj
    cases t
    · exact (h b).mp hi hj
    · exact (h b).mp hj hi
  · intro hc
    have hsub : t35r2_good z ⊆ Finset.univ \ z := by
      intro i hi
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
      intro hiz
      have : i ∈ z ∩ t35r2_good z := Finset.mem_inter.mpr ⟨hiz,hi⟩
      rw [Finset.card_eq_zero.mp hc] at this
      exact Finset.notMem_empty _ this
    have heq : t35r2_good z = Finset.univ \ z := by
      apply Finset.eq_of_subset_of_card_le hsub
      simp [Finset.card_sdiff_of_subset (Finset.subset_univ z), t35r2_good_card, hz]
    intro b
    have h := congrArg (fun s : Finset (Fin 5 × Bool) => (b,true) ∈ s) heq
    simpa [t35r2_mem_good, partner] using (Iff.of_eq h)

/-- The three possible self-intersection sizes determine the exact p-value. -/
lemma t35r2_pvalue_classes (z : Finset (Fin 5 × Bool)) (hz : z ∈ pairedSupport) :
    ((z ∩ t35r2_good z).card = 0 ∧ pairedPValue z = 1/126) ∨
    ((z ∩ t35r2_good z).card = 2 ∧ pairedPValue z = 1) ∨
    ((z ∩ t35r2_good z).card = 4 ∧ pairedPValue z = 13/63) := by
  have hzc := (t35r2_supported_card z).mp hz
  have hle := Finset.card_le_card (s := z ∩ t35r2_good z) Finset.inter_subset_left
  rw [hzc] at hle
  have heven := t35r2_self_intersection z
  have hc : (z ∩ t35r2_good z).card = 0 ∨
      (z ∩ t35r2_good z).card = 2 ∨ (z ∩ t35r2_good z).card = 4 := by omega
  have hp : pairedPValue z =
      (∑ k : Fin 6, if |(2*(k.val:ℝ)-5)/5| ≥
        |(2*((z ∩ t35r2_good z).card:ℝ)-5)/5|
        then (Nat.choose 5 k.val)^2 else 0 : ℕ) / (252:ℝ) := by
    unfold pairedPValue
    rw [t35r2_tail_count z hz, t35r2_stat_card z z hzc]
  rcases hc with hc | hc | hc
  · left
    refine ⟨hc, ?_⟩
    rw [hp,hc]
    norm_num [Fin.sum_univ_succ, Nat.choose]
  · right; left
    refine ⟨hc, ?_⟩
    rw [hp,hc]
    norm_num [Fin.sum_univ_succ, Nat.choose]
  · right; right
    refine ⟨hc, ?_⟩
    rw [hp,hc]
    norm_num [Fin.sum_univ_succ, Nat.choose]

lemma t35r2_split_pvalue (z : Finset (Fin 5 × Bool)) (hz : z ∈ pairedSupport)
    (hs : ∀ b : Fin 5, ((b,false) ∈ z ↔ (b,true) ∉ z)) :
    pairedPValue z = 1/126 := by
  have hc := (t35r2_split_iff z ((t35r2_supported_card z).mp hz)).mp hs
  rcases t35r2_pvalue_classes z hz with h | h | h
  · exact h.2
  · omega
  · omega

lemma t35r2_nonsplit_pvalue (z : Finset (Fin 5 × Bool)) (hz : z ∈ pairedSupport)
    (hs : ¬ (∀ b : Fin 5, ((b,false) ∈ z ↔ (b,true) ∉ z))) :
    13/63 ≤ pairedPValue z := by
  have hc : (z ∩ t35r2_good z).card ≠ 0 :=
    fun h => hs ((t35r2_split_iff z ((t35r2_supported_card z).mp hz)).mpr h)
  rcases t35r2_pvalue_classes z hz with h | h | h
  · exact False.elim (hc h.1)
  · rw [h.2]; norm_num
  · rw [h.2]

/-- A function chooses one of the two members of each reciprocal pair. -/
def t35r2_choice (f : Fin 5 → Bool) : Finset (Fin 5 × Bool) :=
  Finset.univ.image (fun b => (b,f b))

lemma t35r2_mem_choice (f : Fin 5 → Bool) (b : Fin 5) (t : Bool) :
    (b,t) ∈ t35r2_choice f ↔ t = f b := by
  simp [t35r2_choice, eq_comm]

lemma t35r2_choice_card (f : Fin 5 → Bool) : (t35r2_choice f).card = 5 := by
  rw [t35r2_choice, Finset.card_image_of_injective]
  · simp
  · intro a b h
    exact congrArg Prod.fst h

lemma t35r2_choice_split (f : Fin 5 → Bool) :
    ∀ b : Fin 5, ((b,false) ∈ t35r2_choice f ↔ (b,true) ∉ t35r2_choice f) := by
  intro b
  simp only [t35r2_mem_choice]
  cases f b <;> simp

lemma t35r2_split_card :
    (pairedSupport.filter (fun z =>
      ∀ b : Fin 5, ((b,false) ∈ z ↔ (b,true) ∉ z))).card = 32 := by
  have heq : (Finset.univ : Finset (Fin 5 → Bool)).card = 32 := by
    norm_num [Fintype.card_fun]
  rw [← heq]
  symm
  apply Finset.card_bij (fun f _ => t35r2_choice f)
  · intro f _
    exact Finset.mem_filter.mpr
      ⟨(t35r2_supported_card _).mpr (t35r2_choice_card f), t35r2_choice_split f⟩
  · intro f _ g _ h
    funext b
    have hb : (b,f b) ∈ t35r2_choice g := by
      rw [← h]; exact (t35r2_mem_choice _ _ _).mpr rfl
    exact (t35r2_mem_choice _ _ _).mp hb
  · intro z hz
    have hs := (Finset.mem_filter.mp hz).2
    let f : Fin 5 → Bool := fun b => if (b,false) ∈ z then false else true
    refine ⟨f, Finset.mem_univ _, ?_⟩
    ext ⟨b,t⟩
    simp only [t35r2_mem_choice]
    dsimp only [f]
    by_cases hb : (b,false) ∈ z
    · have ht := (hs b).mp hb
      cases t <;> simp [hb, ht]
    · have ht : (b,true) ∈ z := by by_contra h; exact hb ((hs b).mpr h)
      cases t <;> simp [hb, ht]

lemma t35r2_rejection_card :
    (pairedSupport.filter (fun z => pairedPValue z < 1/100)).card = 32 := by
  have heq : pairedSupport.filter (fun z => pairedPValue z < 1/100) =
      pairedSupport.filter (fun z =>
        ∀ b : Fin 5, ((b,false) ∈ z ↔ (b,true) ∉ z)) := by
    apply Finset.filter_congr
    intro z hz
    constructor
    · intro hp
      by_contra hs
      have := t35r2_nonsplit_pvalue z hz hs
      linarith
    · intro hs
      rw [t35r2_split_pvalue z hz hs]
      norm_num
  rw [heq, t35r2_split_card]

/-- The two assignments which select the same side in all four blocks. -/
def t35r2_four_side (t : Bool) : Finset (Fin 4 × (Fin 5 × Bool)) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ {t})

def t35r2_four_support : Finset (Finset (Fin 4 × (Fin 5 × Bool))) :=
  Finset.univ.powerset.filter (fun z =>
    ∀ h, (z.filter (fun i => i.1=h)).card=5)

noncomputable def t35r2_four_stat (z : Finset (Fin 4 × (Fin 5 × Bool))) : ℝ :=
  (∑ i ∈ z, if (partner i.2).2=false then (1:ℝ) else 0)/20 -
  (∑ i ∈ Finset.univ \ z, if (partner i.2).2=false then (1:ℝ) else 0)/20

lemma t35r2_four_side_card (t : Bool) : (t35r2_four_side t).card = 20 := by
  simp [t35r2_four_side]

lemma t35r2_four_side_supported (t : Bool) :
    t35r2_four_side t ∈ t35r2_four_support := by
  simp only [t35r2_four_support, Finset.mem_filter, Finset.mem_powerset,
    Finset.subset_univ, true_and]
  intro h
  have heq : (t35r2_four_side t).filter (fun i => i.1=h) =
      {h} ×ˢ (Finset.univ ×ˢ {t}) := by
    ext ⟨h',b,t'⟩
    simp [t35r2_four_side, and_comm, eq_comm]
  rw [heq]
  simp

lemma t35r2_four_supported_card (z : Finset (Fin 4 × (Fin 5 × Bool)))
    (hz : z ∈ t35r2_four_support) : z.card = 20 := by
  have hb := (Finset.mem_filter.mp hz).2
  calc
    z.card = ∑ h : Fin 4, (z.filter (fun i => i.1=h)).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ = ∑ _h : Fin 4, 5 := by
      apply Finset.sum_congr rfl
      intro h _
      exact hb h
    _ = 20 := by norm_num

lemma t35r2_four_complement :
    Finset.univ \ t35r2_four_side true = t35r2_four_side false := by
  ext ⟨h,b,t⟩
  cases t <;> simp [t35r2_four_side]

lemma t35r2_four_sides_disjoint :
    t35r2_four_side false ∩ t35r2_four_side true = ∅ := by
  ext ⟨h,b,t⟩
  cases t <;> simp [t35r2_four_side]

lemma t35r2_four_stat_card (z : Finset (Fin 4 × (Fin 5 × Bool))) :
    t35r2_four_stat z =
      (2*((z ∩ t35r2_four_side true).card:ℝ)-20)/20 := by
  have hs (i : Fin 4 × (Fin 5 × Bool)) :
      (if (partner i.2).2=false then (1:ℝ) else 0) =
        (if i.2.2=true then (1:ℝ) else 0) := by
    rcases i with ⟨h,b,t⟩
    cases t <;> rfl
  have hf (a : Finset (Fin 4 × (Fin 5 × Bool))) :
      a.filter (fun i => i.2.2=true) = a ∩ t35r2_four_side true := by
    ext ⟨h,b,t⟩
    simp [t35r2_four_side]
  have hd : (Finset.univ \ z) ∩ t35r2_four_side true =
      t35r2_four_side true \ z := by
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact and_comm
  have hc := Finset.card_sdiff_add_card_inter (t35r2_four_side true) z
  rw [Finset.inter_comm, t35r2_four_side_card] at hc
  have hcr : ((t35r2_four_side true \ z).card:ℝ) +
      ((z ∩ t35r2_four_side true).card:ℝ) = 20 := by exact_mod_cast hc
  simp only [t35r2_four_stat, hs, Finset.sum_boole, hf, hd]
  linarith

/-- With twenty selected origins, the absolute maximum forces an entire side. -/
lemma t35r2_four_extreme (z : Finset (Fin 4 × (Fin 5 × Bool))) (hz : z.card=20) :
    |t35r2_four_stat z| ≥ 1 ↔
      z=t35r2_four_side true ∨ z=t35r2_four_side false := by
  have hc := Finset.card_le_card (s := z ∩ t35r2_four_side true) Finset.inter_subset_right
  rw [t35r2_four_side_card] at hc
  have hcr : ((z ∩ t35r2_four_side true).card:ℝ) ≤ 20 := by exact_mod_cast hc
  have hn : (0:ℝ) ≤ (z ∩ t35r2_four_side true).card := Nat.cast_nonneg _
  constructor
  · intro ht
    rw [t35r2_four_stat_card] at ht
    have he : (z ∩ t35r2_four_side true).card=0 ∨
        (z ∩ t35r2_four_side true).card=20 := by
      rcases le_total ((2*((z ∩ t35r2_four_side true).card:ℝ)-20)/20) 0 with h | h
      · rw [abs_of_nonpos h] at ht
        left
        have : ((z ∩ t35r2_four_side true).card:ℝ)=0 := by linarith
        exact_mod_cast this
      · rw [abs_of_nonneg h] at ht
        right
        have : ((z ∩ t35r2_four_side true).card:ℝ)=20 := by linarith
        exact_mod_cast this
    rcases he with he | he
    · right
      have hsub : z ⊆ Finset.univ \ t35r2_four_side true := by
        intro i hi
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, ?_⟩
        intro hj
        have : i ∈ z ∩ t35r2_four_side true := Finset.mem_inter.mpr ⟨hi,hj⟩
        rw [Finset.card_eq_zero.mp he] at this
        exact Finset.notMem_empty _ this
      rw [t35r2_four_complement] at hsub
      exact Finset.eq_of_subset_of_card_le hsub (by rw [hz,t35r2_four_side_card])
    · left
      have hi : z ∩ t35r2_four_side true = t35r2_four_side true :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          (by rw [he,t35r2_four_side_card])
      have hsub : t35r2_four_side true ⊆ z := by
        rw [← hi]
        exact Finset.inter_subset_left
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [hz,t35r2_four_side_card])).symm
  · rintro (rfl | rfl)
    · rw [t35r2_four_stat_card, Finset.inter_self, t35r2_four_side_card]
      norm_num
    · rw [t35r2_four_stat_card, t35r2_four_sides_disjoint]
      norm_num

lemma t35r2_four_tail_card :
    (t35r2_four_support.filter (fun z => |t35r2_four_stat z| ≥ 1)).card = 2 := by
  have heq : t35r2_four_support.filter (fun z => |t35r2_four_stat z| ≥ 1) =
      {t35r2_four_side true, t35r2_four_side false} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz,ht⟩
      exact (t35r2_four_extreme z (t35r2_four_supported_card z hz)).mp ht
    · rintro (rfl | rfl)
      · exact ⟨t35r2_four_side_supported true,
          (t35r2_four_extreme _ (t35r2_four_side_card true)).mpr (Or.inl rfl)⟩
      · exact ⟨t35r2_four_side_supported false,
          (t35r2_four_extreme _ (t35r2_four_side_card false)).mpr (Or.inr rfl)⟩
  have hne : t35r2_four_side true ≠ t35r2_four_side false := by
    intro h
    have hi : ((0:Fin 4),((0:Fin 5),true)) ∈ t35r2_four_side false := by
      rw [← h]
      simp [t35r2_four_side]
    simpa [t35r2_four_side] using hi
  rw [heq, Finset.card_pair hne]

lemma t35r2_observed_supported : pairedObserved ∈ pairedSupport := by
  apply (t35r2_supported_card _).mpr
  norm_num [pairedObserved]

lemma t35r2_observed_split :
    ∀ b : Fin 5, ((b,false) ∈ pairedObserved ↔ (b,true) ∉ pairedObserved) := by
  intro b
  fin_cases b <;> norm_num [pairedObserved]

lemma t35r2_observed_stat :
    pairedStatistic pairedObserved (directOnly pairedObserved) = -1 := by
  have hc := (t35r2_supported_card _).mp t35r2_observed_supported
  have hs := (t35r2_split_iff pairedObserved hc).mp t35r2_observed_split
  rw [t35r2_stat_card _ _ hc, hs]
  norm_num

theorem direct_effect_permutation_counterexample_proof :
    pairedSupport.card=252 ∧ pairedObserved∈pairedSupport ∧
    pairedStatistic pairedObserved (directOnly pairedObserved)=-1 ∧
    (∀ k : Fin 6, (pairedSupport.filter (fun z =>
      pairedStatistic z (directOnly pairedObserved)=((2*(k.val:ℝ)-5)/5))).card=
      (Nat.choose 5 k.val)^2) ∧
    pairedPValue pairedObserved=1/126 ∧ (1/126:ℝ)<1/100 ∧
    (∀ z ∈ pairedSupport,
      (∀ b : Fin 5, ((b,false)∈z ↔ (b,true)∉z)) → pairedPValue z=1/126) ∧
    (∀ z ∈ pairedSupport,
      ¬(∀ b : Fin 5, ((b,false)∈z ↔ (b,true)∉z)) → 13/63≤pairedPValue z) ∧
    ((pairedSupport.filter (fun z => pairedPValue z<1/100)).card:ℝ)/252=8/63 ∧
    (let support4 := Finset.univ.powerset.filter (fun z : Finset (Fin 4 × (Fin 5 × Bool)) =>
      ∀ h, (z.filter (fun i => i.1=h)).card=5)
     let Y := fun i : Fin 4 × (Fin 5 × Bool) => if i.2.2=false then (1:ℝ) else 0
     let stat := fun z : Finset (Fin 4 × (Fin 5 × Bool)) =>
      (∑ i ∈ z, Y (i.1,partner i.2))/20-
      (∑ i ∈ Finset.univ \ z, Y (i.1,partner i.2))/20
     ((support4.filter (fun z => |stat z| ≥ 1)).card:ℝ)/(252:ℝ)^4=2/(252:ℝ)^4) := by
  refine ⟨?_, t35r2_observed_supported, t35r2_observed_stat,
    t35r2_histogram pairedObserved t35r2_observed_supported,
    t35r2_split_pvalue pairedObserved t35r2_observed_supported t35r2_observed_split,
    by norm_num, t35r2_split_pvalue, t35r2_nonsplit_pvalue, ?_, ?_⟩
  · norm_num [pairedSupport, Finset.card_powersetCard, Nat.choose]
  · rw [t35r2_rejection_card]
    norm_num
  · change ((t35r2_four_support.filter (fun z => |t35r2_four_stat z| ≥ 1)).card:ℝ) /
        (252:ℝ)^4 = 2/(252:ℝ)^4
    rw [t35r2_four_tail_card]
    norm_num only [Nat.cast_ofNat]

end AronowAudit.P037.Wave1
