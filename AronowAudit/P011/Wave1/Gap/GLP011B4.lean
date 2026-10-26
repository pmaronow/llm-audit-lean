import AronowAudit.P011.P011_BlockOLSCompletion
import AronowAudit.P011.P011_ExpectationCompletion
import AronowAudit.P011.Wave1.Gap.GP011B3

namespace AronowAudit.P011.Wave1
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
local instance star_nullSingleton : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1:NNReal) ≠ 0)

@[simp] lemma star_family_model (upper : Bool) (k : ℕ) :
    (starFamily upper).model k = starModel upper (k+1) := rfl
@[simp] lemma star_family_size (upper : Bool) (k : ℕ) :
    (starFamily upper).size k = 4*(k+1) := rfl

abbrev star_Source := (Fin 3 → Fin 4) × Fin 48

def star_mu (upper : Bool) : Fin 4 → ℝ :=
  if upper then ![1/2,3/4,1/4,1/2] else ![3/4,1/4,1/4,1/4]

def star_C (upper : Bool) : Matrix (Fin 4) (Fin 4) ℝ :=
  if upper then
    ![![1/4,1/64,1/64,1/48], ![1/64,3/16,0,0],
      ![1/64,0,3/16,0], ![1/48,0,0,1/4]]
  else (3/16 : ℝ) • 1 + (1/64 : ℝ) • adjacency starGraph

def star_source (upper : Bool) (K : ℕ) (u : Fin K → star_Source) : Fin (4*K) → ℝ :=
  fun i => starBlock upper (u (blockIndex (by decide) i)).1
    (u (blockIndex (by decide) i)).2 (localIndex (by decide) i)

lemma star_weighted (upper : Bool) (K : ℕ) (y : Fin (4*K) → ℝ) :
    weighted (starModel upper K) y = y := by
  ext i
  simp [weighted, starModel]

lemma star_memLp (upper : Bool) (K : ℕ) (i : Fin (4*K)) :
    MemLp (fun y : Fin (4*K) → ℝ => y i) 2 (starModel upper K).law :=
  NewFiniteCompletion.finite_memLp (star_source upper K) _ (measurable_pi_apply i) 2

lemma star_binary_block (upper : Bool) (a : star_Source) (r : Fin 4) :
    starBlock upper a.1 a.2 r = 0 ∨ starBlock upper a.1 a.2 r = 1 := by
  have hl (j : Fin 3) : starLeaves upper a.1 j = 0 ∨ starLeaves upper a.1 j = 1 := by
    unfold starLeaves
    split_ifs <;> simp
  fin_cases r
  · dsimp only [starBlock]
    split_ifs <;> simp
  · exact hl 0
  · exact hl 1
  · exact hl 2

lemma star_binary (upper : Bool) (K : ℕ) :
    ∀ᵐ y ∂(starModel upper K).law, ∀ i, y i = 0 ∨ y i = 1 := by
  change ∀ᵐ y ∂uniformLaw (star_source upper K), _
  rw [uniformLaw, ← PMF.toMeasure_map (star_source upper K) (PMF.uniformOfFintype _)
    (measurable_of_finite _)]
  apply (ae_map_iff (measurable_of_finite _).aemeasurable (by measurability)).mpr
  exact Eventually.of_forall fun u i => star_binary_block upper _ _

lemma star_mean (upper : Bool) (K : ℕ) (i : Fin (4*K)) :
    expectation (starModel upper K) (fun y => y i) = star_mu upper (localIndex (by decide) i) :=
  BlockOLSCompletion.star_coordinate_mean upper K i

/-- The heterogeneous coordinates are the three leaf draws and the centre draw. -/
def star_Atom : Fin 3 ⊕ Unit → Type
  | .inl _ => Fin 4
  | .inr _ => Fin 48

instance star_atomFintype (a : Fin 3 ⊕ Unit) : Fintype (star_Atom a) := by
  cases a <;> dsimp [star_Atom] <;> infer_instance
instance star_atomInhabited (a : Fin 3 ⊕ Unit) : Inhabited (star_Atom a) := by
  cases a <;> dsimp [star_Atom] <;> infer_instance
instance star_atomMeasurable (a : Fin 3 ⊕ Unit) : MeasurableSpace (star_Atom a) := ⊤
instance star_atomSingleton (a : Fin 3 ⊕ Unit) : MeasurableSingletonClass (star_Atom a) := ⟨fun _ => trivial⟩

def star_flatEquiv (K : ℕ) :
    (∀ p : Fin K × (Fin 3 ⊕ Unit), star_Atom p.2) ≃ (Fin K → star_Source) where
  toFun u b := (fun j => u (b, .inl j), u (b, .inr ()))
  invFun u p := match p.2 with
    | .inl j => (u p.1).1 j
    | .inr _ => (u p.1).2
  left_inv u := by funext p; rcases p with ⟨b, j | ⟨⟩⟩ <;> rfl
  right_inv u := by rfl

lemma star_uniform_pi {I : Type} [Fintype I] [DecidableEq I] (A : I → Type)
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSingletonClass (A i)] :
    (PMF.uniformOfFintype (∀ i, A i)).toMeasure =
      Measure.pi (fun i => (PMF.uniformOfFintype (A i)).toMeasure) := by
  classical
  apply Measure.ext_of_singleton
  intro u
  simp [Measure.pi_singleton, PMF.toMeasure_apply_singleton,
    PMF.uniformOfFintype_apply, Fintype.card_pi, Nat.cast_prod]
  rw [ENNReal.prod_inv_distrib]
  exact fun _ _ _ _ _ => Or.inr (by simp)

lemma star_product_indep {I : Type} [Fintype I] [DecidableEq I] (A : I → Type)
    [∀ i, Fintype (A i)] [∀ i, Inhabited (A i)]
    [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSingletonClass (A i)]
    {β γ : Type} [MeasurableSpace β] [MeasurableSpace γ]
    (S T : Finset I) (hST : Disjoint S T)
    (f : (∀ i, A i) → β) (g : (∀ i, A i) → γ)
    (hf : ∀ u v, (∀ p ∈ S, u p = v p) → f u = f v)
    (hg : ∀ u v, (∀ p ∈ T, u p = v p) → g u = g v) :
    IndepFun f g (PMF.uniformOfFintype (∀ i, A i)).toMeasure := by
  classical
  rw [star_uniform_pi]
  have hc : iIndepFun (fun i (u : ∀ i, A i) => u i)
      (Measure.pi (fun i => (PMF.uniformOfFintype (A i)).toMeasure)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hr := hc.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  let fill (U : Finset I) (u : ∀ p : U, A p.val) : ∀ i, A i :=
    fun p => if hp : p ∈ U then u ⟨p, hp⟩ else default
  have hleft : (fun u => f (fill S (fun p : S => u p.val))) = f := by
    funext u
    apply hf
    intro p hp
    simp [fill, hp]
  have hright : (fun u => g (fill T (fun p : T => u p.val))) = g := by
    funext u
    apply hg
    intro p hp
    simp [fill, hp]
  have hh := hr.comp (measurable_of_finite (fun u => f (fill S u)))
    (measurable_of_finite (fun u => g (fill T u)))
  simpa only [Function.comp_def, hleft, hright] using hh

abbrev star_Axis (K : ℕ) := Fin K × (Fin 3 ⊕ Unit)
abbrev star_Flat (K : ℕ) := ∀ p : star_Axis K, star_Atom p.2

def star_uses {K : ℕ} (i : Fin (4*K)) (p : star_Axis K) : Prop :=
  blockIndex (by decide) i = p.1 ∧
    (localIndex (by decide) i = 0 ∨
      Sum.elim (fun j => localIndex (by decide) i = j.succ) (fun _ => False) p.2)

def star_sources {K : ℕ} (S : Finset (Fin (4*K))) : Finset (star_Axis K) :=
  univ.filter fun p => ∃ i ∈ S, star_uses i p

lemma star_mask (r s : Fin 4) (a : Fin 3 ⊕ Unit) :
    (r=0 ∨ Sum.elim (fun j => r=j.succ) (fun _ => False) a) →
    (s=0 ∨ Sum.elim (fun j => s=j.succ) (fun _ => False) a) →
    r=s ∨ starGraph.val r s = true := by
  rcases a with j | ⟨⟩
  · fin_cases r <;> fin_cases s <;> fin_cases j <;> norm_num [starGraph]
  · fin_cases r <;> fin_cases s <;> norm_num [starGraph]

lemma star_depends (upper : Bool) (K : ℕ) (S : Finset (Fin (4*K)))
    (u v : star_Flat K) (huv : ∀ p ∈ star_sources S, u p = v p) :
    (fun i : S => star_source upper K (star_flatEquiv K u) i.val) =
      (fun i : S => star_source upper K (star_flatEquiv K v) i.val) := by
  funext i
  have hh (a : Fin 3 ⊕ Unit)
      (ha : localIndex (by decide : 0<4) i.val = 0 ∨
        Sum.elim (fun j => localIndex (by decide) i.val = j.succ) (fun _ => False) a) :
      u (blockIndex (by decide) i.val, a) = v (blockIndex (by decide) i.val, a) := by
    apply huv
    exact mem_filter.mpr ⟨mem_univ _, i.val, i.property, rfl, ha⟩
  unfold star_source
  generalize hr : localIndex (by decide : 0<4) i.val = r
  fin_cases r
  · have hleaves : (star_flatEquiv K u (blockIndex (by decide) i.val)).1 =
        (star_flatEquiv K v (blockIndex (by decide) i.val)).1 := by
      funext j
      exact hh (.inl j) (Or.inl hr)
    have hc := hh (.inr ()) (Or.inl hr)
    change starBlock upper _ _ 0 = starBlock upper _ _ 0
    rw [hleaves]
    exact congrArg (fun a => starBlock upper _ a 0) hc
  · simpa [starBlock, starLeaves, star_flatEquiv] using
      congrArg (fun a : Fin 4 => if a.val < (if upper then 3 else 1) then (1:ℝ) else 0)
        (hh (.inl 0) (Or.inr (by simpa using hr)))
  · simpa [starBlock, starLeaves, star_flatEquiv] using
      congrArg (fun a : Fin 4 => if a.val < 1 then (1:ℝ) else 0)
        (hh (.inl 1) (Or.inr (by simpa using hr)))
  · simpa [starBlock, starLeaves, star_flatEquiv] using
      congrArg (fun a : Fin 4 => if a.val < (if upper then 2 else 1) then (1:ℝ) else 0)
        (hh (.inl 2) (Or.inr (by simpa using hr)))

lemma star_sources_disjoint (upper : Bool) (K : ℕ) (S T : Finset (Fin (4*K)))
    (hST : Disjoint S T)
    (hsep : ∀ i ∈ S, ∀ j ∈ T, (starModel upper K).G.val i j = false) :
    Disjoint (star_sources S) (star_sources T) := by
  apply disjoint_left.mpr
  intro p hpS hpT
  obtain ⟨i, hiS, hi⟩ := (mem_filter.mp hpS).2
  obtain ⟨j, hjT, hj⟩ := (mem_filter.mp hpT).2
  have hquot : i.val / 4 = j.val / 4 := congrArg Fin.val (hi.1.trans hj.1.symm)
  rcases star_mask _ _ p.2 hi.2 hj.2 with hlocal | hedge
  · have hmod : i.val % 4 = j.val % 4 := congrArg Fin.val hlocal
    have hij : i=j := Fin.ext (by omega)
    exact disjoint_left.mp hST hiS (hij.symm ▸ hjT)
  · have hg : (starModel upper K).G.val i j = true := by
      simp [starModel, blockGraph, hquot, hedge]
    have hh := hsep i hiS j hjT
    rw [hg] at hh
    cases hh

lemma star_source_map (upper : Bool) (K : ℕ) :
    (PMF.uniformOfFintype (star_Flat K)).toMeasure.map
      (star_source upper K ∘ star_flatEquiv K) = (starModel upper K).law := by
  rw [PMF.toMeasure_map _ _ (measurable_of_finite _)]
  change uniformLaw (star_source upper K ∘ star_flatEquiv K) = uniformLaw (star_source upper K)
  exact NewFiniteCompletion.uniformLaw_equiv (star_flatEquiv K) _

lemma star_pushforward {A B C D : Type} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μ : Measure A) (g : A → B)
    (hg : Measurable g) (f : B → C) (h : B → D) (hf : Measurable f) (hh : Measurable h)
    (hi : IndepFun (f ∘ g) (h ∘ g) μ) : IndepFun f h (μ.map g) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  rw [Measure.map_apply hg ((hs.preimage hf).inter (ht.preimage hh)),
    Measure.map_apply hg (hs.preimage hf), Measure.map_apply hg (ht.preimage hh)]
  simpa only [Set.preimage_inter, Set.preimage_preimage, Function.comp_def] using
    hi.measure_inter_preimage_eq_mul s t hs ht

lemma star_flat_indep (upper : Bool) (K : ℕ) (S T : Finset (Fin (4*K)))
    (hST : Disjoint S T)
    (hsep : ∀ i ∈ S, ∀ j ∈ T, (starModel upper K).G.val i j = false) :
    IndepFun
      (fun u : star_Flat K => fun i : S => star_source upper K (star_flatEquiv K u) i.val)
      (fun u : star_Flat K => fun j : T => star_source upper K (star_flatEquiv K u) j.val)
      (PMF.uniformOfFintype (star_Flat K)).toMeasure := by
  apply star_product_indep (fun p : star_Axis K => star_Atom p.2) (β := S → ℝ) (γ := T → ℝ)
    (star_sources S) (star_sources T) (star_sources_disjoint upper K S T hST hsep)
    (fun u => fun i : S => star_source upper K (star_flatEquiv K u) i.val)
    (fun u => fun j : T => star_source upper K (star_flatEquiv K u) j.val)
  · exact star_depends upper K S
  · exact star_depends upper K T

lemma star_dependency (upper : Bool) (K : ℕ) : Dependency (starModel upper K) := by
  intro S T hST hsep
  change IndepFun (fun y : Fin (4*K) → ℝ => fun i : S => y i.val) (fun y : Fin (4*K) → ℝ => fun j : T => y j.val) _
  rw [←star_source_map upper K]
  apply star_pushforward _ _ (measurable_of_finite _)
    (fun y : Fin (4*K) → ℝ => fun i : S => y i.val)
    (fun y : Fin (4*K) → ℝ => fun j : T => y j.val) (by fun_prop) (by fun_prop)
  exact star_flat_indep upper K S T hST hsep

/-- Enumerating the 64 leaf assignments, without enumerating growing block arrays. -/
def star_leafEquiv : (Fin 4 × Fin 4 × Fin 4) ≃ (Fin 3 → Fin 4) where
  toFun a := ![a.1, a.2.1, a.2.2]
  invFun u := (u 0, u 1, u 2)
  left_inv a := rfl
  right_inv u := by ext j; fin_cases j <;> rfl

def star_leafValue (upper : Bool) (u : Fin 3 → Fin 4) : Fin 4 → ℝ :=
  ![0, starLeaves upper u 0, starLeaves upper u 1, starLeaves upper u 2]

lemma star_v_pair (upper : Bool) (u : Fin 3 → Fin 4) (r s : Fin 4) :
    (∑ v : Fin 48, starBlock upper u v r * starBlock upper u v s) =
      if r=0 ∧ s=0 then (if upper then 18 else 33)+4*∑j, starLeaves upper u j
      else if r=0 then ((if upper then 18 else 33)+4*∑j,starLeaves upper u j) * star_leafValue upper u s
      else if s=0 then star_leafValue upper u r * ((if upper then 18 else 33)+4*∑j,starLeaves upper u j)
      else 48 * star_leafValue upper u r * star_leafValue upper u s := by
  have hb (v : Fin 48) : starBlock upper u v 0 * starBlock upper u v 0 = starBlock upper u v 0 := by
    rcases star_binary_block upper (u,v) 0 with h|h <;> simp [h]
  have hl (r : Fin 4) (hr : r ≠ 0) (v : Fin 48) :
      starBlock upper u v r = star_leafValue upper u r := by
    fin_cases r
    · exact (hr rfl).elim
    · rfl
    · rfl
    · rfl
  by_cases hr : r=0 <;> by_cases hs : s=0
  · subst r; subst s
    rw [if_pos ⟨rfl,rfl⟩]
    simp_rw [hb]
    exact BlockOLSCompletion.star_center_sum upper u
  · rw [if_neg (by simp [hs]), if_pos hr]
    subst r
    simp_rw [hl s hs]
    rw [←Finset.sum_mul, BlockOLSCompletion.star_center_sum]
  · rw [if_neg (by simp [hr]), if_neg hr, if_pos hs]
    subst s
    simp_rw [hl r hr]
    rw [←Finset.mul_sum, BlockOLSCompletion.star_center_sum]
  · rw [if_neg (by simp [hr]), if_neg hr, if_neg hs]
    simp_rw [hl r hr, hl s hs]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

lemma star_source_second (upper : Bool) (r s : Fin 4) :
    (∑ a : star_Source, starBlock upper a.1 a.2 r * starBlock upper a.1 a.2 s)/3072 =
      star_C upper r s + star_mu upper r * star_mu upper s := by
  rw [Fintype.sum_prod_type]
  simp_rw [star_v_pair]
  rw [←star_leafEquiv.sum_comp]
  cases upper <;> fin_cases r <;> fin_cases s <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, star_leafEquiv,
      star_leafValue, starLeaves, star_C, star_mu, adjacency, starGraph,
      Matrix.one_apply]

lemma star_pair_integral (upper : Bool) (K : ℕ) (i j : Fin (4*K))
    (hij : blockIndex (by decide : 0<4) i = blockIndex (by decide) j) :
    expectation (starModel upper K) (fun y => y i*y j) =
      star_C upper (localIndex (by decide) i) (localIndex (by decide) j) +
        star_mu upper (localIndex (by decide) i) * star_mu upper (localIndex (by decide) j) := by
  unfold expectation
  change (∫y, y i*y j ∂uniformLaw (star_source upper K)) = _
  rw [uniformLaw, ←PMF.toMeasure_map _ _ (measurable_of_finite _),
    integral_map (measurable_of_finite _).aemeasurable (by fun_prop)]
  simp only [star_source, ←hij]
  change (∫u : Fin K → star_Source,
    (fun a : star_Source => starBlock upper a.1 a.2 (localIndex (by decide) i) *
      starBlock upper a.1 a.2 (localIndex (by decide) j)) (u (blockIndex (by decide) i))
      ∂(PMF.uniformOfFintype (Fin K → star_Source)).toMeasure) = _
  rw [BlockOLSCompletion.uniform_evaluation_integral (blockIndex (by decide) i)
    (fun a : star_Source => starBlock upper a.1 a.2 (localIndex (by decide) i) *
      starBlock upper a.1 a.2 (localIndex (by decide) j))]
  norm_num only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  exact star_source_second upper _ _

lemma star_covariance (upper : Bool) (K : ℕ) (i j : Fin (4*K)) :
    covariance (starModel upper K) i j =
      if blockIndex (by decide : 0<4) i = blockIndex (by decide) j then
        star_C upper (localIndex (by decide) i) (localIndex (by decide) j) else 0 := by
  let : IsProbabilityMeasure (starModel upper K).law := (starModel upper K).probability
  by_cases h : blockIndex (by decide : 0<4) i = blockIndex (by decide) j
  · rw [if_pos h, QuadraticCompletion.covariance_eq_mathlib]
    simp only [star_weighted]
    rw [ProbabilityTheory.covariance_eq_sub (star_memLp upper K i) (star_memLp upper K j)]
    change expectation (starModel upper K) (fun y => y i*y j) -
      expectation (starModel upper K) (fun y => y i)*expectation (starModel upper K) (fun y => y j) = _
    rw [star_pair_integral upper K i j h, star_mean, star_mean]
    ring
  · rw [if_neg h]
    exact OracleCompletion.covariance_support _ (star_dependency upper K)
      (fun a => by simpa only [star_weighted] using star_memLp upper K a)
      i j (fun he => h (congrArg (blockIndex (by decide)) he)) (by
        have hq : i.val / 4 ≠ j.val / 4 := fun hq => h (Fin.ext hq)
        simp [starModel, blockGraph, hq])

lemma star_block_index {K : ℕ} (b : Fin K) (r : Fin 4) :
    blockIndex (by decide : 0<4) (StarCompletion.blockEquiv 4 K (b,r)) = b :=
  Fin.ext (StarCompletion.block_quot (by decide) (b,r))

lemma star_block_matrix {K : ℕ} (b c : Fin K) (r s : Fin 4) :
    oracleMatrix (blockGraph (by decide : 0<4) starGraph K)
      (StarCompletion.blockEquiv 4 K (b,r)) (StarCompletion.blockEquiv 4 K (c,s)) =
      if b=c then oracleMatrix starGraph r s else 0 := by
  have he : StarCompletion.blockEquiv 4 K (b,r) = StarCompletion.blockEquiv 4 K (c,s) ↔ b=c ∧ r=s := by
    rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  simp only [oracleMatrix, Matrix.add_apply, Matrix.one_apply, adjacency, blockGraph,
    StarCompletion.block_quot (by decide : 0<4), StarCompletion.block_local (by decide : 0<4), he]
  by_cases h : b=c
  · subst c; simp
  · have hv : b.val ≠ c.val := fun hv => h (Fin.ext hv)
    simp [h, hv]

lemma star_sum_block_matrix (K : ℕ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (∑ i : Fin (4*K), ∑ j : Fin (4*K),
      if blockIndex (by decide : 0<4) i = blockIndex (by decide) j then
        M (localIndex (by decide) i) (localIndex (by decide) j) else 0) =
      (K:ℝ) * ∑ r, ∑ s, M r s := by
  rw [←(StarCompletion.blockEquiv 4 K).sum_comp, Fintype.sum_prod_type]
  simp_rw [←(StarCompletion.blockEquiv 4 K).sum_comp, Fintype.sum_prod_type,
    star_block_index, StarCompletion.block_local (by decide : 0<4)]
  simp

lemma star_beta (upper : Bool) (K : ℕ) (hK : 0<K) :
    beta (starModel upper K) = if upper then 1/2 else 3/8 := by
  let : IsProbabilityMeasure (starModel upper K).law := (starModel upper K).probability
  unfold beta expectation betaHat average
  simp only [star_weighted]
  rw [integral_div, integral_finsetSum univ (fun i _ => (star_memLp upper K i).integrable (by norm_num))]
  change (∑i, expectation (starModel upper K) (fun y => y i)) / (4*K:ℕ) = _
  simp_rw [star_mean]
  rw [BlockOLSCompletion.local_sum (by decide : 0<4)]
  have hK0 : (K:ℝ) ≠ 0 := by positivity
  cases upper <;> norm_num [star_mu, Fin.sum_univ_succ] <;> field_simp <;> ring

lemma star_scaledTrue (upper : Bool) (k : ℕ) :
    scaledTrue (starFamily upper) k = if upper then 47/192 else 27/128 := by
  unfold scaledTrue
  change (4*(k+1):ℕ)*var (starModel upper (k+1)) (betaHat (starModel upper (k+1))) = _
  rw [QuadraticCompletion.beta_variance _ (fun i => by simpa only [star_weighted] using star_memLp upper (k+1) i)]
  unfold QuadraticCompletion.total
  simp_rw [star_covariance]
  rw [star_sum_block_matrix]
  have hK0 : ((k+1:ℕ):ℝ) ≠ 0 := by positivity
  cases upper <;> norm_num [star_C, adjacency, starGraph, Matrix.one_apply, Fin.sum_univ_succ] <;>
    push_cast <;> field_simp <;> ring

lemma star_covariance_primary (K : ℕ) (i j : Fin (4*K)) :
    covariance (starModel false K) i j =
      ((3/16 : ℝ) • (1 : Matrix (Fin (4*K)) (Fin (4*K)) ℝ) +
        (1/64 : ℝ) • adjacency (starModel false K).G) i j := by
  classical
  obtain ⟨⟨b,r⟩,rfl⟩ := (StarCompletion.blockEquiv 4 K).surjective i
  obtain ⟨⟨c,s⟩,rfl⟩ := (StarCompletion.blockEquiv 4 K).surjective j
  have he : StarCompletion.blockEquiv 4 K (b,r) = StarCompletion.blockEquiv 4 K (c,s) ↔ b=c ∧ r=s := by
    rw [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  rw [star_covariance]
  simp only [star_block_index, StarCompletion.block_local (by decide : 0<4), star_C,
    Bool.false_eq_true, if_false, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, adjacency, starModel, blockGraph,
    StarCompletion.block_local (by decide : 0<4), StarCompletion.block_quot (by decide : 0<4), he]
  by_cases h : b=c
  · subst c; simp
  · have hv : b.val ≠ c.val := fun hv => h (Fin.ext hv)
    simp [h, hv]

lemma star_quadratic_local (K : ℕ) (v : Fin 4 → ℝ) :
    quadratic (oracleMatrix (blockGraph (by decide : 0<4) starGraph K))
      (fun i => v (localIndex (by decide) i)) = (K:ℝ) * quadratic (oracleMatrix starGraph) v := by
  classical
  unfold quadratic
  rw [←(StarCompletion.blockEquiv 4 K).sum_comp, Fintype.sum_prod_type]
  simp_rw [←(StarCompletion.blockEquiv 4 K).sum_comp, Fintype.sum_prod_type,
    star_block_matrix, StarCompletion.block_local (by decide : 0<4)]
  have ht (b c : Fin K) (r s : Fin 4) :
      (if b=c then oracleMatrix starGraph r s else 0)*v r*v s =
        if c=b then oracleMatrix starGraph r s*v r*v s else 0 := by
    by_cases h : b=c <;> simp [h, Ne.symm, eq_comm]
  simp_rw [ht]
  simp

lemma star_meanBias (upper : Bool) (K : ℕ) (hK : 0<K) :
    meanBias (starModel upper K) = if upper then 1/32 else -3/128 := by
  have hd : delta (starModel upper K) = fun i =>
      (star_mu upper (localIndex (by decide) i) - if upper then 1/2 else 3/8) := by
    ext i
    unfold delta
    simp only [star_weighted, star_mean, star_beta upper K hK]
  unfold meanBias
  rw [hd]
  change quadratic (oracleMatrix (blockGraph (by decide) starGraph K))
    (fun i => (fun r => star_mu upper r - if upper then 1/2 else 3/8)
      (localIndex (by decide) i)) / (4*K:ℕ) = _
  rw [star_quadratic_local K (fun r => star_mu upper r - if upper then 1/2 else 3/8)]
  have hK0 : (K:ℝ) ≠ 0 := by positivity
  cases upper <;> norm_num [star_mu, quadratic, oracleMatrix, adjacency, starGraph,
    Matrix.one_apply, Fin.sum_univ_succ] <;> field_simp <;> ring

lemma star_row_covariance (upper : Bool) (K : ℕ) (i : Fin (4*K)) :
    (∑j, covariance (starModel upper K) i j) = ∑s, star_C upper (localIndex (by decide) i) s := by
  classical
  simp_rw [star_covariance]
  rw [←(StarCompletion.blockEquiv 4 K).sum_comp, Fintype.sum_prod_type]
  simp_rw [star_block_index, StarCompletion.block_local (by decide : 0<4)]
  simp [eq_comm]

lemma star_total_product (K : ℕ) :
    QuadraticCompletion.total (oracleMatrix (starModel false K).G * covariance (starModel false K)) =
      (K:ℝ)*(69/32) := by
  classical
  rw [←QuadraticCompletion.row_total_right]
  simp_rw [star_row_covariance]
  rw [←(StarCompletion.blockEquiv 4 K).sum_comp, Fintype.sum_prod_type]
  simp_rw [←(StarCompletion.blockEquiv 4 K).sum_comp, Fintype.sum_prod_type,
    StarCompletion.block_local (by decide : 0<4)]
  change (∑b : Fin K, ∑r : Fin 4, ∑c : Fin K, ∑s : Fin 4,
    (oracleMatrix (blockGraph (by decide) starGraph K)
      (StarCompletion.blockEquiv 4 K (b,r)) (StarCompletion.blockEquiv 4 K (c,s))) *
      ∑t, star_C false s t) = _
  simp_rw [star_block_matrix]
  have ht (b c : Fin K) (r s : Fin 4) :
      (if b=c then oracleMatrix starGraph r s else 0)*(∑t, star_C false s t) =
        if c=b then oracleMatrix starGraph r s*(∑t, star_C false s t) else 0 := by
    by_cases h : b=c <;> simp [h, Ne.symm, eq_comm]
  simp_rw [ht]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', mem_univ, ite_true]
  norm_num [star_C, oracleMatrix, adjacency, starGraph, Matrix.one_apply, Fin.sum_univ_succ]

lemma star_total_oracle (K : ℕ) :
    QuadraticCompletion.total (oracleMatrix (starModel false K).G) = (K:ℝ)*10 := by
  change (∑ i, ∑ j, oracleMatrix (blockGraph (by decide) starGraph K) i j) = _
  have hh := star_quadratic_local K (fun _ => 1)
  norm_num [quadratic, oracleMatrix, adjacency, starGraph, Matrix.one_apply, Fin.sum_univ_succ] at hh ⊢
  exact hh

lemma star_finite_expectation (k : ℕ) :
    expectation (starModel false (k+1)) (scaledOracle (starFamily false) k) =
      3*(64*((k+1:ℕ):ℝ)-47)/(1024*((k+1:ℕ):ℝ)) := by
  have he := ExpectationCompletion.oracle_expectation_error (by omega : 0<4*(k+1))
    (starModel false (k+1)) (star_dependency false (k+1))
    (fun i => by simpa only [star_weighted] using star_memLp false (k+1) i)
  have ht := star_scaledTrue false k
  change (4*(k+1):ℕ)*var (starModel false (k+1)) (betaHat (starModel false (k+1))) = 27/128 at ht
  have hv : var (starModel false (k+1)) (betaHat (starModel false (k+1))) =
      (27/128)/(4*(k+1):ℕ) := (eq_div_iff (by positivity)).mpr (by simpa only [mul_comm] using ht)
  rw [star_meanBias false (k+1) (by omega), star_total_product, star_total_oracle, hv] at he
  change expectation (starModel false (k+1)) (scaledOracle (starFamily false) k) -
    (4*(k+1):ℕ)*((27/128)/(4*(k+1):ℕ)) - (if false then (1/32:ℝ) else -3/128) = _ at he
  have hK0 : ((k+1:ℕ):ℝ) ≠ 0 := by positivity
  norm_num only [Bool.false_eq_true, if_false, Nat.cast_mul, Nat.cast_ofNat] at he ⊢
  field_simp at he ⊢
  nlinarith [he]

lemma star_nested (upper : Bool) : Nested (starFamily upper) := by
  constructor
  · intro k l h
    change 4*(k+1) ≤ 4*(l+1)
    omega
  · intro k
    have hk : (starFamily upper).size k ≤ (starFamily upper).size (k+1) := by
      change 4*(k+1) ≤ 4*(k+1+1)
      omega
    refine ⟨⟨Fin.castLE hk, ?_⟩, ?_⟩
    · intro i j hij
      exact Fin.ext (congrArg (fun x : Fin ((starFamily upper).size (k+1)) => x.val) hij)
    · intro i j
      rfl

lemma star_bound (upper : Bool) (K : ℕ) (hK : 0<K) :
    ∀ᵐ y ∂(starModel upper K).law, ∀i, |weighted (starModel upper K) y i - beta (starModel upper K)| ≤ 1 := by
  filter_upwards [star_binary upper K] with y hy i
  rw [star_weighted, star_beta upper K hK]
  rcases hy i with hi|hi <;> rw [hi] <;> cases upper <;> norm_num

lemma star_scaling (upper : Bool) :
    Scaling (starFamily upper) 1 3 (if upper then 47/192 else 27/128) 2 := by
  refine ⟨star_nested upper, by norm_num, by norm_num, ?_, by norm_num,
    fun k => star_dependency upper (k+1), fun k => star_bound upper (k+1) (by omega), ?_, ?_, ?_⟩
  · cases upper <;> norm_num
  · intro k i
    change (degree (blockGraph (by decide) starGraph (k+1)) i : ℝ) ≤ 3
    rw [StarCompletion.block_degree]
    generalize localIndex (by decide : 0<4) i = r
    fin_cases r <;> norm_num [degree, starGraph, Fin.sum_univ_succ]
  · change Tendsto (scaledTrue (starFamily upper)) atTop _
    have he : scaledTrue (starFamily upper) =
        fun _ => if upper then (47/192:ℝ) else 27/128 := funext (star_scaledTrue upper)
    rw [he]
    exact tendsto_const_nhds
  · intro k i
    change |(1:ℝ)|<2
    norm_num

lemma star_compatible (upper : Bool) (K : ℕ) (A : Graph (4*K)) :
    Compatible (starModel upper K).R (starModel upper K).d A ↔ A=(starModel upper K).G := by
  have hd : (starModel upper K).d = degree (starModel upper K).G := by
    ext i
    exact (StarCompletion.block_degree (by decide) starGraph i).symm
  rw [hd]
  exact saturated_graph_singleton _ _

lemma star_valid (upper : Bool) : Valid (starFamily upper) := by
  intro k
  exact (star_compatible upper (k+1) _).mpr rfl

lemma star_limit (upper : Bool) :
    InProbability (starFamily upper) (scaledOracle (starFamily upper))
      (fun _ => if upper then 53/192 else 3/16) := by
  have hc := revised_oracle_convergence (starFamily upper) 1 3
    (if upper then 47/192 else 27/128) 2 (star_scaling upper)
  have he (k : ℕ) : (starFamily upper).size k *
      var ((starFamily upper).model k) (betaHat ((starFamily upper).model k)) +
      meanBias ((starFamily upper).model k) = if upper then 53/192 else 3/16 := by
    rw [←scaledTrue, star_scaledTrue]
    change (if upper then (47/192:ℝ) else 27/128) + meanBias (starModel upper (k+1)) = _
    rw [star_meanBias upper (k+1) (by omega)]
    cases upper <;> norm_num
  intro ε hε
  have hh := hc ε hε
  simpa only [he, scaledOracle] using hh

lemma star_underestimate :
    Tendsto (fun k => probability ((starFamily false).model k)
      {y | 27/128-scaledOracle (starFamily false) k y > 3/256}) atTop (𝓝 1) := by
  let (k : ℕ) : IsProbabilityMeasure ((starFamily false).model k).law :=
    ((starFamily false).model k).probability
  have hc := star_limit false (1/512) (by norm_num)
  have hl := (tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop)).sub hc
  have hb (k : ℕ) : 1-probability ((starFamily false).model k)
      {y | |scaledOracle (starFamily false) k y-3/16| > 1/512} ≤
      probability ((starFamily false).model k)
        {y | 27/128-scaledOracle (starFamily false) k y > 3/256} := by
    have hsub : {y | |scaledOracle (starFamily false) k y-3/16| > 1/512}ᶜ ⊆
        {y | 27/128-scaledOracle (starFamily false) k y > 3/256} := by
      intro y hy
      have hh : |scaledOracle (starFamily false) k y-3/16| ≤ 1/512 := le_of_not_gt hy
      have hh' := (abs_le.mp hh).2
      change 27/128-scaledOracle (starFamily false) k y > 3/256
      linarith
    have hmeas : MeasurableSet {y | |scaledOracle (starFamily false) k y-3/16| > 1/512} := by
      unfold scaledOracle V1 centered weighted average quadratic
      measurability
    have hm := measureReal_mono (μ:=((starFamily false).model k).law) hsub
    rw [measureReal_compl hmeas] at hm
    unfold probability
    simpa only [probReal_univ] using hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hl) tendsto_const_nhds hb
  intro k
  exact measureReal_le_one

lemma star_true_error_limit (upper : Bool) :
    InProbability (starFamily upper)
      (fun k y => quadratic (oracleMatrix ((starFamily upper).model k).G)
        (fun i => y i-star_mu upper (localIndex (by decide) i)) /
          ((starFamily upper).size k:ℝ))
      (fun _ => if upper then 47/192 else 27/128) := by
  let a := fun k (i : Fin ((starFamily upper).size k)) => star_mu upper (localIndex (by decide) i)
  have hb (k : ℕ) : ∀ᵐ y ∂((starFamily upper).model k).law, ∀ i,
      |msr_shift ((starFamily upper).model k) (a k) i y| ≤ 1 := by
    filter_upwards [star_binary upper (k+1)] with y hy i
    simp only [msr_shift, star_family_model, star_weighted]
    dsimp only [a]
    generalize localIndex (by decide : 0<4) i = r
    rcases hy i with hi|hi <;> rw [hi] <;> cases upper <;> fin_cases r <;> norm_num [star_mu]
  have hc := msr_quadratic_concentration (starFamily upper) 1 3
    (if upper then 47/192 else 27/128) 2 (star_scaling upper) a 1 (by norm_num) hb
  have hmean (k : ℕ) (i : Fin ((starFamily upper).size k)) :
      expectation ((starFamily upper).model k)
        (fun y => weighted ((starFamily upper).model k) y i) = a k i := by
    convert star_mean upper (k+1) i using 1 <;>
      simp only [star_family_model, star_weighted, a]
    rfl
  simp only [hmean, sub_self, quadratic, mul_zero, sum_const_zero, zero_div,
    add_zero, star_scaledTrue] at hc
  intro ε hε
  have hh := hc ε hε
  simpa only [msr_Q, msr_shift, star_family_model, star_weighted, a, quadratic] using hh

lemma star_biased_coverage (F : Family) (c v : ℝ) (hc : 0<c) (hv : 0<v)
    (h : Scaling F 1 3 c 2) (htrue : ∀ k, scaledTrue F k=c)
    (hlim : InProbability F (scaledOracle F) (fun _ => v))
    (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    Tendsto (fun k => coverage (F.model k)
      (fun y => V1 (F.model k).G (weighted (F.model k) y)) α)
      atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (v/c))-1)) := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  let μ := fun k => (F.model k).law
  let z := normalQuantile α
  have hz : 0<z := CoverageCompletion.quantile_positive α hα hα1
  let f : ℝ×ℝ → ℝ := fun p => z * Real.sqrt (max p.1 0) / Real.sqrt p.2
  have hf : ContinuousAt f (v,c) := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact (Real.sqrt_pos.mpr hc).ne'
  have hfc : f (v,c) = z * Real.sqrt (v/c) := by
    simp only [f, max_eq_left hv.le, Real.sqrt_div hv.le]
    ring
  let W := fun k y => f (scaledOracle F k y, scaledTrue F k)
  have hdet : Tendsto (scaledTrue F) atTop (𝓝 c) := by
    have he : scaledTrue F = fun _ => c := funext htrue
    rw [he]
    exact tendsto_const_nhds
  have hW : CoverageCompletion.RowCP μ W (z*Real.sqrt (v/c)) := by
    rw [←hfc]
    apply CoverageCompletion.rowCP_continuous_pair μ _ _ v c hlim
      (CoverageCompletion.rowCP_det μ (scaledTrue F) c hdet) f hf
  have hPhi : Continuous Phi := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact AronowAudit.P053.NormalCompletion.cdf_continuousAt (gaussianReal 0 1) t
  have hZ (k : ℕ) : Measurable (standardized (F.model k)) :=
    ((ProbabilityCompletion.betaHat_measurable _).sub measurable_const).div_const _
  have hL := CoverageCompletion.row_random_width_interval μ (fun k => standardized (F.model k)) W hZ
    Phi (dependency_graph_clt F 1 3 c 2 h) hPhi (monotone_cdf (μ:=gaussianReal 0 1))
    (z*Real.sqrt (v/c)) (mul_pos hz (Real.sqrt_pos.mpr (div_pos hv hc))) hW
  have hsym (t : ℝ) : Phi (-t) = 1-Phi t :=
    AronowAudit.P053.NormalCompletion.normal_cdf_neg t
  rw [hsym] at hL
  have hmass : Phi (z*Real.sqrt (v/c)) - (1-Phi (z*Real.sqrt (v/c))) =
      2*Phi (z*Real.sqrt (v/c))-1 := by ring
  rw [hmass] at hL
  have hvpos (k : ℕ) : 0 < var (F.model k) (betaHat (F.model k)) := by
    have hh := htrue k
    unfold scaledTrue at hh
    have hn : 0<(F.size k:ℝ) := by exact_mod_cast F.positive k
    nlinarith
  have heq (k : ℕ) : coverage (F.model k)
      (fun y => V1 (F.model k).G (weighted (F.model k) y)) α =
      (μ k).real {y | |standardized (F.model k) y| ≤ W k y} := by
    apply congrArg ((μ k).real)
    ext y
    change (|betaHat (F.model k) y-beta (F.model k)| ≤ z*Real.sqrt (max (V1 (F.model k).G (weighted (F.model k) y)) 0)) ↔ _
    dsimp [W, f, scaledOracle, scaledTrue]
    rw [CoverageCompletion.scaled_width _ _ _ _ (by exact_mod_cast F.positive k), standardized,
      abs_div, abs_of_pos (Real.sqrt_pos.mpr (hvpos k))]
    exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr (hvpos k))).symm
  simpa only [heq] using hL

lemma star_coverage_strict (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    2*Phi (normalQuantile α * Real.sqrt (8/9))-1 < 1-α := by
  have hz := CoverageCompletion.quantile_positive α hα hα1
  have hs : Real.sqrt (8/9:ℝ)<1 := (Real.sqrt_lt' (by norm_num : (0:ℝ)<1)).mpr (by norm_num)
  have hm : normalQuantile α*Real.sqrt (8/9) < normalQuantile α := by nlinarith
  have hh := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hm
  have hq := AronowAudit.P053.NormalCompletion.normalCritical_cdf α hα hα1
  rw [←CoverageCompletion.quantile_eq] at hq
  rw [AronowAudit.P053.NormalCompletion.standardNormalCDF_eq_cdf] at hq
  change Phi (normalQuantile α*Real.sqrt (8/9)) < Phi (normalQuantile α) at hh
  change Phi (normalQuantile α) = 1-α/2 at hq
  linarith

theorem star_counterexample_proof :
    Scaling (starFamily false) 1 3 (27/128) 2 ∧ Valid (starFamily false) ∧
    (∀ k, Homoskedastic ((starFamily false).model k) ∧
      (∀ᵐ y ∂((starFamily false).model k).law, ∀ i, y i=0 ∨ y i=1) ∧
      (∀ i, expectation ((starFamily false).model k) (fun y => y i) =
        (![3/4,1/4,1/4,1/4] : Fin 4 → ℝ) (localIndex (by decide) i)) ∧
      (∀ i j, covariance ((starFamily false).model k) i j =
        ((3/16 : ℝ) • (1 : Matrix (Fin ((starFamily false).size k))
          (Fin ((starFamily false).size k)) ℝ) + (1/64 : ℝ) • adjacency ((starFamily false).model k).G) i j)) ∧
    (∀ k, beta ((starFamily false).model k) = 3/8 ∧ scaledTrue (starFamily false) k = 27/128 ∧
      meanBias ((starFamily false).model k) = -3/128 ∧
      (∀ A, Compatible ((starFamily false).model k).R ((starFamily false).model k).d A
        ↔ A = ((starFamily false).model k).G) ∧
      expectation ((starFamily false).model k) (scaledOracle (starFamily false) k) =
        3*(64*((k+1 : ℕ) : ℝ)-47)/(1024*((k+1 : ℕ) : ℝ))) ∧
    InProbability (starFamily false) (scaledOracle (starFamily false)) (fun _ => 3/16) ∧
    Tendsto (fun k => probability ((starFamily false).model k)
      {y | 27/128 - scaledOracle (starFamily false) k y > 3/256}) atTop (𝓝 1) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      Tendsto (fun k => coverage ((starFamily false).model k)
        (fun y => V1 ((starFamily false).model k).G (weighted ((starFamily false).model k) y)) α)
        atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (8/9)) - 1)) ∧
      2*Phi (normalQuantile α * Real.sqrt (8/9)) - 1 < 1-α) ∧
    Scaling (starFamily true) 1 3 (47/192) 2 ∧ Valid (starFamily true) ∧
    (∀ k, beta ((starFamily true).model k) = 1/2 ∧ scaledTrue (starFamily true) k = 47/192) ∧
    InProbability (starFamily true) (scaledOracle (starFamily true)) (fun _ => 53/192) ∧
    (∀ upper : Bool,
      InProbability (starFamily upper)
        (fun k y => quadratic (oracleMatrix ((starFamily upper).model k).G)
          (fun i => y i - (if upper then (![1/2,3/4,1/4,1/2] : Fin 4 → ℝ)
            (localIndex (by decide) i) else (![3/4,1/4,1/4,1/4] : Fin 4 → ℝ)
            (localIndex (by decide) i))) / ((starFamily upper).size k : ℝ))
        (fun _ => if upper then 47/192 else 27/128)) := by
  refine ⟨star_scaling false, star_valid false, ?_, ?_, star_limit false,
    star_underestimate, ?_, star_scaling true, star_valid true, ?_, star_limit true, ?_⟩
  · intro k
    have hd (i : Fin (4*(k+1))) : covariance (starModel false (k+1)) i i = 3/16 := by
      rw [star_covariance_primary]
      simp [Matrix.one_apply, adjacency, (starModel false (k+1)).G.property.2]
    refine ⟨?_, star_binary false (k+1), star_mean false (k+1), star_covariance_primary (k+1)⟩
    intro i j
    exact (hd i).trans (hd j).symm
  · intro k
    exact ⟨star_beta false (k+1) (by omega), star_scaledTrue false k,
      star_meanBias false (k+1) (by omega), star_compatible false (k+1), star_finite_expectation k⟩
  · intro α hα hα1
    refine ⟨?_, star_coverage_strict α hα hα1⟩
    have hh := star_biased_coverage (starFamily false) (27/128) (3/16)
      (by norm_num) (by norm_num) (star_scaling false) (star_scaledTrue false)
      (star_limit false) α hα hα1
    simpa only [show (3/16:ℝ)/(27/128)=8/9 by norm_num] using hh
  · intro k
    exact ⟨star_beta true (k+1) (by omega), star_scaledTrue true k⟩
  · intro upper
    simpa only [star_mu, ite_apply] using star_true_error_limit upper

end
end AronowAudit.P011.Wave1
