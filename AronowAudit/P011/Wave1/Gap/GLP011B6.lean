import AronowAudit.P011.P011_BlockOLSCompletion
import AronowAudit.P011.P011_ExpectationCompletion

/-! The all-block path counterexample. -/
namespace AronowAudit.P011.Wave1
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false
set_option backward.isDefEq.respectTransparency false

local instance instNullSingletonGLP011B6 : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1:NNReal) ≠ 0)

-- Block transport uses the blockEquiv lemmas in P011_StarCompletion.
lemma path_ce_blockIndex (m : ℕ) (b : Fin m) (r : Fin 3) :
    blockIndex (by decide) (StarCompletion.blockEquiv 3 m (b,r)) = b := by
  apply Fin.ext
  exact StarCompletion.block_quot (by decide) (b,r)

lemma path_ce_index_eq {m : ℕ} (i j : Fin (3*m))
    (hb : blockIndex (by decide) i = blockIndex (by decide) j)
    (hr : localIndex (by decide) i = localIndex (by decide) j) : i = j := by
  apply Fin.ext
  have hb' := congrArg Fin.val hb
  have hr' := congrArg Fin.val hr
  dsimp [blockIndex,localIndex] at hb' hr'
  omega

def path_ce_source (t : ℝ) (m : ℕ) (u : Fin m → Fin 2 → Bool) : Fin (3*m) → ℝ :=
  fun i => pathBlock t (sign (u (blockIndex (by decide) i) 0))
    (sign (u (blockIndex (by decide) i) 1)) (localIndex (by decide) i)

def path_ce_flat (t : ℝ) (m : ℕ) (u : Fin m × Fin 2 → Bool) : Fin (3*m) → ℝ :=
  path_ce_source t m (fun b r => u (b,r))

lemma path_ce_law_flat (t : ℝ) (m : ℕ) :
    (pathModel t m).law = uniformLaw (path_ce_flat t m) := by
  let e : (Fin m → Fin 2 → Bool) ≃ (Fin m × Fin 2 → Bool) :=
    { toFun := fun u p => u p.1 p.2
      invFun := fun u b r => u (b,r)
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  change uniformLaw ((path_ce_flat t m) ∘ e) = _
  exact NewFiniteCompletion.uniformLaw_equiv e _

def path_ce_localSupport (r : Fin 3) : Finset (Fin 2) :=
  if r = 0 then {0} else if r = 2 then {1} else univ

lemma path_ce_local_overlap (r s : Fin 3) (a : Fin 2)
    (hr : a ∈ path_ce_localSupport r) (hs : a ∈ path_ce_localSupport s) :
    r = s ∨ pathGraph.val r s = true := by
  revert r s a
  decide

lemma path_ce_block_congr (t : ℝ) (r : Fin 3) (u v : Fin 2 → Bool)
    (h : ∀ a ∈ path_ce_localSupport r, u a = v a) :
    pathBlock t (sign (u 0)) (sign (u 1)) r =
      pathBlock t (sign (v 0)) (sign (v 1)) r := by
  fin_cases r
  · change t + sign (u 0) = t + sign (v 0)
    rw [h 0 (by simp [path_ce_localSupport])]
  · change -2*t+3/5*sign (u 0)+4/5*sign (u 1) = -2*t+3/5*sign (v 0)+4/5*sign (v 1)
    rw [h 0 (by simp [path_ce_localSupport]),h 1 (by simp [path_ce_localSupport])]
  · change t + sign (u 1) = t + sign (v 1)
    rw [h 1 (by simp [path_ce_localSupport])]

def path_ce_shocks {m : ℕ} (S : Finset (Fin (3*m))) : Finset (Fin m × Fin 2) :=
  S.biUnion (fun i => (path_ce_localSupport (localIndex (by decide) i)).image
    (fun a => (blockIndex (by decide) i,a)))

lemma path_ce_shock_mem {m : ℕ} (S : Finset (Fin (3*m))) (i : S) (a : Fin 2)
    (ha : a ∈ path_ce_localSupport (localIndex (by decide) i.val)) :
    (blockIndex (by decide) i.val,a) ∈ path_ce_shocks S := by
  exact mem_biUnion.mpr ⟨i.val,i.property,mem_image.mpr ⟨a,ha,rfl⟩⟩

lemma path_ce_shocks_disjoint {m : ℕ} (S T : Finset (Fin (3*m)))
    (hd : Disjoint S T)
    (hg : ∀ i ∈ S, ∀ j ∈ T, (pathModel 0 m).G.val i j = false) :
    Disjoint (path_ce_shocks S) (path_ce_shocks T) := by
  apply disjoint_left.mpr
  intro p hpS hpT
  obtain ⟨i,hi,hpi⟩ := mem_biUnion.mp hpS
  obtain ⟨a,ha,hap⟩ := mem_image.mp hpi
  obtain ⟨j,hj,hpj⟩ := mem_biUnion.mp hpT
  obtain ⟨b,hb,hbp⟩ := mem_image.mp hpj
  have hp : (blockIndex (by decide) i,a) = (blockIndex (by decide) j,b) := hap.trans hbp.symm
  have hbij := congrArg Prod.fst hp
  have hab := congrArg Prod.snd hp
  change a = b at hab
  subst b
  rcases path_ce_local_overlap _ _ a ha hb with hr | he
  · exact (disjoint_left.mp hd hi) (path_ce_index_eq i j hbij hr ▸ hj)
  · have hval : i.val / 3 = j.val / 3 := congrArg Fin.val hbij
    simpa [pathModel,blockGraph,hval,he] using hg i hi j hj

-- General pushforward transport, the vector-valued version of PathFiniteCompletion.indep_pushforward.
lemma path_ce_indep_map {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] (μ : Measure A) (g : A → B) (hg : Measurable g)
    (f : B → C) (h : B → D) (hf : Measurable f) (hh : Measurable h)
    (hi : IndepFun (f ∘ g) (h ∘ g) μ) : IndepFun f h (μ.map g) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  rw [Measure.map_apply hg ((hs.preimage hf).inter (ht.preimage hh)),
    Measure.map_apply hg (hs.preimage hf),Measure.map_apply hg (ht.preimage hh)]
  simpa only [Set.preimage_inter,Set.preimage_preimage,Function.comp_def] using
    hi.measure_inter_preimage_eq_mul s t hs ht

lemma path_ce_dependency (t : ℝ) (m : ℕ) : Dependency (pathModel t m) := by
  let μ := (PMF.uniformOfFintype (Fin m × Fin 2 → Bool)).toMeasure
  have hind : iIndepFun (fun p (u : Fin m × Fin 2 → Bool) => u p) μ := by
    have he : μ = Measure.pi (fun _ : Fin m × Fin 2 => (PMF.uniformOfFintype Bool).toMeasure) := by
      apply Measure.ext_of_singleton
      intro u
      simp [μ,Measure.pi_singleton,PMF.toMeasure_apply_singleton,
        PMF.uniformOfFintype_apply,Fintype.card_fun,ENNReal.inv_pow]
    exact he.symm ▸ iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  intro S T hd hg
  have hd' : Disjoint (path_ce_shocks S) (path_ce_shocks T) :=
    path_ce_shocks_disjoint S T hd hg
  let reconstruct (S : Finset (Fin (3*m)))
      (v : {p // p ∈ path_ce_shocks S} → Bool) : {i // i ∈ S} → ℝ :=
    fun i => path_ce_flat t m
      (fun p => if h : p ∈ path_ce_shocks S then v ⟨p,h⟩ else false) i.val
  have hrec (S : Finset (Fin (3*m))) (u : Fin m × Fin 2 → Bool) :
      reconstruct S (fun p => u p.val) = fun i : S => path_ce_flat t m u i.val := by
    funext i
    dsimp [reconstruct,path_ce_flat,path_ce_source]
    apply path_ce_block_congr t (localIndex (by decide) i.val)
      (fun a => if h : (blockIndex (by decide) i.val,a) ∈ path_ce_shocks S then u (blockIndex (by decide) i.val,a) else false)
      (fun a => u (blockIndex (by decide) i.val,a))
    intro a ha
    simp only [dif_pos (path_ce_shock_mem S i a ha)]
  have hi := (hind.indepFun_finset _ _ hd' (fun p => measurable_pi_apply p)).comp
    (measurable_of_finite (reconstruct S)) (measurable_of_finite (reconstruct T))
  have hi' : IndepFun (fun u => fun i : S => path_ce_flat t m u i.val)
      (fun u => fun j : T => path_ce_flat t m u j.val) μ := by
    simpa only [Function.comp_def,hrec] using hi
  change IndepFun (fun y : Fin (3*m) → ℝ => fun i : S => y i.val)
    (fun y : Fin (3*m) → ℝ => fun j : T => y j.val) (pathModel t m).law
  rw [path_ce_law_flat,uniformLaw,←PMF.toMeasure_map _ _ (measurable_of_finite (path_ce_flat t m))]
  exact path_ce_indep_map μ (path_ce_flat t m) (measurable_of_finite _)
    _ _ (by fun_prop) (by fun_prop) hi'

lemma path_ce_memLp (t : ℝ) (m : ℕ) (i : Fin (3*m)) :
    MemLp (fun y => weighted (pathModel t m) y i) 2 (pathModel t m).law := by
  exact NewFiniteCompletion.finite_memLp (path_ce_source t m) _
    (ProbabilityCompletion.weighted_measurable _ _) 2

lemma path_ce_weighted (t : ℝ) (m : ℕ) (y : Fin (3*m) → ℝ) :
    weighted (pathModel t m) y = y := by
  funext i
  simp [weighted,pathModel]

lemma path_ce_mean (t : ℝ) (m : ℕ) (i : Fin (3*m)) :
    expectation (pathModel t m) (fun y => weighted (pathModel t m) y i) =
      (![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) i) := by
  simp only [path_ce_weighted]
  exact BlockOLSCompletion.path_coordinate_mean t m i

lemma path_ce_beta (t : ℝ) (m : ℕ) : beta (pathModel t m) = 0 := by
  let : IsProbabilityMeasure (pathModel t m).law := (pathModel t m).probability
  unfold beta betaHat average expectation
  rw [integral_div,integral_finsetSum univ (fun i _ =>
    (path_ce_memLp t m i).integrable (by norm_num))]
  change (∑ i, expectation (pathModel t m) (fun y => weighted (pathModel t m) y i)) / _ = 0
  simp_rw [path_ce_mean]
  rw [BlockOLSCompletion.local_sum (by decide : 0<3)]
  have hz : (∑ r : Fin 3, (![t,-2*t,t] : Fin 3 → ℝ) r) = 0 := by
    simp [Fin.sum_univ_succ]
    ring
  rw [hz]
  simp

def path_ce_C : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1,3/5,0],![3/5,1,4/5],![0,4/5,1]]

def path_ce_lift (m : ℕ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin (3*m)) (Fin (3*m)) ℝ := fun i j =>
  if blockIndex (by decide) i = blockIndex (by decide) j then
    M (localIndex (by decide) i) (localIndex (by decide) j) else 0

lemma path_ce_lift_apply (m : ℕ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (b c : Fin m) (r s : Fin 3) :
    path_ce_lift m M (StarCompletion.blockEquiv 3 m (b,r))
      (StarCompletion.blockEquiv 3 m (c,s)) = if b=c then M r s else 0 := by
  simp [path_ce_lift,path_ce_blockIndex,StarCompletion.block_local]

lemma path_ce_block_cov (t : ℝ) (r s : Fin 3) :
    (∑ u : Fin 2 → Bool,
      (pathBlock t (sign (u 0)) (sign (u 1)) r - (![t,-2*t,t] : Fin 3 → ℝ) r) *
      (pathBlock t (sign (u 0)) (sign (u 1)) s - (![t,-2*t,t] : Fin 3 → ℝ) s)) / 4 =
      path_ce_C r s := by
  rw [←(finTwoArrowEquiv Bool).symm.sum_comp]
  fin_cases r <;> fin_cases s <;>
    norm_num [Fintype.sum_prod_type,Fintype.sum_bool,finTwoArrowEquiv,pathBlock,sign,path_ce_C] <;> ring

lemma path_ce_covariance (t : ℝ) (m : ℕ) :
    covariance (pathModel t m) = path_ce_lift m path_ce_C := by
  ext i j
  by_cases hb : blockIndex (by decide) i = blockIndex (by decide) j
  · simp only [path_ce_lift,hb,if_true]
    unfold covariance
    rw [path_ce_mean t m i,path_ce_mean t m j]
    simp only [path_ce_weighted]
    unfold expectation
    change (∫ y, (y i - _)*(y j - _) ∂uniformLaw (path_ce_source t m)) = _
    rw [uniformLaw,←PMF.toMeasure_map _ _ (measurable_of_finite (path_ce_source t m)),
      integral_map (measurable_of_finite (path_ce_source t m)).aemeasurable
        (show Measurable (fun y : Fin (3*m) → ℝ =>
          (y i-(![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) i))*
          (y j-(![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) j))) by fun_prop).aestronglyMeasurable]
    simp only [path_ce_source,←hb]
    rw [BlockOLSCompletion.uniform_evaluation_integral (blockIndex (by decide) i)
      (fun u : Fin 2 → Bool =>
        (pathBlock t (sign (u 0)) (sign (u 1)) (localIndex (by decide) i) -
          (![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) i))*
        (pathBlock t (sign (u 0)) (sign (u 1)) (localIndex (by decide) j) -
          (![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) j)))]
    norm_num only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    exact path_ce_block_cov t _ _
  · simp only [path_ce_lift,hb,if_false]
    apply OracleCompletion.covariance_support _ (path_ce_dependency t m) (path_ce_memLp t m)
    · intro h; exact hb (congrArg (blockIndex (by decide)) h)
    · have hv : i.val / 3 ≠ j.val / 3 := fun h => hb (Fin.ext h)
      simp [pathModel,blockGraph,hv]

-- Block-matrix transport by finite reindexing.
lemma path_ce_lift_mul (m : ℕ) (M N : Matrix (Fin 3) (Fin 3) ℝ) :
    path_ce_lift m M * path_ce_lift m N = path_ce_lift m (M*N) := by
  ext i j
  obtain ⟨⟨b,r⟩,rfl⟩ := (StarCompletion.blockEquiv 3 m).surjective i
  obtain ⟨⟨c,s⟩,rfl⟩ := (StarCompletion.blockEquiv 3 m).surjective j
  simp only [Matrix.mul_apply]
  rw [←(StarCompletion.blockEquiv 3 m).sum_comp,Fintype.sum_prod_type]
  rw [sum_eq_single b]
  · by_cases h : b=c
    · subst c; simp [path_ce_lift_apply,Matrix.mul_apply]
    · simp [path_ce_lift_apply,h,Matrix.mul_apply]
  · intro d hd hdb; simp [path_ce_lift_apply,Ne.symm hdb]
  · simp

lemma path_ce_lift_oracle (m : ℕ) :
    path_ce_lift m (oracleMatrix pathGraph) =
      oracleMatrix (blockGraph (by decide) pathGraph m) := by
  ext i j
  obtain ⟨⟨b,r⟩,rfl⟩ := (StarCompletion.blockEquiv 3 m).surjective i
  obtain ⟨⟨c,s⟩,rfl⟩ := (StarCompletion.blockEquiv 3 m).surjective j
  rw [path_ce_lift_apply]
  by_cases h : b=c
  · subst c
    simp [oracleMatrix,adjacency,blockGraph,StarCompletion.block_local,
      StarCompletion.block_quot,Matrix.one_apply,Equiv.apply_eq_iff_eq]
  · have hv : b.val ≠ c.val := fun he => h (Fin.ext he)
    simp [oracleMatrix,adjacency,blockGraph,StarCompletion.block_local,
      StarCompletion.block_quot,Matrix.one_apply,Equiv.apply_eq_iff_eq,h,hv]

lemma path_ce_lift_total (m : ℕ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    QuadraticCompletion.total (path_ce_lift m M) = (m:ℝ)*QuadraticCompletion.total M := by
  unfold QuadraticCompletion.total
  rw [←(StarCompletion.blockEquiv 3 m).sum_comp,Fintype.sum_prod_type]
  have hi (b : Fin m) (r : Fin 3) :
      (∑ j, path_ce_lift m M (StarCompletion.blockEquiv 3 m (b,r)) j) = ∑ s, M r s := by
    rw [←(StarCompletion.blockEquiv 3 m).sum_comp,Fintype.sum_prod_type]
    simp [path_ce_lift_apply]
  simp_rw [hi]
  simp

lemma path_ce_lift_quadratic (m : ℕ) (M : Matrix (Fin 3) (Fin 3) ℝ)
    (x : Fin (3*m) → ℝ) : quadratic (path_ce_lift m M) x =
      ∑ b : Fin m, quadratic M (fun r => x (StarCompletion.blockEquiv 3 m (b,r))) := by
  have hi (b : Fin m) (r : Fin 3) :
      (∑ j, path_ce_lift m M (StarCompletion.blockEquiv 3 m (b,r)) j *
        x (StarCompletion.blockEquiv 3 m (b,r))*x j) =
      ∑ s : Fin 3, M r s*x (StarCompletion.blockEquiv 3 m (b,r))*
        x (StarCompletion.blockEquiv 3 m (b,s)) := by
    rw [←(StarCompletion.blockEquiv 3 m).sum_comp,Fintype.sum_prod_type]
    rw [sum_eq_single b]
    · simp [path_ce_lift_apply]
    · intro c hc hcb; simp [path_ce_lift_apply,Ne.symm hcb]
    · simp
  unfold quadratic
  rw [←(StarCompletion.blockEquiv 3 m).sum_comp,Fintype.sum_prod_type]
  simp_rw [hi]

lemma path_ce_scaled_variance (t : ℝ) (m : ℕ) (hm : 0<m) :
    (3*m:ℕ)*var (pathModel t m) (betaHat (pathModel t m)) = (29:ℝ)/15 := by
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  rw [QuadraticCompletion.beta_variance _ (path_ce_memLp t m),path_ce_covariance,path_ce_lift_total]
  norm_num [QuadraticCompletion.total,path_ce_C,Fin.sum_univ_succ]
  field_simp
  <;> ring

lemma path_ce_meanBias (t : ℝ) (m : ℕ) (hm : 0<m) :
    meanBias (pathModel t m) = -2*t^2/3 := by
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have hd : delta (pathModel t m) = fun i =>
      (![t,-2*t,t] : Fin 3 → ℝ) (localIndex (by decide) i) := by
    funext i; simp [delta,path_ce_mean,path_ce_beta]
  unfold meanBias
  change quadratic (oracleMatrix (blockGraph (by decide) pathGraph m)) _ / _ = _
  rw [←path_ce_lift_oracle,hd,path_ce_lift_quadratic]
  simp only [StarCompletion.block_local,(path_block_moments t).1,sum_const,card_univ,
    Fintype.card_fin,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
  field_simp
  <;> ring

lemma path_ce_expected (t : ℝ) (m : ℕ) (hm : 0<m) :
    expectation (pathModel t m) (fun y => (3*m:ℕ)*V1 (pathModel t m).G
      (weighted (pathModel t m) y)) = (29-10*t^2)/15 - 217/(135*(m:ℝ)) := by
  have hm0 : (m:ℝ) ≠ 0 := by positivity
  have he := ExpectationCompletion.oracle_expectation_error (by omega : 0<3*m)
    (pathModel t m) (path_ce_dependency t m) (path_ce_memLp t m)
  have hv := path_ce_scaled_variance t m hm
  have hprod : QuadraticCompletion.total (oracleMatrix (pathModel t m).G * covariance (pathModel t m)) =
      (m:ℝ)*14 := by
    change QuadraticCompletion.total (oracleMatrix (blockGraph (by decide) pathGraph m) * _) = _
    rw [←path_ce_lift_oracle,path_ce_covariance,path_ce_lift_mul,path_ce_lift_total]
    norm_num [QuadraticCompletion.total,oracleMatrix,adjacency,pathGraph,path_ce_C,
      Matrix.mul_apply,Matrix.one_apply,Fin.sum_univ_succ]
  have htotal : QuadraticCompletion.total (oracleMatrix (pathModel t m).G) = (m:ℝ)*7 := by
    change QuadraticCompletion.total (oracleMatrix (blockGraph (by decide) pathGraph m)) = _
    rw [←path_ce_lift_oracle,path_ce_lift_total]
    norm_num [QuadraticCompletion.total,oracleMatrix,adjacency,pathGraph,Matrix.one_apply,Fin.sum_univ_succ]
  rw [path_ce_meanBias t m hm,hprod,htotal] at he
  have hv' : var (pathModel t m) (betaHat (pathModel t m)) = (29:ℝ)/(45*(m:ℝ)) := by
    push_cast at hv
    field_simp at hv ⊢
    nlinarith
  rw [hv'] at he
  push_cast at he ⊢
  field_simp at he ⊢
  nlinarith

lemma path_ce_degree (t : ℝ) (m : ℕ) (i : Fin (3*m)) :
    degree (pathModel t m).G i ≤ 2 := by
  change degree (blockGraph (by decide) pathGraph m) i ≤ 2
  rw [StarCompletion.block_degree]
  have hh : ∀ r : Fin 3, degree pathGraph r ≤ 2 := by decide
  exact hh _

lemma path_ce_compatible (t : ℝ) (m : ℕ) (A : Graph (3*m)) :
    Compatible (pathModel t m).R (pathModel t m).d A ↔ A = (pathModel t m).G := by
  have hd : (pathModel t m).d = degree (pathModel t m).G := by
    funext i
    exact (StarCompletion.block_degree (by decide) pathGraph i).symm
  rw [hd]
  exact saturated_graph_singleton _ _

lemma path_ce_homoskedastic (t : ℝ) (m : ℕ) : Homoskedastic (pathModel t m) := by
  have hdiag (i : Fin (3*m)) : covariance (pathModel t m) i i = 1 := by
    rw [path_ce_covariance]
    simp only [path_ce_lift,if_pos rfl]
    have hh : ∀ r : Fin 3, path_ce_C r r = 1 := by
      intro r
      fin_cases r <;> norm_num [path_ce_C]
    exact hh _
  intro i j
  rw [hdiag,hdiag]

lemma path_ce_nested (t : ℝ) : Nested (pathFamily t) := by
  constructor
  · intro k l hkl
    change 3*(k+1) ≤ 3*(l+1)
    omega
  · intro k
    let e : Fin (3*(k+1)) ↪ Fin (3*(k+1+1)) :=
      ⟨fun i => ⟨i.val,by have := i.isLt; omega⟩,by
        intro i j hij
        exact Fin.ext (congrArg (fun x : Fin (3*(k+1+1)) => x.val) hij)⟩
    refine ⟨e,?_⟩
    intro i j
    rfl

lemma path_ce_block_bound (t : ℝ) (ht : t=1 ∨ t=2) (u v : Bool) (r : Fin 3) :
    |pathBlock t (sign u) (sign v) r| ≤ 6 := by
  rcases ht with rfl | rfl <;> cases u <;> cases v <;> fin_cases r <;>
    norm_num [pathBlock,sign]

lemma path_ce_bound (t : ℝ) (ht : t=1 ∨ t=2) (m : ℕ) :
    ∀ᵐ y ∂(pathModel t m).law, ∀ i,
      |weighted (pathModel t m) y i - beta (pathModel t m)| ≤ 6 := by
  simp only [path_ce_weighted,path_ce_beta,sub_zero]
  rw [path_ce_law_flat,uniformLaw,←PMF.toMeasure_map _ _ (measurable_of_finite (path_ce_flat t m))]
  have hset : MeasurableSet {y : Fin (3*m) → ℝ | ∀ i, |y i| ≤ 6} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le
      (continuous_abs.measurable.comp (measurable_pi_apply i)) measurable_const)
  apply (ae_map_iff (measurable_of_finite (path_ce_flat t m)).aemeasurable hset).mpr
  filter_upwards [] with u
  intro i
  exact path_ce_block_bound t ht (u (blockIndex (by decide) i,0))
    (u (blockIndex (by decide) i,1)) (localIndex (by decide) i)

lemma path_ce_scaling (t : ℝ) (ht : t=1 ∨ t=2) :
    Scaling (pathFamily t) 6 2 (29/15) 2 := by
  refine ⟨path_ce_nested t,by norm_num,by norm_num,by norm_num,by norm_num,
    fun k => path_ce_dependency t (k+1),fun k => path_ce_bound t ht (k+1),?_,?_,?_⟩
  · intro k i
    exact_mod_cast path_ce_degree t (k+1) i
  · have he : (fun k => ((pathFamily t).size k:ℝ)*
        var ((pathFamily t).model k) (betaHat ((pathFamily t).model k))) = fun _ : ℕ => (29:ℝ)/15 := by
      funext k
      exact path_ce_scaled_variance t (k+1) (by omega)
    rw [he]
    exact tendsto_const_nhds
  · intro k i
    change |(1:ℝ)| < 2
    norm_num

lemma path_ce_valid (t : ℝ) : Valid (pathFamily t) := by
  intro k
  exact (path_ce_compatible t (k+1) _).mpr rfl

lemma path_ce_limit (t : ℝ) (ht : t=1 ∨ t=2) :
    InProbability (pathFamily t) (scaledOracle (pathFamily t)) (fun _ => (29-10*t^2)/15) := by
  have h := revised_oracle_convergence (pathFamily t) 6 2 (29/15) 2 (path_ce_scaling t ht)
  have hc (k : ℕ) : ((pathFamily t).size k:ℝ)*
      var ((pathFamily t).model k) (betaHat ((pathFamily t).model k)) +
      meanBias ((pathFamily t).model k) = (29-10*t^2)/15 := by
    change (3*(k+1):ℕ)*var (pathModel t (k+1)) (betaHat (pathModel t (k+1))) +
      meanBias (pathModel t (k+1)) = _
    rw [path_ce_scaled_variance t (k+1) (by omega),path_ce_meanBias t (k+1) (by omega)]
    ring
  unfold InProbability scaledOracle
  unfold InProbability at h
  simpa only [hc] using h

lemma path_ce_scaled_measurable (t : ℝ) (k : ℕ) :
    Measurable (scaledOracle (pathFamily t) k) := by
  unfold scaledOracle V1 quadratic centered average weighted
  fun_prop

-- A neighborhood of the probability limit forces any event containing that neighborhood.
lemma path_ce_event_limit (F : Family) (T : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (c : ℝ) (hT : ∀ k, Measurable (T k)) (hlim : InProbability F T (fun _ => c))
    (E : ∀ k, Set (Fin (F.size k) → ℝ)) (δ : ℝ) (hδ : 0<δ)
    (hgood : ∀ k y, |T k y-c| ≤ δ → y ∈ E k) :
    Tendsto (fun k => probability (F.model k) (E k)) atTop (𝓝 1) := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  have ht := hlim δ hδ
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (by simpa using tendsto_const_nhds.sub ht) tendsto_const_nhds
  · intro k
    have hset : MeasurableSet {y | |T k y-c| > δ} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp ((hT k).sub_const c))
    have hc := measureReal_compl (μ := (F.model k).law) hset
    rw [probReal_univ] at hc
    change 1 - (F.model k).law.real {y | |T k y-c| > δ} ≤ _
    apply le_trans (le_of_eq hc.symm)
    exact measureReal_mono (μ := (F.model k).law)
      (fun y hy => hgood k y (by
        change ¬ δ < |T k y-c| at hy
        exact le_of_not_gt hy)) (measure_ne_top _ _)
  · intro k
    simpa [probability] using measureReal_mono (μ := (F.model k).law)
      (Set.subset_univ (E k)) (measure_ne_top _ _)

lemma path_ce_failure (ε : ℝ) (hε : 0<ε) (hε' : ε<2/3) :
    Tendsto (fun k => probability ((pathFamily 1).model k)
      {y | |scaledOracle (pathFamily 1) k y - 29/15| > ε}) atTop (𝓝 1) ∧
    Tendsto (fun k => probability ((pathFamily 1).model k)
      {y | 29/15 - scaledOracle (pathFamily 1) k y > ε}) atTop (𝓝 1) := by
  have hlim : InProbability (pathFamily 1) (scaledOracle (pathFamily 1)) (fun _ => 19/15) := by
    convert path_ce_limit 1 (Or.inl rfl) using 1 <;> norm_num
  have hd : 0 < (2/3-ε)/2 := by linarith
  constructor
  · apply path_ce_event_limit _ _ _ (path_ce_scaled_measurable 1) hlim _ _ hd
    intro k y hy
    have hh := (abs_le.mp hy).2
    have ha := neg_le_abs (scaledOracle (pathFamily 1) k y - 29/15)
    change ε < |scaledOracle (pathFamily 1) k y - 29/15|
    linarith
  · apply path_ce_event_limit _ _ _ (path_ce_scaled_measurable 1) hlim _ _ hd
    intro k y hy
    have hh := (abs_le.mp hy).2
    change ε < 29/15-scaledOracle (pathFamily 1) k y
    linarith

lemma path_ce_negative :
    Tendsto (fun k => probability ((pathFamily 2).model k)
      {y | V1 ((pathFamily 2).model k).G (weighted ((pathFamily 2).model k) y) < 0}) atTop (𝓝 1) := by
  have hlim : InProbability (pathFamily 2) (scaledOracle (pathFamily 2)) (fun _ => -11/15) := by
    convert path_ce_limit 2 (Or.inr rfl) using 1 <;> norm_num
  apply path_ce_event_limit _ _ _ (path_ce_scaled_measurable 2) hlim _ (11/30) (by norm_num)
  intro k y hy
  have hh := (abs_le.mp hy).2
  change V1 _ _ < 0
  dsimp [scaledOracle] at hh
  have hn : 0 < ((pathFamily 2).size k:ℝ) := by exact_mod_cast (pathFamily 2).positive k
  nlinarith

lemma path_ce_Phi_continuous : Continuous Phi := by
  exact continuous_iff_continuousAt.mpr
    (fun t => AronowAudit.P053.NormalCompletion.cdf_continuousAt (gaussianReal 0 1) t)

lemma path_ce_zero_width (F : Family) (Z W : ∀ k, (Fin (F.size k) → ℝ) → ℝ)
    (hZ : ∀ k, Measurable (Z k))
    (hCD : ∀ x, Tendsto (fun k => probability (F.model k) {y | Z k y ≤ x}) atTop (𝓝 (Phi x)))
    (hW : CoverageCompletion.RowCP (fun k => (F.model k).law) W 0) :
    Tendsto (fun k => probability (F.model k) {y | |Z k y| ≤ W k y}) atTop (𝓝 0) := by
  let (k : ℕ) : IsProbabilityMeasure (F.model k).law := (F.model k).probability
  suffices hh : Tendsto (fun k => probability (F.model k) {y | |Z k y| ≤ W k y}) atTop
      (𝓝 (Phi 0-Phi (-0))) by simpa using hh
  apply CoverageCompletion.continuous_squeeze_zero
    (show ContinuousAt (fun e : ℝ => Phi e-Phi (-e)) 0 by
      exact (path_ce_Phi_continuous.sub (path_ce_Phi_continuous.comp continuous_neg)).continuousAt)
  intro ε hε
  have hI := CoverageCompletion.row_random_width_interval (fun k => (F.model k).law)
    Z (fun _ _ => ε) hZ Phi hCD path_ce_Phi_continuous
    (monotone_cdf (μ := gaussianReal 0 1)) ε hε
    (CoverageCompletion.rowCP_det _ (fun _ => ε) ε tendsto_const_nhds)
  have hsum := hI.add (hW ε hε)
  simp only [sub_zero,add_zero] at hsum
  have hu := hsum.eventually (eventually_lt_nhds
    (show Phi ε-Phi (-ε) < Phi ε-Phi (-ε)+ε by linarith))
  filter_upwards [hu] with k hk
  constructor
  · have hm : Phi (-ε) ≤ Phi ε := (monotone_cdf (μ := gaussianReal 0 1)) (by linarith)
    have hn : 0 ≤ probability (F.model k) {y | |Z k y| ≤ W k y} := measureReal_nonneg
    simp only [neg_neg]
    linarith
  · have hsub : {y | |Z k y| ≤ W k y} ⊆
        {y | |Z k y| ≤ ε} ∪ {y | |W k y| > ε} := by
      intro y hy
      by_cases hb : |W k y| > ε
      · exact Or.inr hb
      · exact Or.inl (hy.trans ((le_abs_self _).trans (le_of_not_gt hb)))
    have hle := (measureReal_mono (μ := (F.model k).law) hsub).trans (measureReal_union_le _ _)
    exact hle.trans hk.le

lemma path_ce_coverage_general (t : ℝ) (ht : t=1 ∨ t=2) (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    let w := normalQuantile α * Real.sqrt (max ((29-10*t^2)/15) 0) / Real.sqrt (29/15)
    Tendsto (fun k => coverage ((pathFamily t).model k)
      (fun y => V1 ((pathFamily t).model k).G (weighted ((pathFamily t).model k) y)) α)
      atTop (𝓝 (Phi w-Phi (-w))) := by
  let F := pathFamily t
  let μ := fun k => (F.model k).law
  let (k : ℕ) : IsProbabilityMeasure (μ k) := (F.model k).probability
  let a : ℝ := (29-10*t^2)/15
  let z := normalQuantile α
  let w := z*Real.sqrt (max a 0)/Real.sqrt (29/15)
  let W := fun k y => z*Real.sqrt (max (scaledOracle F k y) 0)/Real.sqrt (29/15)
  have hz : 0<z := CoverageCompletion.quantile_positive α hα hα1
  have hw0 : 0≤w := by dsimp [w]; positivity
  have hcp : CoverageCompletion.RowCP μ (scaledOracle F) a := path_ce_limit t ht
  have hW : CoverageCompletion.RowCP μ W w := by
    exact CoverageCompletion.rowCP_continuous_pair μ (scaledOracle F) (fun _ _ => 0) a 0 hcp
      (CoverageCompletion.rowCP_det μ (fun _ => 0) 0 tendsto_const_nhds)
      (fun p : ℝ × ℝ => z*Real.sqrt (max p.1 0)/Real.sqrt (29/15)) (by fun_prop)
  have hZ (k : ℕ) : Measurable (standardized (F.model k)) :=
    ((ProbabilityCompletion.betaHat_measurable _).sub measurable_const).div_const _
  have hCLT := dependency_graph_clt F 6 2 (29/15) 2 (path_ce_scaling t ht)
  have hlim : Tendsto (fun k => (μ k).real {y | |standardized (F.model k) y| ≤ W k y})
      atTop (𝓝 (Phi w-Phi (-w))) := by
    by_cases hw : 0<w
    · exact CoverageCompletion.row_random_width_interval μ (fun k => standardized (F.model k)) W hZ
        Phi hCLT path_ce_Phi_continuous (monotone_cdf (μ := gaussianReal 0 1)) w hw hW
    · have he : w=0 := le_antisymm (le_of_not_gt hw) hw0
      rw [he] at hW ⊢
      simpa only [probability,μ,neg_zero,sub_self] using path_ce_zero_width F _ W hZ hCLT hW
  have htrue (k : ℕ) : (F.size k:ℝ)*var (F.model k) (betaHat (F.model k)) = 29/15 :=
    path_ce_scaled_variance t (k+1) (by omega)
  have hvar (k : ℕ) : 0 < var (F.model k) (betaHat (F.model k)) := by
    have hh := htrue k
    have hn : 0 < (F.size k:ℝ) := by exact_mod_cast F.positive k
    nlinarith
  have heq : (fun k => coverage (F.model k)
      (fun y => V1 (F.model k).G (weighted (F.model k) y)) α) =
      (fun k => (μ k).real {y | |standardized (F.model k) y| ≤ W k y}) := by
    funext k
    apply congrArg ((μ k).real)
    ext y
    have hwidth : W k y = z*Real.sqrt (max (V1 (F.model k).G (weighted (F.model k) y)) 0) /
        Real.sqrt (var (F.model k) (betaHat (F.model k))) := by
      dsimp only [W,scaledOracle]
      rw [←htrue k]
      exact CoverageCompletion.scaled_width _ _ _ _ (by exact_mod_cast F.positive k)
    change (|betaHat (F.model k) y-beta (F.model k)| ≤ z*Real.sqrt (max (V1 _ _) 0)) ↔
      (|standardized (F.model k) y| ≤ W k y)
    rw [hwidth,standardized,abs_div,abs_of_pos (Real.sqrt_pos.mpr (hvar k))]
    exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr (hvar k))).symm
  rw [heq]
  exact hlim

lemma path_ce_coverage_one (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    Tendsto (fun k => coverage ((pathFamily 1).model k)
      (fun y => V1 ((pathFamily 1).model k).G (weighted ((pathFamily 1).model k) y)) α)
      atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (19/29)) - 1)) ∧
    2*Phi (normalQuantile α * Real.sqrt (19/29)) - 1 < 1-α := by
  have h := path_ce_coverage_general 1 (Or.inl rfl) α hα hα1
  have hs : Real.sqrt (19/15)/Real.sqrt (29/15) = Real.sqrt (19/29) := by
    rw [←Real.sqrt_div (by norm_num : (0:ℝ) ≤ 19/15)]
    norm_num
  have hw : normalQuantile α * Real.sqrt (max ((29-10*(1:ℝ)^2)/15) 0) / Real.sqrt (29/15) =
      normalQuantile α * Real.sqrt (19/29) := by
    norm_num only [one_pow,mul_one,show (29-10:ℝ)/15 = 19/15 by norm_num,
      max_eq_left (show (0:ℝ) ≤ 19/15 by norm_num)]
    rw [mul_div_assoc,hs]
  dsimp only at h
  rw [hw] at h
  have hneg (x : ℝ) : Phi (-x) = 1-Phi x := AronowAudit.P053.NormalCompletion.normal_cdf_neg x
  rw [hneg] at h
  constructor
  · convert h using 2 <;> ring
  · have hz := CoverageCompletion.quantile_positive α hα hα1
    have hslt : Real.sqrt (19/29) < 1 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 19/29),Real.sqrt_nonneg (19/29)]
    have hc := AronowAudit.P053.NormalCompletion.strictMono_normal_cdf
      (show normalQuantile α * Real.sqrt (19/29) < normalQuantile α by nlinarith)
    have hm := CoverageCompletion.quantile_mass α hα hα1
    rw [hneg] at hm
    change Phi (normalQuantile α * Real.sqrt (19/29)) < Phi (normalQuantile α) at hc
    linarith

lemma path_ce_coverage_two (α : ℝ) (hα : 0<α) (hα1 : α<1) :
    Tendsto (fun k => coverage ((pathFamily 2).model k)
      (fun y => V1 ((pathFamily 2).model k).G (weighted ((pathFamily 2).model k) y)) α)
      atTop (𝓝 0) := by
  have h := path_ce_coverage_general 2 (Or.inr rfl) α hα hα1
  norm_num at h
  exact h

theorem path_counterexample_proof (t : ℝ) (ht : t = 1 ∨ t = 2) :
    Scaling (pathFamily t) 6 2 (29/15) 2 ∧ Valid (pathFamily t) ∧
    (∀ k, Homoskedastic ((pathFamily t).model k)) ∧
    (∀ k, beta ((pathFamily t).model k) = 0 ∧ scaledTrue (pathFamily t) k = 29/15 ∧
      (∀ A, Compatible ((pathFamily t).model k).R ((pathFamily t).model k).d A
        ↔ A = ((pathFamily t).model k).G) ∧
      expectation ((pathFamily t).model k) (scaledOracle (pathFamily t) k) =
        (29-10*t^2)/15 - 217/(135*((k+1 : ℕ) : ℝ))) ∧
    InProbability (pathFamily t) (scaledOracle (pathFamily t)) (fun _ => (29-10*t^2)/15) ∧
    (t = 1 → (∀ ε : ℝ, 0 < ε → ε < 2/3 →
      Tendsto (fun k => probability ((pathFamily t).model k)
        {y | |scaledOracle (pathFamily t) k y - 29/15| > ε}) atTop (𝓝 1) ∧
      Tendsto (fun k => probability ((pathFamily t).model k)
        {y | 29/15-scaledOracle (pathFamily t) k y > ε}) atTop (𝓝 1)) ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        Tendsto (fun k => coverage ((pathFamily t).model k)
          (fun y => V1 ((pathFamily t).model k).G (weighted ((pathFamily t).model k) y)) α)
          atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (19/29)) - 1)) ∧
        2*Phi (normalQuantile α * Real.sqrt (19/29)) - 1 < 1-α)) ∧
    (t = 2 → Tendsto (fun k => probability ((pathFamily t).model k)
      {y | V1 ((pathFamily t).model k).G (weighted ((pathFamily t).model k) y) < 0}) atTop (𝓝 1) ∧
      (∀ α : ℝ, 0 < α → α < 1 →
        Tendsto (fun k => coverage ((pathFamily t).model k)
          (fun y => V1 ((pathFamily t).model k).G (weighted ((pathFamily t).model k) y)) α)
          atTop (𝓝 0))) := by
  refine ⟨path_ce_scaling t ht,path_ce_valid t,fun k => path_ce_homoskedastic t (k+1),?_,
    path_ce_limit t ht,?_,?_⟩
  · intro k
    exact ⟨path_ce_beta t (k+1),path_ce_scaled_variance t (k+1) (by omega),
      path_ce_compatible t (k+1),path_ce_expected t (k+1) (by omega)⟩
  · intro h
    subst t
    exact ⟨path_ce_failure,path_ce_coverage_one⟩
  · intro h
    subst t
    exact ⟨path_ce_negative,path_ce_coverage_two⟩

end
end AronowAudit.P011.Wave1
