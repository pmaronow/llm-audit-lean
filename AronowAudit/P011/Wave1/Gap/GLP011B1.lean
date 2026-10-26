import AronowAudit.P011.P011_BlockOLSCompletion
import AronowAudit.P011.P011_FiniteLawCompletion
import AronowAudit.P011.P011_QuadraticCompletion
import AronowAudit.P011.P011_CoverageCompletion
import AronowAudit.P011.P011_OracleCompletion

namespace AronowAudit.P011.Wave1
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology Classical Matrix NNReal ENNReal
attribute [-simp] Finset.sum_boole
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

/- Transport between block coordinates and finite vertex indices. -/
lemma cycleCE_blockIndex (m : ℕ) (b : Fin m) (r : Fin 4) :
    blockIndex (by decide) (StarCompletion.blockEquiv 4 m (b,r)) = b := by
  apply Fin.ext
  exact StarCompletion.block_quot (by decide) (b,r)

def cycleCE_lift (m : ℕ) (M : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix (Fin (4*m)) (Fin (4*m)) ℝ := fun i j =>
  if blockIndex (by decide) i = blockIndex (by decide) j then
    M (localIndex (by decide) i) (localIndex (by decide) j) else 0

lemma cycleCE_lift_apply (m : ℕ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (b c : Fin m) (r s : Fin 4) :
    cycleCE_lift m M (StarCompletion.blockEquiv 4 m (b,r))
      (StarCompletion.blockEquiv 4 m (c,s)) = if b=c then M r s else 0 := by
  simp [cycleCE_lift,cycleCE_blockIndex,StarCompletion.block_local]


lemma cycleCE_lift_oracle (m : ℕ) :
    cycleCE_lift m (oracleMatrix cycleGraph) =
      oracleMatrix (blockGraph (by decide) cycleGraph m) := by
  ext i j
  obtain ⟨⟨b,r⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective i
  obtain ⟨⟨c,s⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective j
  rw [cycleCE_lift_apply]
  by_cases h : b=c
  · subst c
    simp [oracleMatrix,adjacency,blockGraph,StarCompletion.block_local,
      StarCompletion.block_quot,Matrix.one_apply,Equiv.apply_eq_iff_eq]
  · have hv : b.val ≠ c.val := fun he => h (Fin.ext he)
    simp [oracleMatrix,adjacency,blockGraph,StarCompletion.block_local,
      StarCompletion.block_quot,Matrix.one_apply,Equiv.apply_eq_iff_eq,h,hv]

lemma cycleCE_lift_quadratic (m : ℕ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (x : Fin (4*m) → ℝ) : quadratic (cycleCE_lift m M) x =
      ∑ b : Fin m, quadratic M (fun r => x (StarCompletion.blockEquiv 4 m (b,r))) := by
  have hi (b : Fin m) (r : Fin 4) :
      (∑ j, cycleCE_lift m M (StarCompletion.blockEquiv 4 m (b,r)) j *
        x (StarCompletion.blockEquiv 4 m (b,r))*x j) =
      ∑ s : Fin 4, M r s*x (StarCompletion.blockEquiv 4 m (b,r))*
        x (StarCompletion.blockEquiv 4 m (b,s)) := by
    rw [← (StarCompletion.blockEquiv 4 m).sum_comp,Fintype.sum_prod_type]
    rw [Finset.sum_eq_single b]
    · simp [cycleCE_lift_apply]
    · intro c hc hcb
      simp [cycleCE_lift_apply,Ne.symm hcb]
    · simp
  unfold quadratic
  rw [← (StarCompletion.blockEquiv 4 m).sum_comp,Fintype.sum_prod_type]
  simp_rw [hi]


def cycleCE_bits : (Fin 4 → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun u := (u 0,u 1,u 2,u 3)
  invFun v := ![v.1,v.2.1,v.2.2.1,v.2.2.2]
  left_inv u := by funext r; fin_cases r <;> rfl
  right_inv v := by rcases v with ⟨b0,b1,b2,b3⟩; rfl

def cycleCE_avg {A : Type} [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card A

lemma cycleCE_avg_inst {A : Type} (F G : Fintype A) (f : A → ℝ) :
    @cycleCE_avg A F f = @cycleCE_avg A G f := by
  rw [Subsingleton.elim F G]

lemma cycleCE_avg_const {A : Type} [Fintype A] [Nonempty A] (c : ℝ) :
    cycleCE_avg (fun _ : A => c) = c := by
  simp [cycleCE_avg, mul_div_cancel_left₀, Fintype.card_ne_zero]

lemma cycleCE_avg_add {A : Type} [Fintype A] (f g : A → ℝ) :
    cycleCE_avg (fun x => f x+g x) = cycleCE_avg f+cycleCE_avg g := by
  simp [cycleCE_avg,Finset.sum_add_distrib,add_div]

lemma cycleCE_avg_sub {A : Type} [Fintype A] (f g : A → ℝ) :
    cycleCE_avg (fun x => f x-g x) = cycleCE_avg f-cycleCE_avg g := by
  simp [cycleCE_avg,Finset.sum_sub_distrib,sub_div]

lemma cycleCE_avg_mul_left {A : Type} [Fintype A] (c : ℝ) (f : A → ℝ) :
    cycleCE_avg (fun x => c*f x) = c*cycleCE_avg f := by
  simp [cycleCE_avg,← Finset.mul_sum,mul_div_assoc]

lemma cycleCE_avg_mul_right {A : Type} [Fintype A] (f : A → ℝ) (c : ℝ) :
    cycleCE_avg (fun x => f x*c) = cycleCE_avg f*c := by
  simp [cycleCE_avg,← Finset.sum_mul,div_mul_eq_mul_div]

lemma cycleCE_avg_div {A : Type} [Fintype A] (f : A → ℝ) (c : ℝ) :
    cycleCE_avg (fun x => f x/c) = cycleCE_avg f/c := by
  simp only [div_eq_mul_inv,cycleCE_avg_mul_right]

lemma cycleCE_avg_equiv {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (f : B → ℝ) : cycleCE_avg (fun x => f (e x)) = cycleCE_avg f := by
  simp only [cycleCE_avg,e.sum_comp,Fintype.card_congr e]

lemma cycleCE_avg_prod {A B : Type} [Fintype A] [Fintype B] (f : A × B → ℝ) :
    cycleCE_avg f = cycleCE_avg (fun x => cycleCE_avg (fun y => f (x,y))) := by
  simp only [cycleCE_avg,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,
    ← Finset.sum_div]
  ring

lemma cycleCE_avg_succ {A : Type} [Fintype A] (m : ℕ) (f : (Fin (m+1) → A) → ℝ) :
    cycleCE_avg f = cycleCE_avg (fun u : Fin m → A =>
      cycleCE_avg (fun v : A => f (Fin.cons v u))) := by
  rw [← cycleCE_avg_equiv (Fin.consEquiv (fun _ : Fin (m+1) => A)) f,
    cycleCE_avg_prod]
  simp only [cycleCE_avg,← Finset.sum_div]
  rw [Finset.sum_comm]
  change ((∑ y, ∑ x, f (Fin.cons x y)) / Fintype.card (Fin m → A)) / Fintype.card A = _
  ring

def cycleCE_w (u : Fin 4 → Bool) : ℝ := ∑ r, sign (u r)
def cycleCE_q (u : Fin 4 → Bool) : ℝ :=
  quadratic (oracleMatrix cycleGraph) (cycleBlock (3/2) (fun r => sign (u r)))

lemma cycleCE_block_moments :
    cycleCE_avg cycleCE_w = 0 ∧
    cycleCE_avg (fun u => cycleCE_w u^2) = 4 ∧
    cycleCE_avg (fun u => cycleCE_w u^3) = 0 ∧
    cycleCE_avg (fun u => cycleCE_w u^4) = 40 ∧
    cycleCE_avg cycleCE_q = 7 ∧
    cycleCE_avg (fun u => cycleCE_q u^2) = 225 ∧
    cycleCE_avg (fun u => cycleCE_q u*cycleCE_w u) = 0 ∧
    cycleCE_avg (fun u => cycleCE_q u*cycleCE_w u^2) = 92 := by
  simp only [← cycleCE_avg_equiv cycleCE_bits.symm]
  norm_num [cycleCE_avg,cycleCE_bits,cycleCE_w,cycleCE_q,cycleBlock,sign,
    quadratic,oracleMatrix,adjacency,cycleGraph,Matrix.add_apply,Matrix.one_apply,
    Fintype.sum_prod_type,Fintype.sum_bool,Fin.sum_univ_succ]

lemma cycleCE_step (x y : ℝ) :
    cycleCE_avg (fun v => cycleCE_w v+x) = x ∧
    cycleCE_avg (fun v => (cycleCE_w v+x)^2) = 4+x^2 ∧
    cycleCE_avg (fun v => (cycleCE_w v+x)^3) = 12*x+x^3 ∧
    cycleCE_avg (fun v => (cycleCE_w v+x)^4) = 40+24*x^2+x^4 ∧
    cycleCE_avg (fun v => cycleCE_q v+y) = 7+y ∧
    cycleCE_avg (fun v => (cycleCE_q v+y)^2) = 225+14*y+y^2 ∧
    cycleCE_avg (fun v => (cycleCE_q v+y)*(cycleCE_w v+x)^2) =
      92+7*x^2+4*y+y*x^2 := by
  rcases cycleCE_block_moments with ⟨h1,h2,h3,h4,hq,hq2,hqw,hqw2⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    conv_lhs => arg 1; ext v; ring_nf
    simp only [cycleCE_avg_add,cycleCE_avg_mul_left,cycleCE_avg_mul_right,
      cycleCE_avg_const,h1,h2,h3,h4,hq,hq2,hqw,hqw2] <;> ring

lemma cycleCE_step_w1 (x : ℝ) :
    cycleCE_avg (fun v => cycleCE_w v+x) = x := (cycleCE_step x 0).1

lemma cycleCE_step_w2 (x : ℝ) :
    cycleCE_avg (fun v => (cycleCE_w v+x)^2) = 4+x^2 := (cycleCE_step x 0).2.1

lemma cycleCE_step_w3 (x : ℝ) :
    cycleCE_avg (fun v => (cycleCE_w v+x)^3) = 12*x+x^3 := (cycleCE_step x 0).2.2.1

lemma cycleCE_step_w4 (x : ℝ) :
    cycleCE_avg (fun v => (cycleCE_w v+x)^4) = 40+24*x^2+x^4 := (cycleCE_step x 0).2.2.2.1

lemma cycleCE_step_q1 (y : ℝ) :
    cycleCE_avg (fun v => cycleCE_q v+y) = 7+y := (cycleCE_step 0 y).2.2.2.2.1

lemma cycleCE_step_q2 (y : ℝ) :
    cycleCE_avg (fun v => (cycleCE_q v+y)^2) = 225+14*y+y^2 := (cycleCE_step 0 y).2.2.2.2.2.1

lemma cycleCE_step_qw2 (x y : ℝ) :
    cycleCE_avg (fun v => (cycleCE_q v+y)*(cycleCE_w v+x)^2) = 92+7*x^2+4*y+y*x^2 := (cycleCE_step x y).2.2.2.2.2.2

def cycleCE_W (m : ℕ) (u : Fin m → Fin 4 → Bool) : ℝ := ∑ b, cycleCE_w (u b)
def cycleCE_Q (m : ℕ) (u : Fin m → Fin 4 → Bool) : ℝ := ∑ b, cycleCE_q (u b)

lemma cycleCE_aggregate_moments (m : ℕ) :
    cycleCE_avg (cycleCE_W m) = 0 ∧
    cycleCE_avg (fun u => cycleCE_W m u^2) = 4*m ∧
    cycleCE_avg (fun u => cycleCE_W m u^3) = 0 ∧
    cycleCE_avg (fun u => cycleCE_W m u^4) = 48*(m : ℝ)^2-8*m ∧
    cycleCE_avg (cycleCE_Q m) = 7*m ∧
    cycleCE_avg (fun u => cycleCE_Q m u^2) = 49*(m : ℝ)^2+176*m ∧
    cycleCE_avg (fun u => cycleCE_Q m u*cycleCE_W m u^2) = 28*(m : ℝ)^2+64*m := by
  induction m with
  | zero => norm_num [cycleCE_W,cycleCE_Q,cycleCE_avg]
  | succ m ih =>
    rcases ih with ⟨h1,h2,h3,h4,hq,hq2,hqw2⟩
    have hW (u : Fin m → Fin 4 → Bool) (v : Fin 4 → Bool) :
        cycleCE_W (m+1) (Fin.cons v u) = cycleCE_w v+cycleCE_W m u := by
      simp [cycleCE_W,Fin.sum_univ_succ]
    have hQ (u : Fin m → Fin 4 → Bool) (v : Fin 4 → Bool) :
        cycleCE_Q (m+1) (Fin.cons v u) = cycleCE_q v+cycleCE_Q m u := by
      simp [cycleCE_Q,Fin.sum_univ_succ]
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    all_goals
      rw [cycleCE_avg_succ]
      simp only [hW,hQ]
    · simpa only [cycleCE_step_w1] using h1
    · simp only [cycleCE_step_w2,cycleCE_avg_add,cycleCE_avg_const,h2]
      push_cast
      ring
    · simp only [cycleCE_step_w3,cycleCE_avg_add,cycleCE_avg_mul_left,h1,h3]
      ring
    · simp only [cycleCE_step_w4,cycleCE_avg_add,cycleCE_avg_const,
        cycleCE_avg_mul_left,h2,h4]
      push_cast
      ring
    · simp only [cycleCE_step_q1,cycleCE_avg_add,cycleCE_avg_const,hq,cycleCE_block_moments.2.2.2.2.1]
      push_cast
      ring
    · simp only [cycleCE_step_q2,cycleCE_avg_add,cycleCE_avg_const,
        cycleCE_avg_mul_left,hq,hq2]
      push_cast
      ring
    · simp only [cycleCE_step_qw2,cycleCE_avg_add,cycleCE_avg_const,
        cycleCE_avg_mul_left,h2,hq,hqw2]
      push_cast
      ring

lemma cycleCE_uniform_avg {A : Type} [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] (f : A → ℝ) :
    (∫ u, f u ∂(PMF.uniformOfFintype A).toMeasure) = cycleCE_avg f := by
  rw [PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply,ENNReal.toReal_inv,ENNReal.toReal_natCast,
    smul_eq_mul,cycleCE_avg,div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

lemma cycleCE_avg_eval {I A : Type} [Fintype I] [Fintype A]
    [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A] (i : I) (f : A → ℝ) :
    cycleCE_avg (fun u : I → A => f (u i)) = cycleCE_avg f :=
  BlockOLSCompletion.uniform_coordinate_sum i f

lemma cycleCE_uniform_inst {A : Type} [Nonempty A] [MeasurableSpace A]
    (F G : Fintype A) :
    (@PMF.uniformOfFintype A F _).toMeasure = (@PMF.uniformOfFintype A G _).toMeasure := by
  rw [Subsingleton.elim F G]

lemma cycleCE_independent_coords {I A : Type} [Fintype I] [DecidableEq I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [MeasurableSingletonClass A] :
    iIndepFun (fun i (u : I → A) => u i) (PMF.uniformOfFintype (I → A)).toMeasure := by
  have hp : (PMF.uniformOfFintype (I → A)).toMeasure =
      Measure.pi (fun _ : I => (PMF.uniformOfFintype A).toMeasure) :=
    (cycleCE_uniform_inst _ _).trans (uniform_function_product I A)
  rw [hp]
  exact iIndepFun_pi (μ := fun _ : I => (PMF.uniformOfFintype A).toMeasure)
    (X := fun _ (a : A) => a) (fun _ => measurable_id.aemeasurable)

lemma cycleCE_avg_pair {I A : Type} [Fintype I] [Fintype A]
    [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (i j : I) (hij : i ≠ j) (f g : A → ℝ) :
    cycleCE_avg (fun u : I → A => f (u i)*g (u j)) = cycleCE_avg f*cycleCE_avg g := by
  have hi := (cycleCE_independent_coords (I := I) (A := A)).indepFun hij
  have hh := (hi.comp (measurable_of_finite f) (measurable_of_finite g)).integral_fun_mul_eq_mul_integral
    (measurable_of_finite _).aestronglyMeasurable (measurable_of_finite _).aestronglyMeasurable
  simp only [Function.comp_def,cycleCE_uniform_avg,cycleCE_avg_eval] at hh
  exact hh

def cycleCE_source (a : ℝ) (m : ℕ) (u : Fin m → Fin 4 → Bool) : Fin (4*m) → ℝ := fun i =>
  cycleBlock a (fun r => sign (u (blockIndex (by decide) i) r)) (localIndex (by decide) i)

lemma cycleCE_source_apply (a : ℝ) (m : ℕ) (u : Fin m → Fin 4 → Bool)
    (b : Fin m) (r : Fin 4) :
    cycleCE_source a m u (StarCompletion.blockEquiv 4 m (b,r)) =
      cycleBlock a (fun s => sign (u b s)) r := by
  simp [cycleCE_source,cycleCE_blockIndex,StarCompletion.block_local]

lemma cycleCE_integral (a : ℝ) (m : ℕ) (f : (Fin (4*m) → ℝ) → ℝ)
    (hf : Measurable f) : expectation (cycleModel a m) f =
      cycleCE_avg (fun u => f (cycleCE_source a m u)) :=
  uniform_integral _ (measurable_of_finite _) f hf

lemma cycleCE_weighted (a : ℝ) (m : ℕ) (y : Fin (4*m) → ℝ) :
    weighted (cycleModel a m) y = y := by
  funext i
  simp [weighted,cycleModel]

lemma cycleCE_sum_block (a : ℝ) (u : Fin 4 → Bool) :
    (∑ r, cycleBlock a (fun s => sign (u s)) r) = 2*cycleCE_w u := by
  simp [cycleBlock,cycleCE_w,Fin.sum_univ_succ]
  ring

lemma cycleCE_beta_source (a : ℝ) (m : ℕ) (u : Fin m → Fin 4 → Bool) :
    betaHat (cycleModel a m) (cycleCE_source a m u) = cycleCE_W m u/(2*m : ℝ) := by
  rw [betaHat,cycleCE_weighted]
  unfold average
  rw [← (StarCompletion.blockEquiv 4 m).sum_comp,Fintype.sum_prod_type]
  simp_rw [cycleCE_source_apply,cycleCE_sum_block]
  simp only [← Finset.mul_sum,cycleCE_W]
  push_cast
  ring

lemma cycleCE_center_block (x : Fin 4 → ℝ) (a : ℝ) :
    quadratic (oracleMatrix cycleGraph) (fun r => x r-a) =
      quadratic (oracleMatrix cycleGraph) x-6*a*(∑ r, x r)+12*a^2 := by
  norm_num [quadratic,oracleMatrix,adjacency,cycleGraph,Matrix.add_apply,Matrix.one_apply,
    Fin.sum_univ_succ]
  <;> ring

lemma cycleCE_quadratic_shift (a : ℝ) (u : Fin 4 → Bool) :
    quadratic (oracleMatrix cycleGraph) (cycleBlock a (fun r => sign (u r))) =
      cycleCE_q u+9-4*a^2 := by
  norm_num [cycleCE_q,quadratic,oracleMatrix,adjacency,cycleGraph,cycleBlock,
    Matrix.add_apply,Matrix.one_apply,Fin.sum_univ_succ]
  <;> ring

lemma cycleCE_scaled_source (a : ℝ) (m : ℕ) (hm : 0 < m) (u : Fin m → Fin 4 → Bool) :
    (4*m : ℝ)*V1 (cycleModel a m).G
      (weighted (cycleModel a m) (cycleCE_source a m u)) =
      cycleCE_Q m u/(4*m : ℝ)+9/4-a^2-3*(cycleCE_W m u/(2*m : ℝ))^2 := by
  have hn0 : (4*m : ℝ) ≠ 0 := by positivity
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hV (y : Fin (4*m) → ℝ) : V1 (cycleModel a m).G y =
      quadratic (oracleMatrix (blockGraph (by decide) cycleGraph m)) (centered y) /
        ((4*m : ℕ) : ℝ)^2 := by
    rw [← variance_form_oracle]
    rfl
  rw [cycleCE_weighted,hV,← cycleCE_lift_oracle,cycleCE_lift_quadratic]
  have hb : average (cycleCE_source a m u) = cycleCE_W m u/(2*m : ℝ) := by
    simpa only [betaHat,cycleCE_weighted] using cycleCE_beta_source a m u
  simp only [centered,cycleCE_source_apply,hb]
  simp_rw [cycleCE_center_block,cycleCE_quadratic_shift,cycleCE_sum_block]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,cycleCE_Q,cycleCE_W]
  push_cast
  field_simp
  <;> ring

def cycleCE_mu (a : ℝ) : Fin 4 → ℝ := ![a,-a,a,-a]

lemma cycleCE_block_mean (a : ℝ) (r : Fin 4) :
    cycleCE_avg (fun u : Fin 4 → Bool => cycleBlock a (fun s => sign (u s)) r) =
      cycleCE_mu a r := by
  rw [← cycleCE_avg_equiv cycleCE_bits.symm]
  fin_cases r <;> norm_num [cycleCE_avg,cycleCE_bits,cycleCE_mu,cycleBlock,sign,
    Fintype.sum_prod_type,Fintype.sum_bool] <;> ring

lemma cycleCE_block_cov (a : ℝ) (r s : Fin 4) :
    cycleCE_avg (fun u : Fin 4 → Bool =>
      (cycleBlock a (fun t => sign (u t)) r-cycleCE_mu a r)*
      (cycleBlock a (fun t => sign (u t)) s-cycleCE_mu a s)) =
      ((2 : ℝ) • (1 : Matrix (Fin 4) (Fin 4) ℝ)+adjacency cycleGraph) r s := by
  rw [← cycleCE_avg_equiv cycleCE_bits.symm]
  fin_cases r <;> fin_cases s <;> norm_num [cycleCE_avg,cycleCE_bits,cycleCE_mu,cycleBlock,sign,
    adjacency,cycleGraph,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,
    Fintype.sum_prod_type,Fintype.sum_bool] <;> ring

lemma cycleCE_coordinate_mean (a : ℝ) (m : ℕ) (i : Fin (4*m)) :
    expectation (cycleModel a m) (fun y => y i) = cycleCE_mu a (localIndex (by decide) i) := by
  rw [cycleCE_integral _ _ _ (measurable_pi_apply i)]
  change cycleCE_avg (fun u : Fin m → Fin 4 → Bool =>
    cycleBlock a (fun t => sign (u (blockIndex (by decide) i) t)) (localIndex (by decide) i)) = _
  calc
    _ = cycleCE_avg (fun u : Fin 4 → Bool =>
        cycleBlock a (fun t => sign (u t)) (localIndex (by decide) i)) := by
      exact (cycleCE_avg_inst _ _ _).trans (cycleCE_avg_eval (blockIndex (by decide : 0 < 4) i)
        (fun u : Fin 4 → Bool => cycleBlock a (fun t => sign (u t)) (localIndex (by decide) i)))
    _ = _ := cycleCE_block_mean _ _

lemma cycleCE_covariance (a : ℝ) (m : ℕ) (i j : Fin (4*m)) :
    covariance (cycleModel a m) i j =
      ((2 : ℝ) • (1 : Matrix (Fin (4*m)) (Fin (4*m)) ℝ)+
        adjacency (cycleModel a m).G) i j := by
  unfold covariance
  simp only [cycleCE_weighted,cycleCE_coordinate_mean]
  rw [cycleCE_integral _ _ _ (by fun_prop)]
  obtain ⟨⟨b,r⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective i
  obtain ⟨⟨c,s⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective j
  simp only [cycleCE_source_apply,StarCompletion.block_local]
  by_cases h : b=c
  · subst c
    have he := cycleCE_avg_eval b (fun u : Fin 4 → Bool =>
      (cycleBlock a (fun t => sign (u t)) r-cycleCE_mu a r)*
      (cycleBlock a (fun t => sign (u t)) s-cycleCE_mu a s))
    calc
      _ = cycleCE_avg (fun u : Fin 4 → Bool =>
          (cycleBlock a (fun t => sign (u t)) r-cycleCE_mu a r)*
          (cycleBlock a (fun t => sign (u t)) s-cycleCE_mu a s)) :=
        (cycleCE_avg_inst _ _ _).trans he
      _ = _ := cycleCE_block_cov a r s
      _ = _ := by
        simp [cycleModel,blockGraph,adjacency,StarCompletion.block_local,StarCompletion.block_quot,
          Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,Equiv.apply_eq_iff_eq]

  · have he := cycleCE_avg_pair b c h
      (fun u : Fin 4 → Bool => cycleBlock a (fun t => sign (u t)) r-cycleCE_mu a r)
      (fun u : Fin 4 → Bool => cycleBlock a (fun t => sign (u t)) s-cycleCE_mu a s)
    have he' : cycleCE_avg (fun u : Fin m → Fin 4 → Bool =>
      (cycleBlock a (fun t => sign (u b t)) r-cycleCE_mu a r)*
      (cycleBlock a (fun t => sign (u c t)) s-cycleCE_mu a s)) = _ := (cycleCE_avg_inst _ _ _).trans he
    rw [he']
    have hm (t : Fin 4) : cycleCE_avg (fun u : Fin 4 → Bool =>
        cycleBlock a (fun r => sign (u r)) t-cycleCE_mu a t) = 0 := by
      rw [cycleCE_avg_sub,cycleCE_block_mean,cycleCE_avg_const,sub_self]
    rw [hm,hm,zero_mul]
    have hv : b.val ≠ c.val := fun hh => h (Fin.ext hh)
    simp [cycleModel,blockGraph,adjacency,StarCompletion.block_local,StarCompletion.block_quot,
      Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,Equiv.apply_eq_iff_eq,h,hv]

lemma cycleCE_beta_zero (a : ℝ) (m : ℕ) : beta (cycleModel a m) = 0 := by
  rw [beta,cycleCE_integral _ _ _ (ProbabilityCompletion.betaHat_measurable _)]
  simp only [cycleCE_beta_source,div_eq_mul_inv,cycleCE_avg_mul_right,
    (cycleCE_aggregate_moments m).1,zero_mul]

lemma cycleCE_true_variance (a : ℝ) (m : ℕ) (hm : 0 < m) :
    var (cycleModel a m) (betaHat (cycleModel a m)) = 1/(m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold var
  rw [show expectation (cycleModel a m) (betaHat (cycleModel a m)) = 0 from cycleCE_beta_zero a m]
  rw [cycleCE_integral _ _ _ (by unfold betaHat average weighted; fun_prop)]
  simp only [cycleCE_beta_source,sub_zero,div_pow]
  rw [cycleCE_avg_div, (cycleCE_aggregate_moments m).2.1]
  field_simp
  <;> ring

lemma cycleCE_mean_bias (a : ℝ) (m : ℕ) (hm : 0 < m) :
    meanBias (cycleModel a m) = -a^2 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hd (i : Fin (4*m)) : delta (cycleModel a m) i = cycleCE_mu a (localIndex (by decide) i) := by
    simp only [delta,cycleCE_weighted,cycleCE_coordinate_mean,cycleCE_beta_zero,sub_zero]
  unfold meanBias
  change quadratic (oracleMatrix (blockGraph (by decide) cycleGraph m)) _ / _ = _
  rw [← cycleCE_lift_oracle,cycleCE_lift_quadratic]
  simp only [hd,StarCompletion.block_local]
  have hq : quadratic (oracleMatrix cycleGraph) (cycleCE_mu a) = -4*a^2 :=
    (cycle_covariance_algebra a).2.1
  simp only [hq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  push_cast
  field_simp
  <;> ring

lemma cycleCE_degree (a : ℝ) (m : ℕ) (i : Fin (4*m)) : degree (cycleModel a m).G i = 2 := by
  rw [show (cycleModel a m).G = blockGraph (by decide) cycleGraph m from rfl,
    StarCompletion.block_degree]
  generalize localIndex (by decide) i = r
  fin_cases r <;> norm_num [degree,cycleGraph,Fin.sum_univ_succ]

lemma cycleCE_compatible (a : ℝ) (m : ℕ) (A : Graph (4*m)) :
    Compatible (cycleModel a m).R (cycleModel a m).d A ↔ A = (cycleModel a m).G := by
  have hd : (cycleModel a m).d = degree (cycleModel a m).G :=
    funext fun i => (cycleCE_degree a m i).symm
  rw [hd]
  exact saturated_graph_singleton _ _

lemma cycleCE_homoskedastic (a : ℝ) (m : ℕ) : Homoskedastic (cycleModel a m) := by
  intro i j
  simp [cycleCE_covariance,adjacency,(cycleModel a m).G.property.2]

lemma cycleCE_nested (a : ℝ) : Nested (cycleFamily a) := by
  constructor
  · intro k l hkl
    change 4*(k+1) ≤ 4*(l+1)
    omega
  · intro k
    let e : Fin (4*(k+1)) ↪ Fin (4*(k+1+1)) :=
      ⟨fun i => ⟨i.val, by have hi := i.isLt; omega⟩,
        fun i j hij => Fin.ext (congrArg (fun x : Fin (4*(k+1+1)) => x.val) hij)⟩
    exact ⟨e,fun _ _ => rfl⟩

/- A fill-and-restrict argument gives independence for functions of disjoint coordinate sets. -/
lemma cycleCE_separated_functions {I β γ : Type} [Fintype I] [DecidableEq I]
    [MeasurableSpace β] [MeasurableSpace γ]
    (A B : Finset I) (hAB : Disjoint A B) (f : (I → Bool) → β) (g : (I → Bool) → γ)
    (hf : ∀ u v, (∀ p ∈ A, u p = v p) → f u = f v)
    (hg : ∀ u v, (∀ p ∈ B, u p = v p) → g u = g v) :
    IndepFun f g (PMF.uniformOfFintype (I → Bool)).toMeasure := by
  have hi := iIndepFun.indepFun_finset A B hAB
    (cycleCE_independent_coords (I := I) (A := Bool)) (fun p => measurable_pi_apply p)
  let fill (S : Finset I) (a : S → Bool) : I → Bool :=
    fun p => if hp : p ∈ S then a ⟨p,hp⟩ else false
  let F : (A → Bool) → β := fun a => f (fill A a)
  let G : (B → Bool) → γ := fun b => g (fill B b)
  have hF (u : I → Bool) : F (fun p : A => u p.val) = f u := by
    apply hf
    intro p hp
    simp only [fill,dif_pos hp]
  have hG (u : I → Bool) : G (fun p : B => u p.val) = g u := by
    apply hg
    intro p hp
    simp only [fill,dif_pos hp]
  have hh := hi.comp (measurable_of_finite F) (measurable_of_finite G)
  convert hh using 1
  · funext u
    exact (hF u).symm
  · funext u
    exact (hG u).symm

def cycleCE_inc : Fin 4 → Finset (Fin 4) := ![{0,3},{0,1},{1,2},{2,3}]

def cycleCE_support {m : ℕ} (S : Finset (Fin (4*m))) : Finset (Fin m × Fin 4) :=
  Finset.univ.filter (fun p => ∃ i ∈ S,
    blockIndex (by decide) i = p.1 ∧ p.2 ∈ cycleCE_inc (localIndex (by decide) i))

lemma cycleCE_inc_overlap (r s t : Fin 4) (hr : t ∈ cycleCE_inc r)
    (hs : t ∈ cycleCE_inc s) : r=s ∨ cycleGraph.val r s = true := by
  fin_cases r <;> fin_cases s <;> fin_cases t <;>
    norm_num [cycleCE_inc,cycleGraph] at *

lemma cycleCE_indices_injective {m : ℕ} (i j : Fin (4*m))
    (hb : blockIndex (by decide) i = blockIndex (by decide) j)
    (hr : localIndex (by decide) i = localIndex (by decide) j) : i=j := by
  obtain ⟨⟨b,r⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective i
  obtain ⟨⟨c,s⟩,rfl⟩ := (StarCompletion.blockEquiv 4 m).surjective j
  simp only [cycleCE_blockIndex] at hb
  simp only [StarCompletion.block_local] at hr
  subst c
  subst s
  rfl

lemma cycleCE_support_disjoint {m : ℕ} (S T : Finset (Fin (4*m)))
    (hd : Disjoint S T)
    (hn : ∀ i ∈ S, ∀ j ∈ T, (blockGraph (by decide) cycleGraph m).val i j = false) :
    Disjoint (cycleCE_support S) (cycleCE_support T) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨i,hi,hbi,hri⟩ := (Finset.mem_filter.mp hp).2
  obtain ⟨j,hj,hbj,hrj⟩ := (Finset.mem_filter.mp hq).2
  have hb := hbi.trans hbj.symm
  rcases cycleCE_inc_overlap _ _ p.2 hri hrj with he | he
  · have hij := cycleCE_indices_injective i j hb he
    subst j
    exact Finset.disjoint_left.mp hd hi hj
  · have hval : i.val/4 = j.val/4 := congrArg (fun b : Fin m => b.val) hb
    have hh := hn i hi j hj
    simp only [blockGraph,hval,decide_true,Bool.true_and,he] at hh
    contradiction

lemma cycleCE_source_depends (a : ℝ) (m : ℕ) (S : Finset (Fin (4*m)))
    (u v : (Fin m × Fin 4) → Bool)
    (h : ∀ p ∈ cycleCE_support S, u p = v p) :
    (fun i : S => cycleCE_source a m (Function.curry u) i.val) =
    (fun i : S => cycleCE_source a m (Function.curry v) i.val) := by
  funext i
  have hh (r : Fin 4) (hr : r ∈ cycleCE_inc (localIndex (by decide) i.val)) :
      u (blockIndex (by decide) i.val,r) = v (blockIndex (by decide) i.val,r) := by
    apply h
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,i.val,i.property,rfl,hr⟩
  dsimp only [cycleCE_source,Function.curry]
  generalize localIndex (by decide) i.val = r at *
  fin_cases r <;> simp_all [cycleBlock,cycleCE_inc]

lemma cycleCE_dependency (a : ℝ) (m : ℕ) : Dependency (cycleModel a m) := by
  let e : ((Fin m × Fin 4) → Bool) ≃ (Fin m → Fin 4 → Bool) :=
    Equiv.curry (Fin m) (Fin 4) Bool
  let g : ((Fin m × Fin 4) → Bool) → Fin (4*m) → ℝ :=
    fun u => cycleCE_source a m (e u)
  have hlaw : (cycleModel a m).law = uniformLaw g := by
    exact (NewFiniteCompletion.uniformLaw_equiv e (cycleCE_source a m)).symm
  intro S T hd hn
  have hi := cycleCE_separated_functions (cycleCE_support S) (cycleCE_support T)
    (cycleCE_support_disjoint S T hd hn)
    (fun u => fun i : S => g u i.val) (fun u => fun j : T => g u j.val)
    (cycleCE_source_depends a m S) (cycleCE_source_depends a m T)
  rw [hlaw,uniformLaw,← PMF.toMeasure_map g (PMF.uniformOfFintype _) (measurable_of_finite g)]
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro s t hs ht
  have hS : MeasurableSet ((fun y : Fin (4*m) → ℝ => fun i : S => y i.val) ⁻¹' s) :=
    hs.preimage (by fun_prop)
  have hT : MeasurableSet ((fun y : Fin (4*m) → ℝ => fun j : T => y j.val) ⁻¹' t) :=
    ht.preimage (by fun_prop)
  rw [Measure.map_apply (measurable_of_finite g) (hS.inter hT),
    Measure.map_apply (measurable_of_finite g) hS,Measure.map_apply (measurable_of_finite g) hT]
  simpa only [Set.preimage_inter,Set.preimage_preimage,Function.comp_def] using
    hi.measure_inter_preimage_eq_mul s t hs ht


lemma cycleCE_affine_moments (m : ℕ) (x y z : ℝ) :
    cycleCE_avg (fun u => x*cycleCE_Q m u+y*cycleCE_W m u^2+z) =
      x*(7*m)+y*(4*m)+z ∧
    cycleCE_avg (fun u =>
      (x*cycleCE_Q m u+y*cycleCE_W m u^2+z-(x*(7*m)+y*(4*m)+z))^2) =
      x^2*(176*m)+y^2*(32*(m : ℝ)^2-8*m)+2*x*y*(64*m) := by
  rcases cycleCE_aggregate_moments m with ⟨h1,h2,h3,h4,hq,hq2,hqw2⟩
  have hmix : cycleCE_avg (fun u => cycleCE_W m u^2*cycleCE_Q m u) =
      28*(m : ℝ)^2+64*m := by simpa only [mul_comm] using hqw2
  have hscaled : cycleCE_avg (fun u => x*cycleCE_Q m u*y*cycleCE_W m u^2) =
      x*y*(28*(m : ℝ)^2+64*m) := by
    calc
      _ = cycleCE_avg (fun u => (x*y)*(cycleCE_Q m u*cycleCE_W m u^2)) := by
        congr 1
        funext u
        ring
      _ = _ := by rw [cycleCE_avg_mul_left,hqw2]
  constructor
  · simp only [cycleCE_avg_add,cycleCE_avg_mul_left,cycleCE_avg_const,hq,h2]
  · conv_lhs => arg 1; ext u; ring_nf
    simp only [cycleCE_avg_add,cycleCE_avg_sub,cycleCE_avg_mul_left,
      cycleCE_avg_mul_right,cycleCE_avg_const,h1,h2,h3,h4,hq,hq2,hqw2,hmix,hscaled] <;> ring

def cycleCE_T (a : ℝ) (m : ℕ) (y : Fin (4*m) → ℝ) : ℝ :=
  (4*m : ℝ)*V1 (cycleModel a m).G (weighted (cycleModel a m) y)

lemma cycleCE_T_measurable (a : ℝ) (m : ℕ) : Measurable (cycleCE_T a m) := by
  unfold cycleCE_T V1 centered average quadratic weighted
  fun_prop

lemma cycleCE_T_moments (a : ℝ) (m : ℕ) (hm : 0 < m) :
    expectation (cycleModel a m) (cycleCE_T a m) = 4-a^2-3/(m : ℝ) ∧
    var (cycleModel a m) (cycleCE_T a m) =
      11/(m : ℝ)-6/(m : ℝ)^2-(9/2)/(m : ℝ)^3 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  let x : ℝ := 1/(4*m)
  let y : ℝ := -3/(4*(m : ℝ)^2)
  let z : ℝ := 9/4-a^2
  have hstat (u : Fin m → Fin 4 → Bool) :
      cycleCE_T a m (cycleCE_source a m u) = x*cycleCE_Q m u+y*cycleCE_W m u^2+z := by
    rw [cycleCE_T,cycleCE_scaled_source a m hm]
    dsimp [x,y,z]
    ring
  have hex : x*(7*m)+y*(4*m)+z = 4-a^2-3/(m : ℝ) := by
    dsimp [x,y,z]
    field_simp
    <;> ring
  have hmean : expectation (cycleModel a m) (cycleCE_T a m) = 4-a^2-3/(m : ℝ) := by
    rw [cycleCE_integral _ _ _ (cycleCE_T_measurable a m)]
    simp only [hstat]
    rw [(cycleCE_affine_moments m x y z).1,hex]
  refine ⟨hmean,?_⟩
  unfold var
  rw [hmean]
  have hg : Measurable (fun v : Fin (4*m) → ℝ =>
      (cycleCE_T a m v-(4-a^2-3/(m : ℝ)))^2) := by
    have hh := cycleCE_T_measurable a m
    fun_prop
  rw [cycleCE_integral a m _ hg]
  simp only [hstat,← hex]
  rw [(cycleCE_affine_moments m x y z).2]
  dsimp [x,y]
  field_simp
  <;> ring

lemma cycleCE_block_bound (a : ℝ) (u : Fin 4 → Bool) (r : Fin 4) :
    |cycleBlock a (fun s => sign (u s)) r| ≤ |a|+2 := by
  have hs (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
  have hb (v : ℝ) (p q : Bool) : |v+sign p+sign q| ≤ |v|+2 := by
    calc
      _ ≤ |v+sign p|+|sign q| := abs_add_le _ _
      _ ≤ (|v|+|sign p|)+|sign q| := add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [hs,hs]; ring
  fin_cases r
  · exact hb a (u 0) (u 3)
  · change |-a+sign (u 0)+sign (u 1)| ≤ |a|+2
    simpa only [abs_neg] using hb (-a) (u 0) (u 1)
  · exact hb a (u 1) (u 2)
  · change |-a+sign (u 2)+sign (u 3)| ≤ |a|+2
    simpa only [abs_neg] using hb (-a) (u 2) (u 3)

lemma cycleCE_ae_bound (a : ℝ) (m : ℕ) :
    ∀ᵐ y ∂(cycleModel a m).law, ∀ i, |y i| ≤ |a|+2 := by
  have hf : Measurable (cycleCE_source a m) := measurable_of_finite _
  change ∀ᵐ y ∂uniformLaw (cycleCE_source a m), ∀ i, |y i| ≤ |a|+2
  rw [uniformLaw,← PMF.toMeasure_map _ (PMF.uniformOfFintype _) hf]
  have hset : MeasurableSet {y : Fin (4*m) → ℝ | ∀ i, |y i| ≤ |a|+2} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le (by fun_prop) measurable_const)
  apply (ae_map_iff hf.aemeasurable hset).mpr
  exact Eventually.of_forall (fun u i => cycleCE_block_bound a _ _)

lemma cycleCE_scaling (a c : ℝ) (hc : 0 < c) (hac : |a|+2 ≤ c) :
    Scaling (cycleFamily a) c 2 4 2 ∧ Valid (cycleFamily a) := by
  refine ⟨⟨cycleCE_nested a,hc,by norm_num,by norm_num,by norm_num,?_,?_,?_,?_,?_⟩,?_⟩
  · intro k
    exact cycleCE_dependency a (k+1)
  · intro k
    filter_upwards [cycleCE_ae_bound a (k+1)] with y hy i
    simpa only [cycleFamily,cycleCE_weighted,cycleCE_beta_zero,sub_zero] using (hy i).trans hac
  · intro k i
    change (degree (cycleModel a (k+1)).G i : ℝ) ≤ 2
    rw [cycleCE_degree]
    norm_num
  · have he (k : ℕ) : ((cycleFamily a).size k : ℝ)*
        var ((cycleFamily a).model k) (betaHat ((cycleFamily a).model k)) = 4 := by
      change ((4*(k+1) : ℕ) : ℝ)*var (cycleModel a (k+1)) (betaHat (cycleModel a (k+1))) = 4
      rw [cycleCE_true_variance a (k+1) (by omega)]
      push_cast
      field_simp
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4))
  · intro k i
    change |(1 : ℝ)| < 2
    norm_num
  · intro k
    exact (cycleCE_compatible a (k+1) _).mpr rfl


lemma cycleCE_probability_limit (a : ℝ) :
    InProbability (cycleFamily a) (scaledOracle (cycleFamily a)) (fun _ => 4-a^2) := by
  let μ := fun k => (cycleModel a (k+1)).law
  let (k : ℕ) : IsProbabilityMeasure (μ k) := (cycleModel a (k+1)).probability
  let X := fun k => cycleCE_T a (k+1)
  have hL (k : ℕ) : MemLp (X k) 2 (μ k) :=
    NewFiniteCompletion.finite_memLp (cycleCE_source a (k+1)) _ (cycleCE_T_measurable _ _) 2
  have hmean (k : ℕ) : (∫ y, X k y ∂μ k) = 4-a^2-3/(k+1 : ℝ) := by
    simpa only [expectation,μ,X,Nat.cast_add,Nat.cast_one] using
      (cycleCE_T_moments a (k+1) (by omega)).1
  have hv (k : ℕ) : ProbabilityTheory.variance (X k) (μ k) =
      11/(k+1 : ℝ)-6/(k+1 : ℝ)^2-(9/2)/(k+1 : ℝ)^3 := by
    rw [ProbabilityTheory.variance_eq_integral (hL k).aemeasurable]
    simpa only [var,expectation,μ,X,Nat.cast_add,Nat.cast_one] using
      (cycleCE_T_moments a (k+1) (by omega)).2
  have hN : Tendsto (fun k : ℕ => (k+1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hInv : Tendsto (fun k : ℕ => 1/(k+1 : ℝ)) atTop (𝓝 0) := hN.const_div_atTop 1
  have hvar : Tendsto (fun k => ProbabilityTheory.variance (X k) (μ k)) atTop (𝓝 0) := by
    simp only [hv]
    have hh := ((hInv.const_mul 11).sub ((hInv.pow 2).const_mul 6)).sub
      ((hInv.pow 3).const_mul (9/2))
    convert hh using 1 <;> simp [div_pow] <;> ring
  have hm : Tendsto (fun k : ℕ => 4-a^2-3/(k+1 : ℝ)) atTop (𝓝 (4-a^2)) := by
    simpa using tendsto_const_nhds.sub (hN.const_div_atTop 3)
  have hcp := OracleCompletion.rowCP_of_variance μ X hL hvar
  simp only [hmean] at hcp
  have hh := CoverageCompletion.rowCP_moving_center μ X _ (4-a^2) hcp hm
  intro ε hε
  convert hh ε hε using 1
  funext k
  congr 1
  ext y
  simp only [scaledOracle,cycleFamily,probability,μ,X,cycleCE_T,Nat.cast_mul,
    Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]

lemma cycleCE_neighborhood_mass {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (μ : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (μ k)]
    (X : ∀ k, Ω k → ℝ) (hX : ∀ k, Measurable (X k)) (c : ℝ)
    (hcp : CoverageCompletion.RowCP μ X c) (δ : ℝ) (hδ : 0 < δ)
    (E : ∀ k, Set (Ω k)) (hE : ∀ k ω, |X k ω-c| ≤ δ → ω ∈ E k) :
    Tendsto (fun k => (μ k).real (E k)) atTop (𝓝 1) := by
  have hlo : Tendsto (fun k => 1-(μ k).real {ω | |X k ω-c| > δ}) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hcp δ hδ)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
  · intro k
    change 1-(μ k).real {ω | |X k ω-c| > δ} ≤ (μ k).real (E k)
    have hxk := hX k
    have hs : MeasurableSet {ω | |X k ω-c| > δ} :=
      measurableSet_lt measurable_const (by fun_prop)
    have hc := measureReal_compl (μ := μ k) hs
    rw [probReal_univ] at hc
    rw [← hc]
    apply measureReal_mono (μ := μ k) _ (measure_ne_top _ _)
    intro ω hω
    apply hE
    exact le_of_not_gt hω
  · intro k
    simpa only [probReal_univ] using
      (measureReal_mono (μ := μ k) (Set.subset_univ (E k)))

@[simp] lemma cycleCE_family_model (a : ℝ) (k : ℕ) :
    (cycleFamily a).model k = cycleModel a (k+1) := rfl

@[simp] lemma cycleCE_family_size (a : ℝ) (k : ℕ) :
    (cycleFamily a).size k = 4*(k+1) := rfl

lemma cycleCE_scaled_oracle (a : ℝ) (k : ℕ) :
    scaledOracle (cycleFamily a) k = cycleCE_T a (k+1) := by
  funext y
  simp [scaledOracle,cycleFamily,cycleCE_T]

lemma cycleCE_failure_limits (ε : ℝ) (_hε : 0 < ε) (hε9 : ε < 9/4) :
    Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
      {y | |scaledOracle (cycleFamily (3/2)) k y-4| > ε}) atTop (𝓝 1) ∧
    Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
      {y | 4-scaledOracle (cycleFamily (3/2)) k y > ε}) atTop (𝓝 1) := by
  let F := cycleFamily (3/2)
  let μ := fun k => (F.model k).law
  let (k : ℕ) : IsProbabilityMeasure (μ k) := (F.model k).probability
  have hcp : CoverageCompletion.RowCP μ (scaledOracle F) (7/4) := by
    change InProbability F (scaledOracle F) (fun _ => 7/4)
    convert cycleCE_probability_limit (3/2) using 1 <;> norm_num
  have hmeas (k : ℕ) : Measurable (scaledOracle F k) := by
    change Measurable (scaledOracle (cycleFamily (3/2)) k)
    rw [cycleCE_scaled_oracle]
    exact cycleCE_T_measurable _ _
  let δ : ℝ := (9/4-ε)/2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  constructor
  · apply cycleCE_neighborhood_mass μ _ hmeas (7/4) hcp δ hδ
    intro k y hy
    have hh := (abs_le.mp hy).2
    change ε < |scaledOracle F k y-4|
    have hl := neg_le_abs (scaledOracle F k y-4)
    dsimp [δ] at hh
    linarith
  · apply cycleCE_neighborhood_mass μ _ hmeas (7/4) hcp δ hδ
    intro k y hy
    have hh := (abs_le.mp hy).2
    change ε < 4-scaledOracle F k y
    dsimp [δ] at hh
    linarith


lemma cycleCE_scaled_true (a : ℝ) (k : ℕ) : scaledTrue (cycleFamily a) k = 4 := by
  change ((4*(k+1) : ℕ) : ℝ)*var (cycleModel a (k+1)) (betaHat (cycleModel a (k+1))) = 4
  rw [cycleCE_true_variance a (k+1) (by omega)]
  push_cast
  field_simp

lemma cycleCE_standardized (a : ℝ) (m : ℕ) (hm : 0 < m) (y : Fin (4*m) → ℝ) :
    Real.sqrt ((4*m : ℕ) : ℝ)*betaHat (cycleModel a m) y =
      2*standardized (cycleModel a m) y := by
  rw [standardized,cycleCE_beta_zero,cycleCE_true_variance a m hm]
  push_cast
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  simp only [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),Real.sqrt_one,sub_zero]
  norm_num
  ring

lemma cycleCE_cdf_limit (h : Scaling (cycleFamily (3/2)) (7/2) 2 4 2) (t : ℝ) :
    Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
      {y | Real.sqrt ((cycleFamily (3/2)).size k : ℝ)*betaHat ((cycleFamily (3/2)).model k) y ≤ t})
      atTop (𝓝 (Phi (t/2))) := by
  have hh := dependency_graph_clt (cycleFamily (3/2)) (7/2) 2 4 2 h (t/2)
  convert hh using 1
  funext k
  congr 1
  ext y
  change (Real.sqrt ((4*(k+1) : ℕ) : ℝ)*betaHat (cycleModel (3/2) (k+1)) y ≤ t) ↔ _
  rw [cycleCE_standardized _ _ (by omega)]
  change (2*standardized (cycleModel (3/2) (k+1)) y ≤ t) ↔
    (standardized (cycleModel (3/2) (k+1)) y ≤ t/2)
  constructor <;> intro ht <;> linarith

local instance instNullSingletonGLP011B1 : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num : (1 : NNReal) ≠ 0)

lemma cycleCE_coverage_limit (h : Scaling (cycleFamily (3/2)) (7/2) 2 4 2)
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun k => coverage ((cycleFamily (3/2)).model k)
      (fun y => V1 ((cycleFamily (3/2)).model k).G
        (weighted ((cycleFamily (3/2)).model k) y)) α)
      atTop (𝓝 (2*Phi (normalQuantile α*Real.sqrt (7/16))-1)) ∧
    2*Phi (normalQuantile α*Real.sqrt (7/16))-1 < 1-α := by
  let F := cycleFamily (3/2)
  let μ := fun k => (F.model k).law
  let (k : ℕ) : IsProbabilityMeasure (μ k) := (F.model k).probability
  let z := normalQuantile α
  have hz : 0 < z := CoverageCompletion.quantile_positive α hα hα1
  let f : ℝ × ℝ → ℝ := fun u => z*Real.sqrt (max u.1 0)/2
  let W := fun k y => z*Real.sqrt (max (scaledOracle F k y) 0)/2
  have hcp : CoverageCompletion.RowCP μ (scaledOracle F) (7/4) := by
    change InProbability F (scaledOracle F) (fun _ => 7/4)
    convert cycleCE_probability_limit (3/2) using 1 <;> norm_num
  have hfc : f (7/4,7/4) = z*Real.sqrt (7/16) := by
    dsimp [f]
    rw [max_eq_left (by norm_num : (0 : ℝ) ≤ 7/4),
      show (7/16 : ℝ) = (7/4)/4 by norm_num,Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 7/4)]
    norm_num
    ring
  have hW : CoverageCompletion.RowCP μ W (z*Real.sqrt (7/16)) := by
    convert CoverageCompletion.rowCP_continuous_pair μ _ _ (7/4) (7/4) hcp hcp f
      (by dsimp [f]; fun_prop) using 1
    exact hfc.symm
  have hPhi : Continuous Phi := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact AronowAudit.P053.NormalCompletion.cdf_continuousAt (gaussianReal 0 1) t
  have hZ (k : ℕ) : Measurable (standardized (F.model k)) :=
    ((ProbabilityCompletion.betaHat_measurable _).sub measurable_const).div_const _
  have hw : 0 < z*Real.sqrt (7/16) := mul_pos hz (Real.sqrt_pos.mpr (by norm_num))
  have hlim := CoverageCompletion.row_random_width_interval μ (fun k => standardized (F.model k)) W hZ
    Phi (dependency_graph_clt F (7/2) 2 4 2 h) hPhi (monotone_cdf (μ := gaussianReal 0 1))
    (z*Real.sqrt (7/16)) hw hW
  have hneg (t : ℝ) : Phi (-t) = 1-Phi t :=
    AronowAudit.P053.NormalCompletion.normal_cdf_neg t
  rw [hneg] at hlim
  constructor
  · have heq (k : ℕ) : coverage (F.model k)
        (fun y => V1 (F.model k).G (weighted (F.model k) y)) α =
        (μ k).real {y | |standardized (F.model k) y| ≤ W k y} := by
      apply congrArg ((μ k).real)
      ext y
      change (|betaHat (F.model k) y-beta (F.model k)| ≤
        z*Real.sqrt (max (V1 (F.model k).G (weighted (F.model k) y)) 0)) ↔
          (|standardized (F.model k) y| ≤ W k y)
      have hv : 0 < var (F.model k) (betaHat (F.model k)) := by
        change 0 < var (cycleModel (3/2) (k+1)) (betaHat (cycleModel (3/2) (k+1)))
        rw [cycleCE_true_variance _ _ (by omega)]
        positivity
      have hwidth : W k y = z*Real.sqrt (max (V1 (F.model k).G (weighted (F.model k) y)) 0) /
          Real.sqrt (var (F.model k) (betaHat (F.model k))) := by
        have hh := CoverageCompletion.scaled_width (F.size k : ℝ)
          (var (F.model k) (betaHat (F.model k)))
          (V1 (F.model k).G (weighted (F.model k) y)) z
          (by exact_mod_cast F.positive k)
        change z*Real.sqrt (max (scaledOracle F k y) 0)/Real.sqrt (scaledTrue F k) = _ at hh
        rw [cycleCE_scaled_true] at hh
        norm_num at hh
        exact hh
      rw [hwidth,standardized,abs_div,abs_of_pos (Real.sqrt_pos.mpr hv)]
      exact (div_le_div_iff_of_pos_right (Real.sqrt_pos.mpr hv)).symm
    simp only [← heq] at hlim
    have halg : Phi (z*Real.sqrt (7/16))-(1-Phi (z*Real.sqrt (7/16))) =
        2*Phi (z*Real.sqrt (7/16))-1 := by ring
    rw [halg] at hlim
    exact hlim
  · have hs : Real.sqrt (7/16 : ℝ) < 1 := by
      have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7/16)
      have hn := Real.sqrt_nonneg (7/16 : ℝ)
      nlinarith
    have hlt : z*Real.sqrt (7/16) < z := by nlinarith
    have hPhiLt : Phi (z*Real.sqrt (7/16)) < Phi z :=
      AronowAudit.P053.NormalCompletion.strictMono_normal_cdf hlt
    have hmass := CoverageCompletion.quantile_mass α hα hα1
    rw [hneg] at hmass
    change 2*Phi (z*Real.sqrt (7/16))-1 < 1-α
    dsimp only [z] at hPhiLt
    linarith

theorem cycle_counterexample_proof :
    Scaling (cycleFamily (3/2)) (7/2) 2 4 2 ∧ Valid (cycleFamily (3/2)) ∧
    (∀ k, Homoskedastic ((cycleFamily (3/2)).model k) ∧
      (∀ i, expectation ((cycleFamily (3/2)).model k) (fun y => y i) =
        (![3/2,-3/2,3/2,-3/2] : Fin 4 → ℝ) (localIndex (by decide) i)) ∧
      (∀ i j, covariance ((cycleFamily (3/2)).model k) i j =
        ((2 : ℝ) • (1 : Matrix (Fin ((cycleFamily (3/2)).size k))
          (Fin ((cycleFamily (3/2)).size k)) ℝ) + adjacency ((cycleFamily (3/2)).model k).G) i j)) ∧
    (∀ k, beta ((cycleFamily (3/2)).model k) = 0 ∧
      scaledTrue (cycleFamily (3/2)) k = 4 ∧
      meanBias ((cycleFamily (3/2)).model k) = -9/4 ∧
      (∀ A, Compatible ((cycleFamily (3/2)).model k).R ((cycleFamily (3/2)).model k).d A
        ↔ A = ((cycleFamily (3/2)).model k).G) ∧
      expectation ((cycleFamily (3/2)).model k) (scaledOracle (cycleFamily (3/2)) k) =
        7/4 - 12 / ((cycleFamily (3/2)).size k : ℝ) ∧
      var ((cycleFamily (3/2)).model k) (scaledOracle (cycleFamily (3/2)) k) =
        44 / ((cycleFamily (3/2)).size k : ℝ) - 96 / ((cycleFamily (3/2)).size k : ℝ)^2 -
        288 / ((cycleFamily (3/2)).size k : ℝ)^3) ∧
    InProbability (cycleFamily (3/2)) (scaledOracle (cycleFamily (3/2))) (fun _ => 7/4) ∧
    (∀ ε : ℝ, 0 < ε → ε < 9/4 →
      Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
        {y | |scaledOracle (cycleFamily (3/2)) k y - 4| > ε}) atTop (𝓝 1) ∧
      Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
        {y | 4 - scaledOracle (cycleFamily (3/2)) k y > ε}) atTop (𝓝 1)) ∧
    (∀ t : ℝ, Tendsto (fun k => probability ((cycleFamily (3/2)).model k)
      {y | Real.sqrt ((cycleFamily (3/2)).size k : ℝ)*betaHat ((cycleFamily (3/2)).model k) y ≤ t})
      atTop (𝓝 (Phi (t/2)))) ∧
    (∀ α : ℝ, 0 < α → α < 1 →
      Tendsto (fun k => coverage ((cycleFamily (3/2)).model k)
        (fun y => V1 ((cycleFamily (3/2)).model k).G (weighted ((cycleFamily (3/2)).model k) y)) α)
        atTop (𝓝 (2*Phi (normalQuantile α * Real.sqrt (7/16)) - 1)) ∧
      2*Phi (normalQuantile α * Real.sqrt (7/16)) - 1 < 1-α) ∧
    Scaling (cycleFamily 3) 5 2 4 2 ∧ Valid (cycleFamily 3) ∧
    (∀ k, Homoskedastic ((cycleFamily 3).model k) ∧ beta ((cycleFamily 3).model k)=0 ∧
      scaledTrue (cycleFamily 3) k=4) ∧
    InProbability (cycleFamily 3) (scaledOracle (cycleFamily 3)) (fun _ => -5) ∧
    probability (cycleModel 3 1) {y | y=(![5,-1,5,-1] : Fin 4 → ℝ)}=1/16 ∧
    V1 cycleGraph (![5,-1,5,-1] : Fin 4 → ℝ) = -9/4 := by
  have hsmall := cycleCE_scaling (3/2) (7/2) (by norm_num) (by norm_num)
  have hlarge := cycleCE_scaling 3 5 (by norm_num) (by norm_num)
  refine ⟨hsmall.1,hsmall.2,?_,?_,?_,cycleCE_failure_limits,
    cycleCE_cdf_limit hsmall.1,cycleCE_coverage_limit hsmall.1,
    hlarge.1,hlarge.2,?_,?_,cycle_negative_probability.1,cycle_negative_probability.2⟩
  · intro k
    refine ⟨cycleCE_homoskedastic _ _,?_,cycleCE_covariance _ _⟩
    intro i
    dsimp only [cycleFamily] at i ⊢
    rw [cycleCE_coordinate_mean]
    norm_num [cycleCE_mu]
  · intro k
    refine ⟨cycleCE_beta_zero _ _,cycleCE_scaled_true _ _,?_,cycleCE_compatible _ _,?_,?_⟩
    · simpa only [cycleCE_family_model,show -((3/2 : ℝ)^2) = -9/4 by norm_num] using
        cycleCE_mean_bias (3/2) (k+1) (by omega)
    · have hh := (cycleCE_T_moments (3/2) (k+1) (by omega)).1
      rw [cycleCE_family_model,cycleCE_scaled_oracle,hh]
      simp only [cycleFamily,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
      field_simp
      <;> ring
    · have hh := (cycleCE_T_moments (3/2) (k+1) (by omega)).2
      rw [cycleCE_family_model,cycleCE_scaled_oracle,hh]
      simp only [cycleFamily,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one]
      field_simp
      <;> ring
  · convert cycleCE_probability_limit (3/2) using 1 <;> norm_num
  · intro k
    exact ⟨cycleCE_homoskedastic _ _,cycleCE_beta_zero _ _,cycleCE_scaled_true _ _⟩
  · convert cycleCE_probability_limit 3 using 1 <;> norm_num

end
end AronowAudit.P011.Wave1
