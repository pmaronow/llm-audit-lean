import AronowAudit.P011.P011_ProbabilityCompletion

namespace AronowAudit.P011.CovarianceCompletion
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal ProbabilityTheory
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
local instance : ENNReal.HolderTriple (4:ENNReal) 4 2 := ⟨by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add]⟩

section Generic
variable {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma product4_integrable {a b c d : Ω → ℝ}
    (ha : MemLp a 4 μ) (hb : MemLp b 4 μ) (hc : MemLp c 4 μ) (hd : MemLp d 4 μ) :
    Integrable (fun ω => a ω*b ω*c ω*d ω) μ := by
  have hab : MemLp (fun ω => a ω*b ω) 2 μ := ha.mul hb
  have hcd : MemLp (fun ω => c ω*d ω) 2 μ := hc.mul hd
  exact (hab.integrable_mul hcd).congr (Eventually.of_forall fun ω => by dsimp only [Pi.mul_apply]; ring)

lemma pair_expansion {a b B : Ω → ℝ}
    (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) (hB : MemLp B 2 μ) :
    (∫ ω, (a ω-B ω)*(b ω-B ω) ∂μ) =
      (∫ ω, a ω*b ω ∂μ)-(∫ ω, a ω*B ω ∂μ)-
      (∫ ω, b ω*B ω ∂μ)+(∫ ω, B ω^2 ∂μ) := by
  have haa : Integrable (fun ω => a ω*b ω) μ := (ha.integrable_mul hb).congr (Eventually.of_forall fun ω => rfl)
  have hab : Integrable (fun ω => a ω*B ω) μ := (ha.integrable_mul hB).congr (Eventually.of_forall fun ω => rfl)
  have hbb : Integrable (fun ω => b ω*B ω) μ := (hb.integrable_mul hB).congr (Eventually.of_forall fun ω => rfl)
  have hsq : Integrable (fun ω => B ω^2) μ := (hB.integrable_mul hB).congr (Eventually.of_forall fun ω => by dsimp only [Pi.mul_apply]; ring)
  have hsub : Integrable (fun ω => a ω*b ω-a ω*B ω) μ := haa.sub' hab
  have hsub2 : Integrable (fun ω => a ω*b ω-a ω*B ω-b ω*B ω) μ := hsub.sub' hbb
  calc
    _ = ∫ ω, a ω*b ω-a ω*B ω-b ω*B ω+B ω^2 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply]; ring)
    _ = _ := by
      rw [integral_add hsub2 hsq,
        integral_sub hsub hbb, integral_sub haa hab]

lemma fourth_expansion {a b c d B : Ω → ℝ}
    (ha : MemLp a 4 μ) (hb : MemLp b 4 μ) (hc : MemLp c 4 μ) (hd : MemLp d 4 μ)
    (hB : MemLp B 4 μ) :
    (∫ ω, (a ω-B ω)*(b ω-B ω)*(c ω-B ω)*(d ω-B ω) ∂μ) =
      fourthMoment (fun f => ∫ ω, f ω ∂μ) a b c d B := by
  have hA := product4_integrable ha hb hc hd
  have hB3 : Integrable (fun ω => B ω*(a ω*b ω*c ω+a ω*b ω*d ω+a ω*c ω*d ω+b ω*c ω*d ω)) μ := by
    exact (((product4_integrable hB ha hb hc).add (product4_integrable hB ha hb hd)).add
      (product4_integrable hB ha hc hd) |>.add (product4_integrable hB hb hc hd)).congr
      (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply]; ring)
  have hB2 : Integrable (fun ω => B ω^2*(a ω*b ω+a ω*c ω+a ω*d ω+b ω*c ω+b ω*d ω+c ω*d ω)) μ := by
    exact (((((product4_integrable hB hB ha hb).add (product4_integrable hB hB ha hc)).add
      (product4_integrable hB hB ha hd)).add (product4_integrable hB hB hb hc)).add
      (product4_integrable hB hB hb hd) |>.add (product4_integrable hB hB hc hd)).congr
      (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply]; ring)
  have hB1 : Integrable (fun ω => B ω^3*(a ω+b ω+c ω+d ω)) μ := by
    exact (((product4_integrable hB hB hB ha).add (product4_integrable hB hB hB hb)).add
      (product4_integrable hB hB hB hc) |>.add (product4_integrable hB hB hB hd)).congr
      (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply]; ring)
  have hB4 : Integrable (fun ω => B ω^4) μ :=
    (product4_integrable hB hB hB hB).congr (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply]; ring)
  have hab : Integrable (fun ω => a ω*b ω*c ω*d ω-
      B ω*(a ω*b ω*c ω+a ω*b ω*d ω+a ω*c ω*d ω+b ω*c ω*d ω)) μ := hA.sub' hB3
  have habc : Integrable (fun ω => a ω*b ω*c ω*d ω-
      B ω*(a ω*b ω*c ω+a ω*b ω*d ω+a ω*c ω*d ω+b ω*c ω*d ω)+
      B ω^2*(a ω*b ω+a ω*c ω+a ω*d ω+b ω*c ω+b ω*d ω+c ω*d ω)) μ := hab.fun_add hB2
  have habcd : Integrable (fun ω => a ω*b ω*c ω*d ω-
      B ω*(a ω*b ω*c ω+a ω*b ω*d ω+a ω*c ω*d ω+b ω*c ω*d ω)+
      B ω^2*(a ω*b ω+a ω*c ω+a ω*d ω+b ω*c ω+b ω*d ω+c ω*d ω)-
      B ω^3*(a ω+b ω+c ω+d ω)) μ := habc.sub' hB1
  calc
    _ = ∫ ω, a ω*b ω*c ω*d ω-
        B ω*(a ω*b ω*c ω+a ω*b ω*d ω+a ω*c ω*d ω+b ω*c ω*d ω)+
        B ω^2*(a ω*b ω+a ω*c ω+a ω*d ω+b ω*c ω+b ω*d ω+c ω*d ω)-
        B ω^3*(a ω+b ω+c ω+d ω)+B ω^4 ∂μ :=
      integral_congr_ae (Eventually.of_forall fun ω => fourth_polynomial _ _ _ _ _)
    _ = _ := by
      unfold fourthMoment
      rw [integral_add habcd hB4,
        integral_sub habc hB1,
        integral_add hab hB2, integral_sub hA hB3]

lemma covariance_const_products {a b c d : Ω → ℝ}
    (ha : MemLp a 4 μ) (hb : MemLp b 4 μ) (hc : MemLp c 4 μ) (hd : MemLp d 4 μ)
    (t : ℝ) :
    cov[fun ω => (a ω-t)*(b ω-t), fun ω => (c ω-t)*(d ω-t); μ] =
      cov[fun ω => a ω*b ω, fun ω => c ω*d ω; μ] -
      t*(cov[fun ω => a ω*b ω,c; μ]+cov[fun ω => a ω*b ω,d; μ]+
         cov[a,fun ω => c ω*d ω; μ]+cov[b,fun ω => c ω*d ω; μ]) +
      t^2*(cov[a,c; μ]+cov[a,d; μ]+cov[b,c; μ]+cov[b,d; μ]) := by
  have ha2 : MemLp a 2 μ := ha.mono_exponent (by norm_num)
  have hb2 : MemLp b 2 μ := hb.mono_exponent (by norm_num)
  have hc2 : MemLp c 2 μ := hc.mono_exponent (by norm_num)
  have hd2 : MemLp d 2 μ := hd.mono_exponent (by norm_num)
  have hab : MemLp (fun ω => a ω*b ω) 2 μ := ha.mul hb
  have hcd : MemLp (fun ω => c ω*d ω) 2 μ := hc.mul hd
  have htab : MemLp (fun ω => t*(a ω+b ω)) 2 μ := (ha2.add hb2).const_mul t
  have htcd : MemLp (fun ω => t*(c ω+d ω)) 2 μ := (hc2.add hd2).const_mul t
  have habid : (fun ω => (a ω-t)*(b ω-t)) = (fun ω => a ω*b ω-t*(a ω+b ω)+t^2) := by
    funext ω; ring
  have hcdid : (fun ω => (c ω-t)*(d ω-t)) = (fun ω => c ω*d ω-t*(c ω+d ω)+t^2) := by
    funext ω; ring
  have habsub : MemLp (fun ω => a ω*b ω-t*(a ω+b ω)) 2 μ := by
    exact (memLp_congr_ae (Eventually.of_forall fun ω => rfl)).mp (hab.sub htab)
  have hcdsub : MemLp (fun ω => c ω*d ω-t*(c ω+d ω)) 2 μ := by
    exact (memLp_congr_ae (Eventually.of_forall fun ω => rfl)).mp (hcd.sub htcd)
  rw [habid,hcdid,
    covariance_add_const_left (habsub.integrable (by norm_num)) (t^2),
    covariance_add_const_right (hcdsub.integrable (by norm_num)) (t^2),
    covariance_fun_sub_fun_sub hab htab hcd htcd]
  simp only [covariance_const_mul_left,covariance_const_mul_right]
  have habadd : (fun ω => a ω+b ω) = a+b := by funext ω; rfl
  have hcdadd : (fun ω => c ω+d ω) = c+d := by funext ω; rfl
  rw [habadd,hcdadd]
  rw [covariance_add_right hab hc2 hd2,
    covariance_add_left ha2 hb2 hcd,
    covariance_add_left ha2 hb2 (hc2.add hd2),
    covariance_add_right ha2 hc2 hd2,
    covariance_add_right hb2 hc2 hd2]
  ring


lemma weighted_pair_expansion {u v B : Ω → ℝ} (hu : MemLp u 2 μ)
    (hv : MemLp v 2 μ) (hB : MemLp B 2 μ) (ti tj : ℝ) :
    (∫ ω, (ti*u ω-B ω)*(tj*v ω-B ω) ∂μ) =
      pairMoment (fun f => ∫ ω, f ω ∂μ) u v B ti tj := by
  have h1 : (∫ ω, (ti*u ω)*(tj*v ω) ∂μ) = ti*tj*(∫ ω, u ω*v ω ∂μ) := by
    calc
      _ = ∫ ω, (ti*tj)*(u ω*v ω) ∂μ :=
        integral_congr_ae (Eventually.of_forall fun ω => by dsimp only [Pi.add_apply,Pi.sub_apply,Pi.mul_apply]; ring)
      _ = _ := integral_const_mul _ _
  have h2 : (∫ ω, (ti*u ω)*B ω ∂μ) = ti*(∫ ω, u ω*B ω ∂μ) := by
    simpa only [mul_assoc] using integral_const_mul ti (fun ω => u ω*B ω)
  have h3 : (∫ ω, (tj*v ω)*B ω ∂μ) = tj*(∫ ω, v ω*B ω ∂μ) := by
    simpa only [mul_assoc] using integral_const_mul tj (fun ω => v ω*B ω)
  have hp := pair_expansion (hu.const_mul ti) (hv.const_mul tj) hB
  rw [h1,h2,h3] at hp
  exact hp

end Generic

lemma betaHat_memLp4 {n : ℕ} (m : Model n)
    (hx : ∀ i, MemLp (fun y => weighted m y i) 4 m.law) :
    MemLp (betaHat m) 4 m.law := by
  have hsum : MemLp (fun y => ∑ i, weighted m y i) 4 m.law :=
    by simpa using memLp_finsetSum Finset.univ (fun i _ => hx i)
  change MemLp (fun y => (∑ i, weighted m y i)/(n:ℝ)) 4 m.law
  simpa only [div_eq_mul_inv,mul_comm] using hsum.const_mul (n:ℝ)⁻¹

lemma covOf_eq_cov {n : ℕ} (m : Model n) (f g : (Fin n → ℝ) → ℝ)
    (hf : MemLp f 2 m.law) (hg : MemLp g 2 m.law) :
    covOf m f g = ProbabilityTheory.covariance f g m.law := by
  let : IsProbabilityMeasure m.law := m.probability
  exact (ProbabilityTheory.covariance_eq_sub hf hg).symm

lemma corrected_covariance_expansion_completed {n : ℕ} (_hn : 0 < n) (m : Model n)
    (h4 : ∀ i, MemLp (fun y => y i) 4 m.law) (i j k l : Fin n) :
    (let E := expectation m
     let B := betaHat m
     let r : Fin n → (Fin n → ℝ) → ℝ := fun v y => weighted m y v-B y
     (E (fun y => r i y*r j y) = pairMoment E (fun y => y i) (fun y => y j) B (m.theta i) (m.theta j)) ∧
     covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
       E (fun y => r i y*r j y*r k y*r l y)-E (fun y => r i y*r j y)*E (fun y => r k y*r l y) ∧
     covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
       fourthMoment E (fun y => weighted m y i) (fun y => weighted m y j)
         (fun y => weighted m y k) (fun y => weighted m y l) B -
       pairMoment E (fun y => y i) (fun y => y j) B (m.theta i) (m.theta j)*
         pairMoment E (fun y => y k) (fun y => y l) B (m.theta k) (m.theta l)) ∧
    (∀ b : ℝ,
      covOf m (fun y => (weighted m y i-b)*(weighted m y j-b))
        (fun y => (weighted m y k-b)*(weighted m y l-b)) =
      covOf m (fun y => weighted m y i*weighted m y j) (fun y => weighted m y k*weighted m y l) -
      b*(covOf m (fun y => weighted m y i*weighted m y j) (fun y => weighted m y k)+
         covOf m (fun y => weighted m y i*weighted m y j) (fun y => weighted m y l)+
         covOf m (fun y => weighted m y i) (fun y => weighted m y k*weighted m y l)+
         covOf m (fun y => weighted m y j) (fun y => weighted m y k*weighted m y l)) +
      b^2*(covOf m (fun y => weighted m y i) (fun y => weighted m y k)+
         covOf m (fun y => weighted m y i) (fun y => weighted m y l)+
         covOf m (fun y => weighted m y j) (fun y => weighted m y k)+
         covOf m (fun y => weighted m y j) (fun y => weighted m y l))) := by
  let : IsProbabilityMeasure m.law := m.probability
  have hx (v : Fin n) : MemLp (fun y => weighted m y v) 4 m.law := (h4 v).const_mul _
  have hx2 (v : Fin n) : MemLp (fun y => weighted m y v) 2 m.law :=
    (hx v).mono_exponent (by norm_num)
  have hB := betaHat_memLp4 m hx
  have hB2 : MemLp (betaHat m) 2 m.law := hB.mono_exponent (by norm_num)
  let r := fun (v : Fin n) (y : Fin n → ℝ) => weighted m y v-betaHat m y
  have hp (u v : Fin n) : expectation m (fun y => r u y*r v y) =
      pairMoment (expectation m) (fun y => y u) (fun y => y v) (betaHat m) (m.theta u) (m.theta v) := by
    exact weighted_pair_expansion ((h4 u).mono_exponent (by norm_num))
      ((h4 v).mono_exponent (by norm_num)) hB2 _ _
  have hcov : covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
      expectation m (fun y => r i y*r j y*r k y*r l y)-
      expectation m (fun y => r i y*r j y)*expectation m (fun y => r k y*r l y) := by
    unfold covOf
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by ring
  have hfourth : expectation m (fun y => r i y*r j y*r k y*r l y) =
      fourthMoment (expectation m) (fun y => weighted m y i) (fun y => weighted m y j)
        (fun y => weighted m y k) (fun y => weighted m y l) (betaHat m) :=
    fourth_expansion (hx i) (hx j) (hx k) (hx l) hB
  refine ⟨⟨hp i j,hcov,?_⟩,?_⟩
  · rw [hcov,hfourth,hp i j,hp k l]
  · intro b
    have hc (u v : Fin n) : MemLp (fun y => (weighted m y u-b)*(weighted m y v-b)) 2 m.law :=
      ((hx u).sub (memLp_const b)).mul ((hx v).sub (memLp_const b))
    have hprod (u v : Fin n) : MemLp (fun y => weighted m y u*weighted m y v) 2 m.law :=
      (hx u).mul (hx v)
    rw [covOf_eq_cov m _ _ (hc i j) (hc k l),
      covOf_eq_cov m _ _ (hprod i j) (hprod k l),
      covOf_eq_cov m _ _ (hprod i j) (hx2 k),
      covOf_eq_cov m _ _ (hprod i j) (hx2 l),
      covOf_eq_cov m _ _ (hx2 i) (hprod k l),
      covOf_eq_cov m _ _ (hx2 j) (hprod k l),
      covOf_eq_cov m _ _ (hx2 i) (hx2 k),
      covOf_eq_cov m _ _ (hx2 i) (hx2 l),
      covOf_eq_cov m _ _ (hx2 j) (hx2 k),
      covOf_eq_cov m _ _ (hx2 j) (hx2 l)]
    exact covariance_const_products (hx i) (hx j) (hx k) (hx l) b

end
end AronowAudit.P011.CovarianceCompletion

namespace AronowAudit.P011
open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators Topology ENNReal
theorem corrected_covariance_expansion {n : ℕ} (hn : 0 < n) (m : Model n)
    (h4 : ∀ i, MemLp (fun y => y i) 4 m.law) (i j k l : Fin n) :
    (let E := expectation m
     let B := betaHat m
     let r : Fin n → (Fin n → ℝ) → ℝ := fun v y => weighted m y v-B y
     (E (fun y => r i y*r j y) = pairMoment E (fun y => y i) (fun y => y j) B (m.theta i) (m.theta j)) ∧
     covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
       E (fun y => r i y*r j y*r k y*r l y)-E (fun y => r i y*r j y)*E (fun y => r k y*r l y) ∧
     covOf m (fun y => r i y*r j y) (fun y => r k y*r l y) =
       fourthMoment E (fun y => weighted m y i) (fun y => weighted m y j)
         (fun y => weighted m y k) (fun y => weighted m y l) B -
       pairMoment E (fun y => y i) (fun y => y j) B (m.theta i) (m.theta j)*
         pairMoment E (fun y => y k) (fun y => y l) B (m.theta k) (m.theta l)) ∧
    (∀ b : ℝ,
      covOf m (fun y => (weighted m y i-b)*(weighted m y j-b))
        (fun y => (weighted m y k-b)*(weighted m y l-b)) =
      covOf m (fun y => weighted m y i*weighted m y j) (fun y => weighted m y k*weighted m y l) -
      b*(covOf m (fun y => weighted m y i*weighted m y j) (fun y => weighted m y k)+
         covOf m (fun y => weighted m y i*weighted m y j) (fun y => weighted m y l)+
         covOf m (fun y => weighted m y i) (fun y => weighted m y k*weighted m y l)+
         covOf m (fun y => weighted m y j) (fun y => weighted m y k*weighted m y l)) +
      b^2*(covOf m (fun y => weighted m y i) (fun y => weighted m y k)+
         covOf m (fun y => weighted m y i) (fun y => weighted m y l)+
         covOf m (fun y => weighted m y j) (fun y => weighted m y k)+
         covOf m (fun y => weighted m y j) (fun y => weighted m y l))) := by
  exact CovarianceCompletion.corrected_covariance_expansion_completed hn m h4 i j k l
end AronowAudit.P011

#print axioms AronowAudit.P011.corrected_covariance_expansion
