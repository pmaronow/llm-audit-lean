/- Exact full-interference design bias and a uniform-subset finite witness. -/
import AronowAudit.P009.P009_CompleteConditional
import AronowAudit.P009.P009_PairedCompletion
import Mathlib.Data.Fintype.Powerset
namespace AronowAudit.P009.FullBiasCompletion
open scoped BigOperators
open CompleteConditional
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000

lemma balanced_design_facts {n : ℕ} (hn : 0<n) (heven : Even n) (E : Experiment n)
    (hDesign : Complete E (n/2) ∨ ∃ ρ : Pairing n,Paired E ρ) :
    (∀ i b,marginal E i b=1/2) ∧
    (∀ z,0<E.design.mass z→(∑ i,bit (z i))=(n:ℝ)/2) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  rcases hDesign with hCR | ⟨ρ,hPair⟩
  · have htwo : 2*(n/2)=n := by rcases heven with ⟨r,hr⟩; omega
    have htwoR : (2:ℝ)*(n/2:ℕ)=n := by exact_mod_cast htwo
    have hm : ((n/2:ℕ):ℝ)/(n:ℝ)=1/2 := by apply (div_eq_iff hn0).mpr; nlinarith
    constructor
    · intro i b
      cases b
      · rw [complete_marginal_false E (n/2) hCR i,hm]; norm_num
      · rw [complete_marginal_true E (n/2) hCR i,hm]
    · intro z hz
      rw [supported_treated_count E (n/2) hCR z hz]
      nlinarith
  · refine ⟨fun i b=>PairedCompletion.marginal_half E ρ hPair i b,?_⟩
    intro z hz
    have hh := PairedCompletion.supported_arm_counts E ρ hPair z hz true
    have he : nHat E true z=2*(∑ i,bit (z i)) := by
      unfold nHat
      simp only [PairedCompletion.marginal_half E ρ hPair]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      cases z i <;> norm_num [bit]
    rw [he] at hh
    nlinarith

lemma balance_erase_of_balanced {n : ℕ} (z : Assignment n)
    (hc : (∑ i,bit (z i))=(n:ℝ)/2) (i : Fin n) :
    balance (Finset.univ.erase i) z=1-2*bit (z i) := by
  have hsum : (∑ j : Fin n,(2*bit (z j)-1))=0 := by
    rw [Finset.sum_sub_distrib,←Finset.mul_sum,hc]
    simp
    ring
  have hh := Finset.sum_erase_add Finset.univ (fun j=>2*bit (z j)-1) (Finset.mem_univ i)
  unfold balance
  rw [hsum] at hh
  linarith

lemma balance_erase_update {n : ℕ} (z : Assignment n) (i : Fin n) (a : Bool) :
    balance (Finset.univ.erase i) (Function.update z i a)=balance (Finset.univ.erase i) z := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

lemma full_balanced_values {n : ℕ} (b : Fin n→ℝ) (z : Assignment n)
    (hc : (∑ i,bit (z i))=(n:ℝ)/2) (i : Fin n) :
    fullOutcome b i z=b i ∧
    fullOutcome b i (Function.update z i true)-fullOutcome b i (Function.update z i false)=2*(1-bit (z i)) := by
  have he := balance_erase_of_balanced z hc i
  constructor
  · unfold fullOutcome
    rw [he]
    cases z i <;> norm_num [bit,multiplier]
  · unfold fullOutcome
    rw [balance_erase_update,balance_erase_update,he]
    simp only [Function.update_self,bit,ite_true,Bool.false_eq_true,ite_false,mul_one,mul_zero,zero_add]
    cases z i <;> norm_num [bit,multiplier]

lemma balanced_arm_counts {n : ℕ} (E : Experiment n) (hm : ∀ i b,marginal E i b=1/2)
    (z : Assignment n) (hc : (∑ i,bit (z i))=(n:ℝ)/2) (b : Bool) : nHat E b z=n := by
  unfold nHat
  simp_rw [hm]
  rw [←Finset.sum_div]
  cases b
  · have hi (i : Fin n) : (if z i=false then (1:ℝ) else 0)=1-bit (z i) := by cases hz : z i <;> simp [bit,hz]
    simp_rw [hi]
    rw [Finset.sum_sub_distrib,hc]
    simp
    ring
  · change (∑ i,bit (z i))/(1/2)=n
    rw [hc]
    ring

lemma ht_of_observed_baseline {n : ℕ} (E : Experiment n) (b : Fin n→ℝ)
    (hm : ∀ i a,marginal E i a=1/2) (z : Assignment n) (hy : ∀ i,E.outcome i z=b i) :
    ht E z=2/(n:ℝ)*(∑ i,(2*bit (z i)-1)*b i) := by
  unfold ht muHat
  rw [←sub_div,←Finset.sum_sub_distrib]
  have hi (i : Fin n) : (if z i=true then E.outcome i z else 0)/marginal E i true-
      (if z i=false then E.outcome i z else 0)/marginal E i false=2*((2*bit (z i)-1)*b i) := by
    rw [hm i true,hm i false,hy i]
    cases z i <;> norm_num [bit] <;> ring
  simp_rw [hi]
  rw [←Finset.mul_sum]
  ring

lemma mean_signed_baselines_zero {n : ℕ} (E : Experiment n) (b : Fin n→ℝ)
    (hm : ∀ i a,marginal E i a=1/2) :
    mean E.design (fun z=>2/(n:ℝ)*(∑ i,(2*bit (z i)-1)*b i))=0 := by
  rw [mean_const_mul,mean_sum]
  have hi (i : Fin n) : mean E.design (fun z=>(2*bit (z i)-1)*b i)=0 := by
    have he : (fun z : Assignment n=>(2*bit (z i)-1)*b i)=(fun z=>b i*(2*bit (z i)-1)) := by funext z; ring
    rw [he,mean_const_mul,mean_sub,mean_const_mul,mean_const]
    have hm' : mean E.design (fun z=>bit (z i))=marginal E i true := by
      unfold marginal prob
      apply congrArg (mean E.design)
      funext z
      cases hz : z i <;> simp [bit,hz]
    rw [hm',hm i true]
    ring
  simp_rw [hi]
  simp

lemma mse_shift_one {Ω : Type*} [Fintype Ω] (P : Law Ω) (T : Ω→ℝ) (hT : mean P T=0) :
    mean P (fun w=>(T w-1)^2)=var P T+1 := by
  rw [variance_second_moment,hT]
  have he : (fun w=>(T w-1)^2)=(fun w=>T w^2-2*T w+1) := by funext w; ring
  rw [he,mean_add,mean_sub,mean_const_mul,mean_const,hT]
  ring

theorem full_interference_bias_completed {n : ℕ} (hn : 0 < n) (heven : Even n)
    (E : Experiment n) (b : Fin n → ℝ) (hy : E.outcome = fullOutcome b)
    (hDesign : Complete E (n/2) ∨ ∃ ρ : Pairing n, Paired E ρ) :
    eate E = 1 ∧
    (∀ z, 0 < E.design.mass z →
      (∀ i, E.outcome i z = b i ∧ effect E i z = 2*(1-bit (z i))) ∧
      ateAt E z = 1 ∧ ht E z = hajek E z ∧
      ht E z = 2/(n:ℝ)*(∑ i, (2*bit (z i)-1)*b i)) ∧
    mean E.design (ht E) = 0 ∧ mean E.design (hajek E) = 0 ∧
    mean E.design (ht E)-eate E = -1 ∧ mean E.design (hajek E)-eate E = -1 ∧
    mean E.design (fun z => (ht E z-eate E)^2) = var E.design (ht E)+1 ∧
    mean E.design (fun z => (hajek E z-eate E)^2) = var E.design (hajek E)+1 := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  obtain ⟨hm,hcount⟩ := balanced_design_facts hn heven E hDesign
  have hv (z : Assignment n) (hz : 0<E.design.mass z) (i : Fin n) :
      E.outcome i z=b i ∧ effect E i z=2*(1-bit (z i)) := by
    have hh := full_balanced_values b z (hcount z hz) i
    constructor
    · simpa only [hy] using hh.1
    · simpa only [effect,potential,hy] using hh.2
  have hate (z : Assignment n) (hz : 0<E.design.mass z) : ateAt E z=1 := by
    unfold ateAt
    simp_rw [(hv z hz _).2]
    rw [←Finset.mul_sum,Finset.sum_sub_distrib,hcount z hz]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    field_simp
    ring
  have hEATE : eate E=1 := by
    change mean E.design (ateAt E)=1
    exact (mean_support_congr E.design (ateAt E) (fun _=>1) hate).trans (mean_const _ 1)
  have heq (z : Assignment n) (hz : 0<E.design.mass z) : ht E z=hajek E z := by
    have hT := balanced_arm_counts E hm z (hcount z hz) true
    have hC := balanced_arm_counts E hm z (hcount z hz) false
    have ha : ArmsNonempty E z := ⟨by rw [hT];exact hn0,by rw [hC];exact hn0⟩
    rw [hajek,if_pos ha,hT,hC]
    unfold ht
    field_simp
  have hf (z : Assignment n) (hz : 0<E.design.mass z) :
      ht E z=2/(n:ℝ)*(∑ i,(2*bit (z i)-1)*b i) :=
    ht_of_observed_baseline E b hm z (fun i=>(hv z hz i).1)
  have hMT : mean E.design (ht E)=0 := by
    exact (mean_support_congr E.design _ _ hf).trans (mean_signed_baselines_zero E b hm)
  have hMH : mean E.design (hajek E)=0 := by
    exact (mean_support_congr E.design _ _ (fun z hz=>(heq z hz).symm)).trans hMT
  refine ⟨hEATE,?_,hMT,hMH,?_,?_,?_,?_⟩
  · intro z hz
    exact ⟨hv z hz,hate z hz,heq z hz,hf z hz⟩
  · rw [hMT,hEATE];norm_num
  · rw [hMH,hEATE];norm_num
  · rw [hEATE];exact mse_shift_one E.design (ht E) hMT
  · rw [hEATE];exact mse_shift_one E.design (hajek E) hMH

theorem absolute_bias_population_completed {n : ℕ} (hn : 0 < n) (heven : Even n)
    (E : Experiment n) (b : Fin n → ℝ) (hy : E.outcome = fullOutcome b)
    (hDesign : Complete E (n/2) ∨ ∃ ρ : Pairing n, Paired E ρ) :
    mean E.design (ht E)-eate E = -1 ∧ mean E.design (hajek E)-eate E = -1 ∧
    |mean E.design (ht E)-eate E| = 1 ∧ |mean E.design (hajek E)-eate E| = 1 := by
  have hh := full_interference_bias_completed hn heven E b hy hDesign
  refine ⟨hh.2.2.2.2.1,hh.2.2.2.2.2.1,?_,?_⟩
  · rw [hh.2.2.2.2.1];norm_num
  · rw [hh.2.2.2.2.2.1];norm_num


/- The finite-law construction uses uniform m-subsets and an injective pushforward,
avoiding enumeration of 2^n Boolean assignments. -/
def uniformLaw (Ω : Type*) [Fintype Ω] [Nonempty Ω] : Law Ω where
  mass := fun _ => 1/(Fintype.card Ω:ℝ)
  nonneg := by intro a; positivity
  total := by simp [Fintype.card_ne_zero]

def pushLaw {A B : Type*} [Fintype A] [Fintype B] (P : Law A) (f : A → B) : Law B where
  mass := fun b => ∑ a,if f a=b then P.mass a else 0
  nonneg := by intro b; apply Finset.sum_nonneg; intro a ha; split_ifs <;> simp [P.nonneg]
  total := by
    rw [Finset.sum_comm]
    have he (a : A) : (∑ b,if f a=b then P.mass a else 0)=P.mass a := by simp
    simp only [he,P.total]

theorem push_mass_image {A B : Type*} [Fintype A] [Fintype B] (P : Law A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (pushLaw P f).mass (f a)=P.mass a := by
  simp only [pushLaw, hf.eq_iff]
  simp

theorem push_mass_outside {A B : Type*} [Fintype A] [Fintype B] (P : Law A) (f : A → B)
    (b : B) (hb : ∀ a,f a≠b) : (pushLaw P f).mass b=0 := by
  simp [pushLaw,hb]

abbrev Subsets (n m : ℕ) := {G : Finset (Fin n) // G ∈ (Finset.univ : Finset (Fin n)).powersetCard m}
def subsetAssignment {n m : ℕ} (G : Subsets n m) : Assignment n := fun i => decide (i∈G.val)
theorem subsetAssignment_injective (n m : ℕ) : Function.Injective (@subsetAssignment n m) := by
  intro G H h
  apply Subtype.ext
  ext i
  have hi := congrFun h i
  simpa [subsetAssignment] using hi

theorem subsetAssignment_count {n m : ℕ} (G : Subsets n m) :
    (∑ i,if subsetAssignment G i then (1:ℕ) else 0)=m := by
  have hc : G.val.card=m := (Finset.mem_powersetCard.mp G.property).2
  simpa [subsetAssignment,Finset.sum_boole] using hc

theorem subsets_card (n m : ℕ) : Fintype.card (Subsets n m)=n.choose m := by
  simp [Subsets,Fintype.card_coe,Finset.card_powersetCard]

def completeLaw (n m : ℕ) (hm : m≤n) : Law (Assignment n) := by
  have hne : Nonempty (Subsets n m) := by
    have hp : ((Finset.univ : Finset (Fin n)).powersetCard m).Nonempty := by
      apply Finset.powersetCard_nonempty.mpr
      simpa using hm
    rcases hp with ⟨G,hG⟩
    exact ⟨⟨G,hG⟩⟩
  exact pushLaw (uniformLaw (Subsets n m)) subsetAssignment

theorem completeLaw_mass (n m : ℕ) (hm : m≤n) (z : Assignment n) :
    (completeLaw n m hm).mass z = if (∑ i,if z i then (1:ℕ) else 0)=m then 1/(n.choose m:ℝ) else 0 := by
  classical
  by_cases hz : (∑ i,if z i then (1:ℕ) else 0)=m
  · rw [if_pos hz]
    let G : Finset (Fin n) := Finset.univ.filter (fun i => z i=true)
    have hc : G.card=m := by simpa only [G,Finset.card_eq_sum_ones,Finset.sum_filter] using hz
    let a : Subsets n m := ⟨G,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,hc⟩⟩
    have ha : subsetAssignment a=z := by
      funext i; cases hi:z i <;> simp [subsetAssignment,a,G,hi]
    unfold completeLaw
    rw [← ha,push_mass_image _ _ (subsetAssignment_injective n m)]
    change 1/(Fintype.card (Subsets n m):ℝ)=1/(n.choose m:ℝ)
    rw [subsets_card]
  · rw [if_neg hz]
    unfold completeLaw
    exact push_mass_outside _ _ z (by intro a he; apply hz; rw [← he]; exact subsetAssignment_count a)

def completeExperiment (n m : ℕ) (hm : m≤n) (y : Fin n → Assignment n → ℝ) : Experiment n := ⟨completeLaw n m hm,y⟩
theorem complete_certificate (n m : ℕ) (hpos : 0 < m) (hlt : m<n) (y : Fin n → Assignment n → ℝ) :
    Complete (completeExperiment n m (le_of_lt hlt) y) m :=
  ⟨hpos,hlt,completeLaw_mass n m (le_of_lt hlt)⟩

theorem simulation_bias_counterexample_completed :
    ∃ E : Experiment 100, E.outcome = fullOutcome (fun _ => 0) ∧
      Complete E 50 ∧ eate E = 1 ∧
      (∀ z, E.design.mass z > 0 → ht E z = 0 ∧ hajek E z = 0) ∧
      mean E.design (ht E) - eate E = -1 ∧
      mean E.design (hajek E) - eate E = -1 ∧
      var E.design (ht E) = 0 ∧
      mean E.design (fun z => (ht E z-eate E)^2) = 1 := by
  let E := completeExperiment 100 50 (by norm_num) (fullOutcome (fun _=>0))
  have hCR : Complete E 50 := complete_certificate 100 50 (by norm_num) (by norm_num) _
  have hh := full_interference_bias_completed (by norm_num : 0<100) (by decide : Even 100)
    E (fun _=>0) rfl (Or.inl hCR)
  have hz (z : Assignment 100) (hpos : 0<E.design.mass z) : ht E z=0 ∧ hajek E z=0 := by
    have hf := (hh.2.1 z hpos).2.2.2
    have he := (hh.2.1 z hpos).2.2.1
    have ht : ht E z=0 := by simpa using hf
    exact ⟨ht,he.symm.trans ht⟩
  have hvar : var E.design (ht E)=0 := by
    rw [variance_second_moment,hh.2.2.1]
    have hm : mean E.design (fun z=>(ht E z)^2)=mean E.design (fun _=>0) := by
      apply mean_support_congr
      intro z hpos
      rw [(hz z hpos).1]
      norm_num
    rw [hm,mean_const]
    norm_num
  refine ⟨E,rfl,hCR,hh.1,hz,hh.2.2.2.2.1,hh.2.2.2.2.2.1,hvar,?_⟩
  rw [hh.2.2.2.2.2.2.1,hvar]
  norm_num

end
end AronowAudit.P009.FullBiasCompletion

namespace AronowAudit.P009
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
/-- T24, exact corrected simulation exception (Supplement B pp. 3 and 6):
for ANY fixed baselines and either balanced complete or paired design, EATE
is one, both estimators have mean zero and signed bias -1, and MSE=variance+1. -/
theorem full_interference_bias {n : ℕ} (hn : 0 < n) (heven : Even n)
    (E : Experiment n) (b : Fin n → ℝ) (hy : E.outcome = fullOutcome b)
    (hDesign : Complete E (n/2) ∨ ∃ ρ : Pairing n, Paired E ρ) :
    eate E = 1 ∧
    (∀ z, 0 < E.design.mass z →
      (∀ i, E.outcome i z = b i ∧ effect E i z = 2*(1-bit (z i))) ∧
      ateAt E z = 1 ∧ ht E z = hajek E z ∧
      ht E z = 2/(n:ℝ)*(∑ i, (2*bit (z i)-1)*b i)) ∧
    mean E.design (ht E) = 0 ∧ mean E.design (hajek E) = 0 ∧
    mean E.design (ht E)-eate E = -1 ∧ mean E.design (hajek E)-eate E = -1 ∧
    mean E.design (fun z => (ht E z-eate E)^2) = var E.design (ht E)+1 ∧
    mean E.design (fun z => (hajek E z-eate E)^2) = var E.design (hajek E)+1 := by
  exact FullBiasCompletion.full_interference_bias_completed hn heven E b hy hDesign

/-- T25 part (ii), the corrected interpretation of the full-interference rows:
the population signed error is -1 and its reported magnitude is 1. -/
theorem absolute_bias_population {n : ℕ} (hn : 0 < n) (heven : Even n)
    (E : Experiment n) (b : Fin n → ℝ) (hy : E.outcome = fullOutcome b)
    (hDesign : Complete E (n/2) ∨ ∃ ρ : Pairing n, Paired E ρ) :
    mean E.design (ht E)-eate E = -1 ∧ mean E.design (hajek E)-eate E = -1 ∧
    |mean E.design (ht E)-eate E| = 1 ∧ |mean E.design (hajek E)-eate E| = 1 := by
  exact FullBiasCompletion.absolute_bias_population_completed hn heven E b hy hDesign

/-- T23 finite illustration (Supplement B pp. 2–3): a concrete 100-unit
complete-interference, complete-randomization population has both estimators
exactly zero and EATE one. Its signed bias is -1, squared bias one, and true
variance zero. This is a single zero-baseline population, rather than a
sampling-averaged counterexample. -/
theorem simulation_bias_counterexample :
    ∃ E : Experiment 100, E.outcome = fullOutcome (fun _ => 0) ∧
      Complete E 50 ∧ eate E = 1 ∧
      (∀ z, E.design.mass z > 0 → ht E z = 0 ∧ hajek E z = 0) ∧
      mean E.design (ht E) - eate E = -1 ∧
      mean E.design (hajek E) - eate E = -1 ∧
      var E.design (ht E) = 0 ∧
      mean E.design (fun z => (ht E z-eate E)^2) = 1 := by
  exact FullBiasCompletion.simulation_bias_counterexample_completed

end
end AronowAudit.P009
