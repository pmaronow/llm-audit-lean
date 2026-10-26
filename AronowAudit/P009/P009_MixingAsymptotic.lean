import AronowAudit.P009.P009_MixingBasics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
namespace AronowAudit.P009.MixingAsymptotic
open scoped BigOperators Topology
open Filter
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

theorem overwhelming_fraction_from_threshold (S : Study)
    (hMix : ∀ {n : ℕ} (E : Experiment n) (m : ℕ), Complete E m →
      ∀ (i j : Fin n), d E i j=0 → incoming E i+incoming E j≤n →
      alpha E.design (masked E i) (masked E j) ≤
        3*((incoming E i+incoming E j:ℕ):ℝ)*(((incoming E i+incoming E j:ℕ):ℝ)-1)/
          (2*((n:ℝ)-(incoming E i+incoming E j:ℕ)+1)))
    (hCR : ∀ t, ∃ m, Complete (S.experiment t) m)
    (hBound : ∃ D, ∀ᶠ t in atTop, dAvg (S.experiment t) ≤ D)
    (u : ℕ → ℝ) (hu : ∀ t, 0<u t) (huGrow : Tendsto u atTop atTop)
    (huSmall : Tendsto (fun t=>u t/size S t) atTop (nhds 0))
    (huSq : Tendsto (fun t=>(u t)^2/size S t) atTop (nhds 0)) :
    ∃ exceptions : (t : ℕ) → Finset (Fin (S.N t) × Fin (S.N t)),
      (∀ t, ∀ ij ∈ exceptions t, d (S.experiment t) ij.1 ij.2 = 0) ∧
      Tendsto (fun t => (exceptions t).card / ((Finset.univ.filter
        (fun ij : Fin (S.N t) × Fin (S.N t) => d (S.experiment t) ij.1 ij.2 = 0)).card : ℝ))
        atTop (nhds 0) ∧
      (∀ ε > 0, ∀ᶠ t in atTop, ∀ i j, d (S.experiment t) i j = 0 →
        (i,j) ∉ exceptions t →
        alpha (S.experiment t).design (masked (S.experiment t) i) (masked (S.experiment t) j) < ε) := by
  obtain ⟨D0,hD0⟩:=hBound
  let D : ℝ := max D0 1
  have hD : ∀ᶠ t in atTop,dAvg (S.experiment t)≤D := hD0.mono fun t h=>h.trans (le_max_left _ _)
  have hDp : 0<D:=lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hN : Tendsto (size S) atTop atTop := by
    exact tendsto_natCast_atTop_iff.mpr S.grows
  have hn (t : ℕ) : 0<size S t := by dsimp [size];exact_mod_cast S.positive t
  let exceptions := fun t=>Finset.univ.filter (fun ij : Fin (S.N t)×Fin (S.N t)=>
    d (S.experiment t) ij.1 ij.2=0 ∧
      (u t < incoming (S.experiment t) ij.1 ∨ u t < incoming (S.experiment t) ij.2))
  refine ⟨exceptions,?_,?_,?_⟩
  · intro t ij hij
    exact (Finset.mem_filter.mp hij).2.1
  · have hlim : Tendsto (fun t=>4*D/u t) atTop (nhds 0):=huGrow.const_div_atTop _
    apply squeeze_zero' (Eventually.of_forall (fun t=>div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))) ?_ hlim
    filter_upwards [hD,hN.eventually (eventually_gt_atTop (2*D))] with t hdt hnt
    have hup:=hu t
    let E:=S.experiment t
    have hc:=(MixingBasics.exceptional_pair_finite_counts_completed (S.positive t) E (u t) (hu t))
    let N0:=(Finset.univ.filter (fun ij : Fin (S.N t)×Fin (S.N t)=>d E ij.1 ij.2=0)).card
    have he:((exceptions t).card:ℝ)≤
        ((Finset.univ.filter (fun ij : Fin (S.N t)×Fin (S.N t)=>u t < incoming E ij.1∨u t < incoming E ij.2)).card:ℝ):=by
      exact_mod_cast Finset.card_le_card (show exceptions t⊆_ from fun ij h=>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp h).2.2⟩)
    have hn0:(0:ℝ)<S.N t:=hn t
    have hz:(N0:ℝ)=(S.N t:ℝ)^2-(S.N t:ℝ)*dAvg E:=hc.2.2.2.2
    have hden:(S.N t:ℝ)^2/2≤(N0:ℝ):=by
      rw [hz]
      change (S.N t:ℝ)>2*D at hnt
      change dAvg E≤D at hdt
      nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hdt),
        mul_nonneg hn0.le (sub_nonneg.mpr hnt.le)]
    have hden0:0<(N0:ℝ):=lt_of_lt_of_le (by positivity) hden
    change ((exceptions t).card:ℝ)/(N0:ℝ)≤4*D/u t
    apply (div_le_iff₀ hden0).mpr
    calc
      _ ≤ 2*(S.N t:ℝ)^2*dAvg E/u t := he.trans hc.2.2.2.1
      _ ≤ 2*(S.N t:ℝ)^2*D/u t := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hdt (by positivity)) (hu t).le
      _ = (4*D/u t)*((S.N t:ℝ)^2/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  · intro ε hε
    have hsmall:=huSmall.eventually (eventually_lt_nhds (show (0:ℝ)<1/4 by norm_num))
    have hlim : Tendsto (fun t=>12*(u t)^2/size S t) atTop (nhds 0):=by
      simpa only [mul_div_assoc,mul_zero] using huSq.const_mul 12
    filter_upwards [hsmall,hlim.eventually (eventually_lt_nhds hε)] with t ht hεt
    have hup:=hu t
    intro i j hij hexc
    let E:=S.experiment t
    have hi:(incoming E i:ℝ)≤u t:=by
      by_contra h
      apply hexc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij,Or.inl (lt_of_not_ge h)⟩
    have hj:(incoming E j:ℝ)≤u t:=by
      by_contra h
      apply hexc
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij,Or.inr (lt_of_not_ge h)⟩
    have huN:4*u t<(S.N t:ℝ):=by
      have hh: u t<(1/4:ℝ)*(S.N t:ℝ):=(div_lt_iff₀ (hn t)).mp ht
      linarith
    have hK:(incoming E i:ℝ)+incoming E j≤2*u t:=by linarith
    have hsmallNat:incoming E i+incoming E j≤S.N t:=by
      exact_mod_cast (show (incoming E i:ℝ)+incoming E j≤(S.N t:ℝ) by linarith [hu t])
    obtain ⟨m,hm⟩:=hCR t
    have hb:=hMix E m hm i j hij hsmallNat
    have hden:(S.N t:ℝ)/2≤(S.N t:ℝ)-(incoming E i+incoming E j:ℕ)+1:=by
      push_cast
      linarith
    have hn0:0<(S.N t:ℝ):=hn t
    have hden0:0<(S.N t:ℝ)-(incoming E i+incoming E j:ℕ)+1:=lt_of_lt_of_le (by positivity) hden
    apply lt_of_le_of_lt (hb.trans ?_) hεt
    have hnum:3*((incoming E i+incoming E j:ℕ):ℝ)*(((incoming E i+incoming E j:ℕ):ℝ)-1)≤12*(u t)^2:=by
      push_cast
      nlinarith [Nat.cast_nonneg (α:=ℝ) (incoming E i),Nat.cast_nonneg (α:=ℝ) (incoming E j),
        mul_nonneg (sub_nonneg.mpr hK) (by positivity : 0≤2*u t+(incoming E i:ℝ)+incoming E j)]
    apply (div_le_iff₀ (mul_pos (by norm_num) hden0)).mpr
    have hden':(S.N t:ℝ)≤2*((S.N t:ℝ)-(incoming E i+incoming E j:ℕ)+1):=by linarith
    calc
      _ ≤ 12*(u t)^2:=hnum
      _ = (12*(u t)^2/(S.N t:ℝ))*(S.N t:ℝ):=by field_simp
      _ ≤ _:=mul_le_mul_of_nonneg_left hden' (by positivity)

theorem quarter_power_parameters (S : Study) :
    (∀t,0<(size S t) ^ (1/4:ℝ)) ∧
    Tendsto (fun t=>(size S t) ^ (1/4:ℝ)) atTop atTop ∧
    Tendsto (fun t=>(size S t) ^ (1/4:ℝ)/size S t) atTop (nhds 0) ∧
    Tendsto (fun t=>((size S t) ^ (1/4:ℝ))^2/size S t) atTop (nhds 0) := by
  have hn (t : ℕ) : 0<size S t := by dsimp [size];exact_mod_cast S.positive t
  have hN : Tendsto (size S) atTop atTop := tendsto_natCast_atTop_iff.mpr S.grows
  refine ⟨fun t=>Real.rpow_pos_of_pos (hn t) _,(tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp hN,?_,?_⟩
  · have he (t : ℕ) : (size S t) ^ (1/4:ℝ)/size S t=(size S t) ^ (-(3/4:ℝ)) := by
      rw [←Real.rpow_sub_one (hn t).ne']
      norm_num
    simp_rw [he]
    exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<3/4)).comp hN
  · have he (t : ℕ) : ((size S t) ^ (1/4:ℝ))^2/size S t=(size S t) ^ (-(1/2:ℝ)) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (hn t).le,←Real.rpow_sub_one (hn t).ne']
      norm_num
    simp_rw [he]
    exact (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp hN

end
end AronowAudit.P009.MixingAsymptotic
