import AronowAudit.P004.P004_MCCompletion
namespace AronowAudit.P004.HACCompletion
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000
lemma split_diagonal {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) + ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  calc
    _ = ∑ i, ((∑ j ∈ Finset.univ.erase i, f i j) + f i i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_erase_add Finset.univ (f i) (Finset.mem_univ i)).symm
    _ = _ := by rw [Finset.sum_add_distrib]; ring

lemma expansion {N : ℕ} (z : Assignment N) (e : Fin N → ℝ)
    (Q : Fin N → Fin N → ℝ) (hQ : ∀ i j, Q i j = Q j i)
    (hdiag : ∀ i, Q i i = 1) :
    kernelVariance z e Q =
      (∑ i, bit (z i)*e i^2)/(armCount z true)^2 +
      (∑ i, (1-bit (z i))*e i^2)/(armCount z false)^2 +
      (∑ i, ∑ j ∈ Finset.univ.erase i, bit (z i)*bit (z j)*e i*e j*Q i j)/(armCount z true)^2 -
      2*(∑ i, ∑ j ∈ Finset.univ.erase i, (1-bit (z i))*bit (z j)*e i*e j*Q i j)/(armCount z true*armCount z false) +
      (∑ i, ∑ j ∈ Finset.univ.erase i, (1-bit (z i))*(1-bit (z j))*e i*e j*Q i j)/(armCount z false)^2 := by
  have hpoint (i j : Fin N) : lambda z i * lambda z j * e i * e j * Q i j =
      (bit (z i)*bit (z j)*e i*e j*Q i j)/(armCount z true)^2 -
      (bit (z i)*(1-bit (z j))*e i*e j*Q i j)/(armCount z true*armCount z false) -
      ((1-bit (z i))*bit (z j)*e i*e j*Q i j)/(armCount z true*armCount z false) +
      ((1-bit (z i))*(1-bit (z j))*e i*e j*Q i j)/(armCount z false)^2 := by
    unfold lambda
    ring
  have hswap : (∑ i, ∑ j, bit (z i)*(1-bit (z j))*e i*e j*Q i j) =
      ∑ i, ∑ j, (1-bit (z i))*bit (z j)*e i*e j*Q i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hQ j i]
    ring
  have ht (i : Fin N) : bit (z i)*bit (z i)*e i*e i*Q i i = bit (z i)*e i^2 := by
    rw [hdiag]; cases z i <;> simp [bit] <;> ring
  have hu (i : Fin N) : (1-bit (z i))*(1-bit (z i))*e i*e i*Q i i = (1-bit (z i))*e i^2 := by
    rw [hdiag]; cases z i <;> simp [bit] <;> ring
  have hc (i : Fin N) : (1-bit (z i))*bit (z i)*e i*e i*Q i i = 0 := by
    cases z i <;> simp [bit]
  unfold kernelVariance
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib, ←Finset.sum_div]
  rw [hswap]
  rw [split_diagonal (fun i j => bit (z i)*bit (z j)*e i*e j*Q i j),
    split_diagonal (fun i j => (1-bit (z i))*bit (z j)*e i*e j*Q i j),
    split_diagonal (fun i j => (1-bit (z i))*(1-bit (z j))*e i*e j*Q i j)]
  simp_rw [ht, hu, hc]
  simp only [Finset.sum_const_zero, zero_add]
  ring

end
end AronowAudit.P004.HACCompletion
namespace AronowAudit.P004
open scoped BigOperators
open HACCompletion
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

/-- T29(2–3), corrected diagonal control indicator and random v̂ row
in the HAC expansions, Appendix C pp. 34–37. -/
theorem hac_expansion {N : ℕ} (R : CircleTable N) (D : Fin N → Fin N → ℝ)
    (K : ℝ → ℝ) (b p : ℝ) (z : Assignment N) (hb : 0 < b)
    (hK : KernelConditions K) (hD : ∀ i j, D i j = D j i)
    (hdiag : ∀ i, D i i = 0) (hpos : ∀ i j, 0 ≤ D i j)
    (h1 : 0 < armCount z true) (h0 : 0 < armCount z false) :
    kernelVariance z (residual R z) (distanceKernel D K b) =
      (∑ i, bit (z i)*(residual R z i)^2)/(armCount z true)^2 +
      (∑ i, (1-bit (z i))*(residual R z i)^2)/(armCount z false)^2 +
      (∑ i, ∑ j ∈ Finset.univ.erase i, bit (z i)*bit (z j)*residual R z i*residual R z j*K (D i j/b))/(armCount z true)^2 -
      2*(∑ i, ∑ j ∈ Finset.univ.erase i, (1-bit (z i))*bit (z j)*residual R z i*residual R z j*K (D i j/b))/(armCount z true*armCount z false) +
      (∑ i, ∑ j ∈ Finset.univ.erase i, (1-bit (z i))*(1-bit (z j))*residual R z i*residual R z j*K (D i j/b))/(armCount z false)^2 ∧
    nedV1 p R D K b z = ∑ i, nedVRow p R D K b (armMean R z true) (armMean R z false) i z := by
  constructor
  · exact expansion z (residual R z) (distanceKernel D K b)
      (fun i j => by simp only [distanceKernel, hD i j])
      (fun i => by simp [distanceKernel, hdiag i, hK.1])
  · rfl

end
end AronowAudit.P004
