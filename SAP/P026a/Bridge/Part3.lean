import SAP.P026a.Bridge.Part2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SAP.P026a.Bridge
open Finset
open scoped BigOperators
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem target12 : T12Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro I instF instD instN E x z
    exact AronowAudit.P026.PaperScope.variance_sub_div_T12 (toAuditUnit E)
      (AronowAudit.P026.htTotal (toAuditUnit E).design true x)
      (AronowAudit.P026.htTotal (toAuditUnit E).design false z) (Fintype.card I)
  · intro I instF instD instN E a y
    let D := (toAuditUnit E).design
    have hfull := AronowAudit.P026.PaperScope.ht_covariance_full_T12 (toAuditUnit E) a a y y
    have hlast := AronowAudit.P026.PaperScope.ht_arm_variance_T12 (toAuditUnit E) a y
    refine ⟨hfull, ?_, hlast⟩
    change AronowAudit.P026.variance D (AronowAudit.P026.htTotal D a y) = _
    rw [show AronowAudit.P026.variance D (AronowAudit.P026.htTotal D a y) =
      ∑ i, ∑ j, (AronowAudit.P026.joint D a a i j -
        AronowAudit.P026.marginal D a i * AronowAudit.P026.marginal D a j) *
        (y i / AronowAudit.P026.marginal D a i) * (y j / AronowAudit.P026.marginal D a j)
      from hfull, AronowAudit.P026.sum_diagonal_off]
    congr 1
    apply sum_congr rfl
    intro i hi
    change (AronowAudit.P026.joint D a a i i -
      AronowAudit.P026.marginal D a i * AronowAudit.P026.marginal D a i) *
        (y i / AronowAudit.P026.marginal D a i) * (y i / AronowAudit.P026.marginal D a i) =
      (AronowAudit.P026.joint D a a i i -
      AronowAudit.P026.marginal D a i * AronowAudit.P026.marginal D a i) *
        (y i / AronowAudit.P026.marginal D a i)^2
    ring
  · intro I inst1 inst2 inst3 E a b x z
    exact @AronowAudit.P026.PaperScope.ht_covariance_full_T12 I inst1 inst2 inst3 (toAuditUnit E) a b x z
  · intro I inst1 inst2 inst3 E x z
    exact @AronowAudit.P026.PaperScope.ht_variance_identity_T12 I inst1 inst2 inst3 (toAuditUnit E) x z
  · intro I inst1 inst2 inst3 E x z
    exact @AronowAudit.P026.PaperScope.ht_covariance_split_T12 I inst1 inst2 inst3 (toAuditUnit E) x z

end
end SAP.P026a.Bridge
