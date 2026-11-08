import AronowAudit.P027.Wave1.CancellationLimitBlueprint

/-! Decode first the block index by division, then the two phase coordinates. -/

namespace AronowAudit.P027.Wave1.CancellationLimit

set_option autoImplicit false
noncomputable section
open AronowAudit.P027 MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
attribute [local instance] Classical.propDecidable

theorem n8_proof : N8 := by
  intro r m k l he
  rcases k with ⟨⟨i, b⟩, j⟩
  rcases l with ⟨⟨i', b'⟩, j'⟩
  change 2 * i.val + b.val + 2 * r * j.val =
    2 * i'.val + b'.val + 2 * r * j'.val at he
  have hi_lt := i.isLt
  have hi'_lt := i'.isLt
  have hb_lt := b.isLt
  have hb'_lt := b'.isLt
  have hq : 0 < 2 * r := by omega
  have hphase_lt : 2 * i.val + b.val < 2 * r := by omega
  have hphase'_lt : 2 * i'.val + b'.val < 2 * r := by omega
  have hjval : j.val = j'.val := by
    have hquot := congrArg (fun z : ℕ => z / (2 * r)) he
    simpa only [Nat.add_mul_div_left (2 * i.val + b.val) j.val hq,
      Nat.add_mul_div_left (2 * i'.val + b'.val) j'.val hq, Nat.div_eq_of_lt hphase_lt,
      Nat.div_eq_of_lt hphase'_lt, Nat.zero_add] using hquot
  rw [hjval] at he
  have hphase : 2 * i.val + b.val = 2 * i'.val + b'.val := Nat.add_right_cancel he
  have hi : i = i' := Fin.ext (by omega)
  have hb : b = b' := Fin.ext (by omega)
  have hj : j = j' := Fin.ext hjval
  cases hi
  cases hb
  cases hj
  rfl

end
end AronowAudit.P027.Wave1.CancellationLimit
