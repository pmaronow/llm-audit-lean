import AronowAudit.P002.Wave1.PrintedTheorem2Blueprint

namespace AronowAudit.P002.Wave1.PrintedTheorem2
noncomputable section
open scoped BigOperators ENNReal Matrix Topology
open Filter MeasureTheory
attribute [local instance] Classical.propDecidable

example : AronowAudit.P002.Wave1.PrintedTheorem2.Target ↔ ¬ (type_of% @AronowAudit.P002.printed_theorem2) := Iff.rfl

end
end AronowAudit.P002.Wave1.PrintedTheorem2
