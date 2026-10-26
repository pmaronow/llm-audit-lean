import AronowAudit.P044.Wave1.SimulatedVarianceBlueprint
import AronowAudit.P044.Wave1.SimulatedVariance.N1
import AronowAudit.P044.Wave1.SimulatedVariance.N2
import AronowAudit.P044.Wave1.SimulatedVariance.N3
import AronowAudit.P044.Wave1.SimulatedVariance.N4
import AronowAudit.P044.Wave1.SimulatedVariance.N5
import AronowAudit.P044.Wave1.SimulatedVariance.N6
import AronowAudit.P044.Wave1.SimulatedVariance.N7
import AronowAudit.P044.Wave1.SimulatedVariance.N8
import AronowAudit.P044.Wave1.SimulatedVariance.N9
import AronowAudit.P044.Wave1.SimulatedVariance.N10
import AronowAudit.P044.Wave1.SimulatedVariance.N11
import AronowAudit.P044.Wave1.SimulatedVariance.N12
import AronowAudit.P044.Wave1.SimulatedVariance.N13
import AronowAudit.P044.Wave1.SimulatedVariance.N14
import AronowAudit.P044.Wave1.SimulatedVariance.N15
import AronowAudit.P044.Wave1.SimulatedVariance.N16
import AronowAudit.P044.Wave1.SimulatedVariance.N17
import AronowAudit.P044.Wave1.SimulatedVariance.N18
import AronowAudit.P044.Wave1.SimulatedVariance.N19
import AronowAudit.P044.Wave1.SimulatedVariance.N20
import AronowAudit.P044.Wave1.SimulatedVariance.N21

namespace AronowAudit.P044.Wave1

open MeasureTheory ProbabilityTheory
open scoped BigOperators
open AronowAudit.P044

noncomputable section

theorem printed_simulated_variance_claim_refuted : ¬ PrintedSimulatedConservativeness :=
  AronowAudit.P044.Wave1.SimulatedVariance.assemble
    SimulatedVariance.n1_proof SimulatedVariance.n2_proof SimulatedVariance.n3_proof
    SimulatedVariance.n4_proof SimulatedVariance.n5_proof SimulatedVariance.n6_proof
    SimulatedVariance.n7_proof SimulatedVariance.n8_proof SimulatedVariance.n9_proof
    SimulatedVariance.n10_proof SimulatedVariance.n11_proof SimulatedVariance.n12_proof
    SimulatedVariance.n13_proof SimulatedVariance.n14_proof SimulatedVariance.n15_proof
    SimulatedVariance.n16_proof SimulatedVariance.n17_proof SimulatedVariance.n18_proof
    SimulatedVariance.n19_proof SimulatedVariance.n20_proof SimulatedVariance.n21_proof

end

end AronowAudit.P044.Wave1
