import H0mework.Chemistry.LAlanineHeldForce.ProducerSourceGeneratedHeldDensityRealization
import H0mework.Chemistry.LAlanineHeldForce.ProducerSourceGeneratedHeldEnergy
import H0mework.Chemistry.LAlanineHeldForce.ProducerSourceGeneratedHeldForceLedger

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Producer

open scoped Matrix.Norms.L2Operator
noncomputable section

def heldForceClosure : Prop :=
  Source.realizedHeld = exactHeld + realizationResidual ∧
  ‖realizationResidual‖ < (8 : ℝ) / 10 ^ 9 ∧
  realizationDeltaMagnitude = 242 ∧
  exactHeld ≠ ElectronicFrame.Producer.scfBenchmark ∧
  Source.energyLedger.rowToIntegralExact ∧
  Source.energyLedger.grandRowSum + Source.energyLedger.rowResidualSum +
    Source.energyLedger.componentRoundingResidual + Source.energyLedger.scfRecomputationResidual =
      Source.energyLedger.reportedSCF ∧
  Source.energyLedger.rowResidualSum = -24 ∧
  Source.energyLedger.componentRoundingResidual = 0 ∧
  Source.energyLedger.scfRecomputationResidual = 0 ∧
  Energy.Interface.sumBlockedColumn Source.energyLedger.aoPairBlocks 9 + Source.energyLedger.overlapRoundingResidual =
    Source.energyLedger.overlapTrace ∧
  Source.energyLedger.overlapTrace = 48000000000 ∧
  Source.energyLedger.effectiveOperator.expectation + Source.energyLedger.effectiveOperator.doubleCountingCorrection =
    Source.energyLedger.effectiveOperator.electronicEnergy ∧
  Source.energyLedger.effectiveOperator.expectation ≠ Source.energyLedger.effectiveOperator.electronicEnergy ∧
  Source.energyLedger.effectiveOperator.xcPotentialExpectation ≠ Source.energyLedger.effectiveOperator.xcEnergy ∧
  |Source.rawEnergy - (Source.energyLedger.reportedSCF : ℚ) / 10 ^ 9| < (1 : ℚ) / (2 * 10 ^ 9) ∧
  Source.gradientComponentsReadout.size = 6 ∧
  (∀ atom axis, Inertia.Producer.forceComponentSum Source.gradientComponentsReadout atom axis +
    Source.gradientResidual atom axis = Source.gradientPicohartree atom axis) ∧
  (∀ atom axis, Source.forcePicohartree atom axis = -Source.gradientPicohartree atom axis) ∧
  Source.stationaryCorrection 0 0 = -6823 ∧ Source.stationaryCorrection ≠ 0 ∧
  (∀ atom axis, |Source.rawGradient atom axis - (Source.gradientPicohartree atom axis : ℚ) / 10 ^ 12| <
    (1 : ℚ) / (2 * 10 ^ 12)) ∧
  (∀ atom axis, |Source.gradientResidual atom axis| ≤ 3)

theorem sourceGeneratedHeldForce : heldForceClosure :=
  ⟨realized_held_reconstruction, realized_held_error, realizationDeltaMagnitude_exact,
    ElectronicFrame.Producer.heldState_transport_not_scfReset, everyEnergyRow_exact,
    wholeEnergy_exact, energyResiduals_exact.1, energyResiduals_exact.2.1, energyResiduals_exact.2.2,
    electronBalance_exact.1, electronBalance_exact.2, doubleCounting_exact,
    operator_is_not_energy.1, operator_is_not_energy.2, rawEnergy_resolution, six_force_components,
    forceWholeLedger, force_opposes_gradient, stationary_correction_nonzero.1, stationary_correction_nonzero.2,
    rawGradient_resolution, no_dropped_gradient_residual⟩

end
end LAlanine40K2025.HeldForce.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
