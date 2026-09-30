import H0mework.Chemistry.LAlanineHeldForce.SourceSourceBoundLAlanineHeldForce
import Mathlib.Tactic

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.HeldForce.Producer

open LAlanine40K2025.HeldForce.Source Energy.Interface

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem everyEnergyRow_exact : energyLedger.rowToIntegralExact := by
  intro component
  cases component <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
/-- The legacy field records an independent same-D functional evaluation here, not an SCF optimizer. -/
theorem wholeEnergy_exact :
    energyLedger.grandRowSum + energyLedger.rowResidualSum + energyLedger.componentRoundingResidual +
      energyLedger.scfRecomputationResidual = energyLedger.reportedSCF := by decide

set_option maxRecDepth 4096 in
theorem energyResiduals_exact :
    energyLedger.rowResidualSum = -24 ∧ energyLedger.componentRoundingResidual = 0 ∧
      energyLedger.scfRecomputationResidual = 0 := by decide

set_option maxRecDepth 4096 in
theorem electronBalance_exact :
    sumBlockedColumn energyLedger.aoPairBlocks 9 + energyLedger.overlapRoundingResidual = energyLedger.overlapTrace ∧
      energyLedger.overlapTrace = 48000000000 := by decide

theorem doubleCounting_exact :
    energyLedger.effectiveOperator.expectation + energyLedger.effectiveOperator.doubleCountingCorrection =
      energyLedger.effectiveOperator.electronicEnergy := by decide

theorem operator_is_not_energy :
    energyLedger.effectiveOperator.expectation ≠ energyLedger.effectiveOperator.electronicEnergy ∧
      energyLedger.effectiveOperator.xcPotentialExpectation ≠ energyLedger.effectiveOperator.xcEnergy := by decide

theorem rawEnergy_resolution :
    |rawEnergy - (energyLedger.reportedSCF : ℚ) / 10 ^ 9| < (1 : ℚ) / (2 * 10 ^ 9) := by
  have reference : energyLedger.reportedSCF = -323457454913 := by decide
  rw [reference]
  norm_num [rawEnergy, Inertia.SourceParsing.rationalRead]

end LAlanine40K2025.HeldForce.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
