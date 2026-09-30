import H0mework.Chemistry.LAlanineReentry.SourceSourceBoundReentry

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Producer

open Inertia.SourceParsing Energy.Interface
open LAlanine40K2025.Reentry.Source
noncomputable section

theorem nuclearCurrentEnergyRows_exact : stepReadout.nuclear.currentLedger.rowToIntegralExact :=
  JointNext.Producer.nuclearTargetEnergyRows_exact

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem nuclearTargetEnergyRows_exact : stepReadout.nuclear.targetLedger.rowToIntegralExact := by
  intro component
  cases component <;> decide

theorem nuclearCurrentWholeEnergy :
    stepReadout.nuclear.currentLedger.grandRowSum + stepReadout.nuclear.currentLedger.rowResidualSum +
      stepReadout.nuclear.currentLedger.componentRoundingResidual + stepReadout.nuclear.currentLedger.scfRecomputationResidual =
        stepReadout.nuclear.currentLedger.reportedSCF := JointNext.Producer.nuclearTargetWholeEnergy

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem nuclearTargetWholeEnergy :
    stepReadout.nuclear.targetLedger.grandRowSum + stepReadout.nuclear.targetLedger.rowResidualSum +
      stepReadout.nuclear.targetLedger.componentRoundingResidual + stepReadout.nuclear.targetLedger.scfRecomputationResidual =
        stepReadout.nuclear.targetLedger.reportedSCF := by decide

theorem nuclearTargetEnergyResiduals :
    stepReadout.nuclear.targetLedger.rowResidualSum = -16 ∧
    stepReadout.nuclear.targetLedger.componentRoundingResidual = 0 ∧
    stepReadout.nuclear.targetLedger.scfRecomputationResidual = 0 := by decide

set_option maxRecDepth 4096 in
theorem nuclearTargetEnergyCensus :
    (stepReadout.nuclear.targetLedger.aoPairBlocks.toList.map Array.size).sum = 4851 ∧
    stepReadout.nuclear.targetLedger.nuclearPairs.size = 78 ∧
    stepReadout.nuclear.targetLedger.electronNuclearAtoms.size = 13 ∧
    stepReadout.nuclear.targetLedger.xcGridBlocks.size = 229 := by decide

set_option maxRecDepth 4096 in
theorem nuclearTargetElectronBalance :
    sumBlockedColumn stepReadout.nuclear.targetLedger.aoPairBlocks 9 +
      stepReadout.nuclear.targetLedger.overlapRoundingResidual = stepReadout.nuclear.targetLedger.overlapTrace ∧
    stepReadout.nuclear.targetLedger.overlapTrace = 48000000000 := by decide

theorem nuclearTargetDoubleCounting :
    stepReadout.nuclear.targetLedger.effectiveOperator.expectation +
      stepReadout.nuclear.targetLedger.effectiveOperator.doubleCountingCorrection =
        stepReadout.nuclear.targetLedger.effectiveOperator.electronicEnergy := by decide

theorem nuclearTargetOperator_not_energy :
    stepReadout.nuclear.targetLedger.effectiveOperator.expectation ≠
      stepReadout.nuclear.targetLedger.effectiveOperator.electronicEnergy ∧
    stepReadout.nuclear.targetLedger.effectiveOperator.xcPotentialExpectation ≠
      stepReadout.nuclear.targetLedger.effectiveOperator.xcEnergy := by decide

theorem nuclearCurrentPotential_resolution :
    |stepReadout.nuclear.current.potential - (stepReadout.nuclear.currentLedger.reportedSCF : ℚ) / 10 ^ 9| <
      (1 : ℚ) / (2 * 10 ^ 9) := JointNext.Producer.nuclearTargetPotential_resolution

theorem nuclearTargetPotential_resolution :
    |stepReadout.nuclear.target.potential - (stepReadout.nuclear.targetLedger.reportedSCF : ℚ) / 10 ^ 9| <
      (1 : ℚ) / (2 * 10 ^ 9) := by
  change |rationalRead _ - ((-(_ : ℕ) : Int) : ℚ) / 10 ^ 9| < (1 : ℚ) / (2 * 10 ^ 9)
  norm_num [rationalRead]

end
end LAlanine40K2025.Reentry.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
