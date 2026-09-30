import Mathlib.Tactic
import H0mework.Chemistry.LAlanineEnergy.BoundEnergyLedger

/-! # Same-density molecular energy closure

The six integrals and reported SCF total are independent generated readouts.
These proofs sum the full addressed rows, retain every rounding residual,
and reject effective-operator expectation as a substitute for DFT energy.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Energy.Producer

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Energy.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Energy.Source

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem everyComponent_exact : energyLedger.rowToIntegralExact := by
  intro component
  cases component <;> decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in
theorem completeRowEnergyClosure :
    energyLedger.grandRowSum + energyLedger.rowResidualSum +
      energyLedger.componentRoundingResidual + energyLedger.scfRecomputationResidual =
        energyLedger.reportedSCF := by
  decide

theorem sameReportedSCFEnergy :
    energyLedger.reportedSCF =
      LAlanine40K2025.Source.sourceRecorded.calculation.scfEnergyNanohartree := by
  decide

set_option maxRecDepth 4096 in
theorem overlapElectronClosure :
    sumBlockedColumn energyLedger.aoPairBlocks 9 + energyLedger.overlapRoundingResidual =
      energyLedger.overlapTrace ∧ energyLedger.overlapTrace = 48000000000 := by
  decide

theorem noHiddenRoundingDebt :
    energyLedger.rowResidualSum = -35 ∧
    energyLedger.componentRoundingResidual = 0 ∧
    energyLedger.scfRecomputationResidual = 0 := by
  decide

theorem nuclearAndCoulombContributions_nonzero :
    0 < (energyLedger.integral .nuclearRepulsion).independentIntegral ∧
    0 < (energyLedger.integral .coulomb).independentIntegral := by
  decide

theorem effectiveOperator_isNotElectronicEnergy :
    energyLedger.effectiveOperator.expectation ≠
      energyLedger.effectiveOperator.electronicEnergy ∧
    energyLedger.effectiveOperator.xcPotentialExpectation ≠
      energyLedger.effectiveOperator.xcEnergy := by
  decide

theorem doubleCountingCorrection_closes :
    energyLedger.effectiveOperator.expectation +
      energyLedger.effectiveOperator.doubleCountingCorrection =
        energyLedger.effectiveOperator.electronicEnergy := by
  decide

structure SourceGeneratedLAlanineEnergyCrown : Prop where
  eachComponent : energyLedger.rowToIntegralExact
  completeLedger : energyLedger.grandRowSum + energyLedger.rowResidualSum +
    energyLedger.componentRoundingResidual + energyLedger.scfRecomputationResidual =
      energyLedger.reportedSCF
  originalSCF : type_of% sameReportedSCFEnergy
  electronBalance : type_of% overlapElectronClosure
  visibleRounding : type_of% noHiddenRoundingDebt
  nonzeroContributions : type_of% nuclearAndCoulombContributions_nonzero
  operatorNotEnergy : type_of% effectiveOperator_isNotElectronicEnergy
  doubleCounting : type_of% doubleCountingCorrection_closes

theorem sourceGeneratedLAlanineEnergy_crown : SourceGeneratedLAlanineEnergyCrown where
  eachComponent := everyComponent_exact
  completeLedger := completeRowEnergyClosure
  originalSCF := sameReportedSCFEnergy
  electronBalance := overlapElectronClosure
  visibleRounding := noHiddenRoundingDebt
  nonzeroContributions := nuclearAndCoulombContributions_nonzero
  operatorNotEnergy := effectiveOperator_isNotElectronicEnergy
  doubleCounting := doubleCountingCorrection_closes

end LAlanine40K2025.Energy.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
