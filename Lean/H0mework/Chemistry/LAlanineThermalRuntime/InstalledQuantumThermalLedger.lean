import H0mework.Chemistry.LAlanineThermalRuntime.InstalledThermalCollision
import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedQuantumThermalLedger

/-! # The complete quantum entropy ledger reads the actual installed material target -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Runtime

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Runtime
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Quantum
open scoped ComplexOrder

noncomputable section

/-- The quantity is evaluated on the actual ledger target, not an independently chosen endpoint. -/
def actualQuantumEntropyProduction : ℝ :=
  spectralEntropy actualCollisionTarget.system actualCollisionTarget_positive_normalized.2.2.1
      actualCollisionTarget_positive_normalized.2.2.2.1 - sourceSystemEntropy -
    actualCollisionTarget.inverseTemperature *
      (energy energyHamiltonian actualCollisionTarget.system -
        energy energyHamiltonian actualCollisionTarget.preparedSystem)

theorem actualQuantumEntropyProduction_commutes :
    actualQuantumEntropyProduction = quantumEntropyProduction := by
  have stateEntropy : spectralEntropy actualCollisionTarget.system
      actualCollisionTarget_positive_normalized.2.2.1
      actualCollisionTarget_positive_normalized.2.2.2.1 = targetSystemEntropy :=
    spectralEntropy_eq_of_charpoly actualCollisionTarget.system generatedSystem
      actualCollisionTarget_positive_normalized.2.2.1 generatedSystem_posSemidef
      actualCollisionTarget_positive_normalized.2.2.2.1 generatedSystem_trace
      (congrArg Matrix.charpoly actualCollisionTarget_full_output.2.1)
  unfold actualQuantumEntropyProduction
  rw [stateEntropy, actualCollisionTarget_provenance.2.2.2.2.2.1,
    actualCollisionTarget_full_output.2.1, actualCollisionTarget_provenance.2.2.2.1]
  rfl

theorem actualCollisionTarget_quantum_disposition :
    actualQuantumEntropyProduction = quantumMutualInformation + bathGibbsExcess := by
  rw [actualQuantumEntropyProduction_commutes]
  exact fullQuantumEntropy_disposition

theorem actualCollisionTarget_quantum_clausius : 0 ≤ actualQuantumEntropyProduction := by
  rw [actualQuantumEntropyProduction_commutes]
  exact collisionQuantum_clausius

/-- Coverage, actual write-back and the quantum readout are consumed together at the sealed visit. -/
theorem installedThermalFace_quantum_closure :
    type_of% (thermalRuntimeFace_factorizes electronicRuntimeFirstNative) ∧
    type_of% actualCollisionTarget_receives_installed_effect ∧
    type_of% actualCollisionTarget_quantum_disposition ∧
    0 ≤ actualQuantumEntropyProduction :=
  ⟨thermalRuntimeFace_factorizes electronicRuntimeFirstNative,
    actualCollisionTarget_receives_installed_effect,
    actualCollisionTarget_quantum_disposition, actualCollisionTarget_quantum_clausius⟩

structure SourceInstalledLAlanineQuantumThermalCrown : Prop where
  actualMaterialClosure : SourceInstalledLAlanineThermalCollisionCrown
  sameInstalledFace : type_of% installedThermalFace_quantum_closure
  completeJointEntropy : type_of% targetJointEntropy_preserved
  correlationNonnegative : 0 ≤ quantumMutualInformation
  bathCostNonnegative : 0 ≤ bathGibbsExcess
  fullDisposition : type_of% actualCollisionTarget_quantum_disposition
  quantumClausius : 0 ≤ actualQuantumEntropyProduction

theorem sourceInstalledLAlanineQuantumThermal_crown : SourceInstalledLAlanineQuantumThermalCrown where
  actualMaterialClosure := sourceInstalledLAlanineThermalCollision_crown
  sameInstalledFace := installedThermalFace_quantum_closure
  completeJointEntropy := targetJointEntropy_preserved
  correlationNonnegative := quantumMutualInformation_nonnegative
  bathCostNonnegative := bathGibbsExcess_nonnegative
  fullDisposition := actualCollisionTarget_quantum_disposition
  quantumClausius := actualCollisionTarget_quantum_clausius

end

end LAlanine40K2025.Thermal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
