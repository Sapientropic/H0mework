import H0mework.Chemistry.LAlanineThermalRuntime.InstalledTimedPair
import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedRememberedEntropy

/-! # The actual timed pair target carries its complete energy and entropy disposition -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Runtime

open Propagation.Interface Propagation.Producer Collision Quantum
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Runtime
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Dynamics
open scoped ComplexOrder

noncomputable section

private def systemEntropyRead (joint : JointMatrix Basis) (positive : joint.PosSemidef)
    (normalized : joint.trace = 1) : ℝ :=
  spectralEntropy (systemReduce joint) (systemReduce_posSemidef joint positive)
    ((systemReduce_trace joint).trans normalized)

private theorem systemEntropyRead_commutes (joint : JointMatrix Basis) (positive : joint.PosSemidef)
    (normalized : joint.trace = 1) (elapsed : ℝ) (same : joint = rememberedJoint elapsed) :
    systemEntropyRead joint positive normalized = rememberedSystemEntropy elapsed := by
  apply spectralEntropy_eq_of_charpoly
  exact congrArg (fun state => Matrix.charpoly (systemReduce state)) same

def actualTimedCurrentEntropy (time : ℚ) (held : HoldsCollision time) : ℝ :=
  systemEntropyRead (actualTimedPairCurrent time held)
    (actualTimedPair_positive_normalized time held).1
    (actualTimedPair_positive_normalized time held).2.1

def actualTimedTargetEntropy (time : ℚ) (held : HoldsCollision time) : ℝ :=
  systemEntropyRead (actualTimedPairTarget time held)
    (actualTimedPairTarget_positive_normalized time held).1
    (actualTimedPairTarget_positive_normalized time held).2

theorem actualTimedCurrentEntropy_commutes (time : ℚ) (held : HoldsCollision time) :
    actualTimedCurrentEntropy time held = rememberedSystemEntropy (timedPairAge time : ℝ) :=
  systemEntropyRead_commutes _ _ _ _ (actualTimedPairCurrent_eq_source time held)

theorem actualTimedTargetEntropy_commutes (time : ℚ) (held : HoldsCollision time) :
    actualTimedTargetEntropy time held =
      rememberedSystemEntropy ((timedPairAge time : ℝ) + (nativeClockStep : ℝ)) :=
  systemEntropyRead_commutes _ _ _ _ (actualTimedPairTarget_eq_source time held)

def actualTimedPairEntropyProduction (time : ℚ) (held : HoldsCollision time) : ℝ :=
  actualTimedTargetEntropy time held - sourceSystemEntropy - inverseTemperature *
    (energy energyHamiltonian (systemReduce (actualTimedPairTarget time held)) - energy energyHamiltonian systemCurrent)

theorem actualTimedPairEntropyProduction_commutes (time : ℚ) (held : HoldsCollision time) :
    actualTimedPairEntropyProduction time held =
      rememberedEntropyProduction ((timedPairAge time : ℝ) + (nativeClockStep : ℝ)) := by
  unfold actualTimedPairEntropyProduction
  rw [actualTimedTargetEntropy_commutes, actualTimedPairTarget_eq_source]
  rfl

theorem actualTimedPairEntropy_disposition (time : ℚ) (held : HoldsCollision time) :
    actualTimedPairEntropyProduction time held =
      rememberedCorrelation ((timedPairAge time : ℝ) + (nativeClockStep : ℝ)) +
      rememberedBathGibbsExcess ((timedPairAge time : ℝ) + (nativeClockStep : ℝ)) := by
  rw [actualTimedPairEntropyProduction_commutes]
  exact rememberedQuantumEntropy_disposition _

theorem actualTimedPair_clausius (time : ℚ) (held : HoldsCollision time) :
    0 ≤ actualTimedPairEntropyProduction time held := by
  rw [actualTimedPairEntropyProduction_commutes]
  exact rememberedQuantum_clausius _

def actualTimedPairStepEntropy (time : ℚ) (held : HoldsCollision time) : ℝ :=
  actualTimedTargetEntropy time held - actualTimedCurrentEntropy time held - inverseTemperature *
    (energy energyHamiltonian (systemReduce (actualTimedPairTarget time held)) -
      energy energyHamiltonian (systemReduce (actualTimedPairCurrent time held)))

theorem actualTimedPairStepEntropy_commutes (time : ℚ) (held : HoldsCollision time) :
    actualTimedPairStepEntropy time held =
      rememberedStepEntropy (timedPairAge time : ℝ) ((timedPairAge time : ℝ) + (nativeClockStep : ℝ)) := by
  unfold actualTimedPairStepEntropy
  rw [actualTimedTargetEntropy_commutes, actualTimedCurrentEntropy_commutes,
    actualTimedPairTarget_eq_source, actualTimedPairCurrent_eq_source]
  rfl

theorem actualTimedPairStepEntropy_disposition (time : ℚ) (held : HoldsCollision time) :
    actualTimedPairStepEntropy time held =
      (rememberedCorrelation ((timedPairAge time : ℝ) + (nativeClockStep : ℝ)) -
        rememberedCorrelation (timedPairAge time : ℝ)) +
      (rememberedBathGibbsExcess ((timedPairAge time : ℝ) + (nativeClockStep : ℝ)) -
        rememberedBathGibbsExcess (timedPairAge time : ℝ)) := by
  rw [actualTimedPairStepEntropy_commutes]
  exact rememberedStepEntropy_disposition _ _

theorem actualTimedPair_energyLedger (time : ℚ) (held : HoldsCollision time) :
    energy (jointHamiltonian energyHamiltonian) (actualTimedPairTarget time held) =
      energy (jointHamiltonian energyHamiltonian) (actualTimedPairCurrent time held) ∧
    energy ((pairCoupling : ℂ) • swapOperator) (actualTimedPairTarget time held) =
      energy ((pairCoupling : ℂ) • swapOperator) (actualTimedPairCurrent time held) ∧
    energy (pairH energyHamiltonian pairCoupling) (actualTimedPairTarget time held) =
      energy (pairH energyHamiltonian pairCoupling) (actualTimedPairCurrent time held) := by
  rw [actualTimedPairTarget_generated]
  exact ⟨congrArg Complex.re (pairAdvance_bareEnergy energyHamiltonian energyHamiltonian_hermitian
      pairCoupling _ _),
    congrArg Complex.re (pairAdvance_interactionEnergy energyHamiltonian energyHamiltonian_hermitian
      pairCoupling _ _),
    congrArg Complex.re (pairAdvance_totalEnergy energyHamiltonian energyHamiltonian_hermitian
      pairCoupling _ _)⟩

theorem installedTimedPair_quantum_closure :
    type_of% (timedPairRuntimeFace_factorizes electronicRuntimeSecondNative) ∧
    type_of% (actualTimedPairTarget_generated timedPairInitialTime collision_next_held) ∧
    type_of% (actualTimedPairEntropy_disposition timedPairInitialTime collision_next_held) ∧
    0 ≤ actualTimedPairEntropyProduction timedPairInitialTime collision_next_held :=
  ⟨timedPairRuntimeFace_factorizes electronicRuntimeSecondNative,
    actualTimedPairTarget_generated timedPairInitialTime collision_next_held,
    actualTimedPairEntropy_disposition timedPairInitialTime collision_next_held,
    actualTimedPair_clausius timedPairInitialTime collision_next_held⟩

structure SourceInstalledLAlanineTimedPairQuantumCrown : Prop where
  retainedMaterial : SourceInstalledLAlanineTimedPairCrown
  sealedQuantumClosure : type_of% installedTimedPair_quantum_closure
  sameHamiltonianBlockReadout : ∀ elapsed i a j b, type_of% (timedPairPropagator_entry elapsed i a j b)
  positiveDuration : 0 < (nativeClockStep : ℝ)
  setupBalance : type_of% couplingSetup_disposition
  actualEnergyLedger : ∀ time held, type_of% (actualTimedPair_energyLedger time held)
  cumulativeDisposition : ∀ time held, type_of% (actualTimedPairEntropy_disposition time held)
  cumulativeClausius : ∀ time held, 0 ≤ actualTimedPairEntropyProduction time held
  signedStepDisposition : ∀ time held, type_of% (actualTimedPairStepEntropy_disposition time held)

theorem sourceInstalledLAlanineTimedPairQuantum_crown : SourceInstalledLAlanineTimedPairQuantumCrown where
  retainedMaterial := sourceInstalledLAlanineTimedPair_crown
  sealedQuantumClosure := installedTimedPair_quantum_closure
  sameHamiltonianBlockReadout := timedPairPropagator_entry
  positiveDuration := timedPairNativeStep_positive_duration
  setupBalance := couplingSetup_disposition
  actualEnergyLedger := actualTimedPair_energyLedger
  cumulativeDisposition := actualTimedPairEntropy_disposition
  cumulativeClausius := actualTimedPair_clausius
  signedStepDisposition := actualTimedPairStepEntropy_disposition

end

end LAlanine40K2025.Thermal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
