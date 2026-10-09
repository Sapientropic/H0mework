import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Dynamics.FiniteSpectrumUnitaryPulse
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Charging.Dynamics.SourceGeneratedMaximalCharge
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Runtime.RecoveryActionRuntime

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Charging.Source

open Collision Powered.Dynamics Load.Source Load.Producer Load.Producer.RecoveryLedger
open Load.Recovery.Control Recovery.Producer Propagation.Producer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def receivedState : LoadState := Recovery.Runtime.recoveryCurrentState Recovery.Runtime.recoveryRuntimeAfterFirst.state.current

theorem received_actual : receivedState = recoveryStateFirst := rfl

/-- Fixed from the exact parent current before emission; it is not recomputed on arbitrary inputs. -/
def sourceUnitary : Matrix.unitaryGroup PairController ℂ :=
  Maximum.chargeUnitary Powered.Producer.poweredTotalHamiltonian (pcRead receivedState).joint
    Powered.Producer.poweredTotalHamiltonian_hermitian (pcRead receivedState).positive.isHermitian

def sourceHamiltonian : Matrix PairController PairController ℂ :=
  Pulse.pulseHamiltonian sourceUnitary (nativeClockStep : ℝ)

theorem sourceHamiltonian_hermitian : sourceHamiltonian.IsHermitian := Pulse.pulseHamiltonian_hermitian _ _

def sourceFlow (elapsed : ℝ) : Matrix.unitaryGroup PairController ℂ :=
  flowUnitary 0 0 sourceHamiltonian Matrix.isHermitian_zero sourceHamiltonian_hermitian elapsed

theorem sourceFlow_generated : sourceFlow (nativeClockStep : ℝ) = sourceUnitary := by
  apply Subtype.ext
  rw [sourceFlow, Load.Producer.StrictThermal.flowUnitary_matrix_exp,
    ProjectedOrbit.interactionHamiltonian]
  exact Pulse.pulseHamiltonian_generates sourceUnitary (nativeClockStep : ℝ)
    (ne_of_gt Load.Producer.StrictThermal.nativeClock_small.1)

theorem sourceFlow_conserves_generator (elapsed : ℝ) :
    Commute sourceHamiltonian (sourceFlow elapsed : Matrix PairController PairController ℂ) := by
  apply observable_commutes_with_flow
  rw [ProjectedOrbit.interactionHamiltonian]

def chargeStep (current : LoadState) : LoadState :=
  localState current (sourceFlow (nativeClockStep : ℝ)) (environmentUnitary (nativeClockStep : ℝ)) nativeClockStep

def chargedFirst : LoadState := chargeStep receivedState

theorem chargeStep_joint (current : LoadState) : (chargeStep current).joint =
    Load.Quantum.localConjugation (sourceFlow (nativeClockStep : ℝ))
      (environmentUnitary (nativeClockStep : ℝ)) current.joint := localState_joint _ _ _ _

theorem chargedFirst_pc : (pcRead chargedFirst).joint =
    Maximum.chargedState Powered.Producer.poweredTotalHamiltonian (pcRead receivedState).joint
      Powered.Producer.poweredTotalHamiltonian_hermitian (pcRead receivedState).positive.isHermitian := by
  change systemReduce (localState _ _ _ _).joint = _
  rw [localState_pcMarginal, sourceFlow_generated]
  rfl

def sourceWork (current : LoadState) : ℝ := controlWork sourceHamiltonian current (chargeStep current)

theorem chargeStep_actual_work (current : LoadState) :
    sourceWork current = totalEnergy (chargeStep current) - totalEnergy current :=
  localState_controlWork_balance _ _ _ _ _ (sourceFlow_conserves_generator _) (environmentUnitary_commutes _)

theorem chargeStep_environment (current : LoadState) :
    environmentEnergy (chargeStep current).joint = environmentEnergy current.joint :=
  localState_environmentEnergy _ _ _ _ (environmentUnitary_commutes _)

theorem chargeStep_entropy (current : LoadState) :
    loadEntropyProduction (chargeStep current) = loadEntropyProduction current :=
  localState_entropy _ _ _ _ (environmentUnitary_commutes _)

theorem chargeStep_netAccount (current : LoadState) :
    (loadBindingAccountedFreeEnergy (chargeStep current) - loadBindingAccountedFreeEnergy current) +
      (loadEntropyProduction (chargeStep current) - loadEntropyProduction current) = sourceWork current :=
  localState_netAccount _ _ _ _ _ (sourceFlow_conserves_generator _) (environmentUnitary_commutes _)

theorem chargeStep_capacity_balance (current : LoadState) :
    Powered.Producer.poweredJointCapacity (pcRead (chargeStep current)) -
      Powered.Producer.poweredJointCapacity (pcRead current) =
      pcEnergy (chargeStep current).joint - pcEnergy current.joint :=
  localState_pcCapacity_balance _ _ _ _

end
end LAlanine40K2025.Thermal.Recovery.Charging.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
