import H0mework.Computation.AIGHold.RecoveryMemoryWork
import H0mework.Physics.ReceiverActuation.CommonTarget

/-!
# The actual receiver recharge pays its literal target-memory energy

The current supplies its generated load endpoint, original memory/controls and common recovery
clock. The target is the existing common-recovery writer, not a caller-selected replacement.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer

open Std.Sat Units.Interface Physical.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface

noncomputable section
namespace FiniteADCWholeJointCurrent

variable {β : Type} [DecidableEq β] [Hashable β]
  {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {clockMax : Nat} {technology : AIGCellTechnology}
  (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
  (current : FiniteADCWholeJointCurrent hardware clockMax technology)

def receiverRechargeStoredEnergyAt (time : ℝ) : SIJoule :=
  aigRecoveryMemoryStoredEnergyAt technology (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
    current.memory current.assignment (commonOutputRecoveryInitial downstreamTechnology downstreamGraph current)
    (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value time

def receiverRechargeWorkAt (time : ℝ) : SIJoule :=
  aigRecoveryMemoryWorkAt technology (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
    current.memory current.assignment (commonOutputRecoveryInitial downstreamTechnology downstreamGraph current)
    (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value time

def receiverRechargeHeatAt (time : ℝ) : SIJoule :=
  aigRecoveryMemoryHeatAt technology (receiverWholeGraph hardware.adcCode (Nat.log 2 clockMax + 1))
    current.memory current.assignment (commonOutputRecoveryInitial downstreamTechnology downstreamGraph current)
    (commonOutputRecoveryStart (hardware := hardware) (clockMax := clockMax) (technology := technology)
      downstreamTechnology downstreamGraph).value time

theorem receiverRechargeStoredEnergyAt_integrated_balance (time : ℝ) :
    (receiverRechargeStoredEnergyAt downstreamTechnology downstreamGraph current time).value -
      (receiverRechargeStoredEnergyAt downstreamTechnology downstreamGraph current 0).value =
        (receiverRechargeWorkAt downstreamTechnology downstreamGraph current time).value -
          (receiverRechargeHeatAt downstreamTechnology downstreamGraph current time).value :=
  aigRecoveryMemoryStoredEnergyAt_integrated_balance _ _ _ _ _ _ time

theorem receiverRechargeHeatAt_nonneg (time : ℝ) (nonnegative : 0 ≤ time) :
    0 ≤ (receiverRechargeHeatAt downstreamTechnology downstreamGraph current time).value :=
  aigRecoveryMemoryHeatAt_nonneg _ _ _ _ _ _ time nonnegative

/-- All registered input and capacitor coordinates are read back from the literal target writer. -/
theorem receiverRechargeStoredEnergyAt_target :
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).1.storedEnergy =
      receiverRechargeStoredEnergyAt downstreamTechnology downstreamGraph current
        (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value :=
  aigBankCommonRecoveryMemory_storedEnergy _ _ _ _ _ _ _ _
    (commonOutputRecoveryStart_nonnegative downstreamTechnology downstreamGraph)

/-- Source-generated common time pays the actual target memory and nonnegative complete heat. -/
theorem receiverRecharge_target_paid :
    let time := (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value
    (commonRecoveryTarget downstreamTechnology downstreamGraph current).1.storedEnergy.value -
      (receiverRechargeStoredEnergyAt downstreamTechnology downstreamGraph current 0).value =
        (receiverRechargeWorkAt downstreamTechnology downstreamGraph current time).value -
          (receiverRechargeHeatAt downstreamTechnology downstreamGraph current time).value ∧
      0 ≤ (receiverRechargeHeatAt downstreamTechnology downstreamGraph current time).value := by
  dsimp only
  rw [receiverRechargeStoredEnergyAt_target]
  exact ⟨receiverRechargeStoredEnergyAt_integrated_balance downstreamTechnology downstreamGraph current _,
    receiverRechargeHeatAt_nonneg downstreamTechnology downstreamGraph current _
      (commonRecoverySampleTime_nonnegative downstreamTechnology downstreamGraph current)⟩

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
