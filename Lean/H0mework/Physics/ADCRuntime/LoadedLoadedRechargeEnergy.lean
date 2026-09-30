import H0mework.Physics.ADCRuntime.ReceiverRechargeWork
import H0mework.Physics.DrivenEnergy.GroundedRecipientHeat
import H0mework.Physics.ReceiverActuation.LoadRecoveryJoin

/-! # Whole recharge joins the actual load sheet to the literal recovered pair -/

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

def recoveredJointStoredEnergy : SIJoule :=
  (commonRecoveryTarget downstreamTechnology downstreamGraph current).1.storedEnergy +
    drivenRLCBankStoredEnergy (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2

def rechargePhaseHeat : SIJoule :=
  receiverRechargeHeatAt downstreamTechnology downstreamGraph current
    (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value +
  commonRecipientRecoveryHeatBetween downstreamTechnology downstreamGraph current 0
    (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value

theorem rechargePhaseHeat_nonneg :
    0 ≤ (rechargePhaseHeat downstreamTechnology downstreamGraph current).value :=
  add_nonneg (receiverRechargeHeatAt_nonneg _ _ _ _
      (commonRecoverySampleTime_nonnegative downstreamTechnology downstreamGraph current))
    (commonRecipientRecoveryHeatBetween_nonneg _ _ _ _ _
      (commonRecoverySampleTime_nonnegative downstreamTechnology downstreamGraph current))

theorem loadEnergy_eq_joint_recharge_initial :
    outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current
      (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
        downstreamTechnology downstreamGraph).value =
      receiverRechargeStoredEnergyAt downstreamTechnology downstreamGraph current 0 +
        drivenRLCBankStoredEnergy (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
          (commonRecipientRecoveryAt downstreamTechnology downstreamGraph current 0) := by
  simpa only [receiverRechargeStoredEnergyAt, aigRecoveryMemoryStoredEnergyAt, commonRecoveryStateAt, add_zero] using
    outputLoadWholeStoredEnergyAt_eq_recovery_initial downstreamTechnology downstreamGraph current

/-- Actual receiver source work pays both recharge and the recipient's continuing resistor heat. -/
theorem rechargePhase_integrated_balance :
    (recoveredJointStoredEnergy downstreamTechnology downstreamGraph current).value -
      (outputLoadWholeStoredEnergyAt downstreamTechnology downstreamGraph current
        (commonOutputLoadDuration (hardware := hardware) (clockMax := clockMax) (technology := technology)
          downstreamTechnology downstreamGraph).value).value =
        (receiverRechargeWorkAt downstreamTechnology downstreamGraph current
          (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value).value -
        (rechargePhaseHeat downstreamTechnology downstreamGraph current).value := by
  have receiver := (receiverRecharge_target_paid downstreamTechnology downstreamGraph current).1
  have recipient := commonRecipientRecoveryTotalEnergyAt_integrated_balance downstreamTechnology downstreamGraph current
    0 (commonRecoverySampleTime downstreamTechnology downstreamGraph current).value
  rw [commonRecipientRecoveryTotalEnergyAt_eq_physical, commonRecipientRecoveryTotalEnergyAt_eq_physical] at recipient
  rw [loadEnergy_eq_joint_recharge_initial]
  dsimp only [recoveredJointStoredEnergy, rechargePhaseHeat, SIQuantity.add_value] at *
  change _ - _ = _ at receiver
  change (drivenRLCBankStoredEnergy (resonantDrivenCoreDimensionedSource hardware.meteredSource.fixture.coreSource)
      (commonRecoveryTarget downstreamTechnology downstreamGraph current).2).value - _ = _ at recipient
  linarith

end FiniteADCWholeJointCurrent
end
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
