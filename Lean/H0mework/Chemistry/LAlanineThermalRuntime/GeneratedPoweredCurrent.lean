import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedPoweredFlow
import H0mework.Chemistry.LAlanineWork.FieldActionRuntime

/-! # The finite controller receives the actual controlled pair and carries its own next -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Producer

open Propagation.Interface Propagation.Producer
open scoped ComplexOrder

noncomputable section

def sourceParentState : Work.Runtime.FieldState :=
  Work.Runtime.fieldCurrentState Work.Runtime.fieldRuntimeAfterFirst.state.current

def sourceReceivedPair : Collision.JointMatrix Basis := sourceParentState.pair

theorem sourceReceivedPair_eq_fieldTarget : sourceReceivedPair = Work.Drive.sourceFieldCycleTarget := by
  change Work.Drive.fieldCycleAdvance Work.Runtime.fieldReceivedPair = _
  rw [Work.Runtime.fieldReceivedPair_eq_source]
  rfl

structure PoweredState where
  localClock : ℚ
  joint : Dynamics.ControllerJoint (Basis × Basis)
  positive : joint.PosSemidef
  normalized : joint.trace = 1

/-- Finite charged material is installed once, at this exact source action. -/
def sourceInitialState : PoweredState where
  localClock := 0
  joint := Dynamics.chargedInput sourceReceivedPair
  positive := Dynamics.chargedInput_positive sourceReceivedPair sourceParentState.positive
  normalized := Dynamics.chargedInput_trace sourceReceivedPair sourceParentState.normalized

theorem sourceInitialState_received : sourceInitialState.joint =
    Dynamics.chargedInput (Work.Runtime.fieldCurrentState Work.Runtime.fieldRuntimeAfterFirst.state.current).pair := rfl

def poweredStateNext (current : PoweredState) : PoweredState where
  localClock := current.localClock + nativeClockStep
  joint := sourceAdvance (nativeClockStep : ℝ) current.joint
  positive := sourceAdvance_positive _ current.joint current.positive
  normalized := (sourceAdvance_trace _ current.joint).trans current.normalized

def poweredPairEnergy (current : PoweredState) : ℝ :=
  Dynamics.systemEnergy Work.Drive.fieldBaseline current.joint

def poweredControllerEnergy (current : PoweredState) : ℝ := Dynamics.controllerEnergy 2 current.joint

theorem poweredStateNext_energyBalance (current : PoweredState) :
    (poweredPairEnergy (poweredStateNext current) - poweredPairEnergy current) +
      (poweredControllerEnergy (poweredStateNext current) - poweredControllerEnergy current) = 0 :=
  sourceAdvance_energyBalance _ current.joint

theorem poweredStateNext_energyBound (current : PoweredState) :
    poweredControllerEnergy current - 2 ≤ poweredPairEnergy (poweredStateNext current) - poweredPairEnergy current ∧
      poweredPairEnergy (poweredStateNext current) - poweredPairEnergy current ≤ poweredControllerEnergy current :=
  sourceAdvance_energyBound _ current.joint current.positive current.normalized

theorem poweredControllerEnergy_range (current : PoweredState) :
    0 ≤ poweredControllerEnergy current ∧ poweredControllerEnergy current ≤ 2 :=
  Dynamics.controllerEnergy_range 2 (by norm_num) current.joint current.positive current.normalized

theorem sourceInitialState_energy : poweredControllerEnergy sourceInitialState = 2 :=
  Dynamics.chargedInput_controllerEnergy 2 sourceReceivedPair sourceParentState.normalized

theorem sourceFirst_supplyBound :
    0 ≤ poweredPairEnergy (poweredStateNext sourceInitialState) - poweredPairEnergy sourceInitialState ∧
      poweredPairEnergy (poweredStateNext sourceInitialState) - poweredPairEnergy sourceInitialState ≤ 2 := by
  have bound := poweredStateNext_energyBound sourceInitialState
  simpa only [sourceInitialState_energy, sub_self] using bound

theorem poweredStateNext_no_reset (current : PoweredState)
    (positiveSupply : poweredPairEnergy current < poweredPairEnergy (poweredStateNext current)) :
    Dynamics.controllerReduce (poweredStateNext current).joint ≠ Dynamics.controllerReduce current.joint :=
  Dynamics.positive_supply_changes_controller _ _ _ _ _ sourceResonance _ current.joint positiveSupply

end

end LAlanine40K2025.Thermal.Powered.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
