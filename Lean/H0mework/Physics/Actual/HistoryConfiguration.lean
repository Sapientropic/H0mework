import H0mework.Physics.SpinRuntime.Native

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9CU.History

open Stage9C.Revision
open StageNineHolonomicField
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGlobalOperator
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeJointGlobalSmooth
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite
open StageTenPhysicalRoot

noncomputable section

/-- The revised suffix starts at the registered ingress and only executes
the same source's native successor. -/
def nativeCurrent : ℕ → SpinPair.Current
  | 0 => SpinPair.source.initial
  | index + 1 => SpinPair.next (nativeCurrent index)

def nativeConfiguration (current : SpinPair.Current) : StageNineHolonomicConfiguration :=
  materialConfiguration (SpinPair.support current)

/-- The already registered macro prefix is retained before the revised
source history. Every configuration is read from its actual source current. -/
def configuration : ℕ → StageNineHolonomicConfiguration
  | 0 => (physicalRuntimeVisit 0).current.configuration
  | 1 => (physicalRuntimeVisit 1).current.configuration
  | 2 => (physicalRuntimeVisit 2).current.configuration
  | 3 => firstAssemblyCurrent.configuration
  | 4 => materialConfiguration (materialCurrentSupport (materialVisit 1).current)
  | 5 => materialConfiguration (materialCurrentSupport (materialVisit 2).current)
  | index + 6 => nativeConfiguration (nativeCurrent index)

@[simp] theorem configuration_six :
    configuration 6 =
      materialConfiguration (materialCurrentSupport SpinPair.sourceVisit.current) := rfl

@[simp] theorem configuration_add_seven (index : ℕ) :
    configuration (index + 7) = nativeConfiguration (nativeCurrent (index + 1)) := rfl

private theorem materialConfiguration_smooth (current : MaterialCurrent) :
    (materialConfiguration (materialCurrentSupport current)).Smooth := by
  cases current with
  | ingress => exact root_firstAssembly_smooth
  | running state => exact state.smooth

theorem nativeConfiguration_smooth (current : SpinPair.Current) :
    (nativeConfiguration current).Smooth := by
  cases current with
  | ingress => exact materialConfiguration_smooth SpinPair.sourceVisit.current
  | running state => exact state.smooth

theorem configuration_smooth : ∀ index, (configuration index).Smooth
  | 0 => fixedP506L0CartanECConstraintPreparedActual_smooth
  | 1 => quadraticCofaceSettlement_target_smooth
  | 2 => fixedP506L0CartanECConstraintCauchySafeJointGlobalActual_smooth
  | 3 => root_firstAssembly_smooth
  | 4 => materialConfiguration_smooth (materialVisit 1).current
  | 5 => materialConfiguration_smooth (materialVisit 2).current
  | index + 6 => nativeConfiguration_smooth (nativeCurrent index)

end
end SaturationMonoid.PhysicsCore.Stage9CU.History
