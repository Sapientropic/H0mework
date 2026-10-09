import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Runtime.PoweredActionProgram

/-! # The action-generated descendant runs through the existing canonical runtime -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Powered.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Producer
open scoped ComplexOrder

noncomputable section

theorem poweredRuntimeRoot_generated : generatedPoweredAction.target.targetRoot = poweredLivingRoot := rfl

def poweredProcessCurrent (visit : RootVisit poweredLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt PoweredN := ⟨PoweredV, poweredLivingRoot, .finite visit⟩

def poweredRuntimeProcess : SourceNativeLivingRootProcess PoweredN where
  State := RootVisit poweredLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := poweredProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨PoweredV, poweredLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt PoweredN) =
      ⟨PoweredV, poweredLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := poweredLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨visit.next rfl, rfl, HEq.rfl⟩

def poweredRuntimeFacade : SourceNativeLivingRuntimeFacade PoweredN where
  process := poweredRuntimeProcess
  FaceAt := fun _ => PoweredProjection
  componentAt := fun _ _ => poweredProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def poweredRuntimeSeed : LivingRuntimeState poweredRuntimeProcess := poweredRuntimeFacade.seed

def poweredRuntimeAfterFirst : LivingRuntimeState poweredRuntimeProcess := poweredRuntimeSeed.tick.next

theorem poweredRuntimeFirst_is_generated_action :
    poweredCurrentState poweredRuntimeAfterFirst.state.current = generatedPoweredAction.answer := rfl

theorem poweredRuntimeNext_received (runtime : LivingRuntimeState poweredRuntimeProcess) :
    poweredCurrentState runtime.tick.next.state.current = poweredStateNext (poweredCurrentState runtime.state.current) := rfl

theorem poweredRuntime_nextClock (runtime : LivingRuntimeState poweredRuntimeProcess) :
    (poweredCurrentState runtime.tick.next.state.current).localClock =
      (poweredCurrentState runtime.state.current).localClock + nativeClockStep := rfl

theorem poweredRuntime_energyBalance (runtime : LivingRuntimeState poweredRuntimeProcess) :
    (poweredPairEnergy (poweredCurrentState runtime.tick.next.state.current) -
      poweredPairEnergy (poweredCurrentState runtime.state.current)) +
    (poweredControllerEnergy (poweredCurrentState runtime.tick.next.state.current) -
      poweredControllerEnergy (poweredCurrentState runtime.state.current)) = 0 :=
  poweredStateNext_energyBalance (poweredCurrentState runtime.state.current)

theorem poweredRuntime_energyBound (runtime : LivingRuntimeState poweredRuntimeProcess) :
    poweredControllerEnergy (poweredCurrentState runtime.state.current) - 2 ≤
      poweredPairEnergy (poweredCurrentState runtime.tick.next.state.current) -
        poweredPairEnergy (poweredCurrentState runtime.state.current) ∧
    poweredPairEnergy (poweredCurrentState runtime.tick.next.state.current) -
      poweredPairEnergy (poweredCurrentState runtime.state.current) ≤
        poweredControllerEnergy (poweredCurrentState runtime.state.current) :=
  poweredStateNext_energyBound (poweredCurrentState runtime.state.current)

theorem poweredRuntimeFace_factorizes (runtime : LivingRuntimeState poweredRuntimeProcess)
    (projection : PoweredProjection) :
    type_of% (poweredRuntimeFacade.readoutAt_factorizes runtime projection) :=
  poweredRuntimeFacade.readoutAt_factorizes runtime projection

theorem poweredRuntime_balance_is_installed (runtime : LivingRuntimeState poweredRuntimeProcess) :
    poweredRuntimeFacade.readoutAt runtime .energyBalance =
      (.inl ⟨PUnit.unit, ⟨poweredStateNext_energyBalance (poweredCurrentState runtime.state.current)⟩⟩ :
        SourceNativeProjectionFiberAt poweredProjectionLaw .energyBalance
          (poweredEmitted runtime.state.current)) := rfl

theorem poweredRuntime_controller_is_installed (runtime : LivingRuntimeState poweredRuntimeProcess) :
    poweredRuntimeFacade.readoutAt runtime .controllerEnergy =
      (.inl ⟨PUnit.unit, poweredControllerEnergy (poweredCurrentState runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt poweredProjectionLaw .controllerEnergy
          (poweredEmitted runtime.state.current)) := rfl

theorem poweredRuntime_first_actual_target :
    (poweredCurrentState poweredRuntimeAfterFirst.state.current).joint =
      sourceAdvance (nativeClockStep : ℝ)
        (Dynamics.chargedInput
          (Work.Runtime.fieldCurrentState Work.Runtime.fieldRuntimeAfterFirst.state.current).pair) := rfl

theorem poweredRuntime_capacities_is_installed (runtime : LivingRuntimeState poweredRuntimeProcess) :
    poweredRuntimeFacade.readoutAt runtime .capacities =
      (.inl ⟨PUnit.unit,
        (poweredCapacitiesRead (poweredCurrentState runtime.state.current),
          poweredCapacitiesRead (poweredCurrentState runtime.tick.next.state.current))⟩ :
        SourceNativeProjectionFiberAt poweredProjectionLaw .capacities
          (poweredEmitted runtime.state.current)) := rfl

theorem poweredRuntime_capacityBalance_is_installed (runtime : LivingRuntimeState poweredRuntimeProcess) :
    poweredRuntimeFacade.readoutAt runtime .capacityBalance =
      (.inl ⟨PUnit.unit, ⟨poweredLocal_capacityBalance (poweredCurrentState runtime.state.current),
        poweredJoint_capacityConserved (poweredCurrentState runtime.state.current)⟩⟩ :
        SourceNativeProjectionFiberAt poweredProjectionLaw .capacityBalance
          (poweredEmitted runtime.state.current)) := rfl

theorem poweredRuntime_completeEnergyFace (runtime : LivingRuntimeState poweredRuntimeProcess) :
    type_of% (poweredRuntimeFace_factorizes runtime .energyBalance) ∧
    type_of% (poweredRuntime_balance_is_installed runtime) ∧
    type_of% (poweredRuntimeFace_factorizes runtime .controllerEnergy) ∧
    type_of% (poweredRuntime_controller_is_installed runtime) ∧
    type_of% (poweredRuntimeFace_factorizes runtime .capacities) ∧
    type_of% (poweredRuntime_capacities_is_installed runtime) ∧
    type_of% (poweredRuntimeFace_factorizes runtime .capacityBalance) ∧
    type_of% (poweredRuntime_capacityBalance_is_installed runtime) ∧
    type_of% (poweredRuntimeNext_received runtime) ∧
    type_of% (poweredRuntime_energyBalance runtime) ∧
    type_of% (poweredRuntime_energyBound runtime) :=
  ⟨poweredRuntimeFace_factorizes runtime .energyBalance, poweredRuntime_balance_is_installed runtime,
    poweredRuntimeFace_factorizes runtime .controllerEnergy, poweredRuntime_controller_is_installed runtime,
    poweredRuntimeFace_factorizes runtime .capacities, poweredRuntime_capacities_is_installed runtime,
    poweredRuntimeFace_factorizes runtime .capacityBalance, poweredRuntime_capacityBalance_is_installed runtime,
    poweredRuntimeNext_received runtime, poweredRuntime_energyBalance runtime,
    poweredRuntime_energyBound runtime⟩

end

end LAlanine40K2025.Thermal.Powered.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
