import H0mework.Versions.R9c73a630.Chemistry.LAlanineWork.FieldActionProgram

/-! # The action-generated descendant runs through the existing canonical runtime -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Work.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Propagation.Producer Drive
open scoped ComplexOrder

noncomputable section

theorem fieldRuntimeRoot_generated : generatedFieldAction.target.targetRoot = fieldLivingRoot := rfl

def fieldProcessCurrent (visit : RootVisit fieldLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt FieldN := ⟨FieldV, fieldLivingRoot, .finite visit⟩

def fieldRuntimeProcess : SourceNativeLivingRootProcess FieldN where
  State := RootVisit fieldLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := fieldProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨FieldV, fieldLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt FieldN) =
      ⟨FieldV, fieldLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := fieldLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨visit.next rfl, rfl, HEq.rfl⟩

def fieldRuntimeFacade : SourceNativeLivingRuntimeFacade FieldN where
  process := fieldRuntimeProcess
  FaceAt := fun _ => FieldProjection
  componentAt := fun _ _ => fieldProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def fieldRuntimeSeed : LivingRuntimeState fieldRuntimeProcess := fieldRuntimeFacade.seed

def fieldRuntimeAfterFirst : LivingRuntimeState fieldRuntimeProcess := fieldRuntimeSeed.tick.next

theorem fieldRuntimeFirst_is_generated_action :
    fieldCurrentState fieldRuntimeAfterFirst.state.current = generatedFieldAction.answer := rfl

theorem fieldRuntimeNext_received (runtime : LivingRuntimeState fieldRuntimeProcess) :
    fieldCurrentState runtime.tick.next.state.current = fieldStateNext (fieldCurrentState runtime.state.current) := rfl

theorem fieldRuntime_nextClock (runtime : LivingRuntimeState fieldRuntimeProcess) :
    (fieldCurrentState runtime.tick.next.state.current).localClock =
      (fieldCurrentState runtime.state.current).localClock + nativeClockStep := rfl

theorem fieldRuntime_capacityBalance (runtime : LivingRuntimeState fieldRuntimeProcess) :
    fieldCapacity (fieldCurrentState runtime.tick.next.state.current).pair
        (fieldCurrentState runtime.tick.next.state.current).positive.isHermitian -
      fieldCapacity (fieldCurrentState runtime.state.current).pair
        (fieldCurrentState runtime.state.current).positive.isHermitian =
      (fieldCurrentState runtime.tick.next.state.current).netWork -
        (fieldCurrentState runtime.state.current).netWork :=
  fieldStateNext_capacity (fieldCurrentState runtime.state.current)

theorem fieldRuntimeFace_factorizes (runtime : LivingRuntimeState fieldRuntimeProcess) (projection : FieldProjection) :
    type_of% (fieldRuntimeFacade.readoutAt_factorizes runtime projection) :=
  fieldRuntimeFacade.readoutAt_factorizes runtime projection

theorem fieldRuntime_capacity_is_installed (runtime : LivingRuntimeState fieldRuntimeProcess) :
    fieldRuntimeFacade.readoutAt runtime .capacityBalance =
      (.inl ⟨PUnit.unit, ⟨fieldStateNext_capacity (fieldCurrentState runtime.state.current)⟩⟩ :
        SourceNativeProjectionFiberAt fieldProjectionLaw .capacityBalance (fieldEmitted runtime.state.current)) := rfl

theorem fieldRuntime_completeWorkFace (runtime : LivingRuntimeState fieldRuntimeProcess) :
    type_of% (fieldRuntimeFace_factorizes runtime .capacityBalance) ∧
    type_of% (fieldRuntime_capacity_is_installed runtime) ∧
    type_of% (fieldRuntimeNext_received runtime) ∧ type_of% (fieldRuntime_capacityBalance runtime) :=
  ⟨fieldRuntimeFace_factorizes runtime .capacityBalance, fieldRuntime_capacity_is_installed runtime,
    fieldRuntimeNext_received runtime, fieldRuntime_capacityBalance runtime⟩

end

end LAlanine40K2025.Thermal.Work.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
