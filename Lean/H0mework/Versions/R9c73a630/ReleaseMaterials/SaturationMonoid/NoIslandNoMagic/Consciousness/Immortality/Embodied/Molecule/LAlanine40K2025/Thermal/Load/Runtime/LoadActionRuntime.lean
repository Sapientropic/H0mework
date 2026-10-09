import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Runtime.LoadActionProgram

/-! # The action-generated descendant runs through the existing canonical runtime -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open scoped ComplexOrder

noncomputable section

theorem loadRuntimeRoot_generated : generatedLoadAction.target.targetRoot = loadLivingRoot := rfl

def loadProcessCurrent (visit : RootVisit loadLivingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt LoadN := ⟨LoadV, loadLivingRoot, .finite visit⟩

def loadRuntimeProcess : SourceNativeLivingRootProcess LoadN where
  State := RootVisit loadLivingRoot.toAuthoritativeRoot.toRoot
  stateAt := loadProcessCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨LoadV, loadLivingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt LoadN) =
      ⟨LoadV, loadLivingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := loadLivingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨visit.next rfl, rfl, HEq.rfl⟩

def loadRuntimeFacade : SourceNativeLivingRuntimeFacade LoadN where
  process := loadRuntimeProcess
  FaceAt := fun _ => LoadProjection
  componentAt := fun _ _ => loadProjectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def loadRuntimeSeed : LivingRuntimeState loadRuntimeProcess := loadRuntimeFacade.seed

def loadRuntimeAfterFirst : LivingRuntimeState loadRuntimeProcess := loadRuntimeSeed.tick.next

theorem loadRuntimeFirst_is_generated_action :
    loadCurrentState loadRuntimeAfterFirst.state.current = generatedLoadAction.answer := rfl

theorem loadRuntimeNext_received (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadCurrentState runtime.tick.next.state.current = loadStateNext (loadCurrentState runtime.state.current) := rfl

theorem loadRuntime_nextClock (runtime : LivingRuntimeState loadRuntimeProcess) :
    (loadCurrentState runtime.tick.next.state.current).localClock =
      (loadCurrentState runtime.state.current).localClock + nativeClockStep := rfl

theorem loadRuntimeNext_joint (runtime : LivingRuntimeState loadRuntimeProcess) :
    (loadCurrentState runtime.tick.next.state.current).joint =
      loadAdvance (nativeClockStep : ℝ) (loadCurrentState runtime.state.current).joint :=
  loadStateNext_joint (loadCurrentState runtime.state.current)

theorem loadRuntime_energyBalance (runtime : LivingRuntimeState loadRuntimeProcess) :
    (pcEnergy (loadCurrentState runtime.tick.next.state.current).joint -
      pcEnergy (loadCurrentState runtime.state.current).joint) +
    (environmentEnergy (loadCurrentState runtime.tick.next.state.current).joint -
      environmentEnergy (loadCurrentState runtime.state.current).joint) +
    (boundaryEnergy (loadCurrentState runtime.tick.next.state.current).joint -
      boundaryEnergy (loadCurrentState runtime.state.current).joint) = 0 :=
  loadStateNext_energyBalance (loadCurrentState runtime.state.current)

theorem loadRuntime_entropyDisposition (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadEntropyProduction (loadCurrentState runtime.tick.next.state.current) =
      loadMutualInformation (loadCurrentState runtime.tick.next.state.current) +
        loadGibbsExcess (loadCurrentState runtime.tick.next.state.current) :=
  loadEntropy_disposition (loadCurrentState runtime.tick.next.state.current)

theorem loadRuntime_entropyNonnegative (runtime : LivingRuntimeState loadRuntimeProcess) :
    0 ≤ loadEntropyProduction (loadCurrentState runtime.tick.next.state.current) :=
  loadEntropy_nonnegative (loadCurrentState runtime.tick.next.state.current)

theorem loadRuntime_signedEntropy (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadEntropyProduction (loadCurrentState runtime.tick.next.state.current) -
      loadEntropyProduction (loadCurrentState runtime.state.current) =
    (loadMutualInformation (loadCurrentState runtime.tick.next.state.current) -
      loadMutualInformation (loadCurrentState runtime.state.current)) +
    (loadGibbsExcess (loadCurrentState runtime.tick.next.state.current) -
      loadGibbsExcess (loadCurrentState runtime.state.current)) :=
  loadStateNext_signedEntropy (loadCurrentState runtime.state.current)

theorem loadRuntimeFace_factorizes (runtime : LivingRuntimeState loadRuntimeProcess)
    (projection : LoadProjection) :
    type_of% (loadRuntimeFacade.readoutAt_factorizes runtime projection) :=
  loadRuntimeFacade.readoutAt_factorizes runtime projection

theorem loadRuntime_balance_is_installed (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadRuntimeFacade.readoutAt runtime .energyBalance =
      (.inl ⟨PUnit.unit, ⟨loadStateNext_energyBalance (loadCurrentState runtime.state.current)⟩⟩ :
        SourceNativeProjectionFiberAt loadProjectionLaw .energyBalance
          (loadEmitted runtime.state.current)) := rfl

theorem loadRuntime_entropy_is_installed (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadRuntimeFacade.readoutAt runtime .entropy =
      (.inl ⟨PUnit.unit,
        (loadEntropyRead (loadCurrentState runtime.state.current),
          loadEntropyRead (loadCurrentState runtime.tick.next.state.current))⟩ :
        SourceNativeProjectionFiberAt loadProjectionLaw .entropy
          (loadEmitted runtime.state.current)) := rfl

theorem loadRuntime_disposition_is_installed (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadRuntimeFacade.readoutAt runtime .entropyDisposition =
      (.inl ⟨PUnit.unit, ⟨loadEntropy_disposition (loadCurrentState runtime.tick.next.state.current),
        loadEntropy_nonnegative (loadCurrentState runtime.tick.next.state.current)⟩⟩ :
        SourceNativeProjectionFiberAt loadProjectionLaw .entropyDisposition
          (loadEmitted runtime.state.current)) := rfl

theorem loadRuntime_signedEntropy_is_installed (runtime : LivingRuntimeState loadRuntimeProcess) :
    loadRuntimeFacade.readoutAt runtime .signedEntropy =
      (.inl ⟨PUnit.unit, (loadEntropyProduction (loadCurrentState runtime.tick.next.state.current) -
        loadEntropyProduction (loadCurrentState runtime.state.current),
        ⟨loadStateNext_signedEntropy (loadCurrentState runtime.state.current)⟩)⟩ :
        SourceNativeProjectionFiberAt loadProjectionLaw .signedEntropy
          (loadEmitted runtime.state.current)) := rfl

theorem loadRuntime_first_actual_target :
    (loadCurrentState loadRuntimeAfterFirst.state.current).joint =
      loadAdvance (nativeClockStep : ℝ)
        (Matrix.kronecker (Powered.Runtime.poweredCurrentState
          Powered.Runtime.poweredRuntimeAfterFirst.tick.next.state.current).joint environmentState) := by
  change (loadStateNext loadInitialState).joint = _
  rw [loadStateNext_joint, loadInitialState_received, loadInitialJoint_receives_actual]

theorem loadRuntime_completeEntropyFace (runtime : LivingRuntimeState loadRuntimeProcess) :
    type_of% (loadRuntimeFace_factorizes runtime .energyBalance) ∧
    type_of% (loadRuntime_balance_is_installed runtime) ∧
    type_of% (loadRuntimeFace_factorizes runtime .entropy) ∧
    type_of% (loadRuntime_entropy_is_installed runtime) ∧
    type_of% (loadRuntimeFace_factorizes runtime .entropyDisposition) ∧
    type_of% (loadRuntime_disposition_is_installed runtime) ∧
    type_of% (loadRuntimeFace_factorizes runtime .signedEntropy) ∧
    type_of% (loadRuntime_signedEntropy_is_installed runtime) ∧
    type_of% (loadRuntimeNext_joint runtime) ∧
    type_of% (loadRuntime_energyBalance runtime) ∧
    type_of% (loadRuntime_entropyDisposition runtime) ∧
    type_of% (loadRuntime_entropyNonnegative runtime) ∧
    type_of% (loadRuntime_signedEntropy runtime) :=
  ⟨loadRuntimeFace_factorizes runtime .energyBalance, loadRuntime_balance_is_installed runtime,
    loadRuntimeFace_factorizes runtime .entropy, loadRuntime_entropy_is_installed runtime,
    loadRuntimeFace_factorizes runtime .entropyDisposition, loadRuntime_disposition_is_installed runtime,
    loadRuntimeFace_factorizes runtime .signedEntropy, loadRuntime_signedEntropy_is_installed runtime,
    loadRuntimeNext_joint runtime, loadRuntime_energyBalance runtime,
    loadRuntime_entropyDisposition runtime, loadRuntime_entropyNonnegative runtime,
    loadRuntime_signedEntropy runtime⟩

end

end LAlanine40K2025.Thermal.Load.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
