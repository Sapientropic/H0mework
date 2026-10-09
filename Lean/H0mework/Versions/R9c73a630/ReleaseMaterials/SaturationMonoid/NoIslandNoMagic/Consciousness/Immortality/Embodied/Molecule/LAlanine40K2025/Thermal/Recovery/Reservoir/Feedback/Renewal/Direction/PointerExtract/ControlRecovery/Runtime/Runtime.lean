import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime.Program

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Reservoir.Runtime Propagation.Producer Resource
open scoped ComplexOrder MatrixOrder
noncomputable section

def processCurrent (visit : RootVisit livingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt RecoveryN := ⟨ControlV, livingRoot, .finite visit⟩

def process : SourceNativeLivingRootProcess RecoveryN where
  State := RootVisit livingRoot.toAuthoritativeRoot.toRoot
  stateAt := processCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨ControlV, livingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN) =
      ⟨ControlV, livingRoot, .finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := livingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := fun visit => ⟨visit.next rfl, rfl, HEq.rfl⟩

def facade : SourceNativeLivingRuntimeFacade RecoveryN where
  process := process
  FaceAt := fun _ => Projection
  componentAt := fun _ _ => projectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def seed : LivingRuntimeState process := facade.seed
def afterFirst : LivingRuntimeState process := seed.tick.next
def afterSecond : LivingRuntimeState process := afterFirst.tick.next

theorem face_factorizes (runtime : LivingRuntimeState process) (projection : Projection) :
    type_of% (facade.readoutAt_factorizes runtime projection) :=
  facade.readoutAt_factorizes runtime projection

theorem face_is_installed (runtime : LivingRuntimeState process) (projection : Projection) :
    facade.readoutAt runtime projection = projectionLaw.outcomeAt projection
      (emitted runtime.state.current) := rfl

theorem first_is_generated :
    currentMaterial afterFirst.state.current = generatedAction.answer := rfl

theorem first_is_control : currentMaterial afterFirst.state.current = controlledMaterial := rfl

theorem second_is_load : currentMaterial afterSecond.state.current = loadNext controlledMaterial := rfl

theorem next_joint_actual (runtime : LivingRuntimeState process) :
    (currentMaterial runtime.tick.next.state.current).quantum.joint =
      Quantum.conjugation (action runtime.state.current) (currentMaterial runtime.state.current).quantum.joint :=
  next_joint runtime.state.current

theorem next_is_load (runtime : LivingRuntimeState process) :
    currentMaterial runtime.tick.next.tick.next.state.current =
      loadNext (currentMaterial runtime.tick.next.state.current) := rfl

theorem next_clock_actual (runtime : LivingRuntimeState process) :
    (currentMaterial runtime.tick.next.state.current).quantum.localClock =
      (currentMaterial runtime.state.current).quantum.localClock + nativeClockStep :=
  next_clock runtime.state.current

theorem whole_ledger_installed (runtime : LivingRuntimeState process) :
    facade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, ledgerCompiler.compile (emitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt projectionLaw .wholeLedger
          (emitted runtime.state.current)) := rfl

theorem parent_is_installed (runtime : LivingRuntimeState process) (face : Replenish.Runtime.Projection) :
    facade.readoutAt runtime (.parent face) =
      (.inl ⟨PUnit.unit, (parentFace face, ⟨parent_face_factorizes face,origin_is_parent⟩)⟩ :
        SourceNativeProjectionFiberAt projectionLaw (.parent face) (emitted runtime.state.current)) := rfl

theorem control_is_installed : facade.readoutAt seed .firstControl =
    (.inl ⟨PUnit.unit, ⟨originalControlExtraction⟩⟩ :
      SourceNativeProjectionFiberAt projectionLaw .firstControl (emitted .ingress)) := rfl

theorem control_receipt_not_reissued (runtime : LivingRuntimeState process) :
    facade.readoutAt runtime.tick.next .firstControl =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt projectionLaw .firstControl
        (emitted runtime.tick.next.state.current)) := rfl

theorem control_certificate : type_of% (face_factorizes seed .firstControl) ∧
    OriginalControlExtraction := by
  refine ⟨face_factorizes seed .firstControl, ?_⟩
  rcases facade.readoutAt seed .firstControl with ⟨_, delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract.ControlRecovery.Runtime
