import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Weak.Runtime.Program

/-! # Canonical weak-supply runtime generated from the original nine-q occurrence -/

set_option autoImplicit false
set_option maxRecDepth 16384

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Recovery.Runtime Propagation.Producer
noncomputable section

def processCurrent (visit : RootVisit livingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt RecoveryN := ⟨WeakV, livingRoot, .finite visit⟩

def process : SourceNativeLivingRootProcess RecoveryN where
  State := RootVisit livingRoot.toAuthoritativeRoot.toRoot
  stateAt := processCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨WeakV, livingRoot, .finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN) =
      ⟨WeakV, livingRoot, .finite right⟩ at equality
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
    currentState afterFirst.state.current = generatedAction.answer := rfl

theorem second_is_execution : currentState afterSecond.state.current = execution := rfl

theorem next_joint_actual (runtime : LivingRuntimeState process) :
    (currentState runtime.tick.next.state.current).joint =
      Quantum.conjugation (action runtime.state.current) (currentState runtime.state.current).joint :=
  next_joint runtime.state.current

theorem next_is_load (runtime : LivingRuntimeState process) :
    currentState runtime.tick.next.tick.next.state.current =
      Live.loadNext (currentState runtime.tick.next.state.current) := rfl

theorem next_clock_actual (runtime : LivingRuntimeState process) :
    (currentState runtime.tick.next.state.current).localClock =
      (currentState runtime.state.current).localClock + nativeClockStep :=
  next_clock runtime.state.current

theorem whole_ledger_installed (runtime : LivingRuntimeState process) :
    facade.readoutAt runtime .wholeLedger =
      (.inl ⟨PUnit.unit, ledgerCompiler.compile (emitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt projectionLaw .wholeLedger
          (emitted runtime.state.current)) := rfl

theorem parent_is_installed (runtime : LivingRuntimeState process) (face : SharpNet.Runtime.Face) :
    facade.readoutAt runtime (.parent face) =
      (.inl ⟨PUnit.unit, (parentFace face, ⟨parent_face_factorizes face,origin_is_parent⟩)⟩ :
        SourceNativeProjectionFiberAt projectionLaw (.parent face) (emitted runtime.state.current)) := rfl

theorem supply_is_installed : facade.readoutAt seed .firstSupply =
    (.inl ⟨PUnit.unit, ⟨sourceGeneratedWeakSupplyAndLoad⟩⟩ :
      SourceNativeProjectionFiberAt projectionLaw .firstSupply (emitted .ingress)) := rfl

theorem supply_receipt_not_reissued (runtime : LivingRuntimeState process) :
    facade.readoutAt runtime.tick.next .firstSupply =
      (.inr PUnit.unit : SourceNativeProjectionFiberAt projectionLaw .firstSupply
        (emitted runtime.tick.next.state.current)) := rfl

theorem supply_certificate : type_of% (face_factorizes seed .firstSupply) ∧
    WeakSupplyAndLoadCandidate := by
  refine ⟨face_factorizes seed .firstSupply, ?_⟩
  rcases facade.readoutAt seed .firstSupply with ⟨_, delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Weak.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
