import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime.Program

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
open Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.PointerExtract
noncomputable section

theorem compiled_next (current : BodyCurrent) :
    (source.toRootSource.actual.compile (emitted current)).nextCurrent?=some (nextCurrent current) := by
  cases current <;> rfl

def processCurrent (visit : RootVisit livingRoot.toAuthoritativeRoot.toRoot) :
    SourceNativeLivingRootCurrentAt RecoveryN := ⟨BodyV,livingRoot,.finite visit⟩

def process : SourceNativeLivingRootProcess RecoveryN where
  State := RootVisit livingRoot.toAuthoritativeRoot.toRoot
  stateAt := processCurrent
  stateAt_injective := by
    intro left right equality
    change (⟨BodyV,livingRoot,.finite left⟩ : SourceNativeLivingRootCurrentAt RecoveryN)=
      ⟨BodyV,livingRoot,.finite right⟩ at equality
    injection equality with _ _ visitEq
    exact SourceNativeTemporalVisitAt.finite_injective visitEq
  initial := livingRoot.toAuthoritativeRoot.toRoot.initialVisit
  successorAt := by
    intro visit
    refine ⟨visit.next (compiled_next visit.current),?_,?_⟩
    · rcases visit with ⟨current,history⟩
      cases current <;> rfl
    · rcases visit with ⟨current,history⟩
      cases current <;> exact HEq.rfl

def facade : SourceNativeLivingRuntimeFacade RecoveryN where
  process := process
  FaceAt := fun _ => Projection
  componentAt := fun _ _ => projectionLaw
  installationAt := fun _ _ => .ofEq rfl
  projectionAt := fun _ projection => projection

def seed : LivingRuntimeState process := facade.seed
def afterFirst : LivingRuntimeState process := seed.tick.next

theorem face_factorizes (runtime : LivingRuntimeState process) (face : Projection) :
    type_of% (facade.readoutAt_factorizes runtime face) := facade.readoutAt_factorizes runtime face

def readCurrent (runtime : LivingRuntimeState process) : ActuationResult :=
  match facade.readoutAt runtime .current with
  | .inl ⟨_,result⟩ => result
  | .inr impossible => nomatch impossible

theorem first_generated : readCurrent afterFirst=generatedAction.answer := rfl

theorem generated_visit : afterFirst.current.visit=generatedAction.target.targetVisit := rfl

theorem current_shape (runtime : LivingRuntimeState process) :
    runtime.state.current=.ingress ∨ runtime.state.current=.ready sourceOutput := by
  have keeps : ∀ {state : process.State}, SourceNativeRuntimeReachableAt process state →
      state.current=.ingress ∨ state.current=.ready sourceOutput := by
    intro state reachable
    induction reachable with
    | initial => exact .inl rfl
    | step prior kept =>
        change nextCurrent _=.ingress ∨ nextCurrent _=.ready sourceOutput
        rcases kept with initial | ready
        · rw [initial]; exact .inr rfl
        · rw [ready]; exact .inr rfl
  exact keeps runtime.reachable

theorem next_output (runtime : LivingRuntimeState process) :
    readCurrent runtime.tick.next=sourceOutput := by
  change currentResult (nextCurrent runtime.state.current)=sourceOutput
  rcases current_shape runtime with initial | ready
  · rw [initial]; rfl
  · rw [ready]; rfl

theorem action_certificate : type_of% (face_factorizes seed .firstActuation) ∧ OriginalFiniteActuation := by
  refine ⟨face_factorizes seed .firstActuation,?_⟩
  rcases facade.readoutAt seed .firstActuation with ⟨_,delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

theorem action_not_reissued (runtime : LivingRuntimeState process) :
    ∃ inactive : projectionLaw.InactiveAt .firstActuation (emitted runtime.tick.next.state.current),
      facade.readoutAt runtime.tick.next .firstActuation=.inr inactive := by
  change ∃ inactive : projectionLaw.InactiveAt .firstActuation (emitted (nextCurrent runtime.state.current)),
    projectionLaw.outcomeAt .firstActuation (emitted (nextCurrent runtime.state.current))=.inr inactive
  cases runtime.state.current <;> exact ⟨PUnit.unit,rfl⟩

theorem whole_ledger_installed (runtime : LivingRuntimeState process) :
    facade.readoutAt runtime .wholeLedger=
      (.inl ⟨PUnit.unit,ledgerCompiler.compile (emitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt projectionLaw .wholeLedger (emitted runtime.state.current)) := rfl

theorem parent_is_installed (runtime : LivingRuntimeState process) (face : Coulomb.Runtime.Face) :
    facade.readoutAt runtime (.parent face)=
      (.inl ⟨PUnit.unit,(parentFace face,⟨parent_face_factorizes face⟩)⟩ :
        SourceNativeProjectionFiberAt projectionLaw (.parent face) (emitted runtime.state.current)) := rfl

theorem actual_clocks :
    type_of% (face_factorizes afterFirst .current) ∧
    (readCurrent afterFirst).resource.quantum.localClock=22*Propagation.Producer.nativeClockStep ∧
    (readCurrent afterFirst).bodyClock=7*Propagation.Producer.nativeClockStep :=
  ⟨face_factorizes afterFirst .current,generatedReceipt.resourceClock,generatedReceipt.bodyClock⟩

theorem actual_generated (i : Coordinate) : type_of% (face_factorizes afterFirst .current) ∧
    nuclearPosition .leave duration i=((readCurrent afterFirst).frame.position i.1 i.2 : ℝ) ∧
    nuclearMomentum .leave duration i=((readCurrent afterFirst).frame.momentum i.1 i.2 : ℝ) ∧
    receiver .leave duration=(readCurrent afterFirst).resource.momentum ∧
    gammaPath .leave duration=(readCurrent afterFirst).realized ∧
    quantumPath .leave duration=(readCurrent afterFirst).resource.quantum.joint :=
  ⟨face_factorizes afterFirst .current,generatedReceipt.generatedBody i⟩

theorem actual_positive : type_of% (face_factorizes seed .firstActuation) ∧
    type_of% (face_factorizes afterFirst .current) ∧ 0 < (readCurrent afterFirst).resource.momentum :=
  ⟨action_certificate.1,face_factorizes afterFirst .current,(half_pos initial_receiver_positive).trans action_certificate.2.remainingStock⟩

theorem actual_nonzero : type_of% (face_factorizes seed .firstActuation) ∧
    type_of% (face_factorizes afterFirst .current) ∧
    (readCurrent afterFirst).frame.momentum ≠ (readCurrent seed).frame.momentum :=
  ⟨action_certificate.1,face_factorizes afterFirst .current,action_certificate.2.actualChange⟩

theorem retained_without_tick (runtime : LivingRuntimeState process) :
    readCurrent runtime.tick.next.tick.next=readCurrent runtime.tick.next := by
  rw [next_output,next_output]

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteActuation.Runtime
