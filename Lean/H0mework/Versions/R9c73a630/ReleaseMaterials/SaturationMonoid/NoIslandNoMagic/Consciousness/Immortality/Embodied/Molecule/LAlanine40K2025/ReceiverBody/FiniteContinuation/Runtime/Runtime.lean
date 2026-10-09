import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime.Program

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Thermal.Recovery.Runtime Thermal.Recovery.Reservoir.Runtime
noncomputable section

theorem compiled_next (current : State) :
    (source.toRootSource.actual.compile (emitted current)).nextCurrent?=some (nextState current) := rfl

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
      rfl
    · rcases visit with ⟨current,history⟩
      exact HEq.rfl

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

def readCurrent (runtime : LivingRuntimeState process) : Material :=
  match facade.readoutAt runtime .current with
  | .inl ⟨_,result⟩ => result
  | .inr impossible => nomatch impossible

theorem current_read (runtime : LivingRuntimeState process) : readCurrent runtime=runtime.state.current.1 := rfl

theorem current_admissible (runtime : LivingRuntimeState process) : Admissible (readCurrent runtime) := runtime.state.current.2

theorem next_current (runtime : LivingRuntimeState process) : readCurrent runtime.tick.next=nextMaterial (readCurrent runtime) := rfl

theorem first_generated : readCurrent afterFirst=generatedAction.answer := rfl

theorem generated_visit : afterFirst.current.visit=generatedAction.target.targetVisit := rfl

theorem native_every_tick (runtime : LivingRuntimeState process) :
    runtime.tick.structuralKind=.nativeWrite := rfl

theorem action_certificate (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime .actuation) ∧ ActualStep runtime.state.current := by
  refine ⟨face_factorizes runtime .actuation,?_⟩
  rcases facade.readoutAt runtime .actuation with ⟨_,delivered⟩ | inactive
  · exact delivered.down
  · exact PEmpty.elim inactive

theorem whole_ledger_installed (runtime : LivingRuntimeState process) :
    facade.readoutAt runtime .wholeLedger=
      (.inl ⟨PUnit.unit,ledgerCompiler.compile (emitted runtime.state.current)⟩ :
        SourceNativeProjectionFiberAt projectionLaw .wholeLedger (emitted runtime.state.current)) := rfl

theorem parent_is_installed (runtime : LivingRuntimeState process) (face : FiniteActuation.Runtime.Projection) :
    facade.readoutAt runtime (.parent face)=
      (.inl ⟨PUnit.unit,(parentFace face,⟨parent_face_factorizes face⟩)⟩ :
        SourceNativeProjectionFiberAt projectionLaw (.parent face) (emitted runtime.state.current)) := rfl

def materialHistory (depth : Nat) : SourceGeneratedRuntimeMaterialHistoryAt seed depth :=
  SourceGeneratedRuntimeMaterialHistoryAt.generate seed depth

def atDepth (depth : Nat) : LivingRuntimeState process := (materialHistory depth).target

theorem depth_zero : atDepth 0=seed := rfl

theorem depth_succ (depth : Nat) : atDepth (depth+1)=(atDepth depth).tick.next := rfl

theorem history_factorizes (depth : Nat) : type_of% (materialHistory depth).target_factorizes :=
  (materialHistory depth).target_factorizes

theorem actual_clocks_step (runtime : LivingRuntimeState process) :
    type_of% (face_factorizes runtime .actuation) ∧
    (readCurrent runtime.tick.next).body.resource.quantum.localClock=(readCurrent runtime).body.resource.quantum.localClock+3*Propagation.Producer.nativeClockStep ∧
    (readCurrent runtime.tick.next).body.bodyClock=(readCurrent runtime).body.bodyClock+3*Propagation.Producer.nativeClockStep :=
  ⟨(action_certificate runtime).1,(action_certificate runtime).2.clocks⟩

theorem clocks_at_depth (depth : Nat) :
    (readCurrent (atDepth depth)).body.resource.quantum.localClock=(22+3*(depth : ℚ))*Propagation.Producer.nativeClockStep ∧
    (readCurrent (atDepth depth)).body.bodyClock=(7+3*(depth : ℚ))*Propagation.Producer.nativeClockStep := by
  induction depth with
  | zero =>
      have initial : readCurrent (atDepth 0)=initialMaterial := rfl
      rw [initial]
      simpa only [Nat.cast_zero,mul_zero,add_zero] using initial_clocks
  | succ depth prior =>
      rw [depth_succ]
      have clocks := (actual_clocks_step (atDepth depth)).2
      constructor
      · rw [clocks.1,prior.1]
        push_cast
        ring
      · rw [clocks.2,prior.2]
        push_cast
        ring

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.ReceiverBody.FiniteContinuation.Runtime
