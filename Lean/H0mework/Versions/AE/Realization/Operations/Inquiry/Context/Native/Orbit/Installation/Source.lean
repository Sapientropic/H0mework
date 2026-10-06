import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Relations
import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Observation.Source

/-! A complete source event determines the orbit without a reachability
test. Ordinary updates use its original whole write; settlement registers
the generated residual and consumes that source's own first paid write. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw
  (Current World JointV source emitted targetCurrent mathEntry originalOccurrence ledgerRoot)
end J
namespace R
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (MaterialAt input)
end R
namespace G
export RootGeneratedDebtActivationJointSource (RegisteredAt register initialEvent)
end G
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (next frames runtime)
namespace M
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end M
end A
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}

structure Cursor where
  N : WorldRelationNetwork.{u}
  V : Vocabulary.{u}
  old : SourceNativeLedgerRootClosure N V
  origin : V.Current
  registered : G.RegisteredAt (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort) old origin
  packetAt : (current : V.Current) → RootGeneratedDebtActivationJointSource.Successor.Packet old current
  environment : {current : V.Current} → old.source.source.toRootSource.actual.OccurrenceAt current →
    Env PhysicalValue PhysicalVar
  current : J.Current registered

namespace Cursor
variable (cursor : Cursor (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

def root := J.ledgerRoot cursor.registered cursor.packetAt
def raw : Context.Raw (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) :=
  ⟨cursor.registered.input.environment, cursor.registered.input.expression⟩
def occurrence := J.emitted cursor.registered cursor.packetAt cursor.current

def materialAt (occurrence : cursor.root.source.source.toRootSource.actual.OccurrenceAt cursor.current) :
    R.MaterialAt (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)
      (lower := cursor.root) occurrence := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact { environment := cursor.registered.input.environment
          increment := cursor.environment (cursor.old.emitted cursor.current.1) - cursor.registered.input.environment
          raw := cursor.registered.input.expression
          state := cursor.current.2.state
          owner := J.mathEntry cursor.registered cursor.current }

def material := cursor.materialAt cursor.occurrence
def request := G.register (fun occurrence => R.input (cursor.materialAt occurrence))
def programme (current : J.Current cursor.registered) :=
  (RootGeneratedDebtActivationJointSource.Successor.read? cursor.root current).get (by rfl)
def action := RootGeneratedDebtActivationJointSource.mathAction cursor.current.2

def ordinary : Cursor (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) :=
  { cursor with current := J.targetCurrent cursor.registered cursor.packetAt cursor.current }

def born : Cursor (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) where
  N := J.World cursor.registered
  V := J.JointV cursor.registered cursor.packetAt
  old := cursor.root
  origin := cursor.current
  registered := cursor.request
  packetAt := cursor.programme
  environment := fun {_current} occurrence => cursor.environment
    (J.originalOccurrence cursor.registered cursor.packetAt occurrence)
  current := J.targetCurrent cursor.request cursor.programme
    ⟨cursor.current, G.initialEvent cursor.request⟩

def next := match cursor.action with
  | .inr _ => cursor.ordinary
  | .inl _ => cursor.born

def advance : Nat → Cursor (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
  | 0 => cursor
  | count + 1 => (advance count).next

def orbitEnvironment : Env PhysicalValue (Orbit.Var PhysicalVar) :=
  fun target name => (cursor.advance name.1).raw.environment target name.2

theorem shift_environment :
    SourceOperationScalarPresentation.SourceSubstitution.sourceEnvironment Orbit.binding cursor.orbitEnvironment =
      cursor.next.orbitEnvironment := by
  funext target name
  change (cursor.advance (name.1 + 1)).raw.environment target name.2 =
    (cursor.next.advance name.1).raw.environment target name.2
  have shift : (count : Nat) → cursor.advance (count + 1) = cursor.next.advance count := by
    intro count
    induction count with
    | zero => rfl
    | succ count prior => exact congrArg Cursor.next prior
  exact congrArg (fun value => value.raw.environment target name.2) (shift name.1)

end Cursor

variable (frame : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

def ofFrame : Cursor (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) where
  N := frame.N
  V := frame.V
  old := frame.old.root.toAuthoritativeRoot.toLedgerRoot
  origin := frame.old.visit.current
  registered := frame.registered
  packetAt := frame.packetAt
  environment := frame.environment
  current := RootGeneratedDebtActivationJointSource.Successor.Inquiry.mathCurrent
    frame.old frame.registered frame.packetAt frame.depth

def cursorAt {current : J.Current frame.registered}
    (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    Cursor (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact { N := frame.N
          V := frame.V
          old := frame.old.root.toAuthoritativeRoot.toLedgerRoot
          origin := frame.old.visit.current
          registered := frame.registered
          packetAt := frame.packetAt
          environment := frame.environment
          current := current }

theorem actual_cursor : cursorAt frame (frame.currentState.root.emitted frame.currentState.visit.current) =
    ofFrame frame := rfl

theorem frame_raw : (ofFrame frame).raw = frame.rawRead := rfl

theorem frame_next : (ofFrame frame).next = ofFrame (A.next frame) := by
  have actionEq : (ofFrame frame).action = frame.action := rfl
  unfold Cursor.next
  rw [actionEq]
  unfold SourceOperationInquiry.Context.Faces.Execution.Activation.next
    SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.next
  cases selected : frame.action with
  | inr paid => rfl
  | inl settled => rfl

theorem frame_advance (count : Nat) : (ofFrame frame).advance count = ofFrame (A.frames frame count) := by
  induction count with
  | zero => rfl
  | succ count prior =>
      change ((ofFrame frame).advance count).next = _
      rw [prior, frame_next]
      rfl

end SourceOperationInquiry.Context.Native.Orbit.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
