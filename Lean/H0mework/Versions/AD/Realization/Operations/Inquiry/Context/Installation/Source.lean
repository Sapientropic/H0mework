import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Consumer
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.Successor.Inquiry.Continuation.Runtime

/-! The original frame source generates its complete next raw from its own
mathematical action. This epoch-wide component depends on the supplied
occurrence; it does not attach a completed runtime packet as a constant face. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Installation
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
open RootInquiryCompletion
namespace C
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end C
namespace J
export RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw
  (Current World JointV source emitted originalOccurrence mathEntry ledgerRoot)
end J
namespace R
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (MaterialAt input)
end R
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : C.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

abbrev Occurrence {current : J.Current frame.registered} :=
  (J.source frame.registered frame.packetAt).toRootSource.actual.OccurrenceAt current

def rawAt {current : J.Current frame.registered} (_occurrence : Occurrence frame (current := current)) :
    Raw (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) :=
  ⟨frame.registered.input.environment, frame.registered.input.expression⟩

def residualAt {current : J.Current frame.registered} (occurrence : Occurrence frame (current := current)) :
    R.MaterialAt (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort)
      (lower := J.ledgerRoot frame.registered frame.packetAt) occurrence := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact { environment := frame.registered.input.environment
          increment := frame.environment (frame.old.root.emitted current.1) - frame.registered.input.environment
          raw := frame.registered.input.expression
          state := current.2.state
          owner := J.mathEntry frame.registered current }

def nextRawAt {current : J.Current frame.registered} (occurrence : Occurrence frame (current := current)) :
    Raw (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) :=
  match RootGeneratedDebtActivationJointSource.mathAction current.2 with
  | .inr _ => rawAt frame occurrence
  | .inl _ =>
      let request := R.input (residualAt frame occurrence)
      ⟨request.environment, request.expression⟩

abbrev PairValue := SourceOperationScalarInventoryLift.PairValue PhysicalValue

structure MaterialAt {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {lower : SourceNativeLedgerRootClosure N V} {current : V.Current}
    (occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current) : Type u where
  raw : Raw (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
  nextRaw : Raw (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
  paid : R.MaterialAt (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort) (lower := lower) occurrence
  pair : PhysicalValue sort × PhysicalValue sort
  pairTrace : Trace (pairEnvironment raw.environment (nextRaw.environment - raw.environment))
    (liftExpr raw.expression) (.const pair)
  oldValue : PhysicalValue sort
  oldTrace : Trace raw.environment raw.expression (.const oldValue)
  relations : RelationIndex ℤ raw.environment sort →₀ ℤ

def materialAt {current : J.Current frame.registered} (occurrence : Occurrence frame (current := current)) :
    MaterialAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
      (lower := J.ledgerRoot frame.registered frame.packetAt) occurrence :=
  let raw := rawAt frame occurrence
  let nextRaw := nextRawAt frame occurrence
  let paired := pairEnvironment raw.environment (nextRaw.environment - raw.environment)
  ⟨raw, nextRaw, residualAt frame occurrence, (liftExpr raw.expression).eval paired,
    execution paired (liftExpr raw.expression), raw.expression.eval raw.environment,
    execution raw.environment raw.expression, (execution raw.environment raw.expression).relationWords (R := ℤ)⟩

def component : SourceNativeProjectionLaw
    frame.currentState.root.toAuthoritativeRoot.source.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => MaterialAt (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
      (lower := J.ledgerRoot frame.registered frame.packetAt) occurrence
  project := fun _ {_current} occurrence _ => materialAt frame occurrence

def source := frame.currentState.root.source.base.withProjectionCoface (component frame)

def root := frame.currentState.root.withProjectionCoface (component frame)

def installation := SourceNativeProjectionLaw.InstallationAt.componentCoface
  frame.currentState.root.source.base (component frame)

def face : SourceNativeRootSemanticFaceAt (root frame) frame.currentState.visit where
  projection := (installation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem actual_material : (face frame).rootRead = materialAt frame
    (frame.currentState.root.emitted frame.currentState.visit.current) := rfl

theorem epoch_component : component frame.mathNext = component frame := by
  unfold component
  dsimp only [RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.mathNext]
  congr 1
  funext projection current occurrence active
  rcases occurrence with ⟨support, event⟩
  cases event
  unfold materialAt nextRawAt rawAt residualAt
  cases RootGeneratedDebtActivationJointSource.mathAction current.2 <;> rfl

theorem pair_value {current : J.Current frame.registered} (occurrence : Occurrence frame (current := current)) :
    (materialAt frame occurrence).pair =
      ((rawAt frame occurrence).expression.eval (rawAt frame occurrence).environment,
        (rawAt frame occurrence).expression.effect (rawAt frame occurrence).environment
          ((nextRawAt frame occurrence).environment - (rawAt frame occurrence).environment)) :=
  eval_liftExpr _ _ _

theorem source_ledger : (root frame).toAuthoritativeRoot.toLedgerRoot =
    frame.currentState.root.toAuthoritativeRoot.toLedgerRoot := rfl

end SourceOperationInquiry.Context.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
