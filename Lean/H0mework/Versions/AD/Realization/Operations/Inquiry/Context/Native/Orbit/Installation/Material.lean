import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Relations

/-! Every supplied occurrence generates its complete orbit programme before
emission. The low payload keeps original paid state and occurrence material,
all relation constructors and the executable coefficient word. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation SourceOperationScalarInventoryLift
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (SourceMaterialAt sourceMaterialAt)
end O
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

structure MaterialAt {current : J.Current frame.registered}
    (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) : Type u where
  private mk ::
  original : O.SourceMaterialAt frame.currentState.root.toAuthoritativeRoot occurrence
  physical : SourceOperationInquiry.Context.Installation.MaterialAt
    (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort)
    (lower := J.ledgerRoot frame.registered frame.packetAt) occurrence
  environment : Env PhysicalValue (Orbit.Var PhysicalVar)
  nextEnvironment : Env PhysicalValue (Orbit.Var PhysicalVar)
  expression : Expr PhysicalValue (Orbit.Var PhysicalVar) sort
  trace : Trace nextEnvironment expression (.const (expression.eval nextEnvironment))
  sourceProgramme : RelationIndex ℤ
    (SourceSubstitution.sourceEnvironment Orbit.binding environment) sort →₀ ℤ
  actedProgramme : RelationIndex ℤ environment sort →₀ ℤ
  word : Formal ℤ PhysicalValue (Orbit.Var PhysicalVar) sort
  pairRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value := PairValue PhysicalValue) (Var := Orbit.Var PhysicalVar) (sort := sort)

def materialAt {current : J.Current frame.registered}
    (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    MaterialAt frame occurrence :=
  let cursor := cursorAt frame occurrence
  ⟨O.sourceMaterialAt frame.currentState.root.toAuthoritativeRoot occurrence,
    SourceOperationInquiry.Context.Installation.materialAt frame occurrence,
    cursor.orbitEnvironment, cursor.next.orbitEnvironment, Relations.nextExpression cursor,
    Relations.nextTrace cursor, Relations.programme cursor, Relations.actedProgramme cursor,
    Relations.word cursor, Relations.pairRaw cursor⟩

def component : SourceNativeProjectionLaw frame.currentState.root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => MaterialAt
    (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence
  project := fun _ {_current} occurrence _ => materialAt
    (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame) occurrence

def root := frame.currentState.root.withProjectionCoface (component frame)
def installation := SourceNativeProjectionLaw.InstallationAt.componentCoface
  frame.currentState.root.source.base (component frame)
def face : SourceNativeRootSemanticFaceAt (root frame) frame.currentState.visit where
  projection := (installation frame).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem actual_material : (face frame).rootRead =
    materialAt (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
      (frame.currentState.root.emitted frame.currentState.visit.current) := rfl

theorem component_math : component frame.mathNext = component frame := rfl

theorem generated_word {current : J.Current frame.registered}
    (occurrence : SourceOperationInquiry.Context.Installation.Occurrence frame (current := current)) :
    (materialAt frame occurrence).word =
      substitution (R := ℤ) Orbit.binding
        (Finsupp.single (materialAt frame occurrence).expression 1 -
          Finsupp.single (.const ((materialAt frame occurrence).expression.eval
            (materialAt frame occurrence).nextEnvironment)) 1) :=
  Relations.word_generated (cursorAt frame occurrence)

theorem ledger_preserved : (root frame).toAuthoritativeRoot.toLedgerRoot =
    frame.currentState.root.toAuthoritativeRoot.toLedgerRoot := rfl

end SourceOperationInquiry.Context.Native.Orbit.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
