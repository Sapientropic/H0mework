import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Consumer
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Installation.Source
import H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Inquiry

/-! The occurrence's installed relation programme is executed before the
mother emitter. Its distinct calculation query reads the whole pair; the
original mathematical inquiry and its compilation face remain inherited. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Mother
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarInventoryLift SourceOperationScalarPresentation
namespace S
export SourceOperationInquiry.Context.Installation (Occurrence MaterialAt materialAt component root face actual_material)
end S
namespace Q
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry
  (query state root visit resultFace result_value result_history compiles presentation answered_next
    original_compilation_preserved CalculationQuery)
end Q
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

namespace I
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (mathAnswerFace mathConsumer)
namespace Assembly
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Assembly (compilationInstallation consumerInstallation)
end Assembly
end I

def inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  frame.currentState.root.source.base (S.component frame)

def originalAnswer : SourceNativeRootSemanticFaceAt (S.root frame) frame.currentState.visit where
  projection := (inherited frame).embed (I.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth).projection
  active := (I.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth).active
  classifier_eq := (I.mathAnswerFace frame.old frame.registered frame.packetAt frame.depth).classifier_eq

def originalConsumer : SourceNativeInquiryAnswerConsumerAt (root := S.root frame) (visit := frame.currentState.visit) PUnit.unit
    (ULift.up.{u + 1, u} ((S.root frame).emitted frame.currentState.visit.current))
    (frame.currentState.entryAt PUnit.unit) (originalAnswer frame) where
  projection := (inherited frame).embed (I.mathConsumer frame.old frame.registered frame.packetAt frame.depth).projection
  active := (I.mathConsumer frame.old frame.registered frame.packetAt frame.depth).active
  classifier_eq := (I.mathConsumer frame.old frame.registered frame.packetAt frame.depth).classifier_eq
  project_heq := HEq.rfl

def originalAuthority := (frame.currentState.authorityAt PUnit.unit).withProjectionCoface (S.component frame)

def originalCompilation : SourceNativeInquiryCompilationProgramAt
    (S.root frame) frame.currentState.visit frame.currentState.U7 frame.currentState.calculus
    (S.root frame).source.base.lawSurface PUnit.unit
    (ULift.up.{u + 1, u} ((S.root frame).emitted frame.currentState.visit.current))
    (frame.currentState.entryAt PUnit.unit) (originalAuthority frame) where
  compile := fun _ => .answered (originalAnswer frame) (originalConsumer frame)

/-- This is the already source-answered mathematical query, transported by
the source coface. The frame's earlier goal family remains in the inventory. -/
def baseState : RootInquiryStateAt
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered)
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt) where
  root := S.root frame
  visit := frame.currentState.visit
  U7 := frame.currentState.U7
  calculus := frame.currentState.calculus
  Query := PUnit
  entryAt := fun _ => frame.currentState.entryAt PUnit.unit
  authorityAt := fun _ => originalAuthority frame
  compilationProgramAt := fun query => by cases query; exact originalCompilation frame
  compilationFaceAt := fun query => by
    cases query
    exact { projection := (inherited frame).embed
              ((I.Assembly.compilationInstallation frame.old frame.registered frame.packetAt).embed PUnit.unit)
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ _ _ impossible
    exact nomatch impossible

def material {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : S.Occurrence frame (current := current)) :=
  (S.component frame).project PUnit.unit occurrence PUnit.unit

def wordAt {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : S.Occurrence frame (current := current)) :
    Word (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort) :=
  relationMap (R := ℤ) (material frame occurrence).raw.environment (material frame occurrence).relations

def reader {current : RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
    (occurrence : S.Occurrence frame (current := current)) :
    O.Raw (Value := PairValue PhysicalValue) (Var := PhysicalVar) (sort := sort) :=
  ⟨pairEnvironment (material frame occurrence).raw.environment
      ((material frame occurrence).nextRaw.environment - (material frame occurrence).raw.environment),
    liftExpr (expression (wordAt frame occurrence))⟩

def inquiry := Q.state (baseState frame) (reader frame)
def query (incidence : frame.currentState.Query) := Q.query (baseState frame) (reader frame) incidence
def resultFace := Q.resultFace (baseState frame) (reader frame)

def inheritedMaterialFace : SourceNativeRootSemanticFaceAt (inquiry frame).root (inquiry frame).visit where
  projection := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.oldInstallation
    (baseState frame) (reader frame)).embed (S.face frame).projection
  active := (S.face frame).active
  classifier_eq := (S.face frame).classifier_eq

theorem inherited_material : (inheritedMaterialFace frame).rootRead =
    material frame (frame.currentState.root.emitted frame.currentState.visit.current) := rfl

private theorem pair_expression_eval
    (word : Word (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))
    (old increment : Env PhysicalValue PhysicalVar) :
    (liftExpr (expression word)).eval (pairEnvironment old increment) =
      updateInventory (R := ℤ) old increment word := by
  rw [eval_liftExpr, expression_eval]
  apply Prod.ext
  · rfl
  · apply add_left_cancel (a := evaluation (R := ℤ) old word)
    change evaluation (R := ℤ) old word + (expression word).effect old increment =
      evaluation (R := ℤ) old word + effectEvaluator (R := ℤ) old increment word
    rw [← expression_eval word old, ← Expr.eval_update, expression_eval]
    simpa only [expression_eval, LinearMap.add_apply] using LinearMap.congr_fun
      (evaluation_update (R := ℤ) old increment) word

theorem actual_value : (resultFace frame).rootRead.2.2.1 =
    updateInventory (R := ℤ) (material frame (frame.currentState.root.emitted frame.currentState.visit.current)).raw.environment
      ((material frame (frame.currentState.root.emitted frame.currentState.visit.current)).nextRaw.environment -
        (material frame (frame.currentState.root.emitted frame.currentState.visit.current)).raw.environment)
      (wordAt frame (frame.currentState.root.emitted frame.currentState.visit.current)) :=
  (Q.result_value (baseState frame) (reader frame)).trans
    (pair_expression_eval (wordAt frame (frame.currentState.root.emitted frame.currentState.visit.current))
      (material frame (frame.currentState.root.emitted frame.currentState.visit.current)).raw.environment
      ((material frame (frame.currentState.root.emitted frame.currentState.visit.current)).nextRaw.environment -
        (material frame (frame.currentState.root.emitted frame.currentState.visit.current)).raw.environment))

theorem compiled (incidence : frame.currentState.Query) : (inquiry frame).compileInquiry (query frame incidence) =
    .answered (resultFace frame)
      (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumer
        (baseState frame) (reader frame) (query frame incidence)) := Q.compiles _ _ _

theorem actual_next (incidence : frame.currentState.Query) :
    (RootInquiryProcessNode.answered (Q.presentation (baseState frame) (reader frame)) (query frame incidence)).erase =
      (⟨_, (Q.root (baseState frame) (reader frame)).generatedNextCurrentAt (Q.visit (baseState frame) (reader frame))⟩ :
        AnyAuthoritativeRootCurrent) := Q.answered_next _ _ _

theorem original_query_preserved (incidence : frame.currentState.Query) :
    type_of% (Q.original_compilation_preserved (baseState frame) (reader frame) incidence) :=
  Q.original_compilation_preserved (baseState frame) (reader frame) incidence

end SourceOperationInquiry.Context.Faces.Execution.Mother
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
