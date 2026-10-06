import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Native.Orbit.Installation.Material
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Mother

/-! The mother calculation query executes the occurrence-generated orbit
relation programme. Its source reader consumes the complete event; the
original material, query inventory and canonical whole-ledger next remain
inherited by the existing source installation. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Orbit.Installation.Inquiry
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarInventoryLift SourceOperationScalarPresentation
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Mother (baseState originalAnswer originalConsumer)
end M
namespace Q
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry
  (state query resultFace result_value result_history compiles presentation answered_next original_compilation_preserved)
end Q
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : A.M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))

def sourceRoot := (M.baseState frame).root.withProjectionCoface (component frame)

def inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (M.baseState frame).root.source.base (component frame)

def originalAnswer : SourceNativeRootSemanticFaceAt (sourceRoot frame) (M.baseState frame).visit where
  projection := (inherited frame).embed (M.originalAnswer frame).projection
  active := (M.originalAnswer frame).active
  classifier_eq := (M.originalAnswer frame).classifier_eq

def originalConsumer : SourceNativeInquiryAnswerConsumerAt (root := sourceRoot frame) (visit := (M.baseState frame).visit)
    PUnit.unit (ULift.up.{u + 1, u} ((sourceRoot frame).emitted (M.baseState frame).visit.current))
    ((M.baseState frame).entryAt PUnit.unit) (originalAnswer frame) where
  projection := (inherited frame).embed (M.originalConsumer frame).projection
  active := (M.originalConsumer frame).active
  classifier_eq := (M.originalConsumer frame).classifier_eq
  project_heq := HEq.rfl

def authority := ((M.baseState frame).authorityAt PUnit.unit).withProjectionCoface (component frame)

def originalCompilation : SourceNativeInquiryCompilationProgramAt (sourceRoot frame) (M.baseState frame).visit
    (M.baseState frame).U7 (M.baseState frame).calculus (sourceRoot frame).source.base.lawSurface
    PUnit.unit (ULift.up.{u + 1, u} ((sourceRoot frame).emitted (M.baseState frame).visit.current))
    ((M.baseState frame).entryAt PUnit.unit) (authority frame) where
  compile := fun _ => .answered (originalAnswer frame) (originalConsumer frame)

def baseState : RootInquiryStateAt (J.World frame.registered) (J.JointV frame.registered frame.packetAt) where
  root := sourceRoot frame
  visit := (M.baseState frame).visit
  U7 := (M.baseState frame).U7
  calculus := (M.baseState frame).calculus
  Query := PUnit
  entryAt := fun _ => (M.baseState frame).entryAt PUnit.unit
  authorityAt := fun _ => authority frame
  compilationProgramAt := fun candidate => by cases candidate; exact originalCompilation frame
  compilationFaceAt := fun candidate => by
    cases candidate
    exact { projection := (inherited frame).embed ((M.baseState frame).compilationFaceAt PUnit.unit).projection
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ _ _ impossible
    exact nomatch impossible

def material {current : J.Current frame.registered}
    (occurrence : Context.Installation.Occurrence frame (current := current)) :=
  (component frame).project PUnit.unit occurrence PUnit.unit

def reader {current : J.Current frame.registered}
    (occurrence : Context.Installation.Occurrence frame (current := current)) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue PhysicalValue) (Var := Orbit.Var PhysicalVar) (sort := sort) :=
  (material frame occurrence).pairRaw

def inquiry := Q.state (baseState frame) (reader frame)
def query (incidence : (baseState frame).Query) := Q.query (baseState frame) (reader frame) incidence
def resultFace := Q.resultFace (baseState frame) (reader frame)

def materialFace : SourceNativeRootSemanticFaceAt (inquiry frame).root (inquiry frame).visit where
  projection := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.oldInstallation
    (baseState frame) (reader frame)).embed
      ((SourceNativeProjectionLaw.InstallationAt.componentCoface
        (M.baseState frame).root.source.base (component frame)).embed PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

theorem inherited_material : (materialFace frame).rootRead =
    material frame (frame.currentState.root.emitted frame.currentState.visit.current) := rfl

def complex := SourceSubstitution.complexMorphism (R := ℤ) (s := sort) Orbit.binding
  (materialFace frame).rootRead.environment

theorem complex_generated : complex frame = Relations.complex (ofFrame frame) := rfl

theorem original_material : (materialFace frame).rootRead.original =
    RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
      frame.currentState.root.toAuthoritativeRoot
      (frame.currentState.root.emitted frame.currentState.visit.current) := rfl

theorem physical_material : (materialFace frame).rootRead.physical =
    Context.Installation.materialAt
      (SourceOperationInquiry.Context.Faces.Execution.Activation.epoch frame)
      (frame.currentState.root.emitted frame.currentState.visit.current) := rfl

theorem actual_value : (resultFace frame).rootRead.2.2.1 =
    updateInventory (R := ℤ) (ofFrame frame).orbitEnvironment
      ((ofFrame frame).next.orbitEnvironment - (ofFrame frame).orbitEnvironment)
      (Relations.word (ofFrame frame)) := by
  apply (Q.result_value (baseState frame) (reader frame)).trans
  exact Relations.pair_eval (ofFrame frame)

theorem source_history : (resultFace frame).rootRead.2.1.2.length =
    remaining (Relations.pairRaw (ofFrame frame)).expression :=
  Q.result_history (baseState frame) (reader frame)

theorem compiled (incidence : (baseState frame).Query) :
    type_of% (Q.compiles (baseState frame) (reader frame) (query frame incidence)) :=
  Q.compiles (baseState frame) (reader frame) (query frame incidence)

theorem actual_next (incidence : (baseState frame).Query) :
    type_of% (Q.answered_next (baseState frame) (reader frame) (query frame incidence)) :=
  Q.answered_next (baseState frame) (reader frame) (query frame incidence)

theorem original_query_preserved (incidence : (baseState frame).Query) :
    type_of% (Q.original_compilation_preserved (baseState frame) (reader frame) incidence) :=
  Q.original_compilation_preserved (baseState frame) (reader frame) incidence

end SourceOperationInquiry.Context.Native.Orbit.Installation.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
