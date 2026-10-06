import H0mework.Versions.AB.Realization.Operations.Tree.Installation.Source
import H0mework.Versions.R2.Fock.SourceHistory.Operation.Calculation.Admission.Inquiry.Continuation.Authority

/-! The original physical source occurrence owns the action tree. The
component reads that exact event and retains the prior query compilation;
its source tree is never reconstructed from a target or numeric shadow. -/

set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Installation.Fock
open RootInquiryCompletion SourceOperationEffects
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
namespace I
export SourcePhysicalCalculationAdmission.Inquiry
  (mathState mathAnswerFace mathConsumer mathAuthority mathCompilation mathEntry targetCompilationInstallation)
end I
variable (runtime : LivingRuntimeState process) (depth : Nat)
abbrev original := I.mathState runtime depth
def treeLaw : SourceNativeProjectionLaw (original runtime depth).root.source.base.restructuringSource.toLedgerSource where
  Projection := Bool
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} _ _ => match projection with
    | false => PUnit
    | true => RootedAccountedUnfolding ArithmeticGeneration.UnitHistory
  project := fun projection {_current} occurrence _ => match projection with
    | false => PUnit.unit
    | true => (RootGeneratedDebtActivationJointSource.Unit.originalOccurrence
        (SourcePhysicalCalculationAdmission.registered runtime) occurrence).2.actionTrace

abbrev root := (original runtime depth).root.withProjectionCoface (treeLaw runtime depth)
abbrev visit := (original runtime depth).visit

def answerFace : SourceNativeRootSemanticFaceAt (root runtime depth) (visit runtime depth) where
  projection := .inherited (I.mathAnswerFace runtime depth).projection
  active := PUnit.unit
  classifier_eq := rfl

def consumer : SourceNativeInquiryAnswerConsumerAt (root := root runtime depth) (visit := visit runtime depth)
    PUnit.unit (ULift.up ((root runtime depth).emitted (visit runtime depth).current))
    (I.mathEntry runtime depth) (answerFace runtime depth) where
  projection := .inherited (I.mathConsumer runtime depth).projection
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def authority := (I.mathAuthority runtime depth).withProjectionCoface (treeLaw runtime depth)

def compilation : SourceNativeInquiryCompilationProgramAt (root runtime depth) (visit runtime depth)
    (original runtime depth).U7 (original runtime depth).calculus (root runtime depth).source.base.lawSurface
    PUnit.unit (ULift.up ((root runtime depth).emitted (visit runtime depth).current))
    (I.mathEntry runtime depth) (authority runtime depth) where
  compile := fun _ => .answered (answerFace runtime depth) (consumer runtime depth)

def state : RootInquiryStateAt (SourcePhysicalCalculationAdmission.Inquiry.NewN runtime)
    (RootGeneratedDebtActivationJointSource.Unit.JointV (SourcePhysicalCalculationAdmission.registered runtime)) where
  root := root runtime depth
  visit := visit runtime depth
  U7 := (original runtime depth).U7
  calculus := (original runtime depth).calculus
  Query := PUnit
  entryAt := fun _ => I.mathEntry runtime depth
  authorityAt := fun _ => authority runtime depth
  compilationProgramAt := fun query => by cases query; exact compilation runtime depth
  compilationFaceAt := fun query => by
    cases query
    exact { projection := .inherited ((original runtime depth).compilationFaceAt PUnit.unit).projection
            active := ((original runtime depth).compilationFaceAt PUnit.unit).active
            classifier_eq := ((original runtime depth).compilationFaceAt PUnit.unit).classifier_eq
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro _ _ _ impossible
    exact nomatch impossible

def treeSource {current : (RootGeneratedDebtActivationJointSource.Unit.JointV
    (SourcePhysicalCalculationAdmission.registered runtime)).Current}
    (occurrence : (state runtime depth).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    TreeReadAt (state runtime depth) occurrence where
  projection := .component true
  active := PUnit.unit
  classifier_eq := rfl
  payload_eq := rfl

def incidence : SourceNativeRootInquiryInputAt (state runtime depth).root (state runtime depth).visit
    (state runtime depth).Query where
  projection := .component false
  active := PUnit.unit
  classifier_eq := rfl
  queryType_eq := rfl

abbrev queryState := inputState (state runtime depth) (treeSource runtime depth) (incidence runtime depth)
abbrev actualTree := treeAt (state runtime depth) (treeSource runtime depth)
  ((state runtime depth).root.emitted (state runtime depth).visit.current)

theorem tree_source : actualTree runtime depth =
    (RootGeneratedDebtActivationJointSource.Unit.originalOccurrence
      (SourcePhysicalCalculationAdmission.registered runtime)
      ((original runtime depth).root.emitted (original runtime depth).visit.current)).2.actionTrace := rfl

def nativeProgram : RootGeneratedDebtActivationJointSource.Native.Program
    (queryState runtime depth).root.toAuthoritativeRoot.toLedgerRoot where
  emit current := (RootGeneratedDebtActivationJointSource.Native.read?
    (queryState runtime depth).root.toAuthoritativeRoot.toLedgerRoot current).get (by rfl)

def nativeScope : RootGeneratedDebtActivationJointSource.Native.IdentityScope (nativeProgram runtime depth) where
  defaultAnchor := PUnit.unit
  openAt_subsingleton := SourcePhysicalCalculationAdmission.Inquiry.Continuation.oldOpenSubsingleton runtime
  certify := SourcePhysicalCalculationAdmission.Inquiry.Continuation.oldCertificate runtime

end SourceOperationNative.Tree.Installation.Fock
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
