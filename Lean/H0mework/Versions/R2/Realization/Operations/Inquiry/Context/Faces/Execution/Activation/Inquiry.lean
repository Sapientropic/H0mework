import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Source
import H0mework.Versions.R2.Arithmetic.PrimeShadow.LivingLawRootInquiryInputSourceKernel

/-! The exact visit reads its calculation germ from the source's uniform
query family. The auxiliary answered state supplies the generated pair to
the actual action compiler; it does not choose the macro's next branch. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Faces.Execution.Activation
open RootInquiryCompletion SourceOperationEffects
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
  [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (frame : M.Frame (Value := PhysicalValue) (Var := PhysicalVar) (sort := sort))
namespace Shared
variable (programme : Programme (PhysicalValue := PhysicalValue) (PhysicalVar := PhysicalVar) (sort := sort))

def queryInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (baseRoot frame programme).source.base (queryLaw (epoch frame) programme)).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (queryRoot frame programme).source.base (resultLaw (epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (resultRoot frame programme).source.base (consumerLaw (epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (consumerRoot frame programme).source.base (compilationLaw (epoch frame) programme))

def resultInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (queryRoot frame programme).source.base (resultLaw (epoch frame) programme)).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (resultRoot frame programme).source.base (consumerLaw (epoch frame) programme)) |>.trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (consumerRoot frame programme).source.base (compilationLaw (epoch frame) programme))

def consumerInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (resultRoot frame programme).source.base (consumerLaw (epoch frame) programme)).trans
  (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (consumerRoot frame programme).source.base (compilationLaw (epoch frame) programme))

def compilationInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
  (consumerRoot frame programme).source.base (compilationLaw (epoch frame) programme)

abbrev lower := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.ledgerRoot frame.registered frame.packetAt
abbrev actualVisit : SourceNativeTemporalVisitAt (lower frame) := frame.currentState.visit
abbrev actualOccurrence := frame.currentState.root.emitted (actualVisit frame).current
theorem root_flat : (root frame programme).toAuthoritativeRoot.toLedgerRoot = lower frame := rfl

def visit : SourceNativeTemporalVisitAt (root frame programme).toAuthoritativeRoot.toLedgerRoot :=
  { current := (actualVisit frame).current
    history := Eq.mpr (congrArg (fun lower => SourceNativeTemporalReachableAt lower (actualVisit frame).current)
      (root_flat frame programme)) (actualVisit frame).history }
abbrev Query := GermAt (epoch frame) programme (actualOccurrence frame)

def queryInput : SourceNativeRootInquiryInputAt (root frame programme) (visit frame programme) (Query frame programme) where
  projection := (queryInstallation frame programme).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
  queryType_eq := rfl

def query : Query frame programme := (queryInput frame programme).query

theorem query_generated : query frame programme = germAt (epoch frame) programme (actualOccurrence frame) := rfl
theorem query_unique (candidate : Query frame programme) : candidate = query frame programme := germ_unique _ programme _ candidate

def resultFace : SourceNativeRootSemanticFaceAt (root frame programme) (visit frame programme) where
  projection := (resultInstallation frame programme).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def consumer : SourceNativeInquiryAnswerConsumerAt (root := root frame programme) (visit := visit frame programme)
    (query frame programme) (ULift.up.{u + 1, u} (actualOccurrence frame))
    (frame.currentState.entryAt PUnit.unit) (resultFace frame programme) where
  projection := (consumerInstallation frame programme).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := by
    change HEq (SourceNativeInquiryAnswerConsumerTokenAt.canonical : SourceNativeInquiryAnswerConsumerTokenAt
      (germAt (epoch frame) programme (actualOccurrence frame)) _ (entryAt frame (actualOccurrence frame))
        (resultAt frame programme (actualOccurrence frame))) _
    rfl

def baseAuthority := optionalAuthority
  ((SourceOperationInquiry.Context.Installation.root (epoch frame)))
  ((frame.currentState.authorityAt PUnit.unit).withProjectionCoface
    (SourceOperationInquiry.Context.Installation.component (epoch frame)))
  (datum frame programme).component

def authority : SourceNativeLivingTemporalCausalEntryAuthorityAt (root frame programme) (visit frame programme)
    (frame.currentState.entryAt PUnit.unit) :=
  (baseAuthority frame programme).withProjectionCoface (queryLaw (epoch frame) programme)
    |>.withProjectionCoface (resultLaw (epoch frame) programme) |>.withProjectionCoface (consumerLaw (epoch frame) programme)
    |>.withProjectionCoface (compilationLaw (epoch frame) programme)

def answeredCompilation : SourceNativeInquiryCompilationProgramAt (root frame programme) (visit frame programme)
    (base frame).U7 (base frame).calculus (root frame programme).source.base.lawSurface (query frame programme)
    (ULift.up.{u + 1, u} (actualOccurrence frame)) (frame.currentState.entryAt PUnit.unit) (authority frame programme) where
  compile := fun _ => .answered (resultFace frame programme) (consumer frame programme)

def answeredState : RootInquiryStateAt
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered)
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt) where
  root := root frame programme
  visit := visit frame programme
  U7 := (base frame).U7
  calculus := (base frame).calculus
  Query := Query frame programme
  entryAt := fun _ => frame.currentState.entryAt PUnit.unit
  authorityAt := fun _ => authority frame programme
  compilationProgramAt := fun candidate => query_unique frame programme candidate ▸ answeredCompilation frame programme
  compilationFaceAt := fun candidate => by
    cases query_unique frame programme candidate
    exact { projection := (compilationInstallation frame programme).embed PUnit.unit
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro candidate _ _ impossible
    cases query_unique frame programme candidate
    exact nomatch impossible

theorem answered_compiles : (answeredState frame programme).compileInquiry (query frame programme) =
    .answered (resultFace frame programme) (consumer frame programme) := rfl

end Shared

abbrev queryInstallation := Shared.queryInstallation frame originalProgramme
abbrev resultInstallation := Shared.resultInstallation frame originalProgramme
abbrev consumerInstallation := Shared.consumerInstallation frame originalProgramme
abbrev compilationInstallation := Shared.compilationInstallation frame originalProgramme
abbrev visit := Shared.visit frame originalProgramme
abbrev actualOccurrence := Shared.actualOccurrence frame
abbrev Query := Shared.Query frame originalProgramme
abbrev queryInput := Shared.queryInput frame originalProgramme
abbrev query := Shared.query frame originalProgramme
abbrev query_generated := Shared.query_generated frame originalProgramme
abbrev query_unique := Shared.query_unique frame originalProgramme
abbrev resultFace := Shared.resultFace frame originalProgramme
abbrev consumer := Shared.consumer frame originalProgramme
abbrev authority := Shared.authority frame originalProgramme
abbrev answeredCompilation := Shared.answeredCompilation frame originalProgramme
abbrev answeredState := Shared.answeredState frame originalProgramme
abbrev answered_compiles := Shared.answered_compiles frame originalProgramme

end SourceOperationInquiry.Context.Faces.Execution.Activation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
