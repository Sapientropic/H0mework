import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Faces.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer
import H0mework.Versions.AE.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Perfect.Kernel
import H0mework.Versions.AE.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "SourceGeneratedInquiryReceiptAction"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedInquiryReceiptAction.Faces
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {S : Type u} {PhysicalValue PhysicalVar : S → Type u}
 [∀ target,AddCommGroup (PhysicalValue target)] {slot : S}
variable (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
 (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=slot))
variable (configuration : SourceOperationInquiry.Context.Faces.Execution.Activation.Programme
 (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=slot))
abbrev Coimage := SourceGeneratedPerfectification.PerfectificationCarrier (pairing frame configuration)
abbrev recover : Coimage frame configuration →ₗ[ℤ] Carrier frame configuration := SourceGeneratedCompleteWordDual.coimageRecovery
def sourceAction : Coimage frame configuration →ₗ[ℤ] Coimage frame configuration :=
 (SourceGeneratedPerfectification.canonicalMap (pairing frame configuration)).comp
  ((SourceOperationInquiry.sourceAction (runtime frame configuration)).comp (recover frame configuration))
theorem recover_source (word : Carrier frame configuration) :
 recover frame configuration (SourceGeneratedPerfectification.canonicalMap (pairing frame configuration) word)=word :=
 SourceGeneratedCompleteWordDual.recovery_source word
theorem source_action (word : Carrier frame configuration) :
 sourceAction frame configuration (SourceGeneratedPerfectification.canonicalMap (pairing frame configuration) word)=
 SourceGeneratedPerfectification.canonicalMap (pairing frame configuration)
  (SourceOperationInquiry.sourceAction (runtime frame configuration) word) :=
 congrArg (fun value => SourceGeneratedPerfectification.canonicalMap (pairing frame configuration)
  (SourceOperationInquiry.sourceAction (runtime frame configuration) value)) (recover_source frame configuration word)
def environmentRead : Coimage frame configuration →+ Env (PairValue PhysicalValue) configuration.LowVar :=
 (SourceOperationInquiry.Context.environment (runtime frame configuration) (source frame configuration)).comp
  (recover frame configuration).toAddMonoidHom
def nextEnvironmentRead (state : (runtime frame configuration).State) :=
 environmentRead frame configuration (sourceAction frame configuration (SourceGeneratedPerfectification.canonicalMap
  (pairing frame configuration) (SourceOperationInquiry.point (runtime frame configuration) state)))
theorem next_environment (state : (runtime frame configuration).State) :
 nextEnvironmentRead frame configuration state=SourceOperationInquiry.Context.readEnv
  (runtime frame configuration) (source frame configuration) state.tick.nextState := by
 unfold nextEnvironmentRead
 rw [source_action]
 change SourceOperationInquiry.Context.environment (runtime frame configuration) (source frame configuration)
  (recover frame configuration (SourceGeneratedPerfectification.canonicalMap (pairing frame configuration)
   (SourceOperationInquiry.sourceAction (runtime frame configuration) (SourceOperationInquiry.point (runtime frame configuration) state))))=_
 rw [recover_source]
 exact SourceOperationInquiry.Context.environment_action _ _ _
variable (stage : Nat)
def queryRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
 (Value:=PairValue (PairValue PhysicalValue)) (Var:=configuration.LowVar) (sort:=slot) :=
 ⟨pairEnvironment (actualRaw frame configuration stage).environment
   (nextEnvironmentRead frame configuration ((runtime frame configuration).stateAt stage)-
    (actualRaw frame configuration stage).environment),
 liftExpr (actualRaw frame configuration stage).expression⟩
def query := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
 (original frame configuration stage).root.toAuthoritativeRoot
 (fun _ => queryRaw frame configuration stage) (occurrence frame configuration stage)
def queryLaw := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultLaw
 (original frame configuration stage).root.toAuthoritativeRoot (fun {_current} _ => queryRaw frame configuration stage)
def queryRoot := (original frame configuration stage).root.withProjectionCoface (queryLaw frame configuration stage)
def queryInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
 (original frame configuration stage).root.source.base (queryLaw frame configuration stage)
def queryFace : SourceNativeRootSemanticFaceAt (queryRoot frame configuration stage)
 (original frame configuration stage).visit where
 projection := (queryInstallation frame configuration stage).embed PUnit.unit
 active := PUnit.unit
 classifier_eq := rfl
def queryFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
 (queryRoot frame configuration stage) (original frame configuration stage).visit
 (original frame configuration stage).U7 (original frame configuration stage).calculus
 (fun _ => queryRaw frame configuration stage)
abbrev queryRuntime := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.runtime
 (queryRoot frame configuration stage) (original frame configuration stage).visit
 (original frame configuration stage).U7 (original frame configuration stage).calculus
 (fun _ => queryRaw frame configuration stage)
end SourceGeneratedInquiryReceiptAction.Faces
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
