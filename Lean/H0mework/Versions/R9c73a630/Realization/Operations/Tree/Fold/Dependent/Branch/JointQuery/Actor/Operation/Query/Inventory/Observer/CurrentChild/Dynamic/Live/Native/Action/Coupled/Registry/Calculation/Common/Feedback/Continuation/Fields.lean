import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Material
import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Perfect.Kernel
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationInquiry SourceOperationEffects SourceOperationExecution
namespace Lower.Fields
variable {S : Type u} {W X : S → Type u} [∀ s,AddCommGroup (W s)] {s : S}
variable (initial : M.Frame (Value:=W) (Var:=X) (sort:=s))
variable (nativeFirstCfg : A.Programme (PhysicalValue:=W) (PhysicalVar:=X) (sort:=s))
variable (language : nativeFirstCfg.LowVar=X)
abbrev runtime := Lower.Run.runtime initial (Lower.Facets.firstCfg nativeFirstCfg) language
abbrev carrier := SourceOperationInquiry.Carrier (runtime initial nativeFirstCfg language)
def pairing : carrier initial nativeFirstCfg language →ₗ[ℤ] Module.Dual ℤ (carrier initial nativeFirstCfg language) := SourceGeneratedCompleteWordDual.pairing
abbrev perfect := SourceGeneratedPerfectification.PerfectificationCarrier (pairing initial nativeFirstCfg language)
abbrev recover : perfect initial nativeFirstCfg language →ₗ[ℤ] carrier initial nativeFirstCfg language := SourceGeneratedCompleteWordDual.coimageRecovery

def coimageAction : perfect initial nativeFirstCfg language →ₗ[ℤ] perfect initial nativeFirstCfg language :=
 (SourceGeneratedPerfectification.canonicalMap (pairing initial nativeFirstCfg language)).comp
 ((SourceOperationInquiry.sourceAction (runtime initial nativeFirstCfg language)).comp (recover initial nativeFirstCfg language))

theorem complete_state_word (word : carrier initial nativeFirstCfg language) :
 recover initial nativeFirstCfg language (SourceGeneratedPerfectification.canonicalMap (pairing initial nativeFirstCfg language) word)=word := SourceGeneratedCompleteWordDual.recovery_source word

theorem complete_state_action (word : carrier initial nativeFirstCfg language) :
 coimageAction initial nativeFirstCfg language (SourceGeneratedPerfectification.canonicalMap (pairing initial nativeFirstCfg language) word)=
 SourceGeneratedPerfectification.canonicalMap (pairing initial nativeFirstCfg language)
 (SourceOperationInquiry.sourceAction (runtime initial nativeFirstCfg language) word) :=
 congrArg (fun recovered => SourceGeneratedPerfectification.canonicalMap (pairing initial nativeFirstCfg language)
  (SourceOperationInquiry.sourceAction (runtime initial nativeFirstCfg language) recovered)) (complete_state_word initial nativeFirstCfg language word)

theorem wave_particle (value : SourceOperationInquiry.Field (runtime initial nativeFirstCfg language)) :
 SourceOperationInquiry.equivalence (runtime initial nativeFirstCfg language)
 (SourceOperationInquiry.word (runtime initial nativeFirstCfg language) value)=value := SourceOperationInquiry.source_word _ value

theorem wave_particle_action (value : SourceOperationInquiry.Field (runtime initial nativeFirstCfg language)) :
 SourceOperationInquiry.word (runtime initial nativeFirstCfg language)
 (SourceOperationInquiry.fieldAction (runtime initial nativeFirstCfg language) value)=
 SourceOperationInquiry.sourceAction (runtime initial nativeFirstCfg language)
 (SourceOperationInquiry.word (runtime initial nativeFirstCfg language) value) := SourceOperationInquiry.word_action _ value

abbrev packet (n : Nat) := ((runtime initial nativeFirstCfg language).stateAt n,(runtime initial nativeFirstCfg language).tickAt n,
 Lower.Facets.faceAt initial nativeFirstCfg language n,Lower.Facets.actualFaceAt initial nativeFirstCfg language n,
 Lower.Facets.facesAt initial nativeFirstCfg language n)
end Lower.Fields
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
