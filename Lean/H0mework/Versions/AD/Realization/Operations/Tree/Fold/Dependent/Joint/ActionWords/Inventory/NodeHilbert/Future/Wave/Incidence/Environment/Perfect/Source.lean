import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Perfect.Kernel
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Perfect
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
variable (initialFrame : Frame.{u})
abbrev runtime := WriteBack.runtime initialFrame
abbrev source := WriteBack.actualRawSource initialFrame
abbrev Carrier := SourceOperationInquiry.Carrier (runtime initialFrame)
abbrev pairing : Carrier initialFrame →ₗ[ℤ] Module.Dual ℤ (Carrier initialFrame) :=
 SourceGeneratedCompleteWordDual.pairing
abbrev frameAt (stage : Nat) := Shared.frames initialFrame WriteBack.programme stage
abbrev Occurrence (stage : Nat) := SourceOperationInquiry.Context.Installation.Occurrence (frameAt initialFrame stage)
 (current:=(SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit (frameAt initialFrame stage)).current)
abbrev occurrence (stage : Nat) : Occurrence initialFrame stage := Shared.actualOccurrence (frameAt initialFrame stage)
abbrev Pairing := Carrier initialFrame →ₗ[ℤ] Module.Dual ℤ (Carrier initialFrame)
abbrev Topology (stage : Nat) := type_of% (Configured.topology initialFrame WriteBack.programme stage)
abbrev Logic (stage : Nat) := type_of% (Configured.wordFibre initialFrame WriteBack.programme stage)
abbrev Relation (stage : Nat) := type_of% (SourceOperationInquiry.Context.Faces.actualMorphism (runtime initialFrame) (source initialFrame)
 ((runtime initialFrame).stateAt stage))
abbrev Cochain (stage : Nat) := type_of% (Configured.cochain initialFrame WriteBack.programme stage)
abbrev Packet (stage : Nat) := Σ occurrence : Occurrence initialFrame stage,
 type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot (frameAt initialFrame stage) WriteBack.programme).toAuthoritativeRoot occurrence)

abbrev Input (stage : Nat) := UnifiedFourFace.Input (Packet initialFrame stage)
 (Packet initialFrame stage × Pairing initialFrame)
 (Packet initialFrame stage × type_of% (WriteBack.history (frameAt initialFrame stage) (frameAt initialFrame stage).depth))
 (Packet initialFrame stage × Topology initialFrame stage)
 (Packet initialFrame stage × Logic initialFrame stage)
 (Packet initialFrame stage × Relation initialFrame stage)
 (Packet initialFrame stage × Cochain.{u} stage)
 (Carrier initialFrame) (Carrier initialFrame)
def packet (stage : Nat) : Packet initialFrame stage :=
 ⟨occurrence initialFrame stage,
 RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
  (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot (frameAt initialFrame stage) WriteBack.programme).toAuthoritativeRoot
  (occurrence initialFrame stage)⟩
def input (stage : Nat) : Input initialFrame stage where
 occurrence := .zero (packet initialFrame stage)
 algebraAt := fun original => (original,pairing initialFrame)
 combinatorialAt := fun original => (original,WriteBack.history (frameAt initialFrame stage) (frameAt initialFrame stage).depth)
 topologicalAt := fun original => (original,Configured.topology initialFrame WriteBack.programme stage)
 logicalAt := fun original => (original,Configured.wordFibre initialFrame WriteBack.programme stage)
 relationAt := fun original => (original,SourceOperationInquiry.Context.Faces.actualMorphism (runtime initialFrame) (source initialFrame)
  ((runtime initialFrame).stateAt stage))
 cochainAt := fun original => (original,Configured.cochain initialFrame WriteBack.programme stage)
 dualEvaluationAt := fun _ => pairing initialFrame
 faithfulAt := fun _ => LinearMap.id
def generated (stage : Nat) := UnifiedFourFace.generate (input initialFrame stage)
theorem dual_equation (stage : Nat) : (generated initialFrame stage).embedding.comp (generated initialFrame stage).canonical=
 pairing initialFrame := UnifiedFourFace.generated_dual_readback (input initialFrame stage)
theorem same_occurrence (stage : Nat) : (input initialFrame stage).occurrence.root.1=occurrence initialFrame stage := rfl
abbrev Coimage := SourceGeneratedPerfectification.PerfectificationCarrier (pairing initialFrame)
abbrev recover : Coimage initialFrame →ₗ[ℤ] Carrier initialFrame := SourceGeneratedCompleteWordDual.coimageRecovery
def sourceAction : Coimage initialFrame →ₗ[ℤ] Coimage initialFrame :=
 (SourceGeneratedPerfectification.canonicalMap (pairing initialFrame)).comp
  ((SourceOperationInquiry.sourceAction (runtime initialFrame)).comp (recover initialFrame))
theorem recover_source (word : Carrier initialFrame) :
 recover initialFrame (SourceGeneratedPerfectification.canonicalMap (pairing initialFrame) word)=word :=
 SourceGeneratedCompleteWordDual.recovery_source word
theorem source_action (word : Carrier initialFrame) :
 sourceAction initialFrame (SourceGeneratedPerfectification.canonicalMap (pairing initialFrame) word)=
 SourceGeneratedPerfectification.canonicalMap (pairing initialFrame) (SourceOperationInquiry.sourceAction (runtime initialFrame) word) :=
 congrArg (fun value => SourceGeneratedPerfectification.canonicalMap (pairing initialFrame)
  (SourceOperationInquiry.sourceAction (runtime initialFrame) value)) (recover_source initialFrame word)
def environmentRead : Coimage initialFrame →+ Env Value.{u} Var.{u} :=
 (SourceOperationInquiry.Context.environment (runtime initialFrame) (source initialFrame)).comp (recover initialFrame).toAddMonoidHom
def nextEnvironmentRead (state : (runtime initialFrame).State) :=
 environmentRead initialFrame (sourceAction initialFrame (SourceGeneratedPerfectification.canonicalMap
  (pairing initialFrame) (SourceOperationInquiry.point (runtime initialFrame) state)))
theorem next_environment (state : (runtime initialFrame).State) :
 nextEnvironmentRead initialFrame state=SourceOperationInquiry.Context.readEnv (runtime initialFrame) (source initialFrame) state.tick.nextState := by
 unfold nextEnvironmentRead
 rw [source_action]
 change SourceOperationInquiry.Context.environment (runtime initialFrame) (source initialFrame)
  (recover initialFrame (SourceGeneratedPerfectification.canonicalMap (pairing initialFrame)
   (SourceOperationInquiry.sourceAction (runtime initialFrame) (SourceOperationInquiry.point (runtime initialFrame) state))))=_
 rw [recover_source]
 exact SourceOperationInquiry.Context.environment_action _ _ _
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment.Perfect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
