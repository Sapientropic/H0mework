import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Environment.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Reverse.Consumer
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer
import H0mework.Realization.Operations.ScalarComplex
import H0mework.Realization.Operations.ScalarExact
import H0mework.Realization.Operations.DerivationReduction
import H0mework.Realization.Perfectification.Cofinal.Topology.LivingLawRootGeneratedCofinalAllPrimeTopologyKernel
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "PaidSourceContentEnvironment"
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment
open CategoryTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
namespace Context
export SourceOperationInquiry.Context (RawAt raw readEnv increment actual_operation_receipt)
end Context
namespace NativeObservation
export SourceOperationInquiry.Context.Native.Orbit.Installation.Activation.Observation (rawRestriction raw_restriction)
end NativeObservation
namespace Configured
variable (initialFrame : Frame.{u})
variable (sourceProgramme : A.Programme (PhysicalValue:=Value.{u}) (PhysicalVar:=Var.{u}) (sort:=Slot.orbit))
abbrev contentRuntime := Shared.runtime initialFrame sourceProgramme

def rawSource (state : (contentRuntime initialFrame sourceProgramme).State) :
    SourceOperationInquiry.Context.RawAt (PhysicalValue:=Value.{u}) (PhysicalVar:=Var.{u}) (sort:=Slot.orbit)
      (contentRuntime initialFrame sourceProgramme) state := by
 rcases state with ⟨⟨stage⟩,activation⟩
 exact NativeObservation.rawRestriction (Shared.frames initialFrame sourceProgramme stage.down) sourceProgramme

private def index (engine : Engine (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.process initialFrame sourceProgramme)) : Nat := by
 rcases engine with ⟨stage⟩
 exact stage.down

private theorem raw_state (state : (contentRuntime initialFrame sourceProgramme).State) :
 Context.raw (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) state=
 (Shared.frames initialFrame sourceProgramme (index initialFrame sourceProgramme state.engine)).rawRead := by
 rcases state with ⟨⟨stage⟩,activation⟩
 exact NativeObservation.raw_restriction (Shared.frames initialFrame sourceProgramme stage.down) sourceProgramme

theorem raw_actual (stage : Nat) :
 Context.raw (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) ((contentRuntime initialFrame sourceProgramme).stateAt stage)=
 (Shared.frames initialFrame sourceProgramme stage).rawRead := by
 have atStage : index initialFrame sourceProgramme ((contentRuntime initialFrame sourceProgramme).stateAt stage).engine=stage := by
  have same := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actual_node initialFrame sourceProgramme stage
  generalize engineEq : ((contentRuntime initialFrame sourceProgramme).stateAt stage).engine=engine at same ⊢
  rcases engine with ⟨hidden⟩
  have hiddenEq : hidden=ULift.up stage :=
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.process initialFrame sourceProgramme).erase_injective rfl rfl
    (congrArg RootInquiryProcessNode.erase same)
  subst hidden
  rfl
 exact (raw_state initialFrame sourceProgramme _).trans (congrArg (fun stage => (Shared.frames initialFrame sourceProgramme stage).rawRead) atStage)

theorem environment_actual (stage : Nat) :
 Context.readEnv (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) ((contentRuntime initialFrame sourceProgramme).stateAt stage)=
 (Shared.frames initialFrame sourceProgramme stage).rawRead.environment :=
 congrArg (fun raw => raw.environment) (raw_actual initialFrame sourceProgramme stage)

theorem increment_actual (stage : Nat) :
 Context.increment (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) ((contentRuntime initialFrame sourceProgramme).stateAt stage)=
 (Shared.frames initialFrame sourceProgramme (stage+1)).rawRead.environment-
 (Shared.frames initialFrame sourceProgramme stage).rawRead.environment := by
 change Context.readEnv (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) ((contentRuntime initialFrame sourceProgramme).stateAt (stage+1))-
  Context.readEnv (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) ((contentRuntime initialFrame sourceProgramme).stateAt stage)=_
 rw [environment_actual,environment_actual]

theorem update_inventory (stage : Nat) :
 SourceOperationInquiry.Context.Faces.pairInventory (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)=
 SourceOperationScalarRelations.updateInventory (R:=ℤ)
  (Shared.frames initialFrame sourceProgramme stage).rawRead.environment
  ((Shared.frames initialFrame sourceProgramme (stage+1)).rawRead.environment-
    (Shared.frames initialFrame sourceProgramme stage).rawRead.environment) := by
 unfold SourceOperationInquiry.Context.Faces.pairInventory
 rw [environment_actual,increment_actual]
theorem generated_equation (stage : Nat) :
 (Shared.frames initialFrame sourceProgramme stage).rawRead.expression.eval
  (Shared.frames initialFrame sourceProgramme (stage+1)).rawRead.environment=
 (SourceOperationInquiry.Context.pairValue (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)).1+
 (SourceOperationInquiry.Context.pairValue (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)).2 := by
 have equation := SourceOperationInquiry.Context.next_value (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)
 rw [raw_actual] at equation
 change (Shared.frames initialFrame sourceProgramme stage).rawRead.expression.eval
  (Context.readEnv (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
   ((contentRuntime initialFrame sourceProgramme).stateAt (stage+1)))=_ at equation
 rw [environment_actual] at equation
 exact equation
theorem actual_operation (stage : Nat) : type_of%
 (Context.actual_operation_receipt (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)) :=
 Context.actual_operation_receipt _ _ _
theorem cofinal_relation (stage bound : Nat) (index : Fin (bound+1)) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.relation_read (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) stage bound index) :=
 SourceOperationInquiry.Context.Faces.Cofinal.relation_read _ _ stage bound index
theorem cofinal_fibre (stage : Nat)
 (left right : SourceOperationInquiry.Context.History.Words (PhysicalValue:=Value.{u}) (PhysicalVar:=Var.{u}) (sort:=Slot.orbit)) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.source_fibre (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) stage left right) :=
 SourceOperationInquiry.Context.Faces.Cofinal.source_fibre _ _ stage left right
theorem cofinal_word_readback (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.complete_word_readback (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) stage) :=
 SourceOperationInquiry.Context.Faces.Cofinal.complete_word_readback _ _ stage
theorem cofinal_next (stage bound : Nat) (index : Fin (bound+1)) : type_of%
 (SourceOperationInquiry.Context.Faces.Cofinal.relation_next_read (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) stage bound index) :=
 SourceOperationInquiry.Context.Faces.Cofinal.relation_next_read _ _ stage bound index

abbrev actualRaw (stage : Nat) := Context.raw (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
 ((contentRuntime initialFrame sourceProgramme).stateAt stage)
abbrev exactComplex (stage : Nat) := SourceOperationScalarPresentation.presentationComplex (R:=ℤ) (s:=Slot.orbit)
 (actualRaw initialFrame sourceProgramme stage).environment
theorem exact_complex (stage : Nat) : (exactComplex initialFrame sourceProgramme stage).Exact :=
 SourceOperationScalarPresentation.presentationComplex_exact (R:=ℤ) (s:=Slot.orbit) (actualRaw initialFrame sourceProgramme stage).environment
abbrev cochain (stage : Nat) := SourceOperationScalarCochain.cochain (R:=ℤ) (s:=Slot.orbit)
 (actualRaw initialFrame sourceProgramme stage).environment
 (Context.increment (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) ((contentRuntime initialFrame sourceProgramme).stateAt stage))
theorem cochain_zero (stage : Nat) : (cochain initialFrame sourceProgramme stage).d 0 1 ≫ (cochain initialFrame sourceProgramme stage).d 1 2=0 :=
 (cochain initialFrame sourceProgramme stage).d_comp_d 0 1 2
abbrev derivation (stage : Nat) := SourceOperationDerivations.Derivation.normalize
 (actualRaw initialFrame sourceProgramme stage).environment (actualRaw initialFrame sourceProgramme stage).expression
theorem derivation_effect (stage : Nat) : type_of% (SourceOperationDerivations.Derivation.sound (derivation initialFrame sourceProgramme stage)) :=
 SourceOperationDerivations.Derivation.sound (derivation initialFrame sourceProgramme stage)
abbrev wordFibre (stage : Nat) := SourceOperationLogic.fibreDecomposition
 (SourceOperationScalarRelations.evaluation (R:=ℤ) (s:=Slot.orbit) (actualRaw initialFrame sourceProgramme stage).environment)
theorem complete_word (stage : Nat)
 (word : SourceOperationScalarRelations.Formal ℤ Value.{u} Var.{u} Slot.orbit) :
 (wordFibre initialFrame sourceProgramme stage).symm (wordFibre initialFrame sourceProgramme stage word)=word :=
 (wordFibre initialFrame sourceProgramme stage).symm_apply_apply word
abbrev field (stage : Nat) := SourceOperationInquiry.Context.Faces.Cofinal.Carrier (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) stage
abbrev topology (stage : Nat) := CofinalAllPrimeTopology.allStageSourceUniformity (L:=field initialFrame sourceProgramme stage)
abbrev allPrime (stage : Nat) := CofinalAllPrimeTopology.allPrimeMap (L:=field initialFrame sourceProgramme stage)
theorem topology_residual (stage : Nat) (value : field initialFrame sourceProgramme stage) :
 @Inseparable (field initialFrame sourceProgramme stage) (topology initialFrame sourceProgramme stage).toTopologicalSpace value 0 ↔
 value ∈ LinearMap.ker (allPrime initialFrame sourceProgramme stage) :=
 CofinalAllPrimeTopology.source_inseparable_zero_iff_kernel value

abbrev actualFaces (stage : Nat) := (
 SourceOperationInquiry.Context.Faces.actualMorphism (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage),
 SourceOperationInquiry.Context.Faces.Cofinal.relationField (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme) stage,
 SourceOperationInquiry.Context.Faces.Reverse.reverse (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage),
 SourceOperationInquiry.Context.Faces.Execution.initialRuntime (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)
  (SourceOperationInquiry.Context.Faces.Reverse.nextWord (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
   ((contentRuntime initialFrame sourceProgramme).stateAt stage)))

theorem reverse_execution (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.source_execution (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_execution _ _ _
theorem reverse_pair (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.reverse_pair (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.reverse_pair _ _ _
theorem reverse_whole (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.source_write (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_write _ _ _
theorem reverse_cost (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.source_trace (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_trace _ _ _
theorem reverse_occurrence (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.source_original (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_original _ _ _
theorem reverse_next (stage : Nat) : type_of%
 (SourceOperationInquiry.Context.Faces.Reverse.source_next (contentRuntime initialFrame sourceProgramme) (rawSource initialFrame sourceProgramme)
  ((contentRuntime initialFrame sourceProgramme).stateAt stage)) :=
 SourceOperationInquiry.Context.Faces.Reverse.source_next _ _ _
abbrev withActualFaces := (contentRuntime initialFrame sourceProgramme,rawSource initialFrame sourceProgramme,actualFaces initialFrame sourceProgramme,
 fun stage => (exactComplex initialFrame sourceProgramme stage,cochain initialFrame sourceProgramme stage,derivation initialFrame sourceProgramme stage,wordFibre initialFrame sourceProgramme stage,
 topology initialFrame sourceProgramme stage,allPrime initialFrame sourceProgramme stage))
end Configured

variable (initialFrame : Frame.{u})
abbrev contentRuntime := Configured.contentRuntime initialFrame configuration
abbrev rawSource := Configured.rawSource initialFrame configuration
abbrev raw_actual := Configured.raw_actual initialFrame configuration
abbrev environment_actual := Configured.environment_actual initialFrame configuration
abbrev increment_actual := Configured.increment_actual initialFrame configuration
abbrev update_inventory := Configured.update_inventory initialFrame configuration
abbrev generated_equation := Configured.generated_equation initialFrame configuration
abbrev actual_operation := Configured.actual_operation initialFrame configuration
abbrev cofinal_relation := Configured.cofinal_relation initialFrame configuration
abbrev cofinal_fibre := Configured.cofinal_fibre initialFrame configuration
abbrev cofinal_word_readback := Configured.cofinal_word_readback initialFrame configuration
abbrev cofinal_next := Configured.cofinal_next initialFrame configuration
abbrev actualRaw := Configured.actualRaw initialFrame configuration
abbrev exactComplex := Configured.exactComplex initialFrame configuration
abbrev exact_complex := Configured.exact_complex initialFrame configuration
abbrev cochain := Configured.cochain initialFrame configuration
abbrev cochain_zero := Configured.cochain_zero initialFrame configuration
abbrev derivation := Configured.derivation initialFrame configuration
abbrev derivation_effect := Configured.derivation_effect initialFrame configuration
abbrev wordFibre := Configured.wordFibre initialFrame configuration
abbrev complete_word := Configured.complete_word initialFrame configuration
abbrev field := Configured.field initialFrame configuration
abbrev topology := Configured.topology initialFrame configuration
abbrev allPrime := Configured.allPrime initialFrame configuration
abbrev topology_residual := Configured.topology_residual initialFrame configuration
abbrev actualFaces := Configured.actualFaces initialFrame configuration
abbrev reverse_execution := Configured.reverse_execution initialFrame configuration
abbrev reverse_pair := Configured.reverse_pair initialFrame configuration
abbrev reverse_whole := Configured.reverse_whole initialFrame configuration
abbrev reverse_cost := Configured.reverse_cost initialFrame configuration
abbrev reverse_occurrence := Configured.reverse_occurrence initialFrame configuration
abbrev reverse_next := Configured.reverse_next initialFrame configuration
abbrev withActualFaces := Configured.withActualFaces initialFrame configuration
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceContentEnvironment
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
