import H0mework.Versions.PR.Realization.Operations.Inquiry.Context.Syntax.Source
import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Execution.Consumer

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Syntax
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {Sorts : Type u} {PhysicalValue PhysicalVar : Sorts → Type u}
 [∀ target, AddCommGroup (PhysicalValue target)] {sort : Sorts}
variable (source : RawSource (PhysicalValue:=PhysicalValue) (PhysicalVar:=PhysicalVar) (sort:=sort) runtime)
variable (state : runtime.State)

-- The existing executor pays every coefficient and primitive in the syntax delta.
def deltaExecution := Faces.Execution.initialRuntime runtime source state (deltaWord runtime source state)
def deltaPair := Faces.Execution.value runtime source state (deltaWord runtime source state)
theorem delta_pair : deltaPair runtime source state =
 Faces.pairInventory runtime source state (deltaWord runtime source state) :=
 Faces.Execution.value_pair _ _ _ _
theorem delta_addition : (deltaPair runtime source state).1 + (deltaPair runtime source state).2 =
 deltaValue runtime source state := by
 rw [delta_pair]
 change evaluation (R:=ℤ) (readEnv runtime source state) (deltaWord runtime source state) +
  effectEvaluator (R:=ℤ) (readEnv runtime source state) (increment runtime source state)
   (deltaWord runtime source state) = _
 have square := LinearMap.congr_fun (evaluation_update (R:=ℤ)
  (readEnv runtime source state) (increment runtime source state)) (deltaWord runtime source state)
 rw [updated_environment] at square
 exact square.symm

theorem delta_whole : type_of% (Faces.Execution.actual_whole runtime source state
 (deltaWord runtime source state)) := Faces.Execution.actual_whole _ _ _ _
theorem delta_trace : type_of% (Faces.Execution.trace_cost runtime source state
 (deltaWord runtime source state)) := Faces.Execution.trace_cost _ _ _ _
theorem delta_original : type_of% (Faces.Execution.original_occurrence runtime source state
 (deltaWord runtime source state)) := Faces.Execution.original_occurrence _ _ _ _
theorem delta_next : type_of% (Faces.Execution.actual_tick runtime source state
 (deltaWord runtime source state)) := Faces.Execution.actual_tick _ _ _ _

end SourceOperationInquiry.Context.Syntax
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
