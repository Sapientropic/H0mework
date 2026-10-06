import H0mework.Versions.AE.Realization.Operations.Inquiry.Context.Native.Pairing.Source
import H0mework.Versions.R2.Realization.Operations.Inquiry.Context.Native.Orbit.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Pairing.Orbit
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
namespace O
export SourceOperationInquiry.Context.Native.Orbit (Var binding environment binding_point binding_difference)
end O
abbrev Words := Formal ℤ Value (O.Var Var) slot
def old (state : runtime.State) := O.environment runtime source (SourceOperationInquiry.point runtime state)
def increment (state : runtime.State) := O.environment runtime source
 (SourceOperationInquiry.point runtime state.tick.nextState-SourceOperationInquiry.point runtime state)
def paired : Words (Value:=Value) (Var:=Var) (slot:=slot) →ₗ[ℤ]
 (SourceOperationInquiry.Carrier runtime →ₗ[ℤ] PairValue Value slot) :=
 (Finsupp.linearCombination ℤ (fun state : runtime.State => updateInventory (R:=ℤ) (s:=slot)
  (old runtime source state) (increment runtime source state))).flip
theorem point (word : Words (Value:=Value) (Var:=Var) (slot:=slot)) (state : runtime.State) :
 paired runtime source word (SourceOperationInquiry.point runtime state)=
 updateInventory (R:=ℤ) (old runtime source state) (increment runtime source state) word := by
 change Finsupp.linearCombination ℤ (fun state : runtime.State => updateInventory (R:=ℤ) (s:=slot)
  (old runtime source state) (increment runtime source state)) (Finsupp.single state 1) word=_
 rw [Finsupp.linearCombination_single,one_smul]
def wordAction : Words (Value:=Value) (Var:=Var) (slot:=slot) →ₗ[ℤ] Words (Value:=Value) (Var:=Var) (slot:=slot) :=
 substitution (R:=ℤ) O.binding
def statePullback : (SourceOperationInquiry.Carrier runtime →ₗ[ℤ] PairValue Value slot) →ₗ[ℤ]
 (SourceOperationInquiry.Carrier runtime →ₗ[ℤ] PairValue Value slot) where
 toFun read := read.comp (SourceOperationInquiry.sourceAction runtime)
 map_add' _ _ :=  LinearMap.add_comp _ _ _
 map_smul' _ _ :=  LinearMap.smul_comp _ _ _
theorem point_covariance (word : Words (Value:=Value) (Var:=Var) (slot:=slot)) (state : runtime.State) :
 paired runtime source (wordAction (Value:=Value) (Var:=Var) word) (SourceOperationInquiry.point runtime state)=
 paired runtime source word (SourceOperationInquiry.sourceAction runtime (SourceOperationInquiry.point runtime state)) := by
 rw [point,SourceOperationInquiry.point_action,point]
 apply Prod.ext
 · have h := LinearMap.congr_fun (evaluation_substitution (R:=ℤ) O.binding (old runtime source state)) word
   have next : (fun sort name => (O.binding sort name).eval (old runtime source state))=old runtime source state.tick.nextState :=
    O.binding_point runtime source state
   exact h.trans (congrArg (fun env => evaluation (R:=ℤ) env word) next)
 · have h := LinearMap.congr_fun (effectEvaluator_substitution (R:=ℤ) O.binding
    (old runtime source state) (increment runtime source state)) word
   have next : (fun sort name => (O.binding sort name).eval (old runtime source state))=old runtime source state.tick.nextState :=
    O.binding_point runtime source state
   have change : (fun sort name => (O.binding sort name).effect (old runtime source state) (increment runtime source state))=
    increment runtime source state.tick.nextState := O.binding_difference runtime source state
   exact h.trans (congrArg₂ (fun env delta => effectEvaluator (R:=ℤ) env delta word) next change)
end SourceOperationInquiry.Context.Native.Pairing.Orbit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
