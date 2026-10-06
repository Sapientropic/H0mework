import H0mework.Versions.AD.Realization.Operations.Inquiry.Context.Faces.Cofinal.Consumer
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationInquiry.Context.Native.Pairing
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
variable {process : SourceNativeInquiryEngineProcess.{u}}
variable (runtime : SourceNativeInquiryRuntime process)
variable {S : Type u} {Value Var : S → Type u} [∀ sort,AddCommGroup (Value sort)] {slot : S}
variable (source : RawSource (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=slot) runtime)
abbrev Words := Formal ℤ Value Var slot

def paired : Words (Value:=Value) (Var:=Var) (slot:=slot) →ₗ[ℤ]
 (SourceOperationInquiry.Carrier runtime →ₗ[ℤ] PairValue Value slot) :=
 (Finsupp.linearCombination ℤ (fun state : runtime.State => Context.Faces.pairInventory runtime source state)).flip

theorem point (word : Words (Value:=Value) (Var:=Var) (slot:=slot)) (state : runtime.State) :
 paired runtime source word (SourceOperationInquiry.point runtime state)=Context.Faces.pairInventory runtime source state word := by
 change Finsupp.linearCombination ℤ (fun state : runtime.State => Context.Faces.pairInventory runtime source state)
  (Finsupp.single state 1) word=_
 rw [Finsupp.linearCombination_single,one_smul]

def fieldRead (word : Words (Value:=Value) (Var:=Var) (slot:=slot)) :
 SourceOperationInquiry.Field runtime →ₗ[ℤ] PairValue Value slot :=
 (paired runtime source word).comp (SourceOperationInquiry.word runtime)

theorem field_point (word : Words (Value:=Value) (Var:=Var) (slot:=slot)) (state : runtime.State) :
 fieldRead runtime source word (SourceOperationInquiry.fieldPoint runtime state)=Context.Faces.pairInventory runtime source state word := by
 change paired runtime source word (SourceOperationInquiry.word runtime (SourceOperationInquiry.fieldPoint runtime state))=_
 rw [SourceOperationInquiry.word_point]
 exact point runtime source word state

theorem actual_next (word : Words (Value:=Value) (Var:=Var) (slot:=slot)) (state : runtime.State) :
 fieldRead runtime source word (SourceOperationInquiry.fieldAction runtime (SourceOperationInquiry.fieldPoint runtime state))=
 paired runtime source word (SourceOperationInquiry.sourceAction runtime (SourceOperationInquiry.point runtime state)) := by
 rw [SourceOperationInquiry.field_action,SourceOperationInquiry.point_action]
 exact (field_point runtime source word state.tick.nextState).trans (point runtime source word state.tick.nextState).symm

theorem cofinal_read (word : Words (Value:=Value) (Var:=Var) (slot:=slot)) (offset bound : Nat) (index : Fin (bound+1)) :
 Context.Faces.Cofinal.read runtime source offset bound (Context.Faces.Cofinal.sourceMap runtime source offset word) index=
 fieldRead runtime source word (SourceOperationInquiry.fieldPoint runtime (runtime.stateAt (offset+index.val))) :=
 (Context.Faces.Cofinal.read_source runtime source offset bound word index).trans
 (field_point runtime source word (runtime.stateAt (offset+index.val))).symm
end SourceOperationInquiry.Context.Native.Pairing
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
