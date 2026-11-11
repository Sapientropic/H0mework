import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Admission
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Occurrence

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.FeedGeneratorOccurrence
open SourceOperationEffects SourceOperationExecution CofinalHistorySettlement
open ActualNativeRelationTransport
variable {S : Type u} {V X : S → Type u} [∀ t,AddCommGroup (V t)] {s : S}

/-- The prefix is traversed literally, so repeated requests retain different locations. -/
private def executionBlock (environment : Env V X) :
 (before : List (Request (V:=V) (X:=X) (s:=s))) →
 (request : Request (V:=V) (X:=X) (s:=s)) →
 (after : List (Request (V:=V) (X:=X) (s:=s))) →
 OccurrenceBlock [PresentedRelationEventAt.generator request.expression]
  (RootedAccountedUnfolding.traceBranches (executionBranches environment (before++request::after)))
 | [],request,after => by
  refine ⟨[],RootedAccountedUnfolding.traceBranches
   (SourceOperationPaidRelations.events (receipt environment request))++
   RootedAccountedUnfolding.traceBranches (executionBranches environment after),?_⟩
  rfl
 | head::before,request,after => by
  rcases executionBlock environment before request after with ⟨front,back,equal⟩
  refine ⟨(SourceOperationPaidRelations.exposure (receipt environment head)).trace++front,back,?_⟩
  change (SourceOperationPaidRelations.exposure (receipt environment head)).trace++
   RootedAccountedUnfolding.traceBranches (executionBranches environment (before++request::after))=_
  rw [equal]
  simp only [List.append_assoc]

/-- Recover the generator introduced by this exact request's already generated Feed exposure. -/
def fromSplit (environment : Env V X) (source : Inventory (V:=V) (X:=X) (s:=s))
 (before : List (Request (V:=V) (X:=X) (s:=s)))
 (request : Request (V:=V) (X:=X) (s:=s))
 (after : List (Request (V:=V) (X:=X) (s:=s)))
 (split : requests source=before++request::after) :
 AdmissionReceipt.GeneratorOccurrence (written environment source) := by
 rcases executionBlock environment before request after with ⟨front,back,equal⟩
 refine ⟨source.trace++front,request.expression,back,?_⟩
 rw [written_trace,split,equal]
 simp only [List.append_assoc,List.singleton_append]

@[simp] theorem fromSplit_expression (environment : Env V X)
 (source : Inventory (V:=V) (X:=X) (s:=s))
 (before : List (Request (V:=V) (X:=X) (s:=s)))
 (request : Request (V:=V) (X:=X) (s:=s))
 (after : List (Request (V:=V) (X:=X) (s:=s)))
 (split : requests source=before++request::after) :
 (fromSplit environment source before request after split).expression=request.expression := rfl

private theorem requestsFrom_append (position : Nat)
 (before after : List (Event (V:=V) (X:=X) (s:=s))) :
 requestsFrom position (before++after)=requestsFrom position before++
  requestsFrom (position+before.length) after := by
 induction before generalizing position with
 | nil => simp only [List.nil_append,requestsFrom,List.length_nil,Nat.add_zero]
 | cons head tail previous =>
  simp only [List.cons_append,requestsFrom,List.length_cons]
  rw [previous]
  have ordered : position+(tail.length+1)=(position+1)+tail.length := by omega
  rw [ordered]
  exact (List.append_assoc _ _ _).symm

/-- The source event fixes the request's position; only its finite support list is indexed. -/
private def sourceRequestSplit
 (source : Inventory (V:=V) (X:=X) (s:=s))
 (occurrence : WordReceipt.RelationOccurrence source)
 (item : {entry : Expr V X s × ℤ // entry∈Coefficients.sourceItems occurrence.word}) :
 Σ before : List (Request (V:=V) (X:=X) (s:=s)),
 {after : List (Request (V:=V) (X:=X) (s:=s)) //
  requests source=before++WordReceipt.sourceRequest occurrence item.val::after} := by
 classical
 let entries:=Coefficients.sourceItems occurrence.word
 let offset:=entries.idxOf item.val
 have bounded : offset<entries.length:=List.idxOf_lt_length_iff.mpr item.property
 have actual : entries[offset]'bounded=item.val:=List.getElem_idxOf bounded
 have splitItems : entries=entries.take offset++item.val::entries.drop (offset+1) := by
  have full := List.take_append_drop (offset+1) entries
  rw [List.take_succ_eq_append_getElem bounded,actual] at full
  simpa only [List.append_assoc,List.singleton_append] using full.symm
 let makeRequest := fun entry : Expr V X s × ℤ =>
  (⟨occurrence.before.length,.relation occurrence.word,entry.1,entry.2⟩ : Request (V:=V) (X:=X) (s:=s))
 refine ⟨requestsFrom 0 occurrence.before++(entries.take offset).map makeRequest,
  (entries.drop (offset+1)).map makeRequest++requestsFrom (occurrence.before.length+1) occurrence.after,?_⟩
 unfold requests
 rw [occurrence.trace_eq,requestsFrom_append]
 simp only [Nat.zero_add,requestsFrom,eventItems]
 change requestsFrom 0 occurrence.before++
   ((entries.map makeRequest)++requestsFrom (occurrence.before.length+1) occurrence.after)=_
 have mapped := congrArg (List.map makeRequest) splitItems
 rw [List.map_append,List.map_cons] at mapped
 rw [mapped]
 simp only [WordReceipt.sourceRequest,makeRequest,List.append_assoc,List.cons_append]

/-- The given source relation occurrence and its support item select their own Feed generator. -/
def fromRelationItem (environment : Env V X)
 (source : Inventory (V:=V) (X:=X) (s:=s))
 (occurrence : WordReceipt.RelationOccurrence source)
 (item : {entry : Expr V X s × ℤ // entry∈Coefficients.sourceItems occurrence.word}) :
 AdmissionReceipt.GeneratorOccurrence (written environment source) :=
 let located:=sourceRequestSplit source occurrence item
 fromSplit environment source located.1 (WordReceipt.sourceRequest occurrence item.val)
  located.2.1 located.2.2

@[simp] theorem fromRelationItem_expression (environment : Env V X)
 (source : Inventory (V:=V) (X:=X) (s:=s))
 (occurrence : WordReceipt.RelationOccurrence source)
 (item : {entry : Expr V X s × ℤ // entry∈Coefficients.sourceItems occurrence.word}) :
 (fromRelationItem environment source occurrence item).expression=item.val.1 := rfl

end SourceInventoryExecutionFeed.FeedGeneratorOccurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
