import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Cut
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Partition
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block

set_option autoImplicit false
set_option Elab.async false
noncomputable section
universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.ReceiptOccurrence
open SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations CofinalHistorySettlement
open ActualNativeRelationTransport (OccurrenceBlock)
open OrderedTracePartition (locatePart)
open private executedTrace_append from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Receipt.Block

namespace P
export SourceOperationPaidRelations (exposure ReadStep readStep)
end P

variable {S : Type u} {V X : S → Type u} [∀ t, AddCommGroup (V t)] {s : S}
variable (decoder : Env V X) (requests : List (Request (V := V) (X := X) (s := s)))

private theorem executedTrace_single (request : Request (V := V) (X := X) (s := s)) :
    executedTrace decoder [request] = (P.exposure (receipt decoder request)).trace := by
  change (P.exposure (receipt decoder request)).trace ++ [] = _
  exact List.append_nil _

/-- A relation read selects its original request and paid Step by position. -/
structure ExecutedAtStep (position : Nat) (word : Formal ℤ V X s) where
  requestIndex : Fin requests.length
  localIndex : Nat
  selected : P.ReadStep (receipt decoder (requests.get requestIndex)) localIndex word
  offset_eq : position = (executedTrace decoder (requests.take requestIndex.val)).length + localIndex

def readExecutedStep (position : Nat) (word : Formal ℤ V X s)
    (actual : (executedTrace decoder requests)[position]? = some (.relation word)) :
    ExecutedAtStep decoder requests position word := by
  let preceding := fun n => executedTrace decoder (requests.take n)
  let parts := fun (n : Nat) => executedTrace decoder (requests[n]?).toList
  have advance (n : Nat) : preceding (n+1) = preceding n ++ parts n := by
    change executedTrace decoder (requests.take (n+1)) = _
    rw [List.take_add_one, executedTrace_append]
  have complete : preceding requests.length = executedTrace decoder requests :=
    congrArg (executedTrace decoder) List.take_length
  have present : position < (executedTrace decoder requests).length :=
    (List.getElem?_eq_some_iff.mp actual).elim (fun inside _ => inside)
  let atRequest := locatePart parts preceding rfl advance requests.length position (complete.symm ▸ present)
  have atWord : (parts atRequest.block.val)[atRequest.localIndex.val]? = some (.relation word) :=
    atRequest.read.symm.trans ((congrArg (fun events : List (Event (V := V) (X := X) (s := s)) =>
      events[position]?) complete).trans actual)
  have chunk : parts atRequest.block.val =
      (P.exposure (receipt decoder (requests.get atRequest.block))).trace := by
    change executedTrace decoder (requests[atRequest.block.val]?).toList = _
    rw [List.getElem?_eq_getElem atRequest.block.isLt]
    exact executedTrace_single decoder _
  exact ⟨atRequest.block, atRequest.localIndex.val,
    P.readStep (receipt decoder (requests.get atRequest.block)) atRequest.localIndex.val word
      ((congrArg (fun events : List (Event (V := V) (X := X) (s := s)) =>
        events[atRequest.localIndex.val]?) chunk).symm.trans atWord),
    atRequest.offset_eq⟩

variable {stock : Inventory (V := V) (X := X) (s := s)}
variable (whole : OccurrenceBlock (executedTrace decoder requests) stock.trace)

/-- The addressed request retains its full original execution segment in the same stock. -/
def executionSegmentAt (index : Fin requests.length) :
    SourceInventoryTraceSegment (P.exposure (receipt decoder (requests.get index))) stock := by
  let front := executedTrace decoder (requests.take index.val)
  let back := executedTrace decoder (requests.drop (index.val+1))
  let chunk := (P.exposure (receipt decoder (requests.get index))).trace
  have split : requests = requests.take index.val ++ [requests.get index] ++
      requests.drop (index.val+1) := by
    rw [List.append_assoc]
    exact (List.take_append_drop index.val requests).symm.trans
      (congrArg (requests.take index.val ++ ·) (List.drop_eq_getElem_cons index.isLt))
  have exactTrace : executedTrace decoder requests = front ++ chunk ++ back := by
    exact (congrArg (executedTrace decoder) split).trans (by
      simp only [executedTrace_append, executedTrace_single, front, back, chunk])
  refine ⟨whole.before ++ front, back ++ whole.after, whole.trace_eq.trans ?_⟩
  exact (congrArg (fun events => whole.before ++ events ++ whole.after) exactTrace).trans
    (by simp only [List.append_assoc, chunk])

theorem executionSegmentAt_before (index : Fin requests.length) :
    (executionSegmentAt decoder requests whole index).before.length =
      whole.before.length + (executedTrace decoder (requests.take index.val)).length :=
  List.length_append

end SourceInventoryExecutionFeed.ReceiptOccurrence
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
