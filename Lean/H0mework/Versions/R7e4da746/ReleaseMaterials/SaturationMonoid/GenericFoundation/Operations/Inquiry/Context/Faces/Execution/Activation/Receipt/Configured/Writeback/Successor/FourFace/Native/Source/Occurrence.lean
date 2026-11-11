import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Words
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualNativeRelationTransport
open SourceOperationEffects SourceOperationExecution CofinalHistorySettlement

/-- A generated slice location, retained as data rather than selected from a membership proposition. -/
structure OccurrenceBlock {A : Type u} (chunk target : List A) where
 before : List A
 after : List A
 trace_eq : target=before++chunk++after

private def seed_block_left {A : Type u} (first second : RootedAccountedUnfolding A)
 (chunk : List A) (present : OccurrenceBlock chunk first.trace) :
 OccurrenceBlock chunk (SourceHistoryCommon.seed first second).trace := by
 rcases present with ⟨front,back,equal⟩
 refine ⟨first.root::front,back++second.trace,?_⟩
 change first.root::(first.trace++(second.trace++[]))=_
 rw [equal]
 simp only [List.append_nil,List.cons_append,List.append_assoc]

private def seed_block_right {A : Type u} (first second : RootedAccountedUnfolding A)
 (chunk : List A) (present : OccurrenceBlock chunk second.trace) :
 OccurrenceBlock chunk (SourceHistoryCommon.seed first second).trace := by
 rcases present with ⟨front,back,equal⟩
 refine ⟨first.root::(first.trace++front),back,?_⟩
 change first.root::(first.trace++(second.trace++[]))=_
 rw [equal]
 simp only [List.append_nil,List.cons_append,List.append_assoc]

private def preserve_block_right {A : Type u} (prior : Option (RootedAccountedUnfolding A))
 (generated : RootedAccountedUnfolding A) (chunk : List A)
 (present : OccurrenceBlock chunk generated.trace) :
 OccurrenceBlock chunk (T.preserve prior generated).trace := by
 cases prior with
 | none => exact present
 | some carried => exact seed_block_right carried generated chunk present

variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target,AddCommGroup (Value target)] {sort : Sorts}
variable (frame : A.M.Frame (Value:=Value) (Var:=Var) (sort:=sort))
variable (base : A.Programme (PhysicalValue:=Value) (PhysicalVar:=Var) (sort:=sort))

private def paid_block_generated : OccurrenceBlock (P.exposure (paid frame).state.2).trace
 (AS.generatedStock frame).trace := by
 let seed:=RootedAccountedUnfolding.zero (PresentedRelationEventAt.generator frame.registered.input.expression)
 let within : OccurrenceBlock (P.exposure (paid frame).state.2).trace
   (IP.updatedSeed seed (A.epoch frame) (S.actualOccurrence frame)).trace :=
  seed_block_right _ _ _ ⟨[],[],by simp only [List.nil_append,List.append_nil]; rfl⟩
 unfold AS.generatedStock
 change OccurrenceBlock (P.exposure (paid frame).state.2).trace
  (IP.relationWrite seed (A.epoch frame) (S.actualOccurrence frame)
   (IP.disposition seed (A.epoch frame) (S.actualOccurrence frame))).trace
 unfold IP.relationWrite
 cases IP.disposition seed (A.epoch frame) (S.actualOccurrence frame) with
 | faithful _ _ _ => exact within
 | unsound _ _ => exact within
 | kernelResidual _ _ _ => exact seed_block_left _ _ _ within
 | coverageResidual _ _ _ => exact within

/-- The literal paid exposure's location is produced before the new source executions. -/
def paid_block_source : OccurrenceBlock (P.exposure (paid frame).state.2).trace
 (AS.stockScalar frame base).trace :=
 preserve_block_right _ _ _ (preserve_block_right _ _ _ (paid_block_generated frame))

/-- Appending the Feed retains that same location, including duplicate Steps. -/
def paid_block_born : OccurrenceBlock (P.exposure (paid frame).state.2).trace
 (bornStock frame base).trace := by
 rcases paid_block_source frame base with ⟨front,back,equal⟩
 refine ⟨front,back++RootedAccountedUnfolding.traceBranches
  (SourceInventoryExecutionFeed.executionBranches (AS.stockDecodedEnvironment frame base)
   (SourceInventoryExecutionFeed.requests (AS.stockScalar frame base))),?_⟩
 rw [bornStock,SourceInventoryExecutionFeed.written_trace,equal]
 simp only [List.append_assoc]

/-- The ordered source-paid Step list has a generated contiguous occurrence embedding. -/
def paid_steps_born : OccurrenceBlock
 (PresentedRelationEventAt.generator (paid frame).raw::
  (SourceOperationPaidRelations.words (paid frame).state.2).map PresentedRelationEventAt.relation)
 (bornStock frame base).trace := by
 rcases paid_block_born frame base with ⟨front,back,equal⟩
 refine ⟨front,back,?_⟩
 have expanded : (P.exposure (paid frame).state.2).trace=
   PresentedRelationEventAt.generator (paid frame).raw::
    (SourceOperationPaidRelations.words (paid frame).state.2).map PresentedRelationEventAt.relation := by
  change PresentedRelationEventAt.generator (paid frame).raw::
   RootedAccountedUnfolding.traceBranches (SourceOperationPaidRelations.events (paid frame).state.2) = _
  rw [SourceOperationPaidRelations.events_trace]
 rw [←expanded]
 exact equal

/-- The Feed input retains the ordered Step block before appending any executions. -/
def paid_steps_source : OccurrenceBlock
 (PresentedRelationEventAt.generator (paid frame).raw::
  (SourceOperationPaidRelations.words (paid frame).state.2).map PresentedRelationEventAt.relation)
 (AS.stockScalar frame base).trace := by
 rcases paid_block_source frame base with ⟨front,back,equal⟩
 refine ⟨front,back,?_⟩
 have expanded : (P.exposure (paid frame).state.2).trace=
   PresentedRelationEventAt.generator (paid frame).raw::
    (SourceOperationPaidRelations.words (paid frame).state.2).map PresentedRelationEventAt.relation := by
  change PresentedRelationEventAt.generator (paid frame).raw::
   RootedAccountedUnfolding.traceBranches (SourceOperationPaidRelations.events (paid frame).state.2) = _
  rw [SourceOperationPaidRelations.events_trace]
 rw [←expanded]
 exact equal

/-- This location belongs to the original Feed input, so its receipt is already generated. -/
def paid_step_source_occurrence
 (index : Fin (SourceOperationPaidRelations.words (paid frame).state.2).length) :
 SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence (AS.stockScalar frame base) := by
 let words:=SourceOperationPaidRelations.words (paid frame).state.2
 let block:=paid_steps_source frame base
 refine ⟨block.before++PresentedRelationEventAt.generator (paid frame).raw::
   (words.take index.val).map PresentedRelationEventAt.relation,
  words.get index,(words.drop (index.val+1)).map PresentedRelationEventAt.relation++block.after,?_⟩
 have split : words=words.take index.val++words.get index::words.drop (index.val+1) := by
  change words=words.take index.val++words[index.val]::words.drop (index.val+1)
  rw [List.getElem_cons_drop index.isLt,List.take_append_drop]
 have mapped : words.map PresentedRelationEventAt.relation=
   (words.take index.val).map PresentedRelationEventAt.relation++
    PresentedRelationEventAt.relation (words.get index)::
     (words.drop (index.val+1)).map PresentedRelationEventAt.relation := by
  simpa only [List.map_append,List.map_cons] using congrArg (List.map PresentedRelationEventAt.relation) split
 exact block.trace_eq.trans
  ((congrArg (fun tail=>block.before++(PresentedRelationEventAt.generator (paid frame).raw::tail)++block.after)
   mapped).trans (by simp only [List.cons_append,List.append_assoc]))


/-- This particular Step is located by the generated block and its original Fin index. -/
def paid_step_occurrence
 (index : Fin (SourceOperationPaidRelations.words (paid frame).state.2).length) :
 SourceInventoryExecutionFeed.WordReceipt.RelationOccurrence (bornStock frame base) := by
 let words:=SourceOperationPaidRelations.words (paid frame).state.2
 let block:=paid_steps_born frame base
 refine ⟨block.before++PresentedRelationEventAt.generator (paid frame).raw::
   (words.take index.val).map PresentedRelationEventAt.relation,
  words.get index,(words.drop (index.val+1)).map PresentedRelationEventAt.relation++block.after,?_⟩
 have split : words=words.take index.val++words.get index::words.drop (index.val+1) := by
  change words=words.take index.val++words[index.val]::words.drop (index.val+1)
  rw [List.getElem_cons_drop index.isLt,List.take_append_drop]
 have mapped : words.map PresentedRelationEventAt.relation=
   (words.take index.val).map PresentedRelationEventAt.relation++
    PresentedRelationEventAt.relation (words.get index)::
     (words.drop (index.val+1)).map PresentedRelationEventAt.relation := by
  simpa only [List.map_append,List.map_cons] using congrArg (List.map PresentedRelationEventAt.relation) split
 exact block.trace_eq.trans
  ((congrArg (fun tail=>block.before++(PresentedRelationEventAt.generator (paid frame).raw::tail)++block.after)
   mapped).trans (by simp only [List.cons_append,List.append_assoc]))

theorem paid_step_word
 (index : Fin (SourceOperationPaidRelations.words (paid frame).state.2).length) :
 (paid_step_occurrence frame base index).word=
  (SourceOperationPaidRelations.words (paid frame).state.2).get index := rfl

theorem paid_step_before_length
 (index : Fin (SourceOperationPaidRelations.words (paid frame).state.2).length) :
 (paid_step_occurrence frame base index).before.length=
  (paid_steps_born frame base).before.length+1+index.val := by
 change ((paid_steps_born frame base).before++PresentedRelationEventAt.generator (paid frame).raw::
   ((SourceOperationPaidRelations.words (paid frame).state.2).take index.val).map
    PresentedRelationEventAt.relation).length=_
 simp only [List.length_append,List.length_cons,List.length_map,List.length_take]
 rw [Nat.min_eq_left (Nat.le_of_lt index.isLt)]
 omega

/-- Equal word syntax at two paid Steps still produces two distinct, ordered occurrence positions. -/
theorem paid_step_positions_strict : StrictMono (fun index :
 Fin (SourceOperationPaidRelations.words (paid frame).state.2).length=>
 (paid_step_occurrence frame base index).before.length) := by
 intro first second ordered
 change (paid_step_occurrence frame base first).before.length<
  (paid_step_occurrence frame base second).before.length
 rw [paid_step_before_length frame base first,paid_step_before_length frame base second]
 exact Nat.add_lt_add_left (show first.val<second.val from ordered) _

end ActualNativeRelationTransport
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
