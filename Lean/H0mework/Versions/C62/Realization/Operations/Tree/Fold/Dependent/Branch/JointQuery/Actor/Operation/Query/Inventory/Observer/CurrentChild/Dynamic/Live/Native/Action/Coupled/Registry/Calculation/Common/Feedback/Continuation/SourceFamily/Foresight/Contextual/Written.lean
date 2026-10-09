import H0mework.Versions.C62.Realization.Operations.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.SourceFamily.Foresight.Contextual.Factory
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift SourceOperationScalarRelations
open SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual CofinalHistorySettlement
namespace Lower.SourceFamily.Foresight.Contextual.Written
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch)
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end Q
namespace C
export Lower.SourceFamily.Foresight.Contextual (actionWritten)
end C
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (history disposition queryRaw queryReader queryResult completeWrittenInventory complete_written_preserves)
end J
namespace P
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (pairInventory priorPairInventory liftedInventory)
end P
variable {S : Type u} {W X : S → Type u} [∀ t,AddCommGroup (W t)] {s : S}
attribute [local instance] Lower.SourceFamily.Foresight.Paid.groups
variable (binding : ∀ t,X t → Expr W X t)
variable (n : Nat) (data : Lower.SourceFamily.Packet (W:=W) (X:=X) (s:=s) n)
abbrev stock := Lower.SourceFamily.pair (factory (s:=s) binding) n data
abbrev receiver := Lower.SourceFamily.receiver (factory (s:=s) binding) n data
abbrev nextSeed := Lower.SourceFamily.nextSeed (factory (s:=s) binding) n data

theorem receiver_pair : (receiver binding n data).pairInventory=some (stock binding n data) := rfl

private theorem selected_in_extra (event)
 (fullFound : event ∈ (completeGenerated binding n data).trace) :
 event ∈ ((extraPair binding n data).getD (generated binding n data)).trace := by
 have selectedFound : event ∈ (selectedGenerated binding n data).trace :=
  original_generated_preserved binding n data event fullFound
 have carried : event ∈
  (T.preserve ((Lower.SourceFamily.Foresight.factory (s:=s) binding).extraPair n data.2 data.1)
   (selectedGenerated binding n data)).trace := by
  unfold T.preserve
  cases (Lower.SourceFamily.Foresight.factory (s:=s) binding).extraPair n data.2 data.1 with
  | none => exact selectedFound
  | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event selectedFound
 unfold extraPair
 apply (SourceHistoryCommon.parallel_right _ _ _).1 event
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event carried

private theorem extra_in_stock (event)
 (present : event ∈ ((extraPair binding n data).getD (generated binding n data)).trace) :
 event ∈ (stock binding n data).trace := by
 let carried := Lower.SourceFamily.Foresight.Contextual.Profile.FiniteSource.Indexed.ReaderResidual.ForwardDifference.pairUpdate
  binding n ⟨data.1,data.2⟩ (SourceHistoryCommon.seed
   (T.preserve ((Lower.SourceFamily.Foresight.factory (s:=s) binding).extraPair n data.2 data.1)
    (selectedGenerated binding n ⟨data.1,data.2⟩)) (actionWritten binding n ⟨data.1,data.2⟩))
 have carried_mem : event ∈ carried.trace := by
  simpa [carried, extraPair] using present
 have target : event ∈ (SourceHistoryCommon.seed carried
   (Lower.Stock.pair data.1 (Lower.SourceFamily.cfg (factory (s:=s) binding) n data.2) rfl)).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event carried_mem
 unfold stock Lower.SourceFamily.pair T.preserve
 simp only [factory]
 change event ∈ (SourceHistoryCommon.seed carried _).trace
 exact target

theorem paid_in_stock (source : Lower.SourceFamily.Foresight.Paid.Ledger.SourceEvent (W:=W) (X:=X) (s:=s) n)
 (actual : source ∈ (Lower.SourceFamily.Foresight.Contextual.sourceTree binding n data).trace)
 (event) (paid : event ∈ (Lower.SourceFamily.Foresight.Paid.Ledger.writeEvent binding n data source).trace) :
 event ∈ (stock binding n data).trace := by
 have generatedFound : event ∈ (generated binding n data).trace :=
  Paid.Ledger.run_contains _ _ source actual event paid
 have fullFound : event ∈ (completeGenerated binding n data).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 event
   ((SourceHistoryCommon.parallel_right _ _ _).1 event generatedFound)
 exact extra_in_stock binding n data event (selected_in_extra binding n data event fullFound)

theorem old_extra_in_stock (prior)
 (actual : (Lower.SourceFamily.Foresight.factory (s:=s) binding).extraPair n data.2 data.1=some prior)
 (event) (present : event ∈ prior.trace) : event ∈ (stock binding n data).trace := by
 exact extra_in_stock binding n data event (by
  unfold extraPair
  apply (SourceHistoryCommon.parallel_right _ _ _).1 event
  apply (SourceHistoryCommon.parallel_left _ _ _).1 event
  unfold T.preserve
  rw [actual]
  exact (SourceHistoryCommon.parallel_left _ _ _).1 event present)

theorem native_written_in_stock (event)
 (present : event ∈ (Reader.pairWritten binding n data.2 (Q.epoch data.1) (actualIndex n data.1)).trace) :
 T.liftEvent event ∈ (stock binding n data).trace := by
 have mapped : T.liftEvent event ∈ (nativeWritten binding n data).trace := by
  unfold nativeWritten
  rw [T.mapped_trace]
  exact List.mem_map_of_mem present
 have full : T.liftEvent event ∈ (completeGenerated binding n data).trace :=
  (SourceHistoryCommon.parallel_left _ _ _).1 _
   ((SourceHistoryCommon.parallel_left _ _ _).1 _ mapped)
 exact extra_in_stock binding n data _ (selected_in_extra binding n data _ full)

theorem psi_written_in_stock (event)
 (present : event ∈ (Psi.written binding n data.2 data.1).trace) :
 T.liftEvent event ∈ (stock binding n data).trace := by
 have full : T.liftEvent event ∈ (completeGenerated binding n data).trace :=
  Psi.append_source_event binding n data.2 data.1 _ event present
 exact extra_in_stock binding n data _ (selected_in_extra binding n data _ full)

theorem native_paid_in_stock (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure (Reader.result binding n data.2
  (Q.epoch data.1) (actualIndex n data.1)).2.1.2).trace) :
 T.liftEvent event ∈ (stock binding n data).trace :=
 native_written_in_stock binding n data event
  (Reader.complete_native_trace binding n data.2 (Q.epoch data.1) (actualIndex n data.1) event present)

theorem factory_written (event : PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s))
 (present : event ∈ (Future.Replay.Source.pairWritten (Future.Replay.Binding.at binding n)
  data.2 data.1 (Future.Replay.Installed.Q.actualOccurrence data.1)).trace) :
 T.liftEvent event ∈ (stock binding n data).trace := by
 have source := Future.Replay.Ledger.pair_written (Future.Replay.Binding.at binding n)
  data.2 data.1 event present
 have mapped : T.liftEvent event ∈
  ((Future.Replay.Installed.pairStock (Future.Replay.Binding.at binding n) data.2 data.1).map T.liftEvent).trace := by
  rw [T.mapped_trace]
  exact List.mem_map_of_mem source
 exact old_extra_in_stock binding n data _ rfl _ mapped

theorem factory_paid (event : PresentedRelationEventAt (Expr (PairValue (Lower.Value W n)) X s))
 (present : event ∈ (SourceOperationPaidRelations.exposure (Future.Replay.Source.result
  (Future.Replay.Binding.at binding n) data.2 data.1
  (Future.Replay.Installed.Q.actualOccurrence data.1)).2.1.2).trace) :
 T.liftEvent event ∈ (stock binding n data).trace :=
 factory_written binding n data event (Future.Replay.Read.paid_events
  (Future.Replay.Binding.at binding n) data.2 data.1 _ event present)

abbrev jointStock := P.pairInventory (nextSeed binding n data) (Q.epoch (receiver binding n data))
 (Q.actualOccurrence (receiver binding n data))
abbrev jointHistory := J.history (nextSeed binding n data) (Q.epoch (receiver binding n data))
 (Q.actualOccurrence (receiver binding n data))
abbrev jointIndex := actualIndex (n+1) (receiver binding n data)
abbrev jointRaw := Inquiry.rawAt binding (n+1) (nextSeed binding n data)
 (Q.epoch (receiver binding n data)) (Q.actualOccurrence (receiver binding n data))
abbrev jointDisposition := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Generated.disposition (nextSeed binding n data) (Q.epoch (receiver binding n data))
 (Q.actualOccurrence (receiver binding n data)) (jointRaw binding n data)
abbrev jointWritten := Inquiry.written binding (n+1) (nextSeed binding n data)
 (Q.epoch (receiver binding n data)) (jointIndex binding n data)
abbrev jointQuery := Inquiry.query binding (n+1) (nextSeed binding n data)
 (Q.epoch (receiver binding n data)) (jointIndex binding n data)

theorem action_written_in_stock (event)
 (present : event ∈ (C.actionWritten binding n data).trace) :
 event ∈ (stock binding n data).trace := by
 have extra : event ∈ ((extraPair binding n data).getD (generated binding n data)).trace := by
  simp only [extraPair, Option.getD_some]
  apply (SourceHistoryCommon.parallel_right _ _ _).1 event
  apply (SourceHistoryCommon.parallel_right _ _ _).1 event
  exact present
 exact extra_in_stock binding n data event extra

theorem stock_in_joint (event) (present : event ∈ (stock binding n data).trace) :
 event ∈ (jointStock binding n data).trace :=
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.Acted.Inventory.prior_pair_preserved
  (nextSeed binding n data) (receiver binding n data) (stock binding n data)
  (receiver_pair binding n data) event present

theorem paid_in_joint (source : Lower.SourceFamily.Foresight.Paid.Ledger.SourceEvent (W:=W) (X:=X) (s:=s) n)
 (actual : source ∈ (Lower.SourceFamily.Foresight.Contextual.sourceTree binding n data).trace)
 (event) (paid : event ∈ (Lower.SourceFamily.Foresight.Paid.Ledger.writeEvent binding n data source).trace) :
 event ∈ (jointStock binding n data).trace :=
 stock_in_joint binding n data event (paid_in_stock binding n data source actual event paid)

theorem paid_in_history (source : Lower.SourceFamily.Foresight.Paid.Ledger.SourceEvent (W:=W) (X:=X) (s:=s) n)
 (actual : source ∈ (Lower.SourceFamily.Foresight.Contextual.sourceTree binding n data).trace)
 (event) (paid : event ∈ (Lower.SourceFamily.Foresight.Paid.Ledger.writeEvent binding n data source).trace) :
 event ∈ ((jointHistory binding n data).observation 0).trace :=
 paid_in_joint binding n data source actual event paid

theorem paid_in_complete_written (source : Lower.SourceFamily.Foresight.Paid.Ledger.SourceEvent (W:=W) (X:=X) (s:=s) n)
 (actual : source ∈ (Lower.SourceFamily.Foresight.Contextual.sourceTree binding n data).trace)
 (event) (paid : event ∈ (Lower.SourceFamily.Foresight.Paid.Ledger.writeEvent binding n data source).trace) :
 event ∈ (jointWritten binding n data).trace :=
 Inquiry.source_complete_preserves binding (n+1) (nextSeed binding n data)
 (Q.epoch (receiver binding n data)) (jointIndex binding n data) event (paid_in_joint binding n data source actual event paid)

theorem old_extra_in_complete_written (prior)
 (actual : (Lower.SourceFamily.Foresight.factory (s:=s) binding).extraPair n data.2 data.1=some prior)
 (event) (present : event ∈ prior.trace) : event ∈ (jointWritten binding n data).trace :=
 Inquiry.source_complete_preserves binding (n+1) (nextSeed binding n data)
 (Q.epoch (receiver binding n data)) (jointIndex binding n data) event
 (stock_in_joint binding n data event (old_extra_in_stock binding n data prior actual event present))

theorem query_consumes_disposition : jointQuery binding n data =
 SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Generated.queryRaw
  (nextSeed binding n data) (Q.epoch (receiver binding n data))
  (Q.actualOccurrence (receiver binding n data)) (jointRaw binding n data) (jointDisposition binding n data) := rfl

abbrev nativeQuery :=
 (((Lower.SourceFamily.cfg (factory (s:=s) binding) (n+1) (nextSeed binding n data)).datum
  (Q.epoch (receiver binding n data))).reader (Q.actualOccurrence (receiver binding n data)))

theorem native_query_source : nativeQuery binding n data =
 Reader.raw binding (n+1) (nextSeed binding n data) (Q.epoch (receiver binding n data))
  (actualIndex (n+1) (receiver binding n data)) := rfl

theorem native_query_joint_expression : (nativeQuery binding n data).expression=
 Expr.add (Expr.add (Reader.query binding (n+1) (nextSeed binding n data)
   (Q.epoch (receiver binding n data)) (jointIndex binding n data)).expression
  (Expr.linear (-AddMonoidHom.id _) (Reader.completed binding (n+1) (nextSeed binding n data)
   (Q.epoch (receiver binding n data)) (jointIndex binding n data)).2.1.1))
  (Reader.feedbackExpression binding (n+1) (nextSeed binding n data)
   (Q.epoch (receiver binding n data)) (jointIndex binding n data)) := rfl

end Lower.SourceFamily.Foresight.Contextual.Written
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation
end
