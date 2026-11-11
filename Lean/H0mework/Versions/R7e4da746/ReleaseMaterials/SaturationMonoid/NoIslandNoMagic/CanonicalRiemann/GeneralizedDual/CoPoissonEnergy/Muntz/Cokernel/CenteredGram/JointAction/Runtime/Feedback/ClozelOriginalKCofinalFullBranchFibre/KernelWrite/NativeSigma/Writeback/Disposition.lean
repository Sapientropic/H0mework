import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Next
export BornInstalledJoint.MacroNext (actual_written_native_seed)
end Next
namespace Inventory
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme
 (priorSeed updatedSeed supplied_seed_preserved)
end Inventory
namespace BornStock
export ActualNativeRelationTransport (bornStock born_stock paid_in_born)
end BornStock
namespace Written
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (history completeWrittenInventory complete_written_preserves)
end Written
namespace Lift
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual
 (liftEvent liftedInventory priorPairInventory pairInventory)
end Lift
namespace StockMap
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock
 (mapped_trace)
end StockMap
namespace Relations
export SourceOperationPaidRelations (words exposure events_trace paid_boundary)
end Relations

section InventoryTransport
variable {V X : Unit → Type} [∀ target,AddCommGroup (V target)]
variable (seed : RootedAccountedUnfolding (PresentedRelationEventAt (Expr V X ())))
variable (frame : A.M.Frame (Value:=V) (Var:=X) (sort:=()))

private theorem updated_pair_event (event)
 (belongs : event∈(Inventory.updatedSeed seed (A.epoch frame) (S.actualOccurrence frame)).trace) :
 Lift.liftEvent event∈(Lift.pairInventory seed (A.epoch frame) (S.actualOccurrence frame)).trace := by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 have lifted : Lift.liftEvent event∈(Lift.liftedInventory seed (A.epoch frame) (S.actualOccurrence frame)).trace := by
  rw [Lift.liftedInventory,StockMap.mapped_trace]
  exact List.mem_map.mpr ⟨event,belongs,rfl⟩
 unfold Lift.priorPairInventory
 cases (A.epoch frame).pairInventory with
 | none => exact lifted
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 _ lifted

private theorem frame_inventory_event (stock)
 (source : frame.inventory=some stock) (event) (belongs : event∈stock.trace) :
 event∈(Inventory.updatedSeed seed (A.epoch frame) (S.actualOccurrence frame)).trace := by
 apply (SourceHistoryCommon.parallel_left _ _ _).1
 unfold Inventory.priorSeed
 rw [show (A.epoch frame).inventory=some stock from source]
 exact (SourceHistoryCommon.parallel_right _ _ _).1 _ belongs

private theorem word_event {environment : Env V X} {before after : Expr V X ()}
 (trace : Trace environment before after) (word) (member : word∈Relations.words trace) :
 PresentedRelationEventAt.relation word∈(Relations.exposure trace).trace := by
 change PresentedRelationEventAt.relation word∈PresentedRelationEventAt.generator before ::
  RootedAccountedUnfolding.traceBranches (SourceOperationPaidRelations.events trace)
 apply List.mem_cons_of_mem
 rw [Relations.events_trace]
 exact List.mem_map.mpr ⟨word,member,rfl⟩

end InventoryTransport

local instance dispositionGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

abbrev nativeTrace (native : NativePacket) := (AN.paid (receiptSelected native)).state.2

private theorem native_word_born_written (native : NativePacket) (word)
 (member : word∈Relations.words (nativeTrace native)) :
 PresentedRelationEventAt.relation (liftMap (R:=ℤ) (bornWord native word))∈
 (Written.completeWrittenInventory native.2.1.2
  (A.epoch (AS.bornAfterNative native).2.1.1)
  (S.actualOccurrence (AS.bornAfterNative native).2.1.1)).trace := by
 apply Written.complete_written_preserves
 apply updated_pair_event native.2.1.2 (AS.bornAfterNative native).2.1.1
  (PresentedRelationEventAt.relation (bornWord native word))
 apply frame_inventory_event _ _ (BornStock.bornStock (receiptSelected native) native.2.2.1)
  (BornStock.born_stock (receiptSelected native) native.2.2.1)
 apply BornStock.paid_in_born
 exact word_event (nativeTrace native) word member

private theorem seed_relation_at_native (native : NativePacket) (word)
 (member : PresentedRelationEventAt.relation word∈native.2.1.2.trace) :
 liftMap (R:=ℤ) word∈(Written.history native.2.1.2 (A.epoch native.2.1.1)
  (S.actualOccurrence native.2.1.1)).relationClosure := by
 apply (Written.history native.2.1.2 (A.epoch native.2.1.1)
  (S.actualOccurrence native.2.1.1)).relationStage_le_closure 0
 apply Submodule.subset_span
 change PresentedRelationEventAt.relation (liftMap (R:=ℤ) word)∈
  (Written.history native.2.1.2 (A.epoch native.2.1.1) (S.actualOccurrence native.2.1.1)).observedEvents 0
 simp only [RootGeneratedCofinalHistoryAt.observedEvents,List.range_succ,List.range_zero,
  List.nil_append,List.flatMap_singleton,RootGeneratedCofinalHistoryAt.observation_zero]
 exact updated_pair_event native.2.1.2 native.2.1.1 _
  (Inventory.supplied_seed_preserved native.2.1.2 native.2.1.1 _ member)

private theorem admission_relation (factory : NativeFactory) (packet : NativePacket) (word) :
 BornInstalledJoint.admissionEvent factory packet (PresentedRelationEventAt.relation word)=
 PresentedRelationEventAt.relation (admissionWord factory packet word) := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at sameVar
  cases sameVar
  rfl

def nativeHistory (native : NativePacket) :=
 Written.history native.2.1.2 (A.epoch native.2.1.1) (S.actualOccurrence native.2.1.1)

def nativeReceiptTransfer (factory : NativeFactory) (native : NativePacket) :=
 (liftMap (R:=ℤ)).comp ((admissionWord factory (AS.bornAfterNative native)).comp
  ((liftMap (R:=ℤ)).comp (bornWord native)))

private theorem next_receipt_step (factory : NativeFactory) (native : NativePacket) (word)
 (member : PresentedRelationEventAt.relation
  (admissionWord factory (AS.bornAfterNative native) (liftMap (R:=ℤ) (bornWord native word)))∈
  (AS.nativeAfterAdmission factory (AS.bornAfterNative native)).2.1.2.trace) :
 nativeReceiptTransfer factory native word∈
  (nativeHistory (AS.nativeAfterAdmission factory (AS.bornAfterNative native))).relationClosure :=
 seed_relation_at_native _ _ member

private theorem whole_receipt_relation (native next : NativePacket)
 (transfer : Formal ℤ (L.Value (PairValue C.Value) native.1) C.Var () →ₗ[ℤ]
  Formal ℤ (PairValue (L.Value (PairValue C.Value) next.1)) C.Var ())
 (steps : ∀word∈Relations.words (nativeTrace native),transfer word∈(nativeHistory next).relationClosure) :
 transfer (nativeBoundary native)∈(nativeHistory next).relationClosure := by
 have boundary := Relations.paid_boundary (nativeTrace native)
 change (Relations.words (nativeTrace native)).sum=nativeBoundary native at boundary
 have mapped : transfer (nativeBoundary native)=((Relations.words (nativeTrace native)).map transfer).sum :=
  (congrArg transfer boundary.symm).trans (map_list_sum transfer _)
 have sumIn : ∀words : List (Formal ℤ (PairValue (L.Value (PairValue C.Value) next.1)) C.Var ()),
  (∀word∈words,word∈(nativeHistory next).relationClosure)→words.sum∈(nativeHistory next).relationClosure := by
  intro words
  induction words with
  | nil => intro _; exact Submodule.zero_mem _
  | cons word tail previous =>
   intro belongs
   exact Submodule.add_mem _ (belongs word (List.mem_cons_self))
    (previous (fun entry member=>belongs entry (List.mem_cons_of_mem word member)))
 apply Eq.mpr (congrArg (fun word=>word∈(nativeHistory next).relationClosure) mapped)
 apply sumIn
 intro word member
 obtain ⟨source,sourceMember,rfl⟩:=List.mem_map.mp member
 exact steps source sourceMember

private theorem native_receipt_next_relation (factory : NativeFactory) (native : NativePacket)
 (members : ∀word∈Relations.words (nativeTrace native),
  PresentedRelationEventAt.relation
   (admissionWord factory (AS.bornAfterNative native) (liftMap (R:=ℤ) (bornWord native word)))∈
   (AS.nativeAfterAdmission factory (AS.bornAfterNative native)).2.1.2.trace) :
 nativeReceiptTransfer factory native (nativeBoundary native)∈
 (nativeHistory (AS.nativeAfterAdmission factory (AS.bornAfterNative native))).relationClosure :=
 whole_receipt_relation native (AS.nativeAfterAdmission factory (AS.bornAfterNative native))
  (nativeReceiptTransfer factory native) (fun word member=>next_receipt_step factory native word (members word member))

attribute [local irreducible] AS.localNativeReceipt

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

private theorem actual_native_word_next_seed (word)
 (member : word∈Relations.words (nativeTrace (originalNative observation nontrivial half depth ordinal))) :
 PresentedRelationEventAt.relation
  (admissionWord (D.factory observation nontrivial half) (Next.bornPacket observation nontrivial half depth ordinal)
   (liftMap (R:=ℤ) (bornWord (originalNative observation nontrivial half depth ordinal) word)))∈
 (Next.nextSeed observation nontrivial half depth ordinal).trace := by
 rw [← admission_relation]
 apply Next.actual_written_native_seed
 apply Eq.mpr (congrArg (fun stock=>PresentedRelationEventAt.relation
  (liftMap (R:=ℤ) (bornWord (originalNative observation nontrivial half depth ordinal) word))∈stock.trace)
  (BornInstalledJoint.installed_written observation nontrivial half depth ordinal))
 exact native_word_born_written (originalNative observation nontrivial half depth ordinal) word member

/-- All steps of the same native receipt, with their original total boundary, enter the actual next face. -/
theorem original_sigma_next_relation : type_of%
 (native_receipt_next_relation (D.factory observation nontrivial half)
  (originalNative observation nontrivial half depth ordinal)
  (actual_native_word_next_seed observation nontrivial half depth ordinal)) :=
 native_receipt_next_relation (D.factory observation nontrivial half)
  (originalNative observation nontrivial half depth ordinal)
  (actual_native_word_next_seed observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
