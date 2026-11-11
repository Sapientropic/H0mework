import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.InitBorn
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFeedbackSuccessorAction.Inventory
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKExpandedDualForcingSourceAction.Action
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex BurnolPhysicalState OriginalKFullSourceRAction OriginalKMaterialExpandedDualSourceAction
namespace TraceSource
export OriginalKMaterialPhysicalStockSourceAction (physicalSourceRaw physicalSourceTrace)
end TraceSource
namespace Stock
export OriginalKMaterialPhysicalStockSourceAction.T (preserve)
end Stock
local instance initInstalledGroups (grade : Nat) (target : Unit) : AddCommGroup
 (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
private def initHasEvent {α : Type} (stock : Option (RootedAccountedUnfolding α)) (event : α) : Prop :=
 ∃ stored, stock=some stored ∧ event∈stored.trace

private theorem init_preserve_new {α : Type} (old : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : event∈next.trace) :
 initHasEvent (some (Stock.preserve old next)) event := by
 refine ⟨_,rfl,?_⟩
 cases old with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

private theorem init_preserved_new_event {α : Type} (old : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : event∈next.trace) :
 event∈(Stock.preserve old next).trace := by
 cases old with
 | none => exact present
 | some prior => exact (SourceHistoryCommon.parallel_right _ _ _).1 event present

private theorem init_preserve_prior {α : Type} (old : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : initHasEvent old event) :
 initHasEvent (some (Stock.preserve old next)) event := by
 rcases present with ⟨prior,same,member⟩
 rw [same]
 exact ⟨_,rfl,(SourceHistoryCommon.parallel_left _ _ _).1 event member⟩

private theorem init_fold_prior {α β : Type} (trace : β → RootedAccountedUnfolding α)
 (codes : List β) (old : Option (RootedAccountedUnfolding α)) (event : α) (present : initHasEvent old event) :
 initHasEvent (codes.foldl (fun prior code => some (Stock.preserve prior (trace code))) old) event := by
 induction codes generalizing old with
 | nil => exact present
 | cons code rest ih => exact ih _ (init_preserve_prior _ _ event present)

private theorem init_fold_source {α β : Type} (trace : β → RootedAccountedUnfolding α)
 (codes : List β) (old : Option (RootedAccountedUnfolding α)) (code : β) (installed : code∈codes)
 (event : α) (present : event∈(trace code).trace) :
 initHasEvent (codes.foldl (fun prior code => some (Stock.preserve prior (trace code))) old) event := by
 induction codes generalizing old with
 | nil => simp only [List.not_mem_nil] at installed
 | cons first rest ih =>
  rcases List.mem_cons.mp installed with same | later
  · subst first
    exact init_fold_prior trace rest _ event (init_preserve_new old (trace code) event present)
  · exact ih _ later

private theorem init_preserved_has_event {α : Type} (old : Option (RootedAccountedUnfolding α))
 (next : RootedAccountedUnfolding α) (event : α) (present : initHasEvent old event) :
 event∈(Stock.preserve old next).trace := by
 rcases present with ⟨prior,same,member⟩
 rw [same]
 exact (SourceHistoryCommon.parallel_left _ _ _).1 event member

variable (t : ℝ) (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

/-- Each actual initializer word, including the original full input and mean debt, occurs in the same born scalar stock. -/
theorem actual_init_scalar_nodes_in_born (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (installed : code∈sourceInitInventoryCodes t) (event)
 (present : event∈(SourceOperationPaidRelations.exposure
  (sourceInitQueryTrace factory grade data sourceCfg language code (sourceInitSelected t factory grade data sourceCfg language))).trace) :
 event∈
 ((sourceInitBorn t factory grade data sourceCfg language).inventory.get (by rfl)).trace := by
 cases sourceCfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at language
  cases language
  let cfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()) :=
   ⟨C.Var,datum,inventory,pairInventory⟩
  let selected:=sourceInitSelected t factory grade data cfg rfl
  have added:=init_fold_source
   (fun code => SourceOperationPaidRelations.exposure (sourceInitQueryTrace factory grade data cfg rfl code selected))
   (sourceInitInventoryCodes t) ((sourceSlotInitBase t factory grade data cfg rfl).nextInventory selected)
   code installed event present
  apply SourceInventoryExecutionFeed.original_preserved
  change event∈(Stock.preserve selected.inventory
   (Stock.preserve ((sourceSlotInitStockBase t factory grade data cfg rfl).nextInventory selected) _)).trace
  apply init_preserved_new_event
  exact init_preserved_has_event _ _ event added

/-- Pair words retain the original before/zero-query-increment relation and all literal initializer children. -/
theorem actual_init_pair_nodes_in_born (code : Expr (PairValue (PairValue C.Value)) C.Var ())
 (installed : code∈sourceInitInventoryCodes t) (event)
 (present : event∈(SourceOperationPaidRelations.exposure
  (sourceInitQueryPairTrace factory grade data sourceCfg language code (sourceInitSelected t factory grade data sourceCfg language))).trace) :
 event∈
 ((sourceInitBorn t factory grade data sourceCfg language).pairInventory.get (by rfl)).trace := by
 cases sourceCfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at language
  cases language
  let cfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()) :=
   ⟨C.Var,datum,inventory,pairInventory⟩
  let selected:=sourceInitSelected t factory grade data cfg rfl
  have added:=init_fold_source
   (fun code => SourceOperationPaidRelations.exposure (sourceInitQueryPairTrace factory grade data cfg rfl code selected))
   (sourceInitInventoryCodes t) ((sourceSlotInitBase t factory grade data cfg rfl).nextPairInventory selected)
   code installed event present
  change event∈(Stock.preserve selected.pairInventory
   (Stock.preserve ((sourceSlotInitStockBase t factory grade data cfg rfl).nextPairInventory selected) _)).trace
  apply init_preserved_new_event
  exact init_preserved_has_event _ _ event added
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFeedbackSuccessorAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
