import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Inventory
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
local instance registeredGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var) (N : ℕ)

abbrev actualPhysicalStockHistory := ActualNativeRelationTransport.bornHistory
 (physicalStockSelected factory grade data sourceCfg language N)
 (physicalStockEmitter factory grade data sourceCfg language N)

/-- The already generated tail Trace carries the same actual selected occurrence tag. -/
def actualTailSourceOccurrence :=
 (SourceOperationPaidRelations.exposure
  (physicalSourceTrace factory grade data sourceCfg language (physicalTailCode N)
   (physicalStockSelected factory grade data sourceCfg language N))).map
   (fun event => (S.actualOccurrence (physicalStockSelected factory grade data sourceCfg language N),event))

private theorem tail_trace_inventory_preserved (event)
 (present : event ∈ (SourceOperationPaidRelations.exposure
  (physicalSourceTrace factory grade data sourceCfg language (physicalTailCode N)
   (physicalStockSelected factory grade data sourceCfg language N))).trace) :
 event ∈ (actualPhysicalBornStock factory grade data sourceCfg language N).trace := by
 apply physical_source_trace_is_in_actual_born factory grade data sourceCfg language N event
 unfold physicalSourceInventory
 exact (SourceHistoryCommon.parallel_right _ _ _).1 event
  ((SourceHistoryCommon.parallel_right _ _ _).1 event
   ((SourceHistoryCommon.parallel_left _ _ _).1 event present))

/-- The full tail equation is registered in the exact born cochain history, not merely held beside the root as an evaluated field. -/
theorem actual_tail_boundary_in_born_history :
 SourceOperationScalarPresentation.relationMap (R:=ℤ)
  (physicalSourceRaw factory grade data sourceCfg language (physicalTailCode N)
    (physicalStockSelected factory grade data sourceCfg language N)).environment
  ((physicalSourceTrace factory grade data sourceCfg language (physicalTailCode N)
    (physicalStockSelected factory grade data sourceCfg language N)).relationWords (R:=ℤ)) ∈
 (actualPhysicalStockHistory factory grade data sourceCfg language N).relationClosure := by
 have source := SourceOperationPaidRelations.boundary_in_inventory
   (actualTailSourceOccurrence factory grade data sourceCfg language N)
   (physicalSourceTrace factory grade data sourceCfg language (physicalTailCode N)
    (physicalStockSelected factory grade data sourceCfg language N))
 have preserved : (SourceOperationPaidRelations.prefixHistory
     (actualTailSourceOccurrence factory grade data sourceCfg language N)
     (SourceOperationPaidRelations.exposure
       (physicalSourceTrace factory grade data sourceCfg language (physicalTailCode N)
         (physicalStockSelected factory grade data sourceCfg language N)))).relationClosure ≤
     (actualPhysicalStockHistory factory grade data sourceCfg language N).relationClosure := by
   exact SourceOperationPaidRelations.relations_next _ _ _ _
     (tail_trace_inventory_preserved factory grade data sourceCfg language N)
 exact preserved source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
