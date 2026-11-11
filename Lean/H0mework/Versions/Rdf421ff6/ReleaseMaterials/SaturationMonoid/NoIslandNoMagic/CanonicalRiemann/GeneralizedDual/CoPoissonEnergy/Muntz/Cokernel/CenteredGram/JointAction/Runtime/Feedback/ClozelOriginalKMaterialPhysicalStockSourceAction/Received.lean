import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Trace
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
local instance receivedGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var) (N : ℕ)

def actualStoredPhysicalTail : D.SourceBranches :=
 CF.collapseValue grade ((physicalSourceRaw factory grade data sourceCfg language (physicalTailCode N)
    (physicalStockSelected factory grade data sourceCfg language N)).expression.eval
      (physicalSourceRaw factory grade data sourceCfg language (physicalTailCode N)
        (physicalStockSelected factory grade data sourceCfg language N)).environment)

def actualStoredPhysicalStock : D.SourceBranches :=
 CF.collapseValue grade ((physicalSourceRaw factory grade data sourceCfg language (physicalStockCode N)
    (physicalStockSelected factory grade data sourceCfg language N)).expression.eval
      (physicalSourceRaw factory grade data sourceCfg language (physicalStockCode N)
        (physicalStockSelected factory grade data sourceCfg language N)).environment)

/-- Actual registered stock and tail Trace receipts pay this projection reader; a by-value material identity is never assumed. -/
theorem actual_received_physical_stock_and_tail :
 actualStoredPhysicalStock factory grade data sourceCfg language N =
   sourceMaterialPhysicalStockAction N (actualMaterialStockSourceTotal factory grade data sourceCfg language N) ∧
 actualStoredPhysicalTail factory grade data sourceCfg language N =
   sourceMaterialPhysicalTailAction N (actualMaterialStockSourceTotal factory grade data sourceCfg language N) := by
 constructor
 · exact physical_received_inventory_trace_action factory grade data sourceCfg language N (physicalStockCode N) _
     (physicalSourceTrace factory grade data sourceCfg language (physicalStockCode N)
       (physicalStockSelected factory grade data sourceCfg language N))
 · exact physical_received_inventory_trace_action factory grade data sourceCfg language N (physicalTailCode N) _
     (physicalSourceTrace factory grade data sourceCfg language (physicalTailCode N)
       (physicalStockSelected factory grade data sourceCfg language N))

theorem actual_received_physical_projection_from_born (name : sourceCfg.LowVar ()) :
 sourceMaterialPhysicalProjection (actualMaterialStockSourceTotal factory grade data sourceCfg language N) =
 actualMaterialStockCompleteChange factory grade data sourceCfg language N name -
 actualMaterialStockInheritedChange factory grade data sourceCfg language N name -
 actualStoredPhysicalTail factory grade data sourceCfg language N := by
 rw [(actual_received_physical_stock_and_tail factory grade data sourceCfg language N).2]
 exact actual_material_stock_projection_from_born factory grade data sourceCfg language N name

theorem actual_received_physical_cotest (name : sourceCfg.LowVar ()) (test : BurnolL2) :
 inner ℂ test (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
    (actualMaterialStockSourceTotal factory grade data sourceCfg language N)) : BurnolL2) =
 inner ℂ test (OriginalKFullSourceRAction.originalField
   (actualMaterialStockCompleteChange factory grade data sourceCfg language N name -
    actualMaterialStockInheritedChange factory grade data sourceCfg language N name -
    actualStoredPhysicalTail factory grade data sourceCfg language N)) := by
 have receipt := congrArg OriginalKFullSourceRAction.originalField
   (actual_received_physical_projection_from_born factory grade data sourceCfg language N name)
 change (burnolEvenAmbientProjection (OriginalKFullSourceRAction.originalField
    (actualMaterialStockSourceTotal factory grade data sourceCfg language N)) : BurnolL2) = _ at receipt
 rw [receipt]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
