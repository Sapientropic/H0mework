import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKMaterialPhysicalStockSourceAction.Born
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
local instance transitionGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (factory : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var) (N : ℕ)

def actualMaterialStockSourceTotal : D.SourceBranches :=
 CF.collapseValue grade (physicalStockUpdatedValue factory grade data sourceCfg language N)

def actualMaterialStockInheritedChange (name : sourceCfg.LowVar ()) : D.SourceBranches :=
 actualMaterialStockSourceTotal factory grade data sourceCfg language N -
 CF.collapseValue grade ((physicalStockSelected factory grade data sourceCfg language N).activeEnvironment () name)

def actualMaterialStockCompleteChange (name : sourceCfg.LowVar ()) : D.SourceBranches :=
 CF.collapseValue grade ((physicalStockBorn factory grade data sourceCfg language N).activeEnvironment () name) -
 CF.collapseValue grade ((physicalStockSelected factory grade data sourceCfg language N).activeEnvironment () name)

/-- The actual born change includes the native source update and the source-computed physical stock of its own updated material. -/
theorem actual_material_stock_transition_keeps_complete_change (name : sourceCfg.LowVar ()) :
 actualMaterialStockCompleteChange factory grade data sourceCfg language N name =
 actualMaterialStockInheritedChange factory grade data sourceCfg language N name +
 sourceMaterialPhysicalStockAction N (actualMaterialStockSourceTotal factory grade data sourceCfg language N) := by
 unfold actualMaterialStockCompleteChange actualMaterialStockInheritedChange actualMaterialStockSourceTotal
 rw [physical_stock_active_environment,physical_stock_write_field]
 abel

theorem actual_material_stock_projection_from_born (name : sourceCfg.LowVar ()) :
 sourceMaterialPhysicalProjection (actualMaterialStockSourceTotal factory grade data sourceCfg language N) =
 actualMaterialStockCompleteChange factory grade data sourceCfg language N name -
 actualMaterialStockInheritedChange factory grade data sourceCfg language N name -
 sourceMaterialPhysicalTailAction N (actualMaterialStockSourceTotal factory grade data sourceCfg language N) := by
 rw [actual_material_stock_transition_keeps_complete_change,source_material_physical_stock_complete]
 abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKMaterialPhysicalStockSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
