import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Material

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
local instance effectSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (source : Branches) (shift : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def inheritedSourceIncrement (name : sourceCfg.LowVar ()) : OriginalKFinitePaWindowOperatorSourceAction.Branches :=
 CF.collapseValue grade (updatedSourceTotal source shift
  (splitFactory producer) grade data sourceCfg language) -
 CF.collapseValue grade ((stockSelected source shift producer grade data sourceCfg language).activeEnvironment () name)

/-- The complete source increment is read from actual material, retaining the inherited native fee. -/
theorem actual_material_complete_source_increment (name : sourceCfg.LowVar ()) :
 CF.collapseValue (grade+1) ((stockMaterial source shift producer grade data sourceCfg language).increment () name) =
 inheritedSourceIncrement source shift producer grade data sourceCfg language name +
 (splitAction shift source-splitAction 0 source) := by
 rw [actual_material_source_increment]
 change CF.collapseValue grade
  (((stockBorn source shift producer grade data sourceCfg language).activeEnvironment () name-
    (stockSelected source shift producer grade data sourceCfg language).activeEnvironment () name)+0) = _
 rw [add_zero,OriginalKFiniteWard.collapse_sub]
 have actor := actual_born_split_increment source shift
  (splitFactory producer) grade data sourceCfg language name
 unfold inheritedSourceIncrement
 linear_combination (norm:=module) actor

theorem actual_material_raw_source_stock :
 (stockMaterial source shift producer grade data sourceCfg language).raw =
 CF.codeAt (language.symm ▸ stockReadCode) (grade+1) := by
 have source := actual_material_reader_stock source shift producer grade data sourceCfg language
  (stockSelected source shift producer grade data sourceCfg language)
  (Shared.actualOccurrence (stockSelected source shift producer grade data sourceCfg language))
 exact congrArg (fun raw => raw.expression) source

/-- The complete material effect reads the actual emitted stock while retaining the inherited cost. -/
theorem actual_material_stock_effect :
 CF.collapseValue (grade+1)
  ((stockMaterial source shift producer grade data sourceCfg language).raw.effect
   (stockMaterial source shift producer grade data sourceCfg language).environment
   (stockMaterial source shift producer grade data sourceCfg language).increment) =
 inheritedSourceIncrement source shift producer grade data sourceCfg language (language.symm ▸ ()) +
 (splitAction shift source-splitAction 0 source) := by
 cases sourceCfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at language
  cases language
  let cfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()) :=
   ⟨C.Var,datum,inventory,pairInventory⟩
  rw [actual_material_raw_source_stock,OriginalKFullSourceRAction.Projection.code_effect_base]
  change CF.collapseValue (grade+1)
   ((stockMaterial source shift producer grade data cfg rfl).increment () ()) = _
  exact actual_material_complete_source_increment source shift producer grade data cfg rfl ()

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
