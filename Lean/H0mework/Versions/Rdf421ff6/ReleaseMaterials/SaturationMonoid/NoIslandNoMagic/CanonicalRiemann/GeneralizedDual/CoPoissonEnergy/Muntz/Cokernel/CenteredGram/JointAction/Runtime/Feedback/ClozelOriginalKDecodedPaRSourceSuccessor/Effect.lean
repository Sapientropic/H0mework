import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceSuccessor.Material
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceSuccessor.Division
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceSuccessor
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
local instance effectSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def inheritedSourceIncrement (name : sourceCfg.LowVar ()) : OriginalKFinitePaWindowOperatorSourceAction.Branches :=
 CF.collapseValue grade (updatedSourceTotal observation nontrivial half depth ordinal h H N
  (sourceRFactory observation nontrivial half producer) grade data sourceCfg language) -
 CF.collapseValue grade ((rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).activeEnvironment () name)

/-- The complete source increment is read from actual material, retaining the inherited native fee. -/
theorem actual_material_complete_source_increment (name : sourceCfg.LowVar ()) :
 CF.collapseValue (grade+1) ((rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).increment () name) =
 inheritedSourceIncrement observation nontrivial half depth ordinal h H N producer grade data sourceCfg language name +
 decodedSourceMaterial observation nontrivial half depth ordinal h H N := by
 rw [actual_material_source_increment]
 change CF.collapseValue grade
  (((rBorn observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).activeEnvironment () name-
    (rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).activeEnvironment () name)+0) = _
 rw [add_zero,OriginalKFiniteWard.collapse_sub]
 have actor := actual_born_decoded_source_increment observation nontrivial half depth ordinal h H N
  (sourceRFactory observation nontrivial half producer) grade data sourceCfg language name
 unfold inheritedSourceIncrement
 linear_combination (norm:=module) actor

theorem actual_material_raw_source_R :
 (rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).raw =
 CF.codeAt (language.symm ▸ FullR.sourceCode observation nontrivial half) (grade+1) := by
 have source := actual_material_reader_R observation nontrivial half depth ordinal h H N producer grade data sourceCfg language
  (rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language)
  (Shared.actualOccurrence (rSelected observation nontrivial half depth ordinal h H N producer grade data sourceCfg language))
 exact congrArg (fun raw => raw.expression) source

/-- Actual R raw.effect is generated from its complete increment, with both inherited and decoded actor fields. -/
theorem actual_material_R_effect :
 CF.collapseValue (grade+1)
  ((rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).raw.effect
   (rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).environment
   (rMaterial observation nontrivial half depth ordinal h H N producer grade data sourceCfg language).increment) =
 FullR.variableAction observation nontrivial half
  (inheritedSourceIncrement observation nontrivial half depth ordinal h H N producer grade data sourceCfg language (language.symm ▸ ())) +
 ownSourceR observation nontrivial half depth ordinal h H N := by
 cases sourceCfg with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=C.Var at language
  cases language
  let cfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()) :=
   ⟨C.Var,datum,inventory,pairInventory⟩
  rw [actual_material_raw_source_R,OriginalKFullSourceRAction.Projection.code_effect_base,FullR.source_code_effect]
  change FullR.variableAction observation nontrivial half
   (CF.collapseValue (grade+1) ((rMaterial observation nontrivial half depth ordinal h H N producer grade data cfg rfl).increment () ())) = _
  rw [actual_material_complete_source_increment,map_add]
  rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRSourceSuccessor
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
