import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Material.Delta

import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wholePaSourceMaterialEffectComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction









open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement

local instance sourceMaterialEffectGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (producer : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

/-- The actual material retains the original R AST installed before its source receipt. -/
theorem actual_actor_selected_material_raw (h nextShift : ℝ) :
    (ActorR.actualMaterial
      (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
      (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).raw =
      SourceCF.codeAt (language.symm ▸ OriginalKFullSourceRAction.sourceCode observation nontrivial half) (grade+1) := by
  have source := actual_actor_material_R_raw observation nontrivial half producer grade data sourceCfg language h nextShift
    (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
    (ActorRoot.actualOccurrence (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift))
  exact congrArg (fun raw => raw.expression) source

/-- The original R material effect consumes its complete actual environment delta, retaining the inherited native fee and the generated actor delta in all four faces. -/
theorem actual_material_complete_original_R_effect (h nextShift : ℝ) :
    OriginalKFullSourceRAction.CF.collapseValue (grade+1)
      ((ActorR.actualMaterial
        (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
        (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).raw.effect
        (ActorR.actualMaterial
          (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
          (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).environment
        (ActorR.actualMaterial
          (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
          (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).increment) =
      OriginalKFullSourceRAction.variableAction observation nontrivial half
        (actualInheritedSourceIncrement observation nontrivial half producer grade data sourceCfg language h nextShift (language.symm ▸ ())) +
      OriginalKFullSourceRAction.variableAction observation nontrivial half
        (actualSourceDeltaBranches observation nontrivial half h nextShift) := by
  cases sourceCfg with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = SourceVar at language
    cases language
    let cfg : SourceA.Programme
      (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade)
      (PhysicalVar := SourceVar) (sort := ()) := ⟨SourceVar,datum,inventory,pairInventory⟩
    rw [actual_actor_selected_material_raw,
      OriginalKFullSourceRAction.Projection.code_effect_base,
      OriginalKFullSourceRAction.source_code_effect]
    change OriginalKFullSourceRAction.variableAction observation nontrivial half
      (OriginalKFullSourceRAction.CF.collapseValue (grade+1) ((ActorR.actualMaterial
        (actualActorSelectedFrame observation nontrivial half producer grade data cfg rfl h nextShift)
        (actualActorSelectedCfg observation nontrivial half producer grade data cfg rfl h nextShift)).increment () ())) = _
    rw [actual_material_complete_source_increment,map_add]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
