import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Material.Transition

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
local instance wholePaSourceMaterialDeltaComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction









open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement

local instance sourceMaterialDeltaGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (producer : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

def actualInheritedSourceIncrement (h nextShift : ℝ) (name : sourceCfg.LowVar ()) : SourceBranches :=
  OriginalKFullSourceRAction.CF.collapseValue grade
    (sourceActorStockUpdatedValue observation nontrivial half (actualSourceRActorFactory observation nontrivial half producer)
      grade data sourceCfg language h nextShift) -
  OriginalKFullSourceRAction.CF.collapseValue grade
    ((actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift).activeEnvironment () name)

/-- The material's actual complete source increment keeps both the inherited native source change and the freshly generated fullS actor. -/
theorem actual_material_complete_source_increment (h nextShift : ℝ) (name : sourceCfg.LowVar ()) :
    OriginalKFullSourceRAction.CF.collapseValue (grade+1)
      ((ActorR.actualMaterial
        (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
        (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).increment () name) =
      actualInheritedSourceIncrement observation nontrivial half producer grade data sourceCfg language h nextShift name +
        actualSourceDeltaBranches observation nontrivial half h nextShift := by
  rw [actual_actor_selected_material_increment]
  change OriginalKFullSourceRAction.CF.collapseValue grade
    (((sourceActorStockBorn observation nontrivial half (actualSourceRActorFactory observation nontrivial half producer)
      grade data sourceCfg language h nextShift).activeEnvironment () name -
      (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift).activeEnvironment () name) + 0) = _
  rw [add_zero,OriginalKFiniteWard.collapse_sub]
  have actor := actual_actor_stock_source_delta observation nontrivial half
    (actualSourceRActorFactory observation nontrivial half producer) grade data sourceCfg language h nextShift name
  unfold actualInheritedSourceIncrement
  linear_combination (norm := module) actor

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
