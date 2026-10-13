import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.ActorMaterial

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
local instance wholePaSourceSelectedMaterialComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction








open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace SelectedAI
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation (actual_environment)
end SelectedAI
namespace SelectedShared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next nextBorn actualOccurrence)
end SelectedShared

local instance sourceSelectedMaterialGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (producer : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

/-- Source metadata is read on the actual settled emitter frame, before its actor-written born field. -/
def actualActorSelectedFrame (h nextShift : ℝ) :=
  sourceActorStockSelected observation nontrivial half (actualSourceRActorFactory observation nontrivial half producer)
    grade data sourceCfg language h nextShift

def actualActorSelectedCfg (h nextShift : ℝ) :=
  sourceActorStockCfg observation nontrivial half (actualSourceRActorFactory observation nontrivial half producer)
    grade data sourceCfg language h nextShift

/-- The original calculation source environment remains before the emitted field update. -/
theorem actual_actor_selected_material_before (h nextShift : ℝ) :
    (ActorR.actualMaterial (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
      (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).environment =
    pairEnvironment
      (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift).activeEnvironment 0 := by
  let frame := actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift
  have source := actual_actor_material_R_raw observation nontrivial half producer grade data sourceCfg language h nextShift
    frame (ActorRoot.actualOccurrence frame)
  have environment := congrArg (fun raw => raw.environment) source
  exact environment.trans (congrArg (fun env => pairEnvironment env (0 : Env _ sourceCfg.LowVar))
    (SelectedAI.actual_environment (grade+1) frame))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
