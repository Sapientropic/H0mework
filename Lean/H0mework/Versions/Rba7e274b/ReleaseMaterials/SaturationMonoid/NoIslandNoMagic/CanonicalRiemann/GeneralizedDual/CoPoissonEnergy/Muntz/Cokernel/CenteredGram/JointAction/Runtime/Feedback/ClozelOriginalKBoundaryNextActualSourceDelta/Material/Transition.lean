import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Material.Selected

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
local instance wholePaSourceMaterialTransitionComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction









open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace TransitionAI
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation (actual_environment)
end TransitionAI
namespace TransitionShared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (next nextBorn actualOccurrence)
end TransitionShared
namespace TransitionR
export SourceGeneratedInquiryReceiptAction (afterEnvironment)
end TransitionR

private theorem source_receipt_settled_next
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (cfg : SourceA.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))
    (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
      (Value := Value) (Var := Var) (sort := ())) :
    TransitionShared.next (StockComplete.atReceipt cfg initial 0) cfg =
      TransitionShared.nextBorn (StockComplete.atReceipt cfg initial 0) cfg := by
  have actual := (StockComplete.receipt cfg initial 0).2.2.2
  change (StockComplete.atReceipt cfg initial 0).action = Sum.inl (StockComplete.receipt cfg initial 0).2.1 at actual
  unfold TransitionShared.next
  rw [actual]

local instance sourceMaterialTransitionGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (producer : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

private theorem actual_R_actor_raw_environment (h nextShift : ℝ)
    (frame : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
      (Value := PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade))
      (Var := sourceCfg.LowVar) (sort := ())) :
    (ActorR.actionReader frame
      (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)
      (ActorRoot.actualOccurrence frame)).environment = pairEnvironment frame.activeEnvironment 0 := by
  have source := actual_actor_material_R_raw observation nontrivial half producer grade data sourceCfg language h nextShift
    frame (ActorRoot.actualOccurrence frame)
  have environment := congrArg (fun raw => raw.environment) source
  exact environment.trans (congrArg (fun env => pairEnvironment env (0 : Env _ sourceCfg.LowVar))
    (TransitionAI.actual_environment (grade+1) frame))

/-- The actual settled emitter advances to precisely the source actor's born field, not to an unrelated same-valued frame. -/
theorem actual_actor_selected_next (h nextShift : ℝ) :
    TransitionShared.next
      (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
      (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift) =
      sourceActorStockBorn observation nontrivial half (actualSourceRActorFactory observation nontrivial half producer)
        grade data sourceCfg language h nextShift :=
  source_receipt_settled_next _ _

theorem actual_actor_selected_material_after (h nextShift : ℝ) :
    TransitionR.afterEnvironment
      (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
      (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift) =
    pairEnvironment
      (sourceActorStockBorn observation nontrivial half (actualSourceRActorFactory observation nontrivial half producer)
        grade data sourceCfg language h nextShift).activeEnvironment 0 := by
  unfold TransitionR.afterEnvironment
  rw [actual_actor_selected_next]
  exact actual_R_actor_raw_environment observation nontrivial half producer grade data sourceCfg language h nextShift _

/-- This is the material's own source environment increment, with the complete inherited native source change still present. -/
theorem actual_actor_selected_material_increment (h nextShift : ℝ) :
    (ActorR.actualMaterial
      (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift)
      (actualActorSelectedCfg observation nontrivial half producer grade data sourceCfg language h nextShift)).increment =
    pairEnvironment
      ((sourceActorStockBorn observation nontrivial half (actualSourceRActorFactory observation nontrivial half producer)
          grade data sourceCfg language h nextShift).activeEnvironment -
        (actualActorSelectedFrame observation nontrivial half producer grade data sourceCfg language h nextShift).activeEnvironment) 0 := by
  change TransitionR.afterEnvironment _ _ - (ActorR.actualMaterial _ _).environment = _
  rw [actual_actor_selected_material_after,actual_actor_selected_material_before]
  funext target name
  simp only [Pi.sub_apply,pairEnvironment,Prod.mk_sub_mk,sub_self]
  rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
