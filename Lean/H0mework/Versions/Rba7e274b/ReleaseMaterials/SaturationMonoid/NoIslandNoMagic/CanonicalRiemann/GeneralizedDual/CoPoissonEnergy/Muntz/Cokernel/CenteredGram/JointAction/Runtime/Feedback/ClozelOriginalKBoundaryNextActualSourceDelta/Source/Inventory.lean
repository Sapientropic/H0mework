import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.Datum
import H0mework.Realization.Operations.Execution.Relations.History.Events

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
local instance wholePaSourceActorInventoryComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction






open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace ActorStock
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Stock (preserve)
end ActorStock
namespace ActorShared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (actualOccurrence)
end ActorShared

local instance sourceActorInventoryGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (factory : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

abbrev ActorFrame := RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
  (Value := PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade))
  (Var := sourceCfg.LowVar) (sort := ())

def sourceActorGradedRaw (h nextShift : ℝ) (frame : ActorFrame grade sourceCfg) :
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade))
      (Var := sourceCfg.LowVar) (sort := ()) :=
  ⟨SourceAS.write factory grade data sourceCfg language
      (SourceWB.oldPaid data.1 sourceCfg + SourceWB.nativeAt sourceCfg frame (ActorShared.actualOccurrence frame)),
    language.symm ▸ SourceCF.codeAt (sourceCarrierCode observation nontrivial half h nextShift) grade⟩

def sourceActorGradedTrace (h nextShift : ℝ) (frame : ActorFrame grade sourceCfg) :
    Trace (sourceActorGradedRaw observation nontrivial half factory grade data sourceCfg language h nextShift frame).environment
      (sourceActorGradedRaw observation nontrivial half factory grade data sourceCfg language h nextShift frame).expression
      (.const ((sourceActorGradedRaw observation nontrivial half factory grade data sourceCfg language h nextShift frame).expression.eval
        (sourceActorGradedRaw observation nontrivial half factory grade data sourceCfg language h nextShift frame).environment)) :=
  execution _ _

/-- Every actual source actor Step and relation is retained in the original root inventory, before the next consumer reads its field update. -/
def sourceActorGradedInventory (h nextShift : ℝ) (frame : ActorFrame grade sourceCfg) :=
  SourceOperationPaidRelations.exposure
    (sourceActorGradedTrace observation nontrivial half factory grade data sourceCfg language h nextShift frame)

def sourceEmitterActorBase (h nextShift : ℝ) :=
  { sourceEmitterNextBase observation nontrivial half factory grade data sourceCfg language h nextShift with
    nextInventory := fun frame => some (ActorStock.preserve
      ((sourceEmitterNextBase observation nontrivial half factory grade data sourceCfg language h nextShift).nextInventory frame)
      (sourceActorGradedInventory observation nontrivial half factory grade data sourceCfg language h nextShift frame)) }

theorem source_actor_inventory_installed (h nextShift : ℝ) (frame : ActorFrame grade sourceCfg) :
    (sourceEmitterActorBase observation nontrivial half factory grade data sourceCfg language h nextShift).nextInventory frame =
      some (ActorStock.preserve
        ((sourceEmitterNextBase observation nontrivial half factory grade data sourceCfg language h nextShift).nextInventory frame)
        (sourceActorGradedInventory observation nontrivial half factory grade data sourceCfg language h nextShift frame)) := rfl

theorem source_actor_inventory_relations (h nextShift : ℝ) (frame : ActorFrame grade sourceCfg)
    (word : Expr (PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade)) sourceCfg.LowVar () →₀ ℤ)
    (belongs : PresentedRelationEventAt.relation word ∈
      (sourceActorGradedInventory observation nontrivial half factory grade data sourceCfg language h nextShift frame).trace) :
    SourceOperationScalarRelations.evaluation (R := ℤ)
      (sourceActorGradedRaw observation nontrivial half factory grade data sourceCfg language h nextShift frame).environment word = 0 :=
  SourceOperationPaidRelations.exposure_sound _ _ belongs

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
