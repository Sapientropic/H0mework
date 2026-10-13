import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.Inventory
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.BornRead

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
local instance wholePaSourceActorBornComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction






open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace StockComplete
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Completion (receipt atReceipt receipt_compiles receipt_next)
end StockComplete
namespace StockShared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (nextBorn actualVisit actualOccurrence)
end StockShared
namespace StockEnvironment
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active)
end StockEnvironment
namespace StockAS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource (receiver)
end StockAS
namespace StockWB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback (nativeEventValue)
end StockWB

private theorem source_receipt_native_value
    {Value Var : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (cfg : SourceA.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := ()))
    (initial : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
      (Value := Value) (Var := Var) (sort := ())) :
    StockWB.nativeEventValue (StockComplete.atReceipt cfg initial 0).event =
      (StockComplete.receipt cfg initial 0).2.1.1 := by
  have actual := (StockComplete.receipt cfg initial 0).2.2.2
  change RootGeneratedDebtActivationJointSource.mathAction (StockComplete.atReceipt cfg initial 0).event =
    Sum.inl (StockComplete.receipt cfg initial 0).2.1 at actual
  unfold StockWB.nativeEventValue
  rw [actual]

local instance sourceActorBornGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (factory : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

def sourceActorStockCfg (h nextShift : ℝ) :=
  SourceAS.stockCfg (sourceEmitterActorBase observation nontrivial half factory grade data sourceCfg language h nextShift)

def sourceActorStockReceipt (h nextShift : ℝ) :=
  StockComplete.receipt (sourceActorStockCfg observation nontrivial half factory grade data sourceCfg language h nextShift)
    (StockAS.receiver factory grade data sourceCfg language) 0

def sourceActorStockSelected (h nextShift : ℝ) :=
  StockComplete.atReceipt (sourceActorStockCfg observation nontrivial half factory grade data sourceCfg language h nextShift)
    (StockAS.receiver factory grade data sourceCfg language) 0

def sourceActorStockBorn (h nextShift : ℝ) :=
  StockShared.nextBorn (sourceActorStockSelected observation nontrivial half factory grade data sourceCfg language h nextShift)
    (sourceActorStockCfg observation nontrivial half factory grade data sourceCfg language h nextShift)

def sourceActorStockUpdatedValue (h nextShift : ℝ) :
    PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) () :=
  SourceWB.oldPaid data.1 sourceCfg +
    (show PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) () from
      (sourceActorStockReceipt observation nontrivial half factory grade data sourceCfg language h nextShift).2.1.1)

/-- The original stock admission executes the installed actor decoder; both source and extra inventory callbacks are retained. -/
theorem actual_actor_stock_environment (h nextShift : ℝ) :
    StockEnvironment.At (sourceActorStockBorn observation nontrivial half factory grade data sourceCfg language h nextShift)
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift
        (sourceActorStockUpdatedValue observation nontrivial half factory grade data sourceCfg language h nextShift)) := by
  intro current occurrence
  change sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift
    (SourceWB.oldPaid data.1 sourceCfg +
      (show PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) () from StockWB.nativeEventValue
        (sourceActorStockSelected observation nontrivial half factory grade data sourceCfg language h nextShift).event)) = _
  have value : StockWB.nativeEventValue
      (sourceActorStockSelected observation nontrivial half factory grade data sourceCfg language h nextShift).event =
      (sourceActorStockReceipt observation nontrivial half factory grade data sourceCfg language h nextShift).2.1.1 :=
    source_receipt_native_value _ _
  exact congrArg (fun value => sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift
    (SourceWB.oldPaid data.1 sourceCfg + value)) value

theorem actual_actor_stock_active_environment (h nextShift : ℝ) :
    (sourceActorStockBorn observation nontrivial half factory grade data sourceCfg language h nextShift).activeEnvironment =
      sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift
        (sourceActorStockUpdatedValue observation nontrivial half factory grade data sourceCfg language h nextShift) :=
  StockEnvironment.active (actual_actor_stock_environment observation nontrivial half factory grade data sourceCfg language h nextShift)

theorem actual_actor_stock_receipt_next (h nextShift : ℝ) :
    type_of% (StockComplete.receipt_next
      (sourceActorStockCfg observation nontrivial half factory grade data sourceCfg language h nextShift)
      (StockAS.receiver factory grade data sourceCfg language) 0) := StockComplete.receipt_next _ _ _

theorem actual_actor_stock_receipt_compiles (h nextShift : ℝ) :
    type_of% (StockComplete.receipt_compiles
      (sourceActorStockCfg observation nontrivial half factory grade data sourceCfg language h nextShift)
      (StockAS.receiver factory grade data sourceCfg language) 0) := StockComplete.receipt_compiles _ _ _

/-- Actual source Steps are retained in the same born stock, alongside every inherited source/extra inventory. -/
theorem actual_actor_stock_inventory (h nextShift : ℝ) :
    (sourceActorStockBorn observation nontrivial half factory grade data sourceCfg language h nextShift).inventory =
      (sourceActorStockCfg observation nontrivial half factory grade data sourceCfg language h nextShift).nextInventory
        (sourceActorStockSelected observation nontrivial half factory grade data sourceCfg language h nextShift) := rfl

/-- The received born stock itself, rather than a caller equality, generates the new full source increment. -/
theorem actual_actor_stock_source_delta (h nextShift : ℝ) (name : sourceCfg.LowVar ()) :
    OriginalKFullSourceRAction.CF.collapseValue grade
      ((sourceActorStockBorn observation nontrivial half factory grade data sourceCfg language h nextShift).activeEnvironment () name) -
    OriginalKFullSourceRAction.CF.collapseValue grade
      (sourceActorStockUpdatedValue observation nontrivial half factory grade data sourceCfg language h nextShift) =
      actualSourceDeltaBranches observation nontrivial half h nextShift := by
  rw [actual_actor_stock_active_environment,source_actor_write_base_field]
  exact source_carrier_action_effect observation nontrivial half h nextShift _

/-- Original R acts on that exact newly received source Delta, preserving its four source faces. -/
theorem actual_actor_stock_original_R_effect (h nextShift : ℝ) (name : sourceCfg.LowVar ()) :
    OriginalKFullSourceRAction.variableAction observation nontrivial half
      (OriginalKFullSourceRAction.CF.collapseValue grade
        ((sourceActorStockBorn observation nontrivial half factory grade data sourceCfg language h nextShift).activeEnvironment () name)) -
    OriginalKFullSourceRAction.variableAction observation nontrivial half
      (OriginalKFullSourceRAction.CF.collapseValue grade
        (sourceActorStockUpdatedValue observation nontrivial half factory grade data sourceCfg language h nextShift)) =
      OriginalKFullSourceRAction.variableAction observation nontrivial half
        (actualSourceDeltaBranches observation nontrivial half h nextShift) := by
  have source := congrArg (OriginalKFullSourceRAction.variableAction observation nontrivial half)
    (actual_actor_stock_source_delta observation nontrivial half factory grade data sourceCfg language h nextShift name)
  simpa only [map_sub] using source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
