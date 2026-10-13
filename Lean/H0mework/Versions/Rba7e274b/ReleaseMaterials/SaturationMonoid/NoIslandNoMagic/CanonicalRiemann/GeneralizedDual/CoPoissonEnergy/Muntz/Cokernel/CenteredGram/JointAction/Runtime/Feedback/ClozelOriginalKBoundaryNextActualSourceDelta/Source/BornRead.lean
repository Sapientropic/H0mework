import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.Born
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Consumer

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
local instance wholePaSourceBornReadComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction







open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement

private theorem source_eval_language_transport {Y Z : Unit → Type}
    (same : Y = Z)
    {Value : Unit → Type} [∀ target, AddCommGroup (Value target)]
    (code : Expr Value Z ()) (environment : Env Value Y) :
    (same.symm ▸ code : Expr Value Y ()).eval environment =
      code.eval (same ▸ environment : Env Value Z) := by
  cases same
  rfl

local instance sourceBornReadGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (factory : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

/-- The old/effect graded source is collapsed by its existing paid source model, not by a new occurrence recognition. -/
theorem source_actor_write_base_field (h nextShift : ℝ)
    (value : PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) ())
    (name : sourceCfg.LowVar ()) :
    OriginalKFullSourceRAction.CF.collapseValue grade
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift value () name) =
    sourceCarrierAction observation nontrivial half h nextShift
      (OriginalKFullSourceRAction.CF.collapseValue grade value) := by
  unfold sourceActorWrite
  dsimp only
  rw [source_eval_language_transport language]
  have source := OriginalKFullSourceRAction.CF.code_base_value
    (sourceCarrierCode observation nontrivial half h nextShift) grade
    (language ▸ SourceAS.write factory grade data sourceCfg language value)
  rw [source] 
  rw [source_carrier_code_read]
  congr 1
  congr 1
  cases sourceCfg with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = SourceVar at language
    cases language
    simp only [SourceAS.write, dite_true]

/-- Actual born material now writes the complete source actor Delta over its own inherited R written value, without asserting an S(H) identity. -/
theorem actual_born_source_actor_delta (h nextShift : ℝ) (name : sourceCfg.LowVar ()) :
    OriginalKFullSourceRAction.CF.collapseValue grade
      ((sourceActorBorn observation nontrivial half factory grade data sourceCfg language h nextShift).activeEnvironment () name) -
    OriginalKFullSourceRAction.CF.collapseValue grade
      (sourceActorOldValue observation nontrivial half factory grade data sourceCfg language h nextShift) =
      actualSourceDeltaBranches observation nontrivial half h nextShift := by
  rw [actual_source_actor_active_environment,source_actor_write_base_field]
  exact source_carrier_action_effect observation nontrivial half h nextShift _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
