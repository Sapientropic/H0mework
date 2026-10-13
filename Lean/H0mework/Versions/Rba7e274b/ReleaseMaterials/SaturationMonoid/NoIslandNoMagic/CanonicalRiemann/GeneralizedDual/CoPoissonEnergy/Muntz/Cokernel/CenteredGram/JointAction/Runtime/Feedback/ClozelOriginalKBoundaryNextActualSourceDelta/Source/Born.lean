import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.Datum
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
local instance wholePaSourceBornComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction






open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
namespace BornWB
export SourceGeneratedInquiryReceiptAction.Configured.Writeback
  (born receipt selected nativeValue born_environment updated_total source_target_root source_target_next source_compiles source_whole actual_receipt_compiles actual_receipt_next)
end BornWB
namespace BornEnvironment
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.Environment (At active)
end BornEnvironment

local instance sourceBornGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (factory : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

/-- The existing original emitter actually executes its paid native source and this literal field decoder. -/
def sourceActorBorn (h nextShift : ℝ) :=
  BornWB.born data.1 sourceCfg
    (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift)

/-- This is the real paid inherited source value before the new actor Delta, not the mathematical S(H) endpoint. -/
def sourceActorOldValue (h nextShift : ℝ) :
    PairValue (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) () :=
  SourceWB.oldPaid data.1 sourceCfg +
    BornWB.nativeValue data.1 sourceCfg
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift)

theorem actual_source_actor_born_environment (h nextShift : ℝ) :
    BornEnvironment.At (sourceActorBorn observation nontrivial half factory grade data sourceCfg language h nextShift)
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift
        (sourceActorOldValue observation nontrivial half factory grade data sourceCfg language h nextShift)) :=
  BornWB.born_environment data.1 sourceCfg
    (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift)

theorem actual_source_actor_active_environment (h nextShift : ℝ) :
    (sourceActorBorn observation nontrivial half factory grade data sourceCfg language h nextShift).activeEnvironment =
      sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift
        (sourceActorOldValue observation nontrivial half factory grade data sourceCfg language h nextShift) :=
  BornEnvironment.active (actual_source_actor_born_environment observation nontrivial half factory grade data sourceCfg language h nextShift)

/-- The same actual inherited source receipt generates its next and whole write before target readers. -/
theorem actual_source_actor_whole_next (h nextShift : ℝ) :
    (type_of% (BornWB.source_target_root data.1 sourceCfg
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift))) ∧
    (type_of% (BornWB.source_target_next data.1 sourceCfg
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift))) ∧
    (type_of% (BornWB.source_compiles data.1 sourceCfg
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift))) ∧
    (type_of% (BornWB.source_whole data.1 sourceCfg
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift))) ∧
    (type_of% (BornWB.actual_receipt_compiles data.1 sourceCfg
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift))) ∧
    (type_of% (BornWB.actual_receipt_next data.1 sourceCfg
      (sourceActorWrite observation nontrivial half factory grade data sourceCfg language h nextShift))) :=
  ⟨BornWB.source_target_root _ _ _,BornWB.source_target_next _ _ _,BornWB.source_compiles _ _ _,
    BornWB.source_whole _ _ _,BornWB.actual_receipt_compiles _ _ _,BornWB.actual_receipt_next _ _ _⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
