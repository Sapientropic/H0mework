import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.ActorBorn
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.Consumer

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
local instance wholePaSourceActorConsumerComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction







open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open OriginalKWholePaSourceRankAction
local notation "E" => OriginalKCombCofinalPaAction.E

local instance sourceActorConsumerGradedGroups (grade : Nat) (target : Unit) :
    AddCommGroup (SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
  SourceL.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target

variable (factory : SourceFamily.Factory (PairValue OriginalKFullSourceRAction.C.Value) SourceVar ())
variable (grade : Nat)
variable (data : SourceFamily.Packet (W := PairValue OriginalKFullSourceRAction.C.Value) (X := SourceVar) (s := ()) grade)
variable (sourceCfg : SourceA.Programme
  (PhysicalValue := SourceL.Value (PairValue OriginalKFullSourceRAction.C.Value) grade) (PhysicalVar := SourceVar) (sort := ()))
variable (language : sourceCfg.LowVar = SourceVar)

def actualReceivedSourceDelta (h nextShift : ℝ) (name : sourceCfg.LowVar ()) : BurnolL2 :=
  OriginalKFullSourceRAction.originalField
    (OriginalKFullSourceRAction.CF.collapseValue grade
      ((sourceActorStockBorn observation nontrivial half factory grade data sourceCfg language h nextShift).activeEnvironment () name) -
    OriginalKFullSourceRAction.CF.collapseValue grade
      (sourceActorStockUpdatedValue observation nontrivial half factory grade data sourceCfg language h nextShift))

theorem actual_received_source_delta (h nextShift : ℝ) (name : sourceCfg.LowVar ()) :
    actualReceivedSourceDelta observation nontrivial half factory grade data sourceCfg language h nextShift name =
      OriginalKFullSourceRResponse.completeNativeUpdate observation nontrivial half h nextShift := by
  unfold actualReceivedSourceDelta
  rw [actual_actor_stock_source_delta]
  rfl

def actualReceivedPaCoefficient (h nextShift : ℝ) (name : sourceCfg.LowVar ()) : ℂ :=
  burnolPaResolventSourceCoefficient (actualWholePaDivisionCoordinate observation nontrivial half)
    (E (actualReceivedSourceDelta observation nontrivial half factory grade data sourceCfg language h nextShift name))

def actualReceivedNonPaR (h nextShift : ℝ) (name : sourceCfg.LowVar ()) : BurnolL2 :=
  OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (actualReceivedSourceDelta observation nontrivial half factory grade data sourceCfg language h nextShift name -
      (E (actualReceivedSourceDelta observation nontrivial half factory grade data sourceCfg language h nextShift name) : BurnolL2))

def actualReceivedPairPrice (h nextShift : ℝ) (name : sourceCfg.LowVar ()) : ℂ :=
  star (actualReceivedPaCoefficient observation nontrivial half factory grade data sourceCfg language h nextShift name / 2) *
    actualWholePaUnitPairPrice observation nontrivial half +
  OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
    (actualReceivedNonPaR observation nontrivial half factory grade data sourceCfg language h nextShift name)

def actualReceivedSiblingPrice (h nextShift : ℝ) (name : sourceCfg.LowVar ()) : ℂ :=
  (actualReceivedPaCoefficient observation nontrivial half factory grade data sourceCfg language h nextShift name / 2) *
    actualWholePaUnitSiblingPrice observation nontrivial half +
  OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
    (actualReceivedNonPaR observation nontrivial half factory grade data sourceCfg language h nextShift name)

def actualReceivedCrossEffect (h nextShift : ℝ) (name : sourceCfg.LowVar ()) : ℂ :=
  (actualOriginalCrossFactor observation nextShift-actualOriginalCrossFactor observation h) *
    actualWholePaPairSourcePrice observation nontrivial half h +
  actualOriginalCrossFactor observation nextShift *
    actualReceivedPairPrice observation nontrivial half factory grade data sourceCfg language h nextShift name +
  star (actualOriginalCrossFactor observation nextShift-actualOriginalCrossFactor observation h) *
    actualWholePaSiblingSourcePrice observation nontrivial half h +
  star (actualOriginalCrossFactor observation nextShift) *
    actualReceivedSiblingPrice observation nontrivial half factory grade data sourceCfg language h nextShift name

/-- Both dependent effect readers consume the actual newly received source field before prices. -/
theorem actual_received_Pa_nonPa_R_effect (h nextShift : ℝ) (name : sourceCfg.LowVar ()) :
    actualReceivedPaCoefficient observation nontrivial half factory grade data sourceCfg language h nextShift name =
      actualNativeSourceCoefficientUpdate observation nontrivial half h nextShift ∧
    actualReceivedNonPaR observation nontrivial half factory grade data sourceCfg language h nextShift name =
      actualNonPaNativeRUpdate observation nontrivial half h nextShift := by
  unfold actualReceivedPaCoefficient actualReceivedNonPaR
  rw [actual_received_source_delta]
  exact ⟨rfl,rfl⟩

/-- The independent fixed-actor Cross increment reads this same actual born field's effect; the old R written total is not identified with S(H). -/
theorem actual_received_cross_effect (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift) (name : sourceCfg.LowVar ()) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half nextShift -
      OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      actualReceivedCrossEffect observation nontrivial half factory grade data sourceCfg language h nextShift name := by
  unfold actualReceivedCrossEffect actualReceivedPairPrice actualReceivedSiblingPrice
  rw [(actual_received_Pa_nonPa_R_effect observation nontrivial half factory grade data sourceCfg language h nextShift name).1,
    (actual_received_Pa_nonPa_R_effect observation nontrivial half factory grade data sourceCfg language h nextShift name).2]
  exact actual_original_cross_consumes_native_rank_update observation nontrivial half h nextShift nonnegative ordered

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
