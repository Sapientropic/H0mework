import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundaryNextActualSourceDelta.Source.Actor

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
local instance wholePaNativeSpliceConsumerComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction



open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open OriginalKWholePaSourceRankAction
local notation "E" => OriginalKCombCofinalPaAction.E

def materialSourceDelta (h nextShift : ℝ) (written : SourceBranches) : BurnolL2 :=
  OriginalKFullSourceRAction.originalField
    ((sourceRUpdateRaw observation nontrivial half h nextShift written).environment () ()).2

theorem material_source_delta (h nextShift : ℝ) (written : SourceBranches) :
    materialSourceDelta observation nontrivial half h nextShift written =
      OriginalKFullSourceRResponse.completeNativeUpdate observation nontrivial half h nextShift := by
  exact source_delta_projection observation nontrivial half h nextShift written

def materialPaCoefficient (h nextShift : ℝ) (written : SourceBranches) : ℂ :=
  burnolPaResolventSourceCoefficient (actualWholePaDivisionCoordinate observation nontrivial half)
    (E (materialSourceDelta observation nontrivial half h nextShift written))

def materialNonPaR (h nextShift : ℝ) (written : SourceBranches) : BurnolL2 :=
  OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (materialSourceDelta observation nontrivial half h nextShift written -
      (E (materialSourceDelta observation nontrivial half h nextShift written) : BurnolL2))

def materialPairPrice (h nextShift : ℝ) (written : SourceBranches) : ℂ :=
  star (materialPaCoefficient observation nontrivial half h nextShift written / 2) *
      actualWholePaUnitPairPrice observation nontrivial half +
    OriginalKPairedResponseGramAction.originalPairKernelRead observation nontrivial half
      (materialNonPaR observation nontrivial half h nextShift written)

def materialSiblingPrice (h nextShift : ℝ) (written : SourceBranches) : ℂ :=
  (materialPaCoefficient observation nontrivial half h nextShift written / 2) *
      actualWholePaUnitSiblingPrice observation nontrivial half +
    OriginalKPairedResponseGramAction.originalSiblingKernelRead observation nontrivial half
      (materialNonPaR observation nontrivial half h nextShift written)

/-- The independent scalar reader consumes the stored source increment after R/effect generation. -/
def materialCrossEffect (h nextShift : ℝ) (written : SourceBranches) : ℂ :=
  (actualOriginalCrossFactor observation nextShift - actualOriginalCrossFactor observation h) *
      actualWholePaPairSourcePrice observation nontrivial half h +
    actualOriginalCrossFactor observation nextShift * materialPairPrice observation nontrivial half h nextShift written +
    star (actualOriginalCrossFactor observation nextShift - actualOriginalCrossFactor observation h) *
      actualWholePaSiblingSourcePrice observation nontrivial half h +
    star (actualOriginalCrossFactor observation nextShift) * materialSiblingPrice observation nontrivial half h nextShift written

theorem material_source_coefficient_R (h nextShift : ℝ) (written : SourceBranches) :
    materialPaCoefficient observation nontrivial half h nextShift written =
      actualNativeSourceCoefficientUpdate observation nontrivial half h nextShift ∧
    materialNonPaR observation nontrivial half h nextShift written =
      actualNonPaNativeRUpdate observation nontrivial half h nextShift := by
  unfold materialPaCoefficient materialNonPaR
  rw [material_source_delta]
  exact ⟨rfl,rfl⟩

theorem material_cross_effect_generated (h nextShift : ℝ) (written : SourceBranches) :
    materialCrossEffect observation nontrivial half h nextShift written =
      actualWholePaRankSourceCharacterUpdate observation nontrivial half h nextShift := by
  unfold materialCrossEffect materialPairPrice materialSiblingPrice
  rw [(material_source_coefficient_R observation nontrivial half h nextShift written).1,
    (material_source_coefficient_R observation nontrivial half h nextShift written).2]
  rfl

/-- Original Cross is an independent terminal mathematical reader of the source material, never an input to that material. -/
theorem original_cross_consumes_source_material (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift)
    (written : SourceBranches) :
    OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half nextShift -
      OriginalKPairedResponseGramAction.originalKernelCross observation nontrivial half h =
      materialCrossEffect observation nontrivial half h nextShift written := by
  rw [material_cross_effect_generated]
  exact actual_original_cross_consumes_native_rank_update observation nontrivial half h nextShift nonnegative ordered

/-- The full current consumer keeps all five original residuals when reading the stored action. -/
theorem actual_current_consumes_source_material (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift)
    (bounded : nextShift ≤ Real.log 2) (n : Nat) (written : SourceBranches) :
    (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half nextShift
        (nonnegative.trans ordered) bounded n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half nextShift
        (nonnegative.trans ordered) bounded n) -
    (OriginalKWaveSourceAction.actualBandSourceFiniteCharacter observation nontrivial half h nonnegative (ordered.trans bounded) n +
      OriginalKRealCoordinateSourceUnit.actualUnweightedCharacterResidual observation nontrivial half h nonnegative (ordered.trans bounded) n) =
      materialCrossEffect observation nontrivial half h nextShift written := by
  rw [material_cross_effect_generated]
  exact actual_current_consumes_native_rank_update observation nontrivial half h nextShift nonnegative ordered bounded n

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
