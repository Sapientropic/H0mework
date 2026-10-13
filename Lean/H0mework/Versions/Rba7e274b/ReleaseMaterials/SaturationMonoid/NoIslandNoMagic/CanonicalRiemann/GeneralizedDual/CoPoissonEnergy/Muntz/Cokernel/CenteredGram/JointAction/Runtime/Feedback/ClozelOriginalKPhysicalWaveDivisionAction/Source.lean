import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWaveDivisionAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance complementSourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


namespace Actual
export OriginalCommonInverseForcing.SourceJoint (upperSourceField upperSeedFactor)
export OriginalCommonInverseForcing.SourceJoint.FullStock (meanDebt)
end Actual

/-- Complete actual complement material: the original weighted exterior fields and both original mean debts, before R or any mixed price. -/
def actualComplementMaterial (h : ℝ) : BurnolL2 :=
  -(Actual.upperSourceField c h) + Actual.upperSeedFactor h • (Actual.meanDebt c h : BurnolL2)

/-- This is the same complete source-minus-born-wave occurrence, recovered from its source definitions. -/
theorem actual_complement_material_realizes (h : ℝ) :
    OriginalKWholeWardSource.actualWholeSourceComplement observation nontrivial half h =
      actualComplementMaterial observation nontrivial half h := by
  unfold OriginalKWholeWardSource.actualWholeSourceComplement OriginalKFullSourceRResponse.completeSource
    OriginalKWholeWardSource.actualWholeWaveSource OriginalCommonInverseForcing.SourceJoint.upperSourceCorrection
    actualComplementMaterial
  module

/-- The existing same-source weighted actor generates the full exterior field; it is not identified with an independent full counting value. -/
theorem actual_complement_source_actor (h : ℝ) (nonnegative : 0 ≤ h) :
    actualComplementMaterial observation nontrivial half h =
      Actual.upperSeedFactor h •
        (-(OriginalRieszFinitePairing.CoPoisson.positionSeed c h +
          fourierL2 (OriginalRieszFinitePairing.CoPoisson.fourierSeed c h)) +
          (Actual.meanDebt c h : BurnolL2)) := by
  unfold actualComplementMaterial
  rw [OriginalCommonInverseForcing.SourceJoint.actual_upper_common_seed c h nonnegative]
  module

/-- Actual R acts on the recovered source material; no cancellation or mixed terminal value supplies this constructor. -/
theorem actual_complement_R_actor (h : ℝ) (nonnegative : 0 ≤ h) :
    OriginalKWholeWardSource.actualWholeComplementR observation nontrivial half h =
      Actual.upperSeedFactor h •
        (-(OriginalKFullSourceRResponse.Op.R observation nontrivial half
          (OriginalRieszFinitePairing.CoPoisson.positionSeed c h +
            fourierL2 (OriginalRieszFinitePairing.CoPoisson.fourierSeed c h))) +
          OriginalKFullSourceRResponse.Op.R observation nontrivial half (Actual.meanDebt c h : BurnolL2)) := by
  unfold OriginalKWholeWardSource.actualWholeComplementR
  rw [actual_complement_material_realizes, actual_complement_source_actor observation nontrivial half h nonnegative]
  rw [map_smul,map_add,map_neg]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWaveDivisionAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
