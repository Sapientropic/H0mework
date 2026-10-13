import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRResponse.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRResponse
open Complex MeasureTheory
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
open OriginalRieszFiniteSource OriginalRieszFiniteSynthesis
namespace Full
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalCommonInverseForcing.SourceJoint
 (upperSourceWave upperSourceField upperWaveNativeUpdate upperFieldNativeUpdate actual_upper_material_update)
end Full
namespace Seed
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson (positionSeed fourierSeed)
end Seed
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- Both native means remain actual full source masses; no guessed endpoint
coefficient or integrability subtraction is used. -/
def meanSourceUpdate (h nextShift : ℝ) : BurnolPaAmbientCarrier :=
  gapMeanAdjoint ((∫ x : ℝ,Seed.positionSeed (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) nextShift x)-
    (∫ x : ℝ,Seed.positionSeed (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h x))+
  evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    (gapMeanAdjoint ((∫ x : ℝ,Seed.fourierSeed (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) nextShift x)-
      (∫ x : ℝ,Seed.fourierSeed (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h x)))

theorem actual_two_mean_source_update (h nextShift : ℝ) :
    Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) nextShift-
      Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h=
        meanSourceUpdate observation nontrivial half h nextShift := by
  unfold Full.meanDebt meanSourceUpdate
  rw [map_sub,map_sub,map_sub]
  module

def completeNativeUpdate (h nextShift : ℝ) : BurnolL2 :=
  Full.upperWaveNativeUpdate (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nextShift-
    Full.upperFieldNativeUpdate (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h nextShift+
    (Full.upperSeedFactor nextShift-Full.upperSeedFactor h) •
      (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)+
    Full.upperSeedFactor nextShift • (meanSourceUpdate observation nontrivial half h nextShift : BurnolL2)

theorem actual_complete_native_update (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) :
    completeSource observation nontrivial half nextShift-completeSource observation nontrivial half h=
      completeNativeUpdate observation nontrivial half h nextShift := by
  have native:=Full.actual_upper_material_update (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
    h nextShift nonnegative ordered
  have means:=actual_two_mean_source_update observation nontrivial half h nextShift
  have physicalMeans:=congrArg (fun value : BurnolPaAmbientCarrier=>(value : BurnolL2)) means
  change (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) nextShift : BurnolL2)-
    (Full.meanDebt (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) h : BurnolL2)=
      (meanSourceUpdate observation nontrivial half h nextShift : BurnolL2) at physicalMeans
  unfold completeSource completeNativeUpdate Full.upperSourceCorrection
  rw [←native.1,←native.2,←physicalMeans]
  module

theorem actual_R_response_update (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) :
    pairedResponse observation nontrivial half nextShift-pairedResponse observation nontrivial half h=
      Paid.paired (Op.R observation nontrivial half (completeNativeUpdate observation nontrivial half h nextShift)) ∧
    siblingResponse observation nontrivial half nextShift-siblingResponse observation nontrivial half h=
      Paid.sibling (Op.R observation nontrivial half (completeNativeUpdate observation nontrivial half h nextShift)) := by
  rw [← actual_complete_native_update observation nontrivial half h nextShift nonnegative ordered,map_sub]
  unfold pairedResponse siblingResponse Paid.paired Paid.sibling
  rw [map_sub]
  constructor <;> module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRResponse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

