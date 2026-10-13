import Lean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierKernelDependentRAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)





theorem actual_single_return_compact (coordinate : BurnolCompletedMellinCoordinate) :
 originalPhysicalCutoff q (actualWholeSingleReturn coordinate)=actualWholeSingleReturn coordinate := by
 change burnolRadiusZeroExtension q (burnolRadiusRestriction q
   (burnolRadiusZeroExtension q (actualSingleReturn coordinate : BurnolQuarterIntervalL2)))=_
 rw [burnolRadiusRestriction_zeroExtension]
 rfl

theorem actual_single_source_R_mean_price (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=(OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h : BurnolL2)
 inner ℂ (actualWholeSingleSource coordinate) (OriginalKFullSourceRResponse.Op.R observation nontrivial half material)=0 :=
 OriginalKFourierRegularMeanAction.actual_mean_zero_column_R_price _ _ _ h _

theorem actual_single_return_F_R_price (coordinate : BurnolCompletedMellinCoordinate)
 (material : BurnolPaAmbientCarrier) :
 inner ℂ (fourierL2 (actualWholeSingleReturn coordinate))
   (burnolDirectRightResolvent (coordinate.value/2) (material : BurnolL2))=
 OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate
   (actualWholeSingleReturn coordinate) material :=
 OriginalKCompactAdjointRSource.actual_compact_F_R_source_price _ _
   (actual_single_return_compact coordinate) (actual_single_source_even coordinate).2 material

/-- The receiver R field has only its generated position/even faces; source b is consumed using its own mean-zero inventory. -/
theorem actual_original_FK_response_single_source (h : ℝ) :
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let material:=OriginalKGapMeanRSourceAction.Full.meanDebt coordinate h
 let acted:=OriginalKFullSourceRResponse.Op.R observation nontrivial half (material : BurnolL2)
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) acted=
 inner ℂ (fourierL2 (burnolAmbientEvenPart (burnolAmbientCompletedMellinKernelFormula coordinate))) acted+
 OriginalKCompactAdjointRSource.actualCompactFourierResponsePrice coordinate
   (actualWholeSingleReturn coordinate) material := by
 dsimp only
 rw [actual_original_FK_single_source,inner_add_left,inner_sub_left,
   actual_single_source_R_mean_price,sub_zero]
 congr 1
 exact actual_single_return_F_R_price _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFourierKernelDependentRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
