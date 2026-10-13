import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSeedPhysicalRSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMResidualSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance completeMResidualSourceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


namespace Prior
export OriginalKSeedPhysicalRSource (actualNativeSeedProjectedRField actualPlusSeedNativeProjectedUpdate actualMinusSeedNativeProjectedUpdate actualSeedNativeWeightedKField actualSeedNativeWeightedFKField actualSeedNativeWholeMField)
end Prior
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV

def actualPlusResidualForcing (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
 (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c) •
 (-(OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c U+
     OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c V)+
 (1-c.value) • Prior.actualNativeSeedProjectedRField c-G)
def actualMinusResidualForcing (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
 (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c) •
 (OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c U-
     OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c V+
 (1-c.value) • Prior.actualNativeSeedProjectedRField c-G)

/-- The complete actual source update exposes its residual forcing after both true contact fields are consumed. -/
theorem actual_two_complete_residual_updates (c : BurnolCompletedMellinCoordinate) :
 Prior.actualPlusSeedNativeProjectedUpdate c=(2:ℂ) • OriginalKFourierSectorRGramSource.actualPlusSource c+actualPlusResidualForcing c ∧
 Prior.actualMinusSeedNativeProjectedUpdate c=(2:ℂ) • OriginalKFourierSectorRGramSource.actualMinusSource c+actualMinusResidualForcing c :=by
 unfold Prior.actualPlusSeedNativeProjectedUpdate Prior.actualMinusSeedNativeProjectedUpdate actualPlusResidualForcing actualMinusResidualForcing
 constructor <;> module

def actualCompleteMResidualField (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolPaAmbientCarrier :=
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c •
  (-((∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed c h x)*((c.value-1)⁻¹*2)*OriginalKCommonGapKernelSource.actualCommonDeterminant c) • G-
   ((∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed c h x)*(c.value⁻¹*2)*OriginalKCommonGapKernelSource.actualCommonDeterminant c) • Fphysical G)+
 (OriginalKFourierSectorRGramSource.actualFirstRWeight c h*((star c.value+c.value-1)/2)) •
  (actualPlusResidualForcing c+actualMinusResidualForcing c)+
 (OriginalKFourierSectorRGramSource.actualSecondRWeight c h*((star c.value-c.value)/2)) •
  (actualMinusResidualForcing c-actualPlusResidualForcing c)

/-- Same complete M input and actual coupled source updates generate elimination of the static K/F K fields, with no cancellation supplied at the source mouth. -/
theorem actual_complete_M_residual_source (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
 Prior.actualSeedNativeWholeMField c h=actualCompleteMResidualField c h :=by
 have updates:=actual_two_complete_residual_updates c
 unfold Prior.actualSeedNativeWholeMField Prior.actualSeedNativeWeightedKField Prior.actualSeedNativeWeightedFKField
 rw [updates.1,updates.2]
 have plus:OriginalKFourierSectorRGramSource.actualPlusSource c=K c+Fphysical (K c):=rfl
 have minus:OriginalKFourierSectorRGramSource.actualMinusSource c=K c-Fphysical (K c):=rfl
 rw [plus,minus]
 rw [OriginalKCoupledPhysicalRFieldSource.actual_response_kappa_source]
 unfold OriginalKCoupledPhysicalRFieldSource.actualProjectedMInputField
  OriginalKCoupledPhysicalRFieldSource.actualProjectedCommonField OriginalKCoupledPhysicalRFieldSource.actualProjectedFourierCommonField
  actualCompleteMResidualField
  OriginalKFourierSectorRGramSource.actualFirstRWeight OriginalKFourierSectorRGramSource.actualSecondRWeight
 rw [OriginalKCoupledPhysicalRFieldSource.actual_response_kappa_source]
 module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMResidualSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
