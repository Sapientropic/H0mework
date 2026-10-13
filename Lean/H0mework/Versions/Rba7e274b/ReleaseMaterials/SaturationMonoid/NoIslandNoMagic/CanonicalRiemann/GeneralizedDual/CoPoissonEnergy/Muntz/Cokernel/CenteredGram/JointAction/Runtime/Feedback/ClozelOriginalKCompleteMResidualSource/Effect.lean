import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteMResidualSource.Inventory
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
local instance completeMResidualEffectComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV

def actualPositionMSourceMass (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 (∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.positionSeed c h x)*(c.value-1)⁻¹
def actualFourierMSourceMass (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 (∫ x:ℝ,OriginalRieszFinitePairing.CoPoisson.fourierSeed c h x)*c.value⁻¹

def actualMSourceVCoefficient (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 actualPositionMSourceMass c h*OriginalKGapProjectionEulerSource.actualGapA-
 actualFourierMSourceMass c h*OriginalKGapProjectionEulerSource.actualGapBeta
def actualMSourceUCoefficient (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 -actualPositionMSourceMass c h*OriginalKGapProjectionEulerSource.actualGapBeta+
 actualFourierMSourceMass c h*OriginalKGapProjectionEulerSource.actualGapA

def actualMSourceTateInventory (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
 actualMSourceUCoefficient c h*OriginalKCompactAdjointRSource.actualCompactTailCoefficient c U+
 actualMSourceVCoefficient c h*OriginalKCompactAdjointRSource.actualCompactTailCoefficient c V

def actualCompleteMSourceInventoryField (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolPaAmbientCarrier :=
 actualMSourceTateInventory c h • actualMeanZeroCompactRField c-
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)*actualMSourceVCoefficient c h) •
  K (OriginalKQuarterTailPhysicalSource.actualStarSource c)-
 (2*actualPositionMSourceMass c h) • G-(2*actualFourierMSourceMass c h) • Fphysical G

/-- The complete original M residual consumes the generated native seed contact and both actual source coefficients on their same whole field. -/
theorem actual_complete_M_source_inventory (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
 actualCompleteMResidualField c h=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) •
  actualCompleteMSourceInventoryField c h :=by
 unfold actualCompleteMResidualField actualPlusResidualForcing actualMinusResidualForcing
 have seed:=actual_native_seed_contact_field c
 have up:=(actual_original_UV_compact_R_inventory c).1
 have vp:=(actual_original_UV_compact_R_inventory c).2
 rw [up,vp]
 have plusContact:-(OriginalKCompactAdjointRSource.actualCompactTailCoefficient c U • actualMeanZeroCompactRField c+
    OriginalKCompactAdjointRSource.actualCompactTailCoefficient c V • actualMeanZeroCompactRField c)+
  (1-c.value) • Prior.actualNativeSeedProjectedRField c-G=
  -(OriginalKCompactAdjointRSource.actualCompactTailCoefficient c U • actualMeanZeroCompactRField c+
    OriginalKCompactAdjointRSource.actualCompactTailCoefficient c V • actualMeanZeroCompactRField c)+
  (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)) •
   K (OriginalKQuarterTailPhysicalSource.actualStarSource c) :=by
  calc
   _=-(OriginalKCompactAdjointRSource.actualCompactTailCoefficient c U • actualMeanZeroCompactRField c+
    OriginalKCompactAdjointRSource.actualCompactTailCoefficient c V • actualMeanZeroCompactRField c)+
    ((1-c.value) • Prior.actualNativeSeedProjectedRField c-G) :=by module
   _=_ :=by rw [seed]

 have minusContact:OriginalKCompactAdjointRSource.actualCompactTailCoefficient c U • actualMeanZeroCompactRField c-
    OriginalKCompactAdjointRSource.actualCompactTailCoefficient c V • actualMeanZeroCompactRField c+
  (1-c.value) • Prior.actualNativeSeedProjectedRField c-G=
  OriginalKCompactAdjointRSource.actualCompactTailCoefficient c U • actualMeanZeroCompactRField c-
    OriginalKCompactAdjointRSource.actualCompactTailCoefficient c V • actualMeanZeroCompactRField c+
  (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)) •
   K (OriginalKQuarterTailPhysicalSource.actualStarSource c) :=by
  calc
   _=OriginalKCompactAdjointRSource.actualCompactTailCoefficient c U • actualMeanZeroCompactRField c-
    OriginalKCompactAdjointRSource.actualCompactTailCoefficient c V • actualMeanZeroCompactRField c+
    ((1-c.value) • Prior.actualNativeSeedProjectedRField c-G) :=by module
   _=_ :=by rw [seed]

 rw [plusContact,minusContact]
 unfold actualCompleteMSourceInventoryField actualMSourceTateInventory actualMSourceUCoefficient actualMSourceVCoefficient
  actualPositionMSourceMass actualFourierMSourceMass
  OriginalKCommonGapKernelSource.actualCommonDeterminant OriginalKFourierSectorRGramSource.actualFirstRWeight OriginalKFourierSectorRGramSource.actualSecondRWeight
  OriginalKCommonGapKernelSource.actualCommonFirst OriginalKCommonGapKernelSource.actualCommonSecond
 rw [OriginalKCoupledPhysicalRFieldSource.actual_response_kappa_source]
 module

/-- The original complete R action writes back its whole actual source inventory after the generated static-field elimination. -/
theorem actual_original_complete_M_inventory_action (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) •
  burnolEvenAmbientProjection (burnolDirectRightResolvent (c.value/2) (OriginalKGapMeanRSourceAction.Full.meanDebt c h:BurnolL2))=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*OriginalKCommonGapKernelSource.actualCommonDeterminant c) •
  actualCompleteMSourceInventoryField c h :=by
 rw [OriginalKCoupledPhysicalRFieldSource.actual_complete_weighted_M_source_field,
  OriginalKSeedPhysicalRSource.actual_complete_seed_native_M_field,actual_complete_M_residual_source,actual_complete_M_source_inventory]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMResidualSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
