import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompleteMResidualSource.Source
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
local instance completeMResidualInventoryComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "U" => OriginalRieszSource.Response.wholeU
local notation "V" => OriginalRieszSource.Response.wholeV
local notation "q" => (1/4:ℝ)

def actualMeanZeroCompactRField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier :=
 -(2:ℂ) • K (OriginalKQuarterTailPhysicalSource.actualStarSource c)+
 ((1/2:ℂ)*((((2*q:ℝ):ℂ)*(q:ℂ)^(-c.value))/(c.value/2-1/2))+
  (2:ℂ)*star (burnolMellinGapMoment (OriginalKQuarterTailPhysicalSource.actualStarSource c).value)) • G

/-- Existing whole compact R action and the actual mean-zero source generate one complete field direction; its original Tate coefficient is retained. -/
theorem actual_mean_zero_compact_R_field (c : BurnolCompletedMellinCoordinate) (source : BurnolL2)
 (meanZero : FiniteMobiusResolventFlux.actualMean source=0) :
 OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c source=
 OriginalKCompactAdjointRSource.actualCompactTailCoefficient c source • actualMeanZeroCompactRField c :=by
 unfold OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField actualMeanZeroCompactRField
 rw [meanZero,sub_zero]
 simp only [smul_add,smul_smul]
 module

/-- Both literal original source responses preserve their actual coefficient on the same generated field direction. -/
theorem actual_original_UV_compact_R_inventory (c : BurnolCompletedMellinCoordinate) :
 OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c U=
  OriginalKCompactAdjointRSource.actualCompactTailCoefficient c U • actualMeanZeroCompactRField c ∧
 OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c V=
  OriginalKCompactAdjointRSource.actualCompactTailCoefficient c V • actualMeanZeroCompactRField c :=
 ⟨actual_mean_zero_compact_R_field c U (OriginalKSectorEulerMixedSource.actual_quarter_mean_zero_source OriginalRieszSource.Response.u),
  actual_mean_zero_compact_R_field c V (OriginalKSectorEulerMixedSource.actual_quarter_mean_zero_source OriginalRieszSource.Response.v)⟩

/-- The native seed update consumes its actual source unit after the whole R field has been generated, removing the entire contact G face. -/
theorem actual_native_seed_contact_field (c : BurnolCompletedMellinCoordinate) :
 (1-c.value) • OriginalKSeedPhysicalRSource.actualNativeSeedProjectedRField c-G=
 (2*OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c)) •
  K (OriginalKQuarterTailPhysicalSource.actualStarSource c) :=by
 have unit:=(OriginalKCommonGapKernelSource.actual_common_source_units c).2
 unfold OriginalKSeedPhysicalRSource.actualNativeSeedProjectedRField
 have coefficient:(1-c.value)*(-2/(c.value-1):ℂ)=2 :=by
  field_simp
  ring
 simp only [smul_smul]
 rw [coefficient]
 module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCompleteMResidualSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
