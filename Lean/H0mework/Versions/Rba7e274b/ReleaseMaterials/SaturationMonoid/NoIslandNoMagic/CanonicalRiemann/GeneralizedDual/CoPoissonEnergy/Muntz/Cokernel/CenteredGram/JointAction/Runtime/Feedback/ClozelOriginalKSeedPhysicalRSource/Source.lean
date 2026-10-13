import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKStaticKernelSourceGramSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSeedPhysicalRSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance seedPhysicalSourceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local notation "P" => burnolEvenAmbientProjection
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "s" => OriginalKConstantContactSourceAction.ConstantSource.seed

/-- The already-generated original edge is projected through its paid ownphysical input reader. -/
theorem actual_original_edge_physical_projection (c : BurnolCompletedMellinCoordinate) :
 P (OriginalRieszFiniteSource.edgePrimitive c)=
 OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization c • K c :=by
 apply ext_inner_right ℂ
 intro physical
 have read:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
  |>.inner_orthogonalProjectionOnto_eq_of_mem_right physical (OriginalRieszFiniteSource.edgePrimitive c)
 change inner ℂ (P (OriginalRieszFiniteSource.edgePrimitive c)) physical=
  inner ℂ (OriginalRieszFiniteSource.edgePrimitive c) (physical:BurnolL2) at read
 rw [read,OriginalKConstantSeedWholeRAction.actual_edge_physical_input_price,inner_smul_left]
 rfl

def actualNativeSeedProjectedRField (c : BurnolCompletedMellinCoordinate) : BurnolPaAmbientCarrier:=
 (-2/(c.value-1):ℂ) •
 (OriginalKLiteralEdgeMeanSourcePrice.actualEdgeSourceNormalization (OriginalKQuarterTailPhysicalSource.actualStarSource c) •
  K (OriginalKQuarterTailPhysicalSource.actualStarSource c)+(1/2:ℂ) • G)

/-- The original complete seed R action produces its full dependent physical field before any source price. -/
theorem actual_original_seed_R_physical_field (c : BurnolCompletedMellinCoordinate) :
 P (burnolDirectRightResolvent (c.value/2) s)=actualNativeSeedProjectedRField c :=by
 rw [OriginalKConstantSeedWholeRAction.actual_original_R_seed_whole_field]
 unfold OriginalKConstantSeedWholeRAction.actualWholeSeedRField
 rw [map_smul,map_add,actual_original_edge_physical_projection,OriginalKCoupledPhysicalRFieldSource.actual_seed_projected_field]
 rfl

/-- The earlier actual compact source response consumes this same generated original seed field. -/
theorem actual_compact_seed_native_field (c : BurnolCompletedMellinCoordinate) :
 OriginalKCoupledPhysicalRFieldSource.actualCompactProjectedRField c s=actualNativeSeedProjectedRField c :=
 (OriginalKCoupledPhysicalRFieldSource.actual_original_seed_projected_R_fields c).1.symm.trans
  (actual_original_seed_R_physical_field c)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSeedPhysicalRSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
