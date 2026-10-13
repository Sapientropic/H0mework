import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRealCoordinateSourceUnit.MSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRealCoordinateSourceUnit
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local instance unweightedPrimitiveComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "K" => burnolCompletedMellinRieszVector
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "H" => OriginalKCommonGapKernelSource.actualCommonField
local notation "velocity" => OriginalKCommonGapKernelSource.actualCommonVelocity


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)




def actualUnweightedPrimitiveActionField (h:ℝ) (n:Nat):BurnolPaAmbientCarrier:=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)⁻¹ •
 OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveActionField observation nontrivial half h n
def actualUnweightedPrimitiveActionResidual (h:ℝ) (n:Nat):BurnolPaAmbientCarrier:=
 (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)⁻¹ •
 OriginalKPrimitivePhysicalSourceAction.actualPrimitiveActionResidual observation nontrivial half h n

/-- The literal original primitive action has its complete physical and outside source material restored after the original unit is generated. -/
theorem actual_original_unweighted_primitive_source_action (h:ℝ) (n:Nat):
 burnolEvenAmbientProjection (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)=
 actualUnweightedPrimitiveActionField observation nontrivial half h n+
 actualUnweightedPrimitiveActionResidual observation nontrivial half h n :=by
 have original:=OriginalKPrimitivePhysicalSourceAction.actual_original_primitive_finite_source_residual observation nontrivial half h n
 have whole:OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c •
  burnolEvenAmbientProjection (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)=
  OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveActionField observation nontrivial half h n+
  OriginalKPrimitivePhysicalSourceAction.actualPrimitiveActionResidual observation nontrivial half h n:=by
  linear_combination (norm:=module) original
 have source:=actual_original_response_kappa_ne_zero observation nontrivial half
 have acted:=congrArg (fun field:BurnolPaAmbientCarrier=>(OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)⁻¹ • field) whole
 unfold actualUnweightedPrimitiveActionField actualUnweightedPrimitiveActionResidual
 simpa only [smul_smul,inv_mul_cancel₀ source,one_smul,smul_add] using acted

def actualUnweightedPrimitivePairPrice (h:ℝ) (n:Nat):ℂ:=
 star (inner ℂ (K c+evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K c))
  (actualUnweightedPrimitiveActionField observation nontrivial half h n))
def actualUnweightedPrimitiveSiblingPrice (h:ℝ) (n:Nat):ℂ:=
 inner ℂ (K c-evenFaceFourierEquiv burnolUnscaledCommonGapRadius (K c))
  (actualUnweightedPrimitiveActionField observation nontrivial half h n)

/-- Both true primitive feet retain the exact scalar-star directions before the original character consumes the factor. -/
theorem actual_original_primitive_kappa_price_factors (h:ℝ) (n:Nat):
 OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitivePairPrice observation nontrivial half h n=
 star (OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)*actualUnweightedPrimitivePairPrice observation nontrivial half h n ∧
 OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveSiblingPrice observation nontrivial half h n=
 OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c*actualUnweightedPrimitiveSiblingPrice observation nontrivial half h n :=by
 have unit:=actual_original_response_kappa_ne_zero observation nontrivial half
 have field:OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c • actualUnweightedPrimitiveActionField observation nontrivial half h n=
  OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveActionField observation nontrivial half h n:=by
  unfold actualUnweightedPrimitiveActionField
  rw [smul_smul,mul_inv_cancel₀ unit,one_smul]
 unfold OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitivePairPrice
  OriginalKPrimitivePhysicalSourceAction.actualFinitePrimitiveSiblingPrice
 rw [←field]
 simp only [inner_smul_right,star_mul]
 unfold actualUnweightedPrimitivePairPrice actualUnweightedPrimitiveSiblingPrice
 constructor
 · ring
 · rfl

/-- The actual whole primitive source error keeps the original composed R/outside/action/P cost and the charged inverse-kappa fee. -/
theorem actual_original_unweighted_primitive_source_error (h:ℝ) (n:Nat):
 ‖actualUnweightedPrimitiveActionResidual observation nontrivial half h n‖≤
 ‖(OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c)⁻¹‖*
 OriginalKPrimitivePhysicalSourceAction.actualPrimitiveActionError observation nontrivial half h n :=by
 unfold actualUnweightedPrimitiveActionResidual
 rw [norm_smul]
 have source:=OriginalKPrimitivePhysicalSourceAction.actual_original_primitive_finite_source_error observation nontrivial half h n
 rw [OriginalKPrimitivePhysicalSourceAction.actual_original_primitive_finite_source_residual] at source
 exact mul_le_mul_of_nonneg_left source (norm_nonneg _)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRealCoordinateSourceUnit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
