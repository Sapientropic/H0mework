import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierForcingCofinalAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPrimitivePhysicalSourceAction
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "Fphysical" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local instance primitivePhysicalSourceComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete


local notation "P" => burnolEvenAmbientProjection
namespace Return
export OriginalKSourceScaledMaximalResponse.Return (sourceA primitiveSource original_return_source_equation)
end Return
namespace Physical
export OriginalKCoupledPhysicalRFieldSource (actualResponseKappa actual_original_weighted_R_fields)
export OriginalKSeedPhysicalRSource (actualSeedNativeWeightedKField actual_two_seed_native_weighted_fields)
end Physical

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)

def actualWeightedPrimitivePhysicalSource:BurnolPaAmbientCarrier:=
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 Return.sourceA observation • Physical.actualSeedNativeWeightedKField c-
 Physical.actualResponseKappa c • K c

/-- The actual original returned primitive is projected after its true R source action; the existing whole kappa field generates its same dependent face. -/
theorem actual_original_weighted_primitive_physical_source:
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 Physical.actualResponseKappa c • P (Return.primitiveSource observation nontrivial half)=
 actualWeightedPrimitivePhysicalSource observation nontrivial half :=by
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have original:=Return.original_return_source_equation observation nontrivial half
 have face:=congrArg P original
 rw [map_sub,map_smul,OriginalKCombCofinalRAction.original_R_direct] at face
 have kernel:P (K c:BurnolL2)=K c:=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self _
 change Return.sourceA observation • P (burnolDirectRightResolvent (c.value/2) (K c:BurnolL2))-P (K c:BurnolL2)=
  P (Return.primitiveSource observation nontrivial half) at face
 rw [kernel] at face
 have generated:=congrArg (fun field:BurnolPaAmbientCarrier=>Physical.actualResponseKappa c • field) face
 rw [smul_sub,smul_comm (Physical.actualResponseKappa c),(Physical.actual_original_weighted_R_fields c).1,
  (Physical.actual_two_seed_native_weighted_fields c).1] at generated
 exact generated.symm

/-- The original actual finite action retains its full outside primitive stock; no projection-dilation exchange is supplied. -/
def actualPrimitiveOutsideSource:BurnolL2:=
 OriginalKPairedResponseGramAction.originalOutside (Return.primitiveSource observation nontrivial half)

def actualWeightedPrimitiveFiniteSource (h:ℝ):BurnolPaAmbientCarrier:=
 P (OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h
   (actualWeightedPrimitivePhysicalSource observation nontrivial half:BurnolL2))+
 Physical.actualResponseKappa (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) •
  P (OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h
   (actualPrimitiveOutsideSource observation nontrivial half))

/-- The actual primitive finite action consumes its same whole physical field and exact outside material, preserving the original full carrier. -/
theorem actual_original_weighted_primitive_finite_source (h:ℝ):
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 Physical.actualResponseKappa c • P (OriginalKSourceScaledMaximalResponse.primitiveFiniteAction observation nontrivial half h)=
 actualWeightedPrimitiveFiniteSource observation nontrivial half h :=by
 let c:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 have source:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal
  (Return.primitiveSource observation nontrivial half)
 change (P (Return.primitiveSource observation nontrivial half):BurnolL2)+
  actualPrimitiveOutsideSource observation nontrivial half=Return.primitiveSource observation nontrivial half at source
 have face:=actual_original_weighted_primitive_physical_source observation nontrivial half
 change Physical.actualResponseKappa c • P (Return.primitiveSource observation nontrivial half)=
  actualWeightedPrimitivePhysicalSource observation nontrivial half at face
 have rawface:=congrArg (fun field:BurnolPaAmbientCarrier=>(field:BurnolL2)) face
 change Physical.actualResponseKappa c • (P (Return.primitiveSource observation nontrivial half):BurnolL2)=
  (actualWeightedPrimitivePhysicalSource observation nontrivial half:BurnolL2) at rawface
 change Physical.actualResponseKappa c • P (OriginalKSourceScaledMaximalResponse.literalFiniteAction observation h
  (Return.primitiveSource observation nontrivial half))=_
 rw [←source,map_add,map_add,smul_add,←map_smul,←map_smul,rawface]
 rfl

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPrimitivePhysicalSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
