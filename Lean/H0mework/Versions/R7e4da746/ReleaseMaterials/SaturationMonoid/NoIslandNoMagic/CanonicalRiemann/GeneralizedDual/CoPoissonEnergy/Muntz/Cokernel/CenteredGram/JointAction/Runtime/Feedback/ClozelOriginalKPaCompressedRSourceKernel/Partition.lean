import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCompressedRSourceKernel.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCompressedRSourceKernel
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance paOperatorComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
abbrev PaSourceCarrier := OriginalKPaWindowCofinalSourceCompletion.PaSourceCarrier
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def sourceInclusion : PaSourceCarrier →L[ℂ] BurnolL2 :=
 BurnolPaAmbientCarrier.subtypeL.comp burnolCompactCoPoissonClosedRange.toSubmodule.subtypeL

def compressedR : PaSourceCarrier →L[ℂ] BurnolPaAmbientCarrier :=
 OriginalKCombCofinalPaAction.E.comp ((Op.R observation nontrivial half).comp sourceInclusion)

def physicalResponse (source : PaSourceCarrier) : BurnolPaAmbientCarrier :=
 burnolPaResolventPhysicalResponse observation nontrivial
  (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf
  (source : BurnolPaAmbientCarrier) source.property

def unitRankResponse (source : PaSourceCarrier) : BurnolPaAmbientCarrier :=
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (physicalResponse observation nontrivial half source)

theorem physical_source_read (source : PaSourceCarrier) :
 ((physicalResponse observation nontrivial half source : BurnolPaAmbientCarrier) : BurnolL2)=
 sourceR observation nontrivial half (sourceInclusion source) := by
 unfold sourceR sourceInclusion physicalResponse
 rw [OriginalKCombCofinalRAction.original_R_direct]
 rfl

theorem compressed_physical_source_read (source : PaSourceCarrier) :
 compressedR observation nontrivial half source=
 burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  (physicalResponse observation nontrivial half source) := by
 change burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  (burnolEvenAmbientProjection (sourceR observation nontrivial half (sourceInclusion source)))=_
 rw [←physical_source_read]
 rw [burnolEvenAmbientProjection,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem compressed_source_inner_read (source : PaSourceCarrier) :
 inner ℂ (compressedR observation nontrivial half source) (source : BurnolPaAmbientCarrier)=
 inner ℂ (sourceR observation nontrivial half (sourceInclusion source)) (sourceInclusion source) := by
 rw [compressed_physical_source_read]
 have generated := burnolCompactCoPoissonClosedRange.toSubmodule.inner_starProjection_left_eq_right
  (physicalResponse observation nontrivial half source) (source : BurnolPaAmbientCarrier)
 rw [burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_eq_self_iff.mpr source.property] at generated
 exact generated

theorem compressed_full_Gram (source : PaSourceCarrier) :
 ‖sourceR observation nontrivial half (sourceInclusion source)‖^2=
 ‖compressedR observation nontrivial half source‖^2+‖unitRankResponse observation nontrivial half source‖^2 := by
 rw [←physical_source_read,compressed_physical_source_read]
 exact Submodule.norm_sq_eq_add_norm_sq_starProjection
  (physicalResponse observation nontrivial half source) burnolCompactCoPoissonClosedRange.toSubmodule

theorem compressed_full_energy (source : PaSourceCarrier) :
 -(inner ℂ (compressedR observation nontrivial half source) (source : BurnolPaAmbientCarrier)).re=
 (observation.coordinate/2-1/4).re *
  (‖compressedR observation nontrivial half source‖^2+‖unitRankResponse observation nontrivial half source‖^2) := by
 rw [compressed_source_inner_read,source_R_energy,compressed_full_Gram]
 ring

theorem source_original_unit_rank (source : PaSourceCarrier) :
 unitRankResponse observation nontrivial half source=
 burnolPaResolventSourceCoefficient
  (burnolDivisionZeroCompletedMellinCoordinate observation
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf)
  (source : BurnolPaAmbientCarrier) •
 burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  (burnolZeroOwnedUnitTailState observation nontrivial
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).rightHalf) :=
 burnolPaResolventPhysicalResponse_Q _ _ _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCompressedRSourceKernel
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
