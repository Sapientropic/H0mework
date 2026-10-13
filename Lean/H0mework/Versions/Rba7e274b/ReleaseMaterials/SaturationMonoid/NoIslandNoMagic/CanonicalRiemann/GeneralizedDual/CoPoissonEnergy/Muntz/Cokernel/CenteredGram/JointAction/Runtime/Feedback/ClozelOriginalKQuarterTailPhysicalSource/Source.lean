import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFourierQuarterRplusAction.Consumer
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.UnitResponseRadius
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQuarterTailPhysicalSource
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

local instance quarterTailAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem physical_projection_reflection (material : BurnolL2) :
 burnolEvenAmbientProjection (reflectL2 material)=burnolEvenAmbientProjection material := by
 apply ext_inner_right ℂ
 intro physical
 have first:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
   |>.inner_orthogonalProjectionOnto_eq_of_mem_right physical (reflectL2 material)
 have second:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
   |>.inner_orthogonalProjectionOnto_eq_of_mem_right physical material
 have moved:=reflectL2.inner_map_map material (physical : BurnolL2)
 rw [mem_evenL2ClosedFace_iff.mp physical.property.2] at moved
 exact first.trans (moved.trans second.symm)

def actualStarSource (coordinate : BurnolCompletedMellinCoordinate) : BurnolCompletedMellinCoordinate :=
 ⟨star coordinate.value,
  by simpa only [Complex.star_def,Complex.conj_re] using coordinate.rightHalf,
  by simpa only [Complex.star_def,Complex.conj_re] using coordinate.belowOne⟩

/-- The actual normalized quarter source projects to its own dual Riesz face and the actual G mean vector. -/
theorem actual_quarter_tail_physical_source (coordinate : BurnolCompletedMellinCoordinate) :
 burnolEvenAmbientProjection (burnolRadiusNormalizedUnitTail coordinate q (by norm_num))=
 -(2:ℂ) • burnolCompletedMellinRieszVector (actualStarSource coordinate)+
 ((2:ℂ)*star (burnolMellinGapMoment (actualStarSource coordinate).value)) •
   OriginalRieszFiniteSynthesis.gapMeanVector := by
 let dual:=actualStarSource coordinate
 let tail:=burnolRadiusMellinTailKernelL2 q (by norm_num) dual.value dual.rightHalf
 have source:=burnolCompletedMellinRieszVector_eq_ambientProjection dual
 rw [burnolAmbientCompletedMellinRieszVector_eq_kernelFormula] at source
 change burnolCompletedMellinRieszVector dual=burnolEvenAmbientProjection
   (star (burnolMellinGapMoment dual.value) • burnolAmbientGapRieszVector q+tail) at source
 rw [map_add,map_smul] at source
 change burnolEvenAmbientProjection (-(tail+reflectL2 tail))=_
 rw [map_neg,map_add,physical_projection_reflection]
 change -(burnolEvenAmbientProjection tail+burnolEvenAmbientProjection tail)=_
 change burnolCompletedMellinRieszVector dual=
   star (burnolMellinGapMoment dual.value) • OriginalRieszFiniteSynthesis.gapMeanVector+
   burnolEvenAmbientProjection tail at source
 linear_combination (norm:=module) (2:ℂ) • source


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQuarterTailPhysicalSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
