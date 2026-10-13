import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Support
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.JointFlux.Reverse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalJointFluxSource
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology BigOperators

 theorem actual_forward_source_vector (z : ℂ) (right : 1/4<z.re) (value : BurnolL2) :
    Paid.actualFlux z value= -Paid.outerCut (burnolDirectRightResolvent z (Paid.M value))+
      generatedMeanCoefficient z value • Paid.box 4 := by
  rw [actual_forward_flux_source z right value,generated_mean_response_source z right value]

 theorem actual_defect_flux_source (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) :
    Paid.defectFlux (coordinate.value/2) value=Paid.reverseRankSource coordinate (fourierL2 value)+
      burnolTateReciprocalL2 (Paid.outerCut (burnolDirectRightResolvent (coordinate.value/2) (Paid.M value)))-
      generatedMeanCoefficient (coordinate.value/2) value • burnolTateReciprocalL2 (Paid.box 4) := by
  have right : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  have fourierEven : reflectL2 (fourierL2 value)=fourierL2 value := by
    rw [← fourierL2_reflectL2_commute,even]
  unfold Paid.defectFlux
  rw [actual_reverse_flux_source coordinate (fourierL2 value) fourierEven,actual_forward_source_vector _ right,
    map_add,map_neg,map_smul]
  module

 def tateBoxInversePrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
    (OriginalPrimitiveRankBalance.inverseAction (coordinate.value/2) (star coordinate.value/2)
      (burnolTateReciprocalL2 (Paid.box 4)))

def generatedInverseFluxPrice (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) : ℂ :=
  OriginalPrimitiveRankBalance.twoMomentPrice coordinate (fourierL2 value) h-
    generatedMeanCoefficient (coordinate.value/2) value*tateBoxInversePrice coordinate h

theorem actual_inverse_defect_flux_price (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) (h : ℝ) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn coordinate h)
      (OriginalPrimitiveRankBalance.inverseAction (coordinate.value/2) (star coordinate.value/2)
        (Paid.defectFlux (coordinate.value/2) value))=generatedInverseFluxPrice coordinate value h := by
  have right : 1/4<(star coordinate.value/2).re := by rw [Complex.div_re];norm_num [Complex.star_def];linarith [coordinate.rightHalf]
  rw [actual_defect_flux_source coordinate value even,OriginalPrimitiveRankBalance.inverse_source_sub _ _ right,
    OriginalPrimitiveRankBalance.inverse_source_add _ _ right,OriginalPrimitiveRankBalance.inverse_source_smul _ _ _ right,
    inner_sub_right,inner_add_right,inner_smul_right,OriginalPrimitiveRankBalance.reverse_source_two_moments,
    paired_inverse_tate_outer_zero coordinate _ _ _ right,add_zero]
  rfl

 def generatedDirectFluxPrice (columnCoordinate parameter : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) : ℂ :=
  inner ℂ (OriginalPrimitiveRankBalance.pairedColumn columnCoordinate h) (Paid.reverseRankSource parameter (fourierL2 value))-
    generatedMeanCoefficient (parameter.value/2) value*inner ℂ (OriginalPrimitiveRankBalance.pairedColumn columnCoordinate h)
      (burnolTateReciprocalL2 (Paid.box 4))

theorem actual_direct_defect_flux_price (columnCoordinate parameter : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (even : reflectL2 value=value) (h : ℝ) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn columnCoordinate h) (Paid.defectFlux (parameter.value/2) value)=
      generatedDirectFluxPrice columnCoordinate parameter value h := by
  rw [actual_defect_flux_source parameter value even,inner_sub_right,inner_add_right,inner_smul_right,
    paired_tate_outer_zero,add_zero]
  rfl
end OriginalJointFluxSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
