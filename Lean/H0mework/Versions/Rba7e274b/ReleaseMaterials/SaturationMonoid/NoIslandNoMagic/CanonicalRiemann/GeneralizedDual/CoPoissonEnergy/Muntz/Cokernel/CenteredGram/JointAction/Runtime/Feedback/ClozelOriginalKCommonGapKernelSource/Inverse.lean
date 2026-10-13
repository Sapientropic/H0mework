import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCommonGapKernelSource.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCommonGapKernelSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "K" => burnolCompletedMellinRieszVector
local notation "E" => OriginalRieszSource.GapEuler.euler
local notation "FT" => (fourierCLM ℂ (TemperedDistribution ℝ ℂ))
/-- The public Euler law retains the same corrected whole action before Fourier transport. -/
theorem actual_common_field_Euler (coordinate : BurnolCompletedMellinCoordinate) :
 E (actualCommonField coordinate:TemperedDistribution ℝ ℂ)=
 (actualCommonVelocity coordinate:TemperedDistribution ℝ ℂ) :=by
 change E (Lp.toTemperedDistributionCLM ℂ volume 2 (actualCommonField coordinate))=
  Lp.toTemperedDistributionCLM ℂ volume 2 (actualCommonVelocity coordinate)
 rw [←actual_common_corrected_field,←actual_common_corrected_velocity]
 simp only [map_sub,map_add,map_smul,Lp.toTemperedDistributionCLM_apply]
 rw [OriginalRieszFinitePairing.CoPoisson.Ward.RieszEulerDomain.original_euler,
  actual_Fourier_K_corrected_Euler,OriginalKGapProjectionEulerSource.actual_gap_corrected_Euler]

def actualFourierCommonField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2:=fourierL2 (actualCommonField coordinate)
def actualFourierCommonVelocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2:= -fourierL2 (actualCommonVelocity coordinate)

theorem actual_Fourier_common_field_Euler (coordinate : BurnolCompletedMellinCoordinate) :
 E (actualFourierCommonField coordinate:TemperedDistribution ℝ ℂ)=
 (actualFourierCommonVelocity coordinate:TemperedDistribution ℝ ℂ) :=by
 have field:FT (actualCommonField coordinate:TemperedDistribution ℝ ℂ)=
  (fourierL2 (actualCommonField coordinate):TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 have read:FT (actualCommonVelocity coordinate:TemperedDistribution ℝ ℂ)=
  (fourierL2 (actualCommonVelocity coordinate):TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 have anti:E (FT (actualCommonField coordinate:TemperedDistribution ℝ ℂ))=
  -FT (E (actualCommonField coordinate:TemperedDistribution ℝ ℂ)):=OriginalRieszSource.GapEuler.euler_fourier _
 unfold actualFourierCommonField actualFourierCommonVelocity
 rw [←field,anti,actual_common_field_Euler,read]
 exact ((Lp.toTemperedDistributionCLM ℂ volume 2).map_neg _).symm

theorem actual_Fourier_common_field_strong (coordinate : BurnolCompletedMellinCoordinate) :
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (actualFourierCommonField coordinate))
  (actualFourierCommonVelocity coordinate) 0 :=
 OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _ (actual_Fourier_common_field_Euler coordinate)

theorem actual_Fourier_common_inventory (coordinate : BurnolCompletedMellinCoordinate) :
 actualFourierCommonField coordinate=
 actualCommonSecond coordinate • (K coordinate:BurnolL2)+
 actualCommonFirst coordinate • fourierL2 (K coordinate:BurnolL2)-
 actualCommonDeterminant coordinate • fourierL2 (G:BurnolL2) ∧
 actualFourierCommonVelocity coordinate=
 (-(star coordinate.value-1/2)*actualCommonSecond coordinate) • (K coordinate:BurnolL2)+
 ((star coordinate.value-1/2)*actualCommonFirst coordinate) • fourierL2 (K coordinate:BurnolL2)-
 ((1/2:ℂ)*actualCommonDeterminant coordinate) • fourierL2 (G:BurnolL2) :=by
 have even:reflectL2 (K coordinate:BurnolL2)=(K coordinate:BurnolL2):=
  mem_evenL2ClosedFace_iff.mp (K coordinate).property.2
 unfold actualFourierCommonField actualFourierCommonVelocity actualCommonField actualCommonVelocity
 simp only [map_sub,map_add,map_smul]
 rw [fourierL2_fourierL2,even]
 constructor <;> module

private theorem actual_source_R_inverse (coordinate : BurnolCompletedMellinCoordinate)
 (field velocity : BurnolL2)
 (source : HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift field) velocity 0) :
 field=burnolDirectRightResolvent (coordinate.value/2)
  ((-1/2:ℂ) • (velocity+(coordinate.value-1/2) • field)) :=by
 have right:1/4<(coordinate.value/2).re:=by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 apply burnolDirectRightResolvent_of_strongEquation _ right
 have reparam:HasDerivAt (fun time:ℝ=>-time/2) (-1/2:ℝ) 0:=by
  simpa only [Pi.neg_apply,neg_div,id_eq] using ((hasDerivAt_id (0:ℝ)).neg.div_const 2)
 have generated:=source.scomp_of_eq (0:ℝ) reparam (by norm_num)
 convert! generated using 1
 rw [←algebraMap_smul ℂ (-1/2:ℝ)]
 push_cast
 module

/-- The same complete H source produces the original weighted R G field, with no D qualification. -/
theorem actual_common_R_G_field (coordinate : BurnolCompletedMellinCoordinate) :
 ((coordinate.value-1)*actualCommonDeterminant coordinate) •
  burnolDirectRightResolvent (coordinate.value/2) (G:BurnolL2)=
 (2:ℂ) • actualCommonField coordinate+
 ((coordinate.value-star coordinate.value)*actualCommonFirst coordinate) •
  burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2)+
 ((coordinate.value+star coordinate.value-1)*actualCommonSecond coordinate) •
  burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)) :=by
 have source:=actual_source_R_inverse coordinate _ _ (actual_common_field_strong coordinate)
 have force:actualCommonVelocity coordinate+(coordinate.value-1/2) • actualCommonField coordinate=
  ((coordinate.value-star coordinate.value)*actualCommonFirst coordinate) • (K coordinate:BurnolL2)+
  ((coordinate.value+star coordinate.value-1)*actualCommonSecond coordinate) • fourierL2 (K coordinate:BurnolL2)-
  ((coordinate.value-1)*actualCommonDeterminant coordinate) • (G:BurnolL2) :=by
  unfold actualCommonVelocity actualCommonField
  module
 rw [force,burnolDirectRightResolvent_smul] at source
 change actualCommonField coordinate=(-1/2:ℂ) •
  (burnolDirectRightResolventCLM coordinate
   (((coordinate.value-star coordinate.value)*actualCommonFirst coordinate) • (K coordinate:BurnolL2)+
   ((coordinate.value+star coordinate.value-1)*actualCommonSecond coordinate) • fourierL2 (K coordinate:BurnolL2)-
   ((coordinate.value-1)*actualCommonDeterminant coordinate) • (G:BurnolL2))) at source
 rw [map_sub,map_add,map_smul,map_smul,map_smul] at source
 change actualCommonField coordinate=(-1/2:ℂ) •
  (((coordinate.value-star coordinate.value)*actualCommonFirst coordinate) • burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2)+
   ((coordinate.value+star coordinate.value-1)*actualCommonSecond coordinate) • burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2))-
   ((coordinate.value-1)*actualCommonDeterminant coordinate) • burnolDirectRightResolvent (coordinate.value/2) (G:BurnolL2)) at source
 linear_combination (norm:=module) (-2:ℂ) • source

/-- The opposite whole source produces its actual weighted R F G response. -/
theorem actual_common_R_FG_field (coordinate : BurnolCompletedMellinCoordinate) :
 (coordinate.value*actualCommonDeterminant coordinate) •
  burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (G:BurnolL2))=
 (2:ℂ) • actualFourierCommonField coordinate+
 ((coordinate.value-star coordinate.value)*actualCommonSecond coordinate) •
  burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2)+
 ((coordinate.value+star coordinate.value-1)*actualCommonFirst coordinate) •
  burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2)) :=by
 have source:=actual_source_R_inverse coordinate _ _ (actual_Fourier_common_field_strong coordinate)
 have inventory:=actual_Fourier_common_inventory coordinate
 have force:actualFourierCommonVelocity coordinate+(coordinate.value-1/2) • actualFourierCommonField coordinate=
  ((coordinate.value-star coordinate.value)*actualCommonSecond coordinate) • (K coordinate:BurnolL2)+
  ((coordinate.value+star coordinate.value-1)*actualCommonFirst coordinate) • fourierL2 (K coordinate:BurnolL2)-
  (coordinate.value*actualCommonDeterminant coordinate) • fourierL2 (G:BurnolL2) :=by
  rw [inventory.1,inventory.2]
  module
 rw [force,burnolDirectRightResolvent_smul] at source
 change actualFourierCommonField coordinate=(-1/2:ℂ) •
  (burnolDirectRightResolventCLM coordinate
   (((coordinate.value-star coordinate.value)*actualCommonSecond coordinate) • (K coordinate:BurnolL2)+
   ((coordinate.value+star coordinate.value-1)*actualCommonFirst coordinate) • fourierL2 (K coordinate:BurnolL2)-
   (coordinate.value*actualCommonDeterminant coordinate) • fourierL2 (G:BurnolL2))) at source
 rw [map_sub,map_add,map_smul,map_smul,map_smul] at source
 change actualFourierCommonField coordinate=(-1/2:ℂ) •
  (((coordinate.value-star coordinate.value)*actualCommonSecond coordinate) • burnolDirectRightResolvent (coordinate.value/2) (K coordinate:BurnolL2)+
   ((coordinate.value+star coordinate.value-1)*actualCommonFirst coordinate) • burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (K coordinate:BurnolL2))-
   (coordinate.value*actualCommonDeterminant coordinate) • burnolDirectRightResolvent (coordinate.value/2) (fourierL2 (G:BurnolL2))) at source
 linear_combination (norm:=module) (-2:ℂ) • source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCommonGapKernelSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
