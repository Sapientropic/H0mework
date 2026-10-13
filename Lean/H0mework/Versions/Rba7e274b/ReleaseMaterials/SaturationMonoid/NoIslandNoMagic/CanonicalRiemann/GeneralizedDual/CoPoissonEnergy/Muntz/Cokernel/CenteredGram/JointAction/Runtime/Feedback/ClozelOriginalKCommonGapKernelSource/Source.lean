import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKGapProjectionEulerSource.Consumer
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
namespace NativeK
export OriginalKConstantContactSourceAction.ConstantSource (value velocity strong_derivative)
end NativeK
namespace Gap
export OriginalKGapProjectionEulerSource (actualGapA actualGapBeta actual_gap_mean_Euler)
end Gap
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "K" => burnolCompletedMellinRieszVector
local notation "E" => OriginalRieszSource.GapEuler.euler
local notation "Ψ" => OriginalRieszSource.Response.Psi
local notation "FT" => (fourierCLM ℂ (TemperedDistribution ℝ ℂ))

def actualCommonDeterminant (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 (OriginalRieszSource.Kernel.A coordinate)^2-(OriginalRieszSource.Kernel.beta coordinate)^2
def actualCommonFirst (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 Gap.actualGapA*OriginalRieszSource.Kernel.A coordinate-Gap.actualGapBeta*OriginalRieszSource.Kernel.beta coordinate
def actualCommonSecond (coordinate : BurnolCompletedMellinCoordinate) : ℂ:=
 Gap.actualGapA*OriginalRieszSource.Kernel.beta coordinate-Gap.actualGapBeta*OriginalRieszSource.Kernel.A coordinate

def actualCommonField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2:=
 actualCommonFirst coordinate • (K coordinate:BurnolL2)+
 actualCommonSecond coordinate • fourierL2 (K coordinate:BurnolL2)-
 actualCommonDeterminant coordinate • (G:BurnolL2)
def actualCommonVelocity (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2:=
 (-(star coordinate.value-1/2)*actualCommonFirst coordinate) • (K coordinate:BurnolL2)+
 ((star coordinate.value-1/2)*actualCommonSecond coordinate) • fourierL2 (K coordinate:BurnolL2)+
 ((1/2:ℂ)*actualCommonDeterminant coordinate) • (G:BurnolL2)

private theorem actual_typed_Fourier_Euler (field : TemperedDistribution ℝ ℂ) :
 E (FT field)= -FT (E field):=
 OriginalRieszSource.GapEuler.euler_fourier field

/-- The opposite corrected K action consumes the paid whole source and genuine Fourier anti-Euler. -/
theorem actual_Fourier_K_corrected_Euler (coordinate : BurnolCompletedMellinCoordinate) :
 E (fourierL2 (NativeK.value coordinate):TemperedDistribution ℝ ℂ)=
 ((-fourierL2 (NativeK.velocity coordinate):BurnolL2):TemperedDistribution ℝ ℂ) :=by
 have field:FT (NativeK.value coordinate:TemperedDistribution ℝ ℂ)=
  (fourierL2 (NativeK.value coordinate):TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 have read:FT (NativeK.velocity coordinate:TemperedDistribution ℝ ℂ)=
  (fourierL2 (NativeK.velocity coordinate):TemperedDistribution ℝ ℂ):=Lp.fourier_toTemperedDistribution_eq _
 rw [←field,actual_typed_Fourier_Euler,
  OriginalRieszFinitePairing.CoPoisson.Ward.RieszEulerDomain.original_euler,read]
 exact ((Lp.toTemperedDistributionCLM ℂ volume 2).map_neg _).symm

theorem actual_Fourier_K_corrected_strong (coordinate : BurnolCompletedMellinCoordinate) :
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (fourierL2 (NativeK.value coordinate)))
  (-fourierL2 (NativeK.velocity coordinate)) 0 :=
 OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _ (actual_Fourier_K_corrected_Euler coordinate)

/-- Same source coefficients cancel both original seed contacts as a generated whole field. -/
theorem actual_common_corrected_field (coordinate : BurnolCompletedMellinCoordinate) :
 actualCommonFirst coordinate • NativeK.value coordinate+
 actualCommonSecond coordinate • fourierL2 (NativeK.value coordinate)-
 actualCommonDeterminant coordinate • OriginalKGapProjectionEulerSource.actualGapCorrected=
 actualCommonField coordinate :=by
 unfold NativeK.value OriginalKGapProjectionEulerSource.actualGapCorrected actualCommonField
 simp only [map_add,map_sub,map_smul]
 rw [fourierL2_fourierL2,OriginalKGapProjectionEulerSource.actual_seed_even]
 unfold actualCommonFirst actualCommonSecond actualCommonDeterminant
 module

/-- The complete shared source velocities cancel both U/V faces and both contact units. -/
theorem actual_common_corrected_velocity (coordinate : BurnolCompletedMellinCoordinate) :
 actualCommonFirst coordinate • NativeK.velocity coordinate+
 actualCommonSecond coordinate • (-fourierL2 (NativeK.velocity coordinate))-
 actualCommonDeterminant coordinate • OriginalKGapProjectionEulerSource.actualGapVelocity=
 actualCommonVelocity coordinate :=by
 unfold NativeK.velocity OriginalKGapProjectionEulerSource.actualGapVelocity actualCommonVelocity
 simp only [map_add,map_sub,map_smul]
 rw [fourierL2_fourierL2,fourierL2_fourierL2,fourierL2_fourierL2,
  OriginalRieszSource.Response.wholeU_reflection,OriginalRieszSource.Response.wholeV_reflection,
  OriginalKGapProjectionEulerSource.actual_seed_even]
 unfold actualCommonFirst actualCommonSecond actualCommonDeterminant
 module

/-- Actual common whole action is generated from the paid two corrected source actions, without a cancellation premise. -/
theorem actual_common_field_strong (coordinate : BurnolCompletedMellinCoordinate) :
 HasDerivAt (fun shift:ℝ=>burnolMultiplicativeDilation shift (actualCommonField coordinate))
  (actualCommonVelocity coordinate) 0 :=by
 have Ksource:=(NativeK.strong_derivative coordinate).const_smul (actualCommonFirst coordinate)
 have FKsource:=(actual_Fourier_K_corrected_strong coordinate).const_smul (actualCommonSecond coordinate)
 have Gsource:=OriginalKGapProjectionEulerSource.actual_gap_source_strong.const_smul (actualCommonDeterminant coordinate)
 have generated:=(Ksource.add FKsource).sub Gsource
 have acted:(fun shift:ℝ=>actualCommonFirst coordinate • burnolMultiplicativeDilation shift (NativeK.value coordinate)+
  actualCommonSecond coordinate • burnolMultiplicativeDilation shift (fourierL2 (NativeK.value coordinate))-
  actualCommonDeterminant coordinate • burnolMultiplicativeDilation shift OriginalKGapProjectionEulerSource.actualGapCorrected)=
  fun shift=>burnolMultiplicativeDilation shift (actualCommonField coordinate) :=by
  funext shift
  rw [←actual_common_corrected_field coordinate]
  simp only [map_sub,map_add,map_smul]
 change HasDerivAt (fun shift:ℝ=>actualCommonFirst coordinate • burnolMultiplicativeDilation shift (NativeK.value coordinate)+
  actualCommonSecond coordinate • burnolMultiplicativeDilation shift (fourierL2 (NativeK.value coordinate))-
  actualCommonDeterminant coordinate • burnolMultiplicativeDilation shift OriginalKGapProjectionEulerSource.actualGapCorrected) _ 0 at generated
 rw [acted,actual_common_corrected_velocity] at generated
 exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCommonGapKernelSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
