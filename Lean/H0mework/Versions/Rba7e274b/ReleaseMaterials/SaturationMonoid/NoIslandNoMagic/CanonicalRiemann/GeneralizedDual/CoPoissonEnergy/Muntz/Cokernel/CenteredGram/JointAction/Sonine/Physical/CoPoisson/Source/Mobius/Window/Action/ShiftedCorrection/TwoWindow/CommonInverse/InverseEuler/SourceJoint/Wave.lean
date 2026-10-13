import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.UpperSeed
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint
open Complex MeasureTheory Set Filter OriginalRieszSource
open scoped InnerProductSpace Topology
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing InverseEuler
local notation "q" => (1/4:ℝ)
namespace PaidWave
export OriginalRieszFinitePairing.CoPoisson (positionWave fourierWave positionCorrection fourierCorrection positionWave_inPa fourierWave_inPa)
end PaidWave

def upperSourceWave (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  upperSeedFactor h • (PaidWave.positionWave coordinate h+fourierL2 (PaidWave.fourierWave coordinate h))
def upperSourceCorrection (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  upperSourceWave coordinate h-upperSourceField coordinate h

theorem generated_upper_wave_inPa (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    upperSourceWave coordinate h∈burnolOriginalPaInL2 := by
  have actualFourier : fourierL2 (PaidWave.fourierWave coordinate h)∈burnolOriginalPaInL2 := by
    obtain ⟨physical,inPa,actual⟩:=Submodule.mem_map.mp (PaidWave.fourierWave_inPa coordinate h nonnegative bounded)
    refine Submodule.mem_map.mpr ⟨evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical,
      burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inPa,?_⟩
    change fourierL2 (physical:BurnolL2)=fourierL2 (PaidWave.fourierWave coordinate h)
    exact congrArg fourierL2 actual
  exact burnolOriginalPaInL2.smul_mem _
    (burnolOriginalPaInL2.add_mem (PaidWave.positionWave_inPa coordinate h nonnegative bounded) actualFourier)

theorem actual_upper_source_correction (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    upperSourceCorrection coordinate h=upperSeedFactor h •
      (PaidWave.positionCorrection coordinate h+fourierL2 (PaidWave.fourierCorrection coordinate h)) := by
  unfold upperSourceCorrection upperSourceWave
  rw [actual_upper_common_seed coordinate h nonnegative]
  unfold PaidWave.positionCorrection PaidWave.fourierCorrection
  rw [map_sub]
  module

private theorem pa_meanZero_read (value : BurnolL2) (member : value∈burnolOriginalPaInL2) :
    Constructor.zeroMean (burnolQuarterRestriction value)=0 ∧
    Constructor.zeroMean (burnolQuarterRestriction (fourierL2 value))=0 := by
  obtain ⟨physical,_,actual⟩:=Submodule.mem_map.mp member
  change (physical:BurnolL2)=value at actual
  have qualified : value∈evenBurnolClosedFace q := by
    rw [← actual]
    exact physical.property
  have position : burnolQuarterRestriction value∈intervalConstantLine q := qualified.1.1
  have fourier : burnolQuarterRestriction (fourierL2 value)∈intervalConstantLine q := qualified.1.2
  constructor
  · apply Subtype.ext
    change burnolQuarterMeanZeroProjection (burnolQuarterRestriction value)=0
    exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr position
  · apply Subtype.ext
    change burnolQuarterMeanZeroProjection (burnolQuarterRestriction (fourierL2 value))=0
    exact (burnolQuarterMeanZeroProjection_eq_zero_iff _).mpr fourier

private theorem pa_even (value : BurnolL2) (member : value∈burnolOriginalPaInL2) : reflectL2 value=value := by
  obtain ⟨physical,_,actual⟩:=Submodule.mem_map.mp member
  change (physical:BurnolL2)=value at actual
  rw [← actual]
  exact mem_evenL2ClosedFace_iff.mp physical.property.2
private theorem evenPart_fixed (value : BurnolL2) (even : reflectL2 value=value) :
    burnolAmbientEvenPart value=value := by
  unfold burnolAmbientEvenPart
  rw [even]
  module

theorem actual_upper_correction_projections (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    burnolAmbientMeanZeroPosition (upperSourceCorrection coordinate h)=-(sourceColumns coordinate h).2.1 ∧
    burnolAmbientMeanZeroFourier (upperSourceCorrection coordinate h)=-(sourceColumns coordinate h).2.2 := by
  have qualified:=generated_upper_wave_inPa coordinate h nonnegative bounded
  obtain ⟨wavePosition,waveFourier⟩:=pa_meanZero_read _ qualified
  obtain ⟨fieldPosition,fieldFourier⟩:=upper_source_both_restrictions coordinate h nonnegative
  have correctedEven : reflectL2 (upperSourceCorrection coordinate h)=upperSourceCorrection coordinate h := by
    unfold upperSourceCorrection
    rw [map_sub,pa_even _ qualified]
    congr 1
    exact burnolAmbientEvenPart_even _
  have corrected:=evenPart_fixed _ correctedEven
  constructor
  · change Constructor.zeroMean (burnolQuarterRestriction (burnolAmbientEvenPart (upperSourceCorrection coordinate h)))=_
    rw [corrected]
    unfold upperSourceCorrection
    rw [map_sub,map_sub,wavePosition,fieldPosition,zero_sub]
  · change Constructor.zeroMean (burnolQuarterRestriction (fourierL2 (burnolAmbientEvenPart (upperSourceCorrection coordinate h))))=_
    rw [corrected]
    unfold upperSourceCorrection
    rw [map_sub,map_sub,map_sub,waveFourier,fieldFourier,zero_sub]

theorem actual_upper_inverse_source_correction (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    burnolAmbientMeanZeroFirstCorrection (upperSourceCorrection coordinate h)=-(inverseCotest coordinate h).2 ∧
    burnolAmbientMeanZeroSecondCorrection (upperSourceCorrection coordinate h)=(inversePartner coordinate h).2 := by
  obtain ⟨position,fourier⟩:=actual_upper_correction_projections coordinate h nonnegative bounded
  have first : burnolAmbientMeanZeroFirstCorrection (upperSourceCorrection coordinate h)=-(inverseCotest coordinate h).2 := by
    unfold burnolAmbientMeanZeroFirstCorrection burnolMeanZeroBlockFirst burnolAmbientMeanZeroBlockRhs
    rw [position,fourier,map_neg]
    simp only [sub_neg_eq_add]
    change burnolMeanZeroBlockInverse (-(sourceColumns coordinate h).2.1+
      burnolMeanZeroTruncatedFourier (sourceColumns coordinate h).2.2)=_
    rw [show -(sourceColumns coordinate h).2.1+burnolMeanZeroTruncatedFourier (sourceColumns coordinate h).2.2=
      -((sourceColumns coordinate h).2.1-burnolMeanZeroTruncatedFourier (sourceColumns coordinate h).2.2) by module,map_neg]
    rfl
  constructor
  · exact first
  · unfold burnolAmbientMeanZeroSecondCorrection burnolMeanZeroBlockSecond burnolAmbientMeanZeroBlockRhs
    change burnolAmbientMeanZeroFourier (upperSourceCorrection coordinate h)-
      burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection (upperSourceCorrection coordinate h))=_
    rw [fourier,first,map_neg]
    unfold inversePartner
    module

end OriginalCommonInverseForcing.SourceJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
