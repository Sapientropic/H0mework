import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.FiniteUpdate

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint
open Complex MeasureTheory Set Filter OriginalRieszSource
open OriginalTwoWindowInverseForcing OriginalCommonInverseForcing
open scoped InnerProductSpace Topology

def upperCorrectionNativeUpdate (coordinate : BurnolCompletedMellinCoordinate) (h nextShift : ℝ) : BurnolL2 :=
  upperWaveNativeUpdate coordinate h nextShift-upperFieldNativeUpdate coordinate h nextShift

theorem actual_native_correction_update (coordinate : BurnolCompletedMellinCoordinate)
    (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) :
    upperSourceCorrection coordinate nextShift-upperSourceCorrection coordinate h=
      upperCorrectionNativeUpdate coordinate h nextShift := by
  obtain ⟨wave,field⟩:=actual_upper_material_update coordinate h nextShift nonnegative ordered
  unfold upperCorrectionNativeUpdate upperSourceCorrection
  rw [← wave,← field]
  module

theorem actual_field_update_projections (coordinate : BurnolCompletedMellinCoordinate)
    (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) :
    Constructor.zeroMean (burnolQuarterRestriction (upperFieldNativeUpdate coordinate h nextShift))=
        (sourceColumns coordinate nextShift).2.1-(sourceColumns coordinate h).2.1 ∧
    Constructor.zeroMean (burnolQuarterRestriction (fourierL2 (upperFieldNativeUpdate coordinate h nextShift)))=
        (sourceColumns coordinate nextShift).2.2-(sourceColumns coordinate h).2.2 := by
  have field:=(actual_upper_material_update coordinate h nextShift nonnegative ordered).2
  obtain ⟨oldPosition,oldFourier⟩:=upper_source_both_restrictions coordinate h nonnegative
  obtain ⟨newPosition,newFourier⟩:=upper_source_both_restrictions coordinate nextShift (nonnegative.trans ordered)
  rw [← field]
  simp only [map_sub]
  exact ⟨by rw [oldPosition,newPosition],by rw [oldFourier,newFourier]⟩

private theorem first_sub (left right : BurnolL2) :
    burnolAmbientMeanZeroFirstCorrection (left-right)=
      burnolAmbientMeanZeroFirstCorrection left-burnolAmbientMeanZeroFirstCorrection right := by
  unfold burnolAmbientMeanZeroFirstCorrection burnolMeanZeroBlockFirst burnolAmbientMeanZeroBlockRhs
    burnolAmbientMeanZeroPosition burnolAmbientMeanZeroFourier burnolAmbientEvenPart
  simp only [map_sub,map_add,map_smul]
  module

private theorem second_sub (left right : BurnolL2) :
    burnolAmbientMeanZeroSecondCorrection (left-right)=
      burnolAmbientMeanZeroSecondCorrection left-burnolAmbientMeanZeroSecondCorrection right := by
  unfold burnolAmbientMeanZeroSecondCorrection burnolMeanZeroBlockSecond burnolAmbientMeanZeroBlockRhs
  change burnolAmbientMeanZeroFourier (left-right)-
      burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection (left-right))=
    (burnolAmbientMeanZeroFourier left-
      burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection left))-
    (burnolAmbientMeanZeroFourier right-
      burnolMeanZeroTruncatedFourier (burnolAmbientMeanZeroFirstCorrection right))
  rw [first_sub]
  unfold burnolAmbientMeanZeroFourier burnolAmbientEvenPart
  simp only [map_sub,map_add,map_smul]
  module

theorem actual_inverse_correction_update (coordinate : BurnolCompletedMellinCoordinate)
    (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    burnolAmbientMeanZeroFirstCorrection (upperCorrectionNativeUpdate coordinate h nextShift)=
        -((inverseCotest coordinate nextShift).2-(inverseCotest coordinate h).2) ∧
    burnolAmbientMeanZeroSecondCorrection (upperCorrectionNativeUpdate coordinate h nextShift)=
        (inversePartner coordinate nextShift).2-(inversePartner coordinate h).2 := by
  obtain ⟨oldFirst,oldSecond⟩:=actual_upper_inverse_source_correction coordinate h nonnegative (ordered.trans bounded)
  obtain ⟨newFirst,newSecond⟩:=actual_upper_inverse_source_correction coordinate nextShift (nonnegative.trans ordered) bounded
  rw [← actual_native_correction_update coordinate h nextShift nonnegative ordered,first_sub,second_sub]
  exact ⟨by rw [oldFirst,newFirst];module,by rw [oldSecond,newSecond]⟩

theorem actual_wave_update_inPa (coordinate : BurnolCompletedMellinCoordinate)
    (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    upperWaveNativeUpdate coordinate h nextShift∈burnolOriginalPaInL2 := by
  rw [← (actual_upper_material_update coordinate h nextShift nonnegative ordered).1]
  exact burnolOriginalPaInL2.sub_mem
    (generated_upper_wave_inPa coordinate nextShift (nonnegative.trans ordered) bounded)
    (generated_upper_wave_inPa coordinate h nonnegative (ordered.trans bounded))

theorem actual_wave_update_original_K_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h nextShift : ℝ) (nonnegative : 0≤h)
    (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    inner ℂ (upperWaveNativeUpdate coordinate h nextShift) (burnolCompletedMellinRieszVector coordinate:BurnolL2)=0 := by
  obtain ⟨physical,inPa,actual⟩:=Submodule.mem_map.mp
    (actual_wave_update_inPa coordinate h nextShift nonnegative ordered bounded)
  have orthogonal:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
  have read:=(burnolCompactCoPoissonClosedRange.toSubmodule.mem_orthogonal _).mp orthogonal physical inPa
  change inner ℂ (physical:BurnolL2) (burnolCompletedMellinRieszVector coordinate:BurnolL2)=0 at read
  change (physical:BurnolL2)=upperWaveNativeUpdate coordinate h nextShift at actual
  rwa [actual] at read

theorem actual_field_update_original_K_price (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h nextShift : ℝ) (nonnegative : 0≤h)
    (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    inner ℂ (upperFieldNativeUpdate coordinate h nextShift) (burnolCompletedMellinRieszVector coordinate:BurnolL2)=
      -inner ℂ (upperCorrectionNativeUpdate coordinate h nextShift) (burnolCompletedMellinRieszVector coordinate:BurnolL2) := by
  unfold upperCorrectionNativeUpdate
  rw [inner_sub_left,actual_wave_update_original_K_read coordinate zero h nextShift nonnegative ordered bounded]
  ring

end OriginalCommonInverseForcing.SourceJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
