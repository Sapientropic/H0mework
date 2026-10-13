import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.WaveAction

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint
open Complex MeasureTheory Set Filter
open OriginalRieszFiniteSource OriginalRieszFiniteColumns
open scoped InnerProductSpace Topology
namespace Higher
export OriginalRieszFinitePairing.CoPoisson.Ward.Correction
  (higherCountingRaw position_correction_higher_pairing fourier_correction_higher_pairing)
end Higher

def upperHigherSourcePrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  star (upperSeedFactor h)*
    ((∫ x : ℝ,inner ℂ (Higher.higherCountingRaw (NativeWeight.bandLower h) 4
      (NativeWeight.positionWeight coordinate h) x) ((burnolCompletedMellinRieszVector coordinate:BurnolL2) x))+
      ∫ x : ℝ,inner ℂ (Higher.higherCountingRaw (NativeWeight.bandLower h) 4
        (NativeWeight.fourierWeight coordinate h) x) (fourierL2 (burnolCompletedMellinRieszVector coordinate:BurnolL2) x))

theorem actual_upper_correction_higher_price (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    inner ℂ (upperSourceCorrection coordinate h) (burnolCompletedMellinRieszVector coordinate:BurnolL2)=
      upperHigherSourcePrice coordinate h := by
  have twice:fourierL2 (fourierL2 (burnolCompletedMellinRieszVector coordinate:BurnolL2))=
      (burnolCompletedMellinRieszVector coordinate:BurnolL2) := by
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector coordinate).property.2
  have paired:=fourierL2.inner_map_map (PaidWave.fourierCorrection coordinate h)
    (fourierL2 (burnolCompletedMellinRieszVector coordinate:BurnolL2))
  rw [twice] at paired
  rw [actual_upper_source_correction coordinate h nonnegative,inner_smul_left,inner_add_left,paired,
    Higher.position_correction_higher_pairing coordinate h nonnegative,
    Higher.fourier_correction_higher_pairing coordinate h nonnegative]
  rfl

theorem actual_correction_update_higher_price (coordinate : BurnolCompletedMellinCoordinate)
    (h nextShift : ℝ) (nonnegative : 0≤h) (ordered : h≤nextShift) :
    inner ℂ (upperCorrectionNativeUpdate coordinate h nextShift) (burnolCompletedMellinRieszVector coordinate:BurnolL2)=
      upperHigherSourcePrice coordinate nextShift-upperHigherSourcePrice coordinate h := by
  rw [← actual_native_correction_update coordinate h nextShift nonnegative ordered,inner_sub_left,
    actual_upper_correction_higher_price coordinate nextShift (nonnegative.trans ordered),
    actual_upper_correction_higher_price coordinate h nonnegative]

theorem actual_field_update_higher_price (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h nextShift : ℝ) (nonnegative : 0≤h)
    (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    inner ℂ (upperFieldNativeUpdate coordinate h nextShift) (burnolCompletedMellinRieszVector coordinate:BurnolL2)=
      -(upperHigherSourcePrice coordinate nextShift-upperHigherSourcePrice coordinate h) := by
  rw [actual_field_update_original_K_price coordinate zero h nextShift nonnegative ordered bounded,
    actual_correction_update_higher_price coordinate h nextShift nonnegative ordered]

def upperUpdateJointSourcePrice (coordinate : BurnolCompletedMellinCoordinate) (h nextShift : ℝ) : ℂ :=
  star (upperSeedFactor nextShift)*upperSeedEnergy coordinate nextShift-
    star (upperSeedFactor h)*
      (inner ℂ (Seed.positionSeed coordinate h) (positionColumn coordinate nextShift)+
        inner ℂ (Seed.fourierSeed coordinate h) (fourierColumn coordinate nextShift)+
        inner ℂ (Seed.positionSeed coordinate h) (positionColumn coordinate (-nextShift))+
        inner ℂ (Seed.fourierSeed coordinate h) (fourierColumn coordinate (-nextShift)))

theorem actual_update_original_K_joint_action (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h nextShift : ℝ) (nonnegative : 0≤h)
    (ordered : h≤nextShift) (bounded : nextShift≤Real.log 2) :
    inner ℂ (upperWaveNativeUpdate coordinate h nextShift)
      (burnolMultiplicativeDilation nextShift (burnolCompletedMellinRieszVector coordinate:BurnolL2)+
        burnolMultiplicativeDilation (-nextShift) (burnolCompletedMellinRieszVector coordinate:BurnolL2))=
      upperUpdateJointSourcePrice coordinate h nextShift := by
  have positiveBound:|nextShift|≤Real.log 2:=by rwa [abs_of_nonneg (nonnegative.trans ordered)]
  have negativeBound:|-nextShift|≤Real.log 2:=by simpa only [abs_neg] using positiveBound
  have kernelRead:=actual_wave_update_original_K_read coordinate zero h nextShift nonnegative ordered bounded
  rw [original_finite_action coordinate nextShift,original_finite_action coordinate (-nextShift),
    inner_add_right,inner_add_right,inner_add_right,inner_smul_right,inner_smul_right,
    kernelRead,mul_zero,mul_zero,zero_add,zero_add,← inner_add_right]
  rw [← (actual_upper_material_update coordinate h nextShift nonnegative ordered).1,inner_sub_left,
    actual_upper_wave_forcing_energy coordinate nextShift (nonnegative.trans ordered) bounded,
    inner_add_right,actual_upper_wave_forcing_read coordinate h nonnegative (ordered.trans bounded) nextShift positiveBound,
    actual_upper_wave_forcing_read coordinate h nonnegative (ordered.trans bounded) (-nextShift) negativeBound]
  unfold upperUpdateJointSourcePrice
  ring

end OriginalCommonInverseForcing.SourceJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
