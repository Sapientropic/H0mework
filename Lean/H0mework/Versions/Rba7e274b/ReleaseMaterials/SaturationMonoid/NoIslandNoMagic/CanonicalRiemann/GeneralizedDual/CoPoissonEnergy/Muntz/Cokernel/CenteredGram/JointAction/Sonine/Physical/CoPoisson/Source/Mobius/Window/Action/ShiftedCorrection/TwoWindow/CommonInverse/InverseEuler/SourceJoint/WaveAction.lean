import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.CorrectionUpdate
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.Boundary
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Correction

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint
open Complex MeasureTheory Set Filter
open OriginalRieszFiniteSource OriginalRieszFiniteColumns OriginalRieszFiniteSynthesis OriginalPaPhysicalGreen
open scoped InnerProductSpace Topology
local notation "q" => (1/4:ℝ)
namespace SourceEnergy
export OriginalRieszFinitePairing.CoPoisson.Energy
  (source_wave_forcing_pairing source_wave_forcing_energy correction_forcing_pairing
   source_wave_boundary_energy source_wave_pa_component_energy)
end SourceEnergy

def upperSeedEnergy (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  inner ℂ (Seed.positionSeed coordinate h) (Seed.positionSeed coordinate h)+
    inner ℂ (Seed.fourierSeed coordinate h) (Seed.fourierSeed coordinate h)

theorem actual_upper_field_exteriors (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) :
    upperSourceField coordinate h=upperSeedFactor h •
      (positionColumn coordinate (-h)-originalPhysicalCutoff q (positionColumn coordinate (-h))+
        fourierL2 (fourierColumn coordinate h-originalPhysicalCutoff q (fourierColumn coordinate h))) := by
  rw [actual_upper_common_seed coordinate h nonnegative,
    OriginalRieszFinitePairing.CoPoisson.positionSeed_eq_exterior coordinate h nonnegative,
    OriginalRieszFinitePairing.CoPoisson.fourierSeed_eq_exterior coordinate h nonnegative]

theorem actual_upper_wave_forcing_read (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2)
    (time : ℝ) (timeBound : |time|≤Real.log 2) :
    inner ℂ (upperSourceWave coordinate h) (forcingIntegral coordinate time)=
      star (upperSeedFactor h)*(inner ℂ (Seed.positionSeed coordinate h) (positionColumn coordinate time)+
        inner ℂ (Seed.fourierSeed coordinate h) (fourierColumn coordinate time)) := by
  unfold upperSourceWave
  rw [inner_smul_left,SourceEnergy.source_wave_forcing_pairing coordinate h nonnegative bounded time timeBound]
  rfl

theorem actual_upper_wave_forcing_energy (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (upperSourceWave coordinate h) (forcingIntegral coordinate h+forcingIntegral coordinate (-h))=
      star (upperSeedFactor h)*upperSeedEnergy coordinate h := by
  unfold upperSourceWave upperSeedEnergy
  rw [inner_smul_left,SourceEnergy.source_wave_forcing_energy coordinate h nonnegative bounded]
  rfl

theorem actual_upper_wave_boundary_energy (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (upperSourceWave coordinate h) (burnolZeroPairedFixedAnnulusBoundary coordinate zero h:BurnolL2)=
      -(1/2:ℂ)*star (upperSeedFactor h)*upperSeedEnergy coordinate h := by
  unfold upperSourceWave upperSeedEnergy
  rw [inner_smul_left,SourceEnergy.source_wave_boundary_energy coordinate zero h nonnegative bounded]
  simp only [starRingEnd_apply]
  ring

theorem actual_upper_wave_pa_energy (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (upperSourceWave coordinate h) (paComponent coordinate h:BurnolL2)=
      -(1/2:ℂ)*star (upperSeedFactor h)*upperSeedEnergy coordinate h := by
  unfold upperSourceWave upperSeedEnergy
  rw [inner_smul_left,SourceEnergy.source_wave_pa_component_energy coordinate zero h nonnegative bounded]
  simp only [starRingEnd_apply]
  ring

theorem actual_upper_correction_forcing_read (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2)
    (time : ℝ) (timeBound : |time|≤Real.log 2) :
    inner ℂ (upperSourceCorrection coordinate h) (forcingIntegral coordinate time)=
      star (upperSeedFactor h)*
        (-inner ℂ (Seed.positionSeed coordinate h) (fourierL2 (fourierColumn coordinate time))-
          inner ℂ (fourierL2 (Seed.fourierSeed coordinate h)) (positionColumn coordinate time)) := by
  rw [actual_upper_source_correction coordinate h nonnegative,inner_smul_left,
    SourceEnergy.correction_forcing_pairing coordinate h nonnegative bounded time timeBound]
  rfl

private theorem wave_ambient_qualified (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    upperSourceWave coordinate h∈evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  obtain ⟨physical,_,actual⟩:=Submodule.mem_map.mp (generated_upper_wave_inPa coordinate h nonnegative bounded)
  change (physical:BurnolL2)=upperSourceWave coordinate h at actual
  rw [← actual]
  exact physical.property

def upperSourceWaveAmbient (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) : BurnolPaAmbientCarrier :=
  ⟨upperSourceWave coordinate h,wave_ambient_qualified coordinate h nonnegative bounded⟩

theorem actual_upper_ambient_inPa (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    upperSourceWaveAmbient coordinate h nonnegative bounded∈burnolCompactCoPoissonClosedRange := by
  obtain ⟨physical,inPa,actual⟩:=Submodule.mem_map.mp (generated_upper_wave_inPa coordinate h nonnegative bounded)
  have same:physical=upperSourceWaveAmbient coordinate h nonnegative bounded:=Subtype.ext actual
  rwa [← same]

theorem actual_upper_first_source_energy (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    star (firstSourceRead coordinate h (upperSourceWaveAmbient coordinate h nonnegative bounded)+
      firstSourceRead coordinate (-h) (upperSourceWaveAmbient coordinate h nonnegative bounded))=
      star (upperSeedFactor h)*upperSeedEnergy coordinate h := by
  have positiveBound:|h|≤Real.log 2:=by rwa [abs_of_nonneg nonnegative]
  have negativeBound:|-h|≤Real.log 2:=by simpa only [abs_neg] using positiveBound
  have qualified:=actual_upper_ambient_inPa coordinate h nonnegative bounded
  rw [← forcing_firstSourceRead coordinate h positiveBound _ qualified,
    ← forcing_firstSourceRead coordinate (-h) negativeBound _ qualified,
    ← inner_add_left]
  change (starRingEnd ℂ) (inner ℂ (forcingIntegral coordinate h+forcingIntegral coordinate (-h))
    (upperSourceWave coordinate h))=_
  rw [inner_conj_symm]
  exact actual_upper_wave_forcing_energy coordinate h nonnegative bounded

theorem actual_upper_original_K_joint_action (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (upperSourceWave coordinate h)
      (burnolMultiplicativeDilation h (burnolCompletedMellinRieszVector coordinate:BurnolL2)+
        burnolMultiplicativeDilation (-h) (burnolCompletedMellinRieszVector coordinate:BurnolL2))=
      star (upperSeedFactor h)*upperSeedEnergy coordinate h := by
  have kernelRead:inner ℂ (upperSourceWave coordinate h) (burnolCompletedMellinRieszVector coordinate:BurnolL2)=0 := by
    obtain ⟨physical,inPa,actual⟩:=Submodule.mem_map.mp (generated_upper_wave_inPa coordinate h nonnegative bounded)
    have orthogonal:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
    have read:=(burnolCompactCoPoissonClosedRange.toSubmodule.mem_orthogonal _).mp orthogonal physical inPa
    change inner ℂ (physical:BurnolL2) (burnolCompletedMellinRieszVector coordinate:BurnolL2)=0 at read
    change (physical:BurnolL2)=upperSourceWave coordinate h at actual
    rwa [actual] at read
  rw [original_finite_action coordinate h,original_finite_action coordinate (-h),
    inner_add_right,inner_add_right,inner_add_right,inner_smul_right,inner_smul_right,
    kernelRead,mul_zero,mul_zero,zero_add,zero_add,← inner_add_right]
  exact actual_upper_wave_forcing_energy coordinate h nonnegative bounded

end OriginalCommonInverseForcing.SourceJoint
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
