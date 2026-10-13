import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.FullStock.BandInventory

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalCommonInverseForcing.SourceJoint.FullStock
open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszFiniteSource OriginalRieszFiniteSynthesis
local notation "P" => burnolEvenAmbientProjection

local instance ambientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem actual_upper_field_projection (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    P (upperSourceField coordinate h)=
      upperSourceWaveAmbient coordinate h nonnegative bounded-P (upperSourceCorrection coordinate h) := by
  have whole:upperSourceField coordinate h=upperSourceWave coordinate h-upperSourceCorrection coordinate h := by
    unfold upperSourceCorrection
    module
  have admitted:P (upperSourceWave coordinate h)=upperSourceWaveAmbient coordinate h nonnegative bounded := by
    change (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto
      (upperSourceWaveAmbient coordinate h nonnegative bounded)=_
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  rw [whole,map_sub,admitted]

theorem actual_whole_synthesis_source (coordinate : BurnolCompletedMellinCoordinate)
    (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    upperSeedFactor h • (wholeSynthesis coordinate h+wholeSynthesis coordinate (-h))=
      upperSourceWaveAmbient coordinate h nonnegative bounded-P (upperSourceCorrection coordinate h)-
        upperSeedFactor h • meanDebt coordinate h := by
  have positiveBound:|h|≤Real.log 2:=by rwa [abs_of_nonneg nonnegative]
  have negativeBound:|-h|≤Real.log 2:=by simpa only [abs_neg] using positiveBound
  rw [wholeSynthesis_eq_projection coordinate h positiveBound,
    wholeSynthesis_eq_projection coordinate (-h) negativeBound,← map_add,
    actual_whole_forcing_source coordinate h nonnegative,smul_sub,← map_smul,
    ← actual_upper_common_seed coordinate h nonnegative,
    actual_upper_field_projection coordinate h nonnegative bounded]

theorem actual_whole_boundary_source (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    (2*upperSeedFactor h) • burnolZeroPairedFixedAnnulusBoundary coordinate zero h=
      (2*upperSeedFactor h*(pairedMellinTranslationCharacter coordinate.value h-
        pairedMellinTranslationCharacter (star coordinate.value) h)) • burnolCompletedMellinRieszVector coordinate-
      upperSourceWaveAmbient coordinate h nonnegative bounded+P (upperSourceCorrection coordinate h)+
        upperSeedFactor h • meanDebt coordinate h := by
  have positiveBound:|h|≤Real.log 2:=by rwa [abs_of_nonneg nonnegative]
  rw [← boundarySource_eq_original coordinate zero h positiveBound]
  unfold boundarySource
  have actual:=actual_whole_synthesis_source coordinate h nonnegative bounded
  calc
    _=(2*upperSeedFactor h*(pairedMellinTranslationCharacter coordinate.value h-
      pairedMellinTranslationCharacter (star coordinate.value) h)) • burnolCompletedMellinRieszVector coordinate-
      upperSeedFactor h • (wholeSynthesis coordinate h+wholeSynthesis coordinate (-h)) := by module
    _=_ := by rw [actual];module

theorem actual_orthogonal_boundary_source (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value=0) (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    (2*upperSeedFactor h) •
      burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
        (burnolZeroPairedFixedAnnulusBoundary coordinate zero h)=
      (2*upperSeedFactor h*(pairedMellinTranslationCharacter coordinate.value h-
        pairedMellinTranslationCharacter (star coordinate.value) h)) • burnolCompletedMellinRieszVector coordinate+
      burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection (P (upperSourceCorrection coordinate h))+
      upperSeedFactor h • burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection (meanDebt coordinate h) := by
  let orthogonal:=burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
  have generated:=congrArg orthogonal (actual_whole_boundary_source coordinate zero h nonnegative bounded)
  have kernelRead:orthogonal (burnolCompletedMellinRieszVector coordinate)=burnolCompletedMellinRieszVector coordinate:=
    Submodule.starProjection_eq_self_iff.mpr
      (riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero)
  have waveRead:orthogonal (upperSourceWaveAmbient coordinate h nonnegative bounded)=0 := by
    apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
    
    exact burnolCompactCoPoissonClosedRange.toSubmodule.le_orthogonal_orthogonal
      (actual_upper_ambient_inPa coordinate h nonnegative bounded)
  change (2*upperSeedFactor h) • orthogonal (burnolZeroPairedFixedAnnulusBoundary coordinate zero h)=_
  simp only [map_smul,map_add,map_sub,kernelRead,waveRead,sub_zero] at generated
  exact generated

end OriginalCommonInverseForcing.SourceJoint.FullStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
