import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.ZeroRead
import H0mework.Versions.V2.Arithmetic.RieszSynthesis.PaComponent
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Synthesis.Control
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.Interaction

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Energy

open Complex MeasureTheory Set
open scoped InnerProductSpace
open OriginalRieszFinitePairing OriginalRieszFiniteSource OriginalRieszFiniteSynthesis
noncomputable section

local instance boundaryAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem pa_fourier (value : BurnolL2) (member : value ∈ burnolOriginalPaInL2) :
    fourierL2 value ∈ burnolOriginalPaInL2 := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp member
  refine Submodule.mem_map.mpr ⟨evenFaceFourierEquiv burnolUnscaledCommonGapRadius physical,
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange inPa, ?_⟩
  change fourierL2 (physical : BurnolL2) = fourierL2 value
  exact congrArg fourierL2 actual

private theorem source_wave_inPa (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    CoPoisson.positionWave coordinate shift + fourierL2 (CoPoisson.fourierWave coordinate shift) ∈
      burnolOriginalPaInL2 :=
  burnolOriginalPaInL2.add_mem (CoPoisson.positionWave_inPa coordinate shift nonnegative bounded)
    (pa_fourier _ (CoPoisson.fourierWave_inPa coordinate shift nonnegative bounded))

private theorem original_boundary_pa_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) (value : BurnolL2)
    (member : value ∈ burnolOriginalPaInL2) :
    inner ℂ value (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift : BurnolL2) =
      -(1 / 2 : ℂ) * inner ℂ value (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)) := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp member
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
  have killed := (burnolCompactCoPoissonClosedRange.toSubmodule.mem_orthogonal _).mp
    orthogonal physical inPa
  have projected : inner ℂ physical
      (burnolEvenAmbientProjection (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift))) =
        inner ℂ (physical : BurnolL2) (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)) :=
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule
      |>.inner_orthogonalProjectionOnto_eq_of_mem_left physical _
  change (physical : BurnolL2) = value at actual
  rw [← actual]
  change inner ℂ physical (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) = _
  have kernelScalar := inner_smul_right (𝕜 := ℂ) physical (burnolCompletedMellinRieszVector coordinate)
    (pairedMellinTranslationCharacter coordinate.value shift -
      pairedMellinTranslationCharacter (star coordinate.value) shift)
  have sourceScalar := inner_smul_right (𝕜 := ℂ) physical
    (burnolEvenAmbientProjection (forcingIntegral coordinate shift + forcingIntegral coordinate (-shift)))
    (1 / 2 : ℂ)
  rw [original_boundary, inner_sub_right, kernelScalar, sourceScalar,
    killed, mul_zero, zero_sub, projected]
  ring

/-- The complete original boundary consumes the actual counted Pa wave and returns the two source energies. -/
theorem source_wave_boundary_energy (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    inner ℂ (CoPoisson.positionWave coordinate shift + fourierL2 (CoPoisson.fourierWave coordinate shift))
      (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift : BurnolL2) =
        -(1 / 2 : ℂ) * (inner ℂ (CoPoisson.positionSeed coordinate shift) (CoPoisson.positionSeed coordinate shift) +
          inner ℂ (CoPoisson.fourierSeed coordinate shift) (CoPoisson.fourierSeed coordinate shift)) := by
  rw [original_boundary_pa_read coordinate zero shift _
    (source_wave_inPa coordinate shift nonnegative bounded),
    source_wave_forcing_energy coordinate shift nonnegative bounded]

/-- The same source measurement belongs to the literal Pa projection of the original boundary. -/
theorem source_wave_pa_component_energy (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    inner ℂ (CoPoisson.positionWave coordinate shift + fourierL2 (CoPoisson.fourierWave coordinate shift))
      (paComponent coordinate shift : BurnolL2) =
        -(1 / 2 : ℂ) * (inner ℂ (CoPoisson.positionSeed coordinate shift) (CoPoisson.positionSeed coordinate shift) +
          inner ℂ (CoPoisson.fourierSeed coordinate shift) (CoPoisson.fourierSeed coordinate shift)) := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp
    (source_wave_inPa coordinate shift nonnegative bounded)
  change (physical : BurnolL2) =
    CoPoisson.positionWave coordinate shift + fourierL2 (CoPoisson.fourierWave coordinate shift) at actual
  rw [← actual]
  change inner ℂ physical (paComponent coordinate shift) = _
  rw [paComponent_eq_original coordinate zero shift (by rwa [abs_of_nonneg nonnegative]),
    ← burnolCompactCoPoissonClosedRange.toSubmodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr inPa]
  change inner ℂ (physical : BurnolL2)
    (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift : BurnolL2) = _
  rw [actual]
  exact source_wave_boundary_energy coordinate zero shift nonnegative bounded

theorem source_boundary_zero (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    CoPoisson.positionWave coordinate 0 + fourierL2 (CoPoisson.fourierWave coordinate 0) = 0 ∧
      burnolZeroPairedFixedAnnulusBoundary coordinate zero 0 = 0 := by
  have source := CoPoisson.source_programme_zero coordinate
  constructor
  · rw [source.2.2.1, source.2.2.2.1, map_zero, add_zero]
  · rw [← boundarySource_eq_original coordinate zero 0 (by
      simpa only [abs_zero] using Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)), boundarySource_zero]


/-- The existing source-owned Pa membership is available to subsequent dynamic consumers. -/
theorem generated_source_wave_inPa (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    CoPoisson.positionWave coordinate shift + fourierL2 (CoPoisson.fourierWave coordinate shift) ∈
      burnolOriginalPaInL2 :=
  source_wave_inPa coordinate shift nonnegative bounded

end
end OriginalRieszFinitePairing.CoPoisson.Energy
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
