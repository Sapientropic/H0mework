import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.Margin.Boundary

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Observed

open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson OriginalRieszFinitePairing.CoPoisson.Energy

noncomputable section

local instance ambientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def sourceWave (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : BurnolPaAmbientCarrier :=
  burnolEvenAmbientProjection (positionWave coordinate shift + fourierL2 (fourierWave coordinate shift))

theorem sourceWave_native (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    (sourceWave coordinate shift : BurnolL2) =
        positionWave coordinate shift + fourierL2 (fourierWave coordinate shift) ∧
      sourceWave coordinate shift ∈ burnolCompactCoPoissonClosedRange.toSubmodule := by
  obtain ⟨physical, inPa, actual⟩ := Submodule.mem_map.mp
    (generated_source_wave_inPa coordinate shift nonnegative bounded)
  change (physical : BurnolL2) = _ at actual
  have same : sourceWave coordinate shift = physical := by
    unfold sourceWave
    rw [← actual]
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self _
  exact ⟨by rw [same]; exact actual, by rw [same]; exact inPa⟩

theorem sourceWave_current_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    burnolCompletedMellinEvaluator coordinate (sourceWave coordinate shift) = 0 := by
  have orthogonal := riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate zero
  have killed := (Submodule.mem_orthogonal' _ _).mp orthogonal
    (sourceWave coordinate shift) (sourceWave_native coordinate shift nonnegative bounded).2
  rw [burnolCompletedMellinRieszVector_readback] at killed
  exact killed

/-- The original physical paired action reveals the complete source energy to the original reader. -/
theorem sourceWave_next_read (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    burnolCompletedMellinEvaluator coordinate
        (burnolPairedAmbientCompression shift (sourceWave coordinate shift)) =
      (1 / 2 : ℂ) * star (inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
        inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)) := by
  let wave := sourceWave coordinate shift
  let kernel := burnolCompletedMellinRieszVector coordinate
  let energy := inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
    inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)
  have paired := source_wave_boundary_energy coordinate zero shift nonnegative bounded
  rw [← (sourceWave_native coordinate shift nonnegative bounded).1] at paired
  change inner ℂ wave (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) =
    -(1 / 2 : ℂ) * energy at paired
  have left : inner ℂ kernel wave = 0 :=
    (burnolCompletedMellinRieszVector_readback coordinate wave).trans
      (sourceWave_current_read coordinate zero shift nonnegative bounded)
  have right : inner ℂ wave kernel = 0 := by
    rw [← inner_conj_symm (𝕜 := ℂ) wave kernel, left, map_zero]
  have response : inner ℂ wave (burnolPairedAmbientCompression shift kernel) =
      (1 / 2 : ℂ) * energy := by
    unfold burnolZeroPairedFixedAnnulusBoundary at paired
    change inner ℂ wave (pairedMellinTranslationCharacter coordinate.value shift • kernel -
      burnolPairedAmbientCompression shift kernel) = -(1 / 2 : ℂ) * energy at paired
    have scalar := inner_smul_right (𝕜 := ℂ) wave kernel
      (pairedMellinTranslationCharacter coordinate.value shift)
    rw [inner_sub_right, scalar, right, mul_zero, zero_sub] at paired
    linear_combination -paired
  calc
    _ = inner ℂ kernel (burnolPairedAmbientCompression shift wave) :=
      (burnolCompletedMellinRieszVector_readback coordinate _).symm
    _ = star (inner ℂ (burnolPairedAmbientCompression shift wave) kernel) :=
      (inner_conj_symm _ _).symm
    _ = star (inner ℂ wave (burnolPairedAmbientCompression shift kernel)) := by
      rw [burnolPairedAmbientCompression_symmetric]
    _ = _ := by
      rw [response, star_mul]
      change star energy * star (1 / 2 : ℂ) = (1 / 2 : ℂ) * star energy
      have half : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
      rw [half]
      ring

theorem zero_owned_next_read_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ)
    (positive : 0 < shift) (bounded : shift ≤ Real.log 2) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    burnolCompletedMellinEvaluator coordinate
      (burnolPairedAmbientCompression shift (sourceWave coordinate shift)) ≠ 0 := by
  dsimp only
  rw [sourceWave_next_read _ observation.mathlibZero shift positive.le bounded]
  apply mul_ne_zero (by norm_num)
  exact star_ne_zero.mpr
    (Margin.zero_owned_source_energy_ne_zero observation nontrivial rightHalf shift positive)

end
end OriginalRieszFinitePairing.CoPoisson.Observed
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
