import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.Margin.Positive

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Energy.Margin

open Complex
open scoped InnerProductSpace
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson
open OriginalRieszFinitePairing.CoPoisson.Energy OriginalRieszFiniteSynthesis
noncomputable section

/-- The actual source energy and counted Pa wave determine the projection margin before a zero is read. -/
def boundaryMargin (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : ℝ :=
  ‖inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
    inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)‖ /
      (2 * ‖positionWave coordinate shift + fourierL2 (fourierWave coordinate shift)‖)

theorem boundaryMargin_zero (coordinate : BurnolCompletedMellinCoordinate) : boundaryMargin coordinate 0 = 0 := by
  have programme := source_programme_zero coordinate
  simp [boundaryMargin, programme.1, programme.2.1]

/-- Original zero occupation makes the source-defined margin strictly positive; the original Pa boundary pairing pays its norm bound. -/
theorem zero_owned_boundary_margin {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ)
    (positive : 0 < shift) (bounded : shift ≤ Real.log 2) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    0 < boundaryMargin coordinate shift ∧ boundaryMargin coordinate shift ≤ ‖paComponent coordinate shift‖ := by
  dsimp only
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let energy := inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
    inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)
  let wave := positionWave coordinate shift + fourierL2 (fourierWave coordinate shift)
  have energyNe : energy ≠ 0 :=
    zero_owned_source_energy_ne_zero observation nontrivial rightHalf shift positive
  have paired : inner ℂ wave (paComponent coordinate shift : BurnolL2) = -(1 / 2 : ℂ) * energy :=
    source_wave_pa_component_energy coordinate observation.mathlibZero shift positive.le bounded
  have waveNe : wave ≠ 0 := by
    intro vanished
    rw [vanished, inner_zero_left] at paired
    exact energyNe ((mul_eq_zero.mp paired.symm).resolve_left (by norm_num))
  have denominator : 0 < 2 * ‖wave‖ := mul_pos (by norm_num) (norm_pos_iff.mpr waveNe)
  have bound := norm_inner_le_norm (𝕜 := ℂ) wave (paComponent coordinate shift : BurnolL2)
  have halfNorm : ‖-(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [paired, norm_mul, halfNorm] at bound
  change (1 / 2 : ℝ) * ‖energy‖ ≤ ‖wave‖ * ‖paComponent coordinate shift‖ at bound
  change 0 < ‖energy‖ / (2 * ‖wave‖) ∧ ‖energy‖ / (2 * ‖wave‖) ≤ ‖paComponent coordinate shift‖
  refine ⟨div_pos (norm_pos_iff.mpr energyNe) denominator, (div_le_iff₀ denominator).mpr ?_⟩
  linarith

end
end OriginalRieszFinitePairing.CoPoisson.Energy.Margin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
