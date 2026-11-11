import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.Margin.Trace
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Energy.Boundary
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Consumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Energy.Margin

open Complex MeasureTheory
open scoped InnerProductSpace
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson
open OriginalRieszFiniteSynthesis
open OriginalRieszFinitePairing.CoPoisson.Energy

noncomputable section
local notation "K" => burnolCompletedMellinRieszVector

private theorem zero_owned_kernel_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    (K (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) : BurnolL2) ≠ 0 := by
  have native := (Kernel.zero_owned_response observation nontrivial rightHalf).1
  intro zero
  apply native
  apply Subtype.ext
  apply Subtype.ext
  exact zero

theorem zero_owned_source_energy_pos {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) (positive : 0 < shift) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    0 < (inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
      inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)).re := by
  dsimp only
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  by_contra notPositive
  have first : 0 ≤ (inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift)).re :=
    inner_self_nonneg (𝕜 := ℂ) (x := positionSeed coordinate shift)
  have second : 0 ≤ (inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)).re :=
    inner_self_nonneg (𝕜 := ℂ) (x := fourierSeed coordinate shift)
  have total : (inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift)).re +
      (inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)).re = 0 := by
    change ¬ 0 < (inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
      inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)).re at notPositive
    rw [Complex.add_re] at notPositive
    linarith
  have zeroEnergy : inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
      inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift) = 0 := by
    have firstZero : positionSeed coordinate shift = 0 :=
      (re_inner_self_nonpos (𝕜 := ℂ) (x := positionSeed coordinate shift)).mp (by
        change (inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift)).re ≤ 0
        linarith)
    have secondZero : fourierSeed coordinate shift = 0 :=
      (re_inner_self_nonpos (𝕜 := ℂ) (x := fourierSeed coordinate shift)).mp (by
        change (inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)).re ≤ 0
        linarith)
    simp only [firstZero, secondZero, inner_zero_left, add_zero]
  exact zero_owned_kernel_ne_zero observation nontrivial rightHalf
    (source_energy_zero_kernel coordinate shift positive zeroEnergy)

theorem zero_owned_source_energy_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) (positive : 0 < shift) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
      inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift) ≠ 0 := by
  dsimp only
  intro zero
  have actual := zero_owned_source_energy_pos observation nontrivial rightHalf shift positive
  dsimp only at actual
  rw [zero] at actual
  norm_num at actual

theorem zero_owned_boundary_reads_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ)
    (positive : 0 < shift) (bounded : shift ≤ Real.log 2) :
    let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
    inner ℂ (positionWave coordinate shift + fourierL2 (fourierWave coordinate shift))
        (burnolZeroPairedFixedAnnulusBoundary coordinate observation.mathlibZero shift : BurnolL2) ≠ 0 ∧
      inner ℂ (positionWave coordinate shift + fourierL2 (fourierWave coordinate shift))
        (paComponent coordinate shift : BurnolL2) ≠ 0 := by
  dsimp only
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  have energyPositive := zero_owned_source_energy_pos observation nontrivial rightHalf shift positive
  have energyNe : inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
      inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift) ≠ 0 := by
    intro zero
    change 0 < (inner ℂ (positionSeed coordinate shift) (positionSeed coordinate shift) +
      inner ℂ (fourierSeed coordinate shift) (fourierSeed coordinate shift)).re at energyPositive
    rw [zero] at energyPositive
    norm_num at energyPositive
  constructor
  · rw [source_wave_boundary_energy coordinate observation.mathlibZero shift positive.le bounded]
    exact mul_ne_zero (by norm_num) energyNe
  · rw [source_wave_pa_component_energy coordinate observation.mathlibZero shift positive.le bounded]
    exact mul_ne_zero (by norm_num) energyNe

end
end OriginalRieszFinitePairing.CoPoisson.Energy.Margin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
