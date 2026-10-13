import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.ZeroRead

/-! Signed source contact of the two original Pa programmes. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward

open Classical Complex Filter MeasureTheory Set
open scoped InnerProductSpace
open OriginalRieszFinitePairing OriginalRieszFiniteColumns OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson
noncomputable section

local notation "q" => (1 / 4 : ℝ)
local notation "K" => burnolCompletedMellinRieszVector

/-- Both original correction pairings and both original means, with the signs
fixed by the position minus Fourier Pa programme. -/
def signedContact (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) : ℂ :=
  inner ℂ (positionCorrection coordinate shift) (K coordinate : BurnolL2) -
    inner ℂ (fourierCorrection coordinate shift) (fourierL2 (K coordinate : BurnolL2)) +
    positionMean coordinate * star (∫ x : ℝ, positionSeed coordinate shift x) -
    fourierMean coordinate * star (∫ x : ℝ, fourierSeed coordinate shift x)

theorem signed_wave_contact_balance (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    signedContact coordinate shift =
      inner ℂ (positionWave coordinate shift) (K coordinate : BurnolL2) -
        inner ℂ (fourierWave coordinate shift) (fourierL2 (K coordinate : BurnolL2)) +
          annularRead coordinate shift - annularRead coordinate (-shift) := by
  have position := exterior_seed_inner (positionColumn coordinate (-shift))
    (K coordinate : BurnolL2) _ _ _ (positionColumn_integrable coordinate (-shift))
    (burnolRieszState_ae_raw coordinate) (position_raw coordinate)
  rw [← positionSeed_eq_exterior coordinate shift nonnegative] at position
  have fourier := exterior_seed_inner (fourierColumn coordinate shift)
    (fourierL2 (K coordinate : BurnolL2)) _ _ _
    (fourierColumn_integrable coordinate shift)
    (burnolRieszFourier_ae_raw coordinate) (fourier_raw coordinate)
  rw [← fourierSeed_eq_exterior coordinate shift nonnegative] at fourier
  unfold signedContact positionCorrection fourierCorrection
  rw [inner_sub_left, inner_sub_left, position, fourier]
  simp only [annularRead, positionColumn_integral_zero, fourierColumn_integral_zero,
    star_zero, mul_zero, zero_add]
  rw [exteriorRead_zero_of_quarter _ _ (positionColumn_quarter coordinate shift nonnegative),
    exteriorRead_zero_of_quarter _ _
      (fourierColumn_negative_quarter coordinate shift nonnegative)]
  ring

theorem signed_contact_annular (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    signedContact coordinate shift =
      annularRead coordinate shift - annularRead coordinate (-shift) := by
  rw [signed_wave_contact_balance coordinate shift nonnegative,
    positionWave_zero_read coordinate zero shift nonnegative bounded,
    fourierWave_zero_read coordinate zero shift nonnegative bounded]
  ring

/-- The signed band is paid by the complete contact of the actual Pa waves. -/
theorem signed_band_contact (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ)
    (nonnegative : 0 ≤ shift) (bounded : shift ≤ Real.log 2) :
    2 * (Real.exp (shift / 2) : ℂ) *
      ((∫ x : ℝ in (q * Real.exp (-shift))..q,
        star (positionSource coordinate x) * positionSource coordinate (Real.exp shift * x)) -
      (∫ x : ℝ in (q * Real.exp (-shift))..q,
        star (burnolRieszSingleFourierSourceRaw coordinate x) *
          burnolRieszSingleFourierSourceRaw coordinate (Real.exp shift * x))) =
      signedContact coordinate shift := by
  rw [signed_contact_annular coordinate zero shift nonnegative bounded,
    annularRead_nonnegative coordinate shift nonnegative,
    annularRead_negative coordinate shift nonnegative]
  ring

end
end OriginalRieszFinitePairing.CoPoisson.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
