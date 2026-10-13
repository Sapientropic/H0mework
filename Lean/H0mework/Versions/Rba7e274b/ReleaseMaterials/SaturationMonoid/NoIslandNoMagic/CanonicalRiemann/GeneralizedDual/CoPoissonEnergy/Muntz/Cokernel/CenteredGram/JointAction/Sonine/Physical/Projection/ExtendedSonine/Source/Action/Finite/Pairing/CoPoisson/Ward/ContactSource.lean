import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Correction
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.Contact

/-! The complete contact reads the original inverse through its higher integer channels. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward

open Complex Filter MeasureTheory
open scoped InnerProductSpace
open OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson
open OriginalRieszFinitePairing.CoPoisson.Ward
open Correction

noncomputable section

/-- Both actual inverse representatives consume the generated higher-channel
formula. The programme means stay inside their integrals; the two gap means
and the two seed masses remain explicit. -/
theorem signedContact_source (coordinate : BurnolCompletedMellinCoordinate)
    (shift : ℝ) (nonnegative : 0 ≤ shift) :
    signedContact coordinate shift =
      (∫ x : ℝ, star (higherCountingRaw (bandLower shift) 4
        (positionWeight coordinate shift) x) * burnolRieszStateRaw coordinate x) -
      (∫ x : ℝ, star (higherCountingRaw (bandLower shift) 4
        (fourierWeight coordinate shift) x) * burnolRieszFourierRaw coordinate x) +
      positionMean coordinate * star (∫ x : ℝ, positionSeed coordinate shift x) -
      fourierMean coordinate * star (∫ x : ℝ, fourierSeed coordinate shift x) := by
  have position : inner ℂ (positionCorrection coordinate shift)
      (burnolCompletedMellinRieszVector coordinate : BurnolL2) =
      ∫ x : ℝ, star (higherCountingRaw (bandLower shift) 4
        (positionWeight coordinate shift) x) * burnolRieszStateRaw coordinate x := by
    rw [position_correction_higher_pairing coordinate shift nonnegative]
    apply integral_congr_ae
    filter_upwards [burnolRieszState_ae_raw coordinate] with x actual
    rw [actual]
    simp only [RCLike.inner_apply, starRingEnd_apply]
    ring
  have fourier : inner ℂ (fourierCorrection coordinate shift)
      (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2)) =
      ∫ x : ℝ, star (higherCountingRaw (bandLower shift) 4
        (fourierWeight coordinate shift) x) * burnolRieszFourierRaw coordinate x := by
    rw [fourier_correction_higher_pairing coordinate shift nonnegative]
    apply integral_congr_ae
    filter_upwards [burnolRieszFourier_ae_raw coordinate] with x actual
    rw [actual]
    simp only [RCLike.inner_apply, starRingEnd_apply]
    ring
  rw [signedContact, position, fourier]

end
end OriginalRieszFinitePairing.CoPoisson.Ward
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
