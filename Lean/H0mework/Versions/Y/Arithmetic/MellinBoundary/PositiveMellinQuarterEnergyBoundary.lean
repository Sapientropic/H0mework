import H0mework.Arithmetic.MellinBoundary.PositiveMellinQuarterEnergyCharacter
import H0mework.Versions.Y.Arithmetic.RiemannMellinOrbit.ZeroPositiveMellinRadialDefect

/-!
# Energy boundary for a Mellin character

The quarter chart turns a normalized positive dilation into an isometric
translation.  Consequently a nonzero continuous Mellin eigenfunctional on
the actual `L²` carrier has a unit-modulus character.  For a character
`a^(1/4-z)` this forces `Re z = 1/4` when `a > 1`.

This is a consumer criterion, not a producer: the source must still generate
the continuous extension and its eigenlaw.  Neither extension, positivity,
self-adjointness, nor a critical-line equation is hidden in a definition.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory Filter
open QRich
open scoped ENNReal

noncomputable section

/-! ## Direct handoff to the existing radial obstruction -/

theorem zeroOwnedPositiveMellinRadialDefect_zero_of_energy_selected
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (functional : PositiveMellinQuarterEnergy →L[ℂ] ℂ)
    (functional_nonzero : functional ≠ 0)
    (eigenlaw : ∀ value,
      functional
          (positiveMellinQuarterEnergyTranslation
            (Real.log (blockQRichSuccessorScale 0)) value) =
        (blockQRichSuccessorScale 0 : ℂ) ^
            ((1 / 4 : ℂ) - observation.coordinate / 2) *
          functional value) :
    zeroOwnedPositiveMellinRadialDefect observation nontrivial 0 = 0 := by
  have parameter :=
    positiveMellinQuarterEnergy_realPart_eq_quarter
      (observation.coordinate / 2)
      (blockQRichSuccessorScale 0)
      (by rw [blockQRichSuccessorScale_eq_stage_add_three]; norm_num)
      functional functional_nonzero eigenlaw
  apply zeroOwnedPositiveMellinRadialDefect_eq_zero_of_coordinate_re_eq_half
    observation nontrivial 0
  rw [div_ofNat_re] at parameter
  linarith

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
