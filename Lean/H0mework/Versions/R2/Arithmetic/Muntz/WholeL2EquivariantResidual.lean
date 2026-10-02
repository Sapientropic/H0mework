import H0mework.Versions.R2.Arithmetic.Muntz.CoPoissonLogContact
import H0mework.Arithmetic.Mellin.QuarterTest
import H0mework.Realization.Topology.EquivariantDual

/-!
# Canonical equivariant generalized-dual residual for A1c

The lawful test carrier is the intersection of the actual quarter `L²`
carrier with the Mellin-convergent domain.  The generic equivariant dual
restriction produces its canonical residual.  The whole-`L²` deletion proves
that this coordinate is nonzero for every same-owner nontrivial zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex MeasureTheory
open QRich
open SourceGeneratedTestHilbertGeneralizedDual

noncomputable section

def quarterScaleThreeEnergyAction :
    PositiveMellinQuarterEnergy →L[ℂ]
      PositiveMellinQuarterEnergy :=
  (positiveMellinQuarterEnergyTranslationIsometry
    (Real.log positiveMellinQuarterNoGoScale)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem quarterScaleThreeEnergyAction_apply
    (value : PositiveMellinQuarterEnergy) :
    quarterScaleThreeEnergyAction value =
      positiveMellinQuarterEnergyTranslation
        (Real.log positiveMellinQuarterNoGoScale) value :=
  rfl

def wholeL2EquivariantResidualAtCoordinate (coordinate : ℂ) :=
  canonicalEquivariantExtensionResidual
    (quarterMellinL2Feature (coordinate / 2))
    quarterScaleThreeEnergyAction
    ((positiveMellinQuarterNoGoScale : ℂ) ^
      ((1 / 4 : ℂ) - coordinate / 2))
    (quarterMellinL2Functional (coordinate / 2))

def zeroOwnedWholeL2EquivariantResidual
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) :=
  wholeL2EquivariantResidualAtCoordinate observation.coordinate

theorem equivariantExtension_gives_wholeL2Mouth
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (extension : EquivariantBoundedExtension
      (quarterMellinL2Feature (observation.coordinate / 2))
      quarterScaleThreeEnergyAction
      ((positiveMellinQuarterNoGoScale : ℂ) ^
        ((1 / 4 : ℂ) - observation.coordinate / 2))
      (quarterMellinL2Functional (observation.coordinate / 2))) :
    WholeL2BoundedSpectralMouth observation := by
  refine ⟨extension.extension, ?_, ?_⟩
  · intro value convergent
    let test : QuarterMellinL2Test (observation.coordinate / 2) :=
      ⟨value.1, ⟨value.2, convergent⟩⟩
    have readback := LinearMap.congr_fun extension.restricts test
    change extension.extension
        (positiveMellinQuarterLpValue value) =
      mellin (positiveMellinExtension value.1)
        (observation.coordinate / 2) at readback
    exact readback
  · intro value
    simpa only [quarterScaleThreeEnergyAction_apply] using
      extension.eigenlaw value

theorem zeroOwnedWholeL2EquivariantResidual_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    zeroOwnedWholeL2EquivariantResidual observation ≠ 0 := by
  intro residualZero
  change canonicalEquivariantExtensionResidual
      (quarterMellinL2Feature (observation.coordinate / 2))
      quarterScaleThreeEnergyAction
      ((positiveMellinQuarterNoGoScale : ℂ) ^
        ((1 / 4 : ℂ) - observation.coordinate / 2))
      (quarterMellinL2Functional (observation.coordinate / 2)) = 0
    at residualZero
  have bounded :=
    (canonicalEquivariantExtensionResidual_eq_zero_iff
      (quarterMellinL2Feature (observation.coordinate / 2))
      quarterScaleThreeEnergyAction
      ((positiveMellinQuarterNoGoScale : ℂ) ^
        ((1 / 4 : ℂ) - observation.coordinate / 2))
      (quarterMellinL2Functional
        (observation.coordinate / 2))).mp residualZero
  exact not_wholeL2BoundedSpectralMouth observation nontrivial
    (equivariantExtension_gives_wholeL2Mouth observation bounded.some)

/-! The nonzero coordinate records failure of this finite/bounded
representation.  A source-generated rigged spectral annihilator remains to
be constructed; it is not supplied by the generic residual. -/

end
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
