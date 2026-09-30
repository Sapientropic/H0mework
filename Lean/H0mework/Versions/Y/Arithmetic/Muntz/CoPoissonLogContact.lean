import H0mework.Arithmetic.CoPoisson.LogOrbit
import H0mework.Versions.Y.Arithmetic.RiemannSource.TemperedPartnerEffect
import H0mework.Versions.Y.Arithmetic.MellinBoundary.PositiveMellinQuarterExtensionNoGo
import H0mework.Versions.Y.Arithmetic.RiemannMellinOrbit.ZeroPositiveMellinRadialDefect

/-!
# Co-Poisson logarithmic contact and the bounded spectral deletion

The actual co-Poisson orbit has a faithful scale-zero contact with the
nonzero Clozel remainder.  The endpoint effect factors through this contact.
The tempting bounded whole-quarter-`L²` Mellin mouth would force endpoint
path equality, but the existing coverage-complete theorem rejects it.
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

open Complex FourierTransform MeasureTheory
open QRich
open CanonicalUnitArithmeticCoordinateProjectionObstruction
open ClozelEndpointSourceEffect
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

theorem coPoissonLogOrbitMap_zero
    (test : SchwartzMap ℝ ℂ) :
    coPoissonLogOrbitMap test 0 = clozelTemperedRemainder test := by
  simp only [coPoissonLogOrbitMap, coPoissonOrbitMap,
    LinearMap.coe_mk, AddHom.coe_mk, Real.exp_zero]
  unfold coPoissonOrbitValue
  simp only [ofReal_one, one_cpow, one_mul]
  congr 1
  apply SchwartzMap.ext
  intro x
  simp [scaledSchwartzTest_apply]

theorem coPoissonLogOrbitMap_witness_ne_zero :
    coPoissonLogOrbitMap remainderWitnessSchwartz 0 ≠ 0 := by
  rw [coPoissonLogOrbitMap_zero]
  exact clozelTemperedRemainder_witness_value_ne_zero

theorem endpointBoundaryEffect_apply_eq_coPoisson_contact
    (coordinate : ℂ) (test : SchwartzMap ℝ ℂ) :
    clozelEndpointBoundaryEffect coordinate test =
      (coordinate - coordinateReversal coordinate) *
        coPoissonLogOrbitMap test 0 := by
  rw [clozelEndpointBoundaryEffect_normalForm,
    coPoissonLogOrbitMap_zero]
  rfl

theorem endpointPaths_eq_iff_coPoisson_contact_zero
    (coordinate : ℂ) :
    clozelReversedPath coordinate = clozelForwardPath coordinate ↔
      ∀ test : SchwartzMap ℝ ℂ,
        (coordinate - coordinateReversal coordinate) *
          coPoissonLogOrbitMap test 0 = 0 := by
  constructor
  · intro pathsEq test
    have fixed :=
      (clozelReversedPath_eq_forwardPath_iff coordinate).1 pathsEq
    have coefficientZero :
        coordinate - coordinateReversal coordinate = 0 :=
      sub_eq_zero.mpr fixed
    rw [coefficientZero, zero_mul]
  · intro contactZero
    apply (clozelReversedPath_eq_forwardPath_iff coordinate).2
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp
      (contactZero remainderWitnessSchwartz)).resolve_right
        coPoissonLogOrbitMap_witness_ne_zero

/-- Rejected bounded mouth.  It stores only the actual Mellin extension and
scale-three character law; endpoint equality is not a field. -/
def WholeL2BoundedSpectralMouth
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner) : Prop :=
  ∃ functional : PositiveMellinQuarterEnergy →L[ℂ] ℂ,
    IsQuarterMellinExtension
        (observation.coordinate / 2) functional ∧
      ∀ value,
        functional
            (positiveMellinQuarterEnergyTranslation
              (Real.log positiveMellinQuarterNoGoScale) value) =
          (positiveMellinQuarterNoGoScale : ℂ) ^
              ((1 / 4 : ℂ) - observation.coordinate / 2) *
            functional value

theorem endpointPaths_eq_of_wholeL2BoundedSpectralMouth
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (mouth : WholeL2BoundedSpectralMouth observation) :
    clozelReversedPath observation.coordinate =
      clozelForwardPath observation.coordinate := by
  rcases mouth with ⟨functional, extension, eigenlaw⟩
  have positive : 0 < (observation.coordinate / 2).re :=
    selectedPositiveParameter_re_pos observation nontrivial
  have radialZero := zeroOwnedPositiveMellinRadialDefect_zero_of_energy_selected
    observation nontrivial functional
    (isQuarterMellinExtension_nonzero positive functional extension)
    eigenlaw
  have fixed :=
    coordinate_eq_reversal_of_zeroOwnedPositiveMellinRadialDefect_zero
      observation nontrivial 0 radialZero
  exact (clozelReversedPath_eq_forwardPath_iff observation.coordinate).2 fixed

theorem not_wholeL2BoundedSpectralMouth
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    ¬ WholeL2BoundedSpectralMouth observation := by
  rintro ⟨functional, extension, eigenlaw⟩
  exact no_wholeL2_mellin_extension_at_qRich_scale_zero
    (observation.coordinate / 2)
    (selectedPositiveParameter_re_pos observation nontrivial)
    functional extension
    ((positiveMellinQuarterNoGoScale : ℂ) ^
      ((1 / 4 : ℂ) - observation.coordinate / 2)) eigenlaw

/-! The remaining source arrow is a same-zero generalized/rigged spectral
incidence.  This file neither constructs that arrow nor asserts endpoint
effect-zero. -/

end
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
