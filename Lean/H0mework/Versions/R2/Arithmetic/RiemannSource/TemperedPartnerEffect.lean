import H0mework.Versions.R2.Arithmetic.UnitArithmetic.CoordinateProjectionObstruction
import H0mework.Arithmetic.Tempered.RemainderReality

/-!
# Actual Fourier--conjugation partner and endpoint effect

The partner defect is obtained by applying the actual Fourier/conjugation
operator to the forward defect.  On the real, self-Fourier, nonzero Clozel
remainder their difference is exactly the endpoint cross coefficient.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelEndpointSourceEffect

open Complex FourierTransform
open CanonicalUnitArithmeticCoordinateProjectionObstruction

noncomputable section

def temperedTatePartner (distribution : ComplexTempered) : ComplexTempered :=
  𝓕 (realConjugation distribution)

def centeredEigenDefect (distribution : ComplexTempered) (parameter : ℂ) :
    ComplexTempered :=
  centeredScalingGenerator distribution - parameter • distribution

def tatePartnerEigenDefect
    (distribution : ComplexTempered) (parameter : ℂ) : ComplexTempered :=
  centeredScalingGenerator (temperedTatePartner distribution) -
    (-star parameter) • temperedTatePartner distribution

theorem realConjugation_centeredEigenDefect
    (distribution : ComplexTempered) (parameter : ℂ) :
    realConjugation (centeredEigenDefect distribution parameter) =
      realConjugation (centeredScalingGenerator distribution) -
        star parameter • realConjugation distribution := by
  unfold centeredEigenDefect
  rw [show centeredScalingGenerator distribution - parameter • distribution =
      centeredScalingGenerator distribution + (-parameter) • distribution by module]
  rw [realConjugation_add, realConjugation_smul]
  simp only [star_neg]
  have hneg :
      ((-star parameter : ℂ) • realConjugation distribution) =
        -(star parameter • realConjugation distribution) :=
    neg_smul (star parameter) (realConjugation distribution)
  rw [hneg]
  rfl

theorem tatePartnerEigenDefect_factorization
    (distribution : ComplexTempered) (parameter : ℂ) :
    tatePartnerEigenDefect distribution parameter =
      -(𝓕 (realConjugation
        (centeredEigenDefect distribution parameter))) := by
  unfold tatePartnerEigenDefect temperedTatePartner
  calc
    centeredScalingGenerator (𝓕 (realConjugation distribution)) -
          (-star parameter) • 𝓕 (realConjugation distribution) =
        -(𝓕 (centeredScalingGenerator
          (realConjugation distribution))) +
          star parameter • 𝓕 (realConjugation distribution) := by
      rw [centeredScalingGenerator_fourier]
      module
    _ = -(𝓕 (realConjugation
          (centeredScalingGenerator distribution))) +
          star parameter • 𝓕 (realConjugation distribution) := by
      rw [← realConjugation_centeredScalingGenerator]
    _ = -(𝓕 (realConjugation
          (centeredEigenDefect distribution parameter))) := by
      rw [realConjugation_centeredEigenDefect]
      have fourierSub :
          𝓕 (realConjugation (centeredScalingGenerator distribution) -
              star parameter • realConjugation distribution) =
            𝓕 (realConjugation
              (centeredScalingGenerator distribution)) -
              star parameter • 𝓕 (realConjugation distribution) := by
        rw [sub_eq_add_neg, FourierTransform.fourier_add,
          FourierTransform.fourier_neg, fourier_smul]
        rfl
      rw [fourierSub, neg_sub]
      abel

theorem temperedTatePartner_clozelTemperedRemainder :
    temperedTatePartner clozelTemperedRemainder =
      clozelTemperedRemainder := by
  unfold temperedTatePartner
  rw [clozelTemperedRemainder_isReal,
    fourier_clozelTemperedRemainder]

def centeredEndpointParameter (coordinate : ℂ) : ℂ :=
  coordinate - 1 / 2

theorem centeredEndpointParameter_cross (coordinate : ℂ) :
    centeredEndpointParameter coordinate +
        star (centeredEndpointParameter coordinate) =
      coordinate - coordinateReversal coordinate := by
  simp [centeredEndpointParameter, coordinateReversal]
  ring

def clozelForwardPath (coordinate : ℂ) : ComplexTempered :=
  centeredEigenDefect clozelTemperedRemainder
    (centeredEndpointParameter coordinate)

def clozelReversedPath (coordinate : ℂ) : ComplexTempered :=
  tatePartnerEigenDefect clozelTemperedRemainder
    (centeredEndpointParameter coordinate)

theorem clozelReversedPath_actualFactorization (coordinate : ℂ) :
    clozelReversedPath coordinate =
      -(𝓕 (realConjugation (clozelForwardPath coordinate))) :=
  tatePartnerEigenDefect_factorization
    clozelTemperedRemainder (centeredEndpointParameter coordinate)

def clozelEndpointBoundaryEffect (coordinate : ℂ) : ComplexTempered :=
  clozelReversedPath coordinate - clozelForwardPath coordinate

theorem clozelEndpointBoundaryEffect_normalForm (coordinate : ℂ) :
    clozelEndpointBoundaryEffect coordinate =
      (coordinate - coordinateReversal coordinate) •
        clozelTemperedRemainder := by
  unfold clozelEndpointBoundaryEffect clozelReversedPath clozelForwardPath
  unfold tatePartnerEigenDefect centeredEigenDefect
  rw [temperedTatePartner_clozelTemperedRemainder]
  rw [← centeredEndpointParameter_cross]
  module

theorem clozelEndpointBoundaryEffect_eq_zero_iff (coordinate : ℂ) :
    clozelEndpointBoundaryEffect coordinate = 0 ↔
      coordinate = coordinateReversal coordinate := by
  rw [clozelEndpointBoundaryEffect_normalForm]
  rw [smul_eq_zero_iff_left clozelTemperedRemainder_ne_zero,
    sub_eq_zero]

theorem clozelReversedPath_eq_forwardPath_iff (coordinate : ℂ) :
    clozelReversedPath coordinate = clozelForwardPath coordinate ↔
      coordinate = coordinateReversal coordinate := by
  rw [← sub_eq_zero]
  exact clozelEndpointBoundaryEffect_eq_zero_iff coordinate

end

end ClozelEndpointSourceEffect
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
