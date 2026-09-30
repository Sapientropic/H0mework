import H0mework.Versions.Y.Arithmetic.RieszForcing.ForcingMeanZero
import H0mework.Versions.Y.Arithmetic.SonineProjection.Ward

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Euler.WindowTest

open Complex Filter MeasureTheory Set
open scoped Topology ContDiff
open Translator.ForcingMeanZero Constructor
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

private theorem phase_contDiff (frequency : ℝ) : ContDiff ℝ ∞ (phase frequency) := by
  unfold phase
  simp only [Real.fourierChar_apply]
  have realSource : ContDiff ℝ ∞ (fun x : ℝ => 2 * Real.pi * -(frequency * x)) := by fun_prop
  have castSource : ContDiff ℝ ∞ (fun x : ℝ => ((2 * Real.pi * -(frequency * x) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp realSource
  exact (castSource.mul contDiff_const).cexp

def wave (frequency : ℝ) : SchwartzMap ℝ ℂ :=
  ((oneTest_compact.mul_right :
    HasCompactSupport (fun x : ℝ => oneTest x * phase frequency x))).toSchwartzMap
      ((oneTest.smooth ⊤).mul (phase_contDiff frequency))

theorem wave_eq (frequency : ℝ) {x : ℝ}
    (inside : x ∈ Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) :
    wave frequency x = phase frequency x := by
  change oneTest x * phase frequency x = _
  rw [oneTest_eq inside, one_mul]

theorem wave_deriv (frequency : ℝ) {x : ℝ}
    (inside : x ∈ Icc (-(1 / 4 : ℝ)) (1 / 4 : ℝ)) :
    deriv (wave frequency) x =
      -2 * (Real.pi : ℂ) * Complex.I * (frequency : ℂ) * phase frequency x := by
  have generated := (oneTest.hasDerivAt x).mul (phase_derivative frequency x)
  change deriv (fun y : ℝ => oneTest y * phase frequency y) x = _
  simpa only [Pi.mul_def, oneTest_eq inside, oneTest_deriv inside, zero_mul, one_mul,
    zero_add] using generated.deriv

end
end OriginalRieszSource.Euler.WindowTest
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
