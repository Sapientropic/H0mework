import H0mework.Versions.V2.Arithmetic.RieszEuler.GapEulerFourier
import H0mework.Versions.V2.Arithmetic.RiemannUnitRegularity.Euler
import H0mework.Versions.V2.Arithmetic.RemainderSource.ResolventBoundary

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszSource.Dilation

open Complex Filter MeasureTheory
open scoped Topology
open GapEuler
noncomputable section
attribute [local instance 1100] NormedSpace.complexToReal

theorem euler_test (value : TemperedDistribution ℝ ℂ) (test : SchwartzMap ℝ ℂ) :
    euler value test = -(1 / 2 : ℂ) * value test -
      value (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
        (SchwartzMap.derivCLM ℂ ℂ test)) := by
  have source := congrArg (fun T : TemperedDistribution ℝ ℂ => T test) (derivative_position value)
  simp only [TemperedDistribution.derivCLM_apply_apply, map_neg, add_apply] at source
  change -value (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
      (SchwartzMap.derivCLM ℂ ℂ test)) =
    (position (TemperedDistribution.derivCLM ℂ value)) test + value test at source
  change (position (TemperedDistribution.derivCLM ℂ value)) test + (1 / 2 : ℂ) * value test = _
  linear_combination -source

theorem original_weak_at_zero (value : BurnolL2) (test : SchwartzMap ℝ ℂ) :
    HasDerivAt (fun h : ℝ => (burnolMultiplicativeDilation h value : TemperedDistribution ℝ ℂ) test)
      (euler (value : TemperedDistribution ℝ ℂ) test) 0 := by
  have source := burnolDilation_weakDerivative value test
  have reparam : HasDerivAt (fun h : ℝ => -2 * h) (-2 : ℝ) 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).const_mul (-2 : ℝ) using 1
    norm_num
  have generated := source.scomp_of_eq (0 : ℝ) reparam (by norm_num)
  have arguments : (fun h : ℝ => (Lp.toTemperedDistributionCLM ℂ volume 2
      (burnolMultiplicativeDilation (-(-2 * h) / 2) value)) test) =
      (fun h : ℝ => (burnolMultiplicativeDilation h value : TemperedDistribution ℝ ℂ) test) := by
    funext h
    rw [show -(-2 * h) / 2 = h by ring]
    rfl
  change HasDerivAt (fun h : ℝ => (Lp.toTemperedDistributionCLM ℂ volume 2
      (burnolMultiplicativeDilation (-(-2 * h) / 2) value)) test)
    ((-2 : ℝ) • ((1 / 4 : ℂ) * (Lp.toTemperedDistributionCLM ℂ volume 2 value) test +
      (1 / 2 : ℂ) * (Lp.toTemperedDistributionCLM ℂ volume 2 value)
        (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
          (SchwartzMap.derivCLM ℂ ℂ test)))) 0 at generated
  rw [arguments] at generated
  convert! generated using 1
  rw [euler_test]
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    Lp.toTemperedDistributionCLM_apply]
  ring

theorem original_weak_derivative (value : BurnolL2) (test : SchwartzMap ℝ ℂ) (shift : ℝ) :
    HasDerivAt (fun h : ℝ => (burnolMultiplicativeDilation h value : TemperedDistribution ℝ ℂ) test)
      (euler (burnolMultiplicativeDilation shift value : TemperedDistribution ℝ ℂ) test) shift := by
  have source := original_weak_at_zero (burnolMultiplicativeDilation shift value) test
  have shiftDerivative : HasDerivAt (fun h : ℝ => h - shift) 1 shift :=
    (hasDerivAt_id shift).sub_const shift
  have generated := source.scomp_of_eq shift shiftDerivative (by simp)
  have argument : (fun h : ℝ =>
      (burnolMultiplicativeDilation (h - shift) (burnolMultiplicativeDilation shift value) :
        TemperedDistribution ℝ ℂ) test) =
      (fun h : ℝ => (burnolMultiplicativeDilation h value : TemperedDistribution ℝ ℂ) test) := by
    funext h
    rw [burnolMultiplicativeDilation_add, sub_add_cancel]
  simpa only [Function.comp_def, argument, one_smul] using generated

end
end OriginalRieszSource.Dilation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
