import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Time
import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Window

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedQuinticTime NativeUnheatedIntegralBilinear NativeUnheatedStressPairEvolution NativeUnheatedPairGlobalWindow
noncomputable section
variable {nu : Viscosity}

theorem forcing_integrable (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (forcing seed a b c d e) volume start finish := by
  have p : IntervalIntegrable (product seed a b c d e) volume start finish :=
    (product_ac seed a b c d e start finish start0 finish0).continuousOn.intervalIntegrable
  have paid := (productRate_integrable seed a b c d e start finish start0 finish0).add (p.smul (sumRate nu a b c d e))
  apply paid.congr_ae
  filter_upwards [ae_restrict_of_ae (productRate_split_ae seed a b c d e), ae_restrict_mem measurableSet_uIoc] with time actual inside
  have nonnegative := (le_min start0 finish0).trans (uIoc_subset_uIcc inside).1
  change productRate seed a b c d e time+sumRate nu a b c d e • product seed a b c d e time = _
  rw [actual nonnegative]
  abel

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (order : ℕ)
    (observation clockOrigin start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    sumRate nu a b c d e • (∫ time in start..finish,
      kernelWeight order observation clockOrigin time • product seed a b c d e time) =
      (∫ time in start..finish, kernelWeight order observation clockOrigin time • forcing seed a b c d e time) -
      (∫ time in start..finish, kernelWeight (order+1) observation clockOrigin time • product seed a b c d e time) -
      (kernelWeight order observation clockOrigin finish • product seed a b c d e finish -
        kernelWeight order observation clockOrigin start • product seed a b c d e start) := by
  have base : IntervalIntegrable (product seed a b c d e) volume start finish :=
    (product_ac seed a b c d e start finish start0 finish0).continuousOn.intervalIntegrable
  have p (n : ℕ) := base.continuousOn_smul (kernelWeight_continuous n observation clockOrigin).continuousOn
  have q := (forcing_integrable seed a b c d e start finish start0 finish0).continuousOn_smul
    (kernelWeight_continuous order observation clockOrigin).continuousOn
  have scaled : IntervalIntegrable (fun time => sumRate nu a b c d e •
      (kernelWeight order observation clockOrigin time • product seed a b c d e time)) volume start finish := by
    simpa only [Pi.smul_apply] using! (p order).smul (sumRate nu a b c d e)
  have written := integral_of_ac_derivative
    (fun time => kernelWeight order observation clockOrigin time • product seed a b c d e time)
    (fun time => kernelWeight order observation clockOrigin time • forcing seed a b c d e time -
      kernelWeight (order+1) observation clockOrigin time • product seed a b c d e time -
      sumRate nu a b c d e • (kernelWeight order observation clockOrigin time • product seed a b c d e time))
    ((kernel_ac order observation clockOrigin start finish).smul (product_ac seed a b c d e start finish start0 finish0))
    ((q.sub (p (order+1))).sub scaled) (by
      filter_upwards [product_hasDerivAt_ae seed a b c d e, productRate_split_ae seed a b c d e, volume.ae_ne (0 : ℝ)] with time actual split nonzero
      intro inside
      have nonnegative := (le_min start0 finish0).trans inside.1
      have derivative := (kernelWeight_hasDerivAt order observation clockOrigin time).smul
        (actual (lt_of_le_of_ne nonnegative (Ne.symm nonzero)))
      rw [split nonnegative] at derivative
      convert! derivative using 1
      simp only [smul_sub, neg_smul, Complex.real_smul]
      ring)
  rw [intervalIntegral.integral_sub (q.sub (p (order+1))) scaled,
    intervalIntegral.integral_sub q (p (order+1)), intervalIntegral.integral_smul] at written
  linear_combination written

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticWindow
