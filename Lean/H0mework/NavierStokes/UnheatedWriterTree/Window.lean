import H0mework.NavierStokes.UnheatedWriterTree.Time
import H0mework.NavierStokes.UnheatedWriterTriad.Window

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeWindow
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeUnheatedTreeTime NativeUnheatedIntegralBilinear NativeUnheatedStressPairEvolution NativeUnheatedPairGlobalWindow
noncomputable section
variable {nu : Viscosity} {n : ℕ}

theorem forcing_integrable (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (forcing seed slots) volume start finish := by
  have p : IntervalIntegrable (product seed slots) volume start finish :=
    (product_ac seed slots start finish start0 finish0).continuousOn.intervalIntegrable
  have paid := (productRate_integrable seed slots start finish start0 finish0).add (p.smul (sumRate nu slots))
  apply paid.congr_ae
  filter_upwards [ae_restrict_of_ae (productRate_split_ae seed slots), ae_restrict_mem measurableSet_uIoc] with time actual inside
  have nonnegative := (le_min start0 finish0).trans (uIoc_subset_uIcc inside).1
  change productRate seed slots time+sumRate nu slots • product seed slots time = _
  rw [actual nonnegative]
  abel

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (order : ℕ)
    (observation clockOrigin start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    sumRate nu slots • (∫ time in start..finish, kernelWeight order observation clockOrigin time • product seed slots time) =
      (∫ time in start..finish, kernelWeight order observation clockOrigin time • forcing seed slots time) -
      (∫ time in start..finish, kernelWeight (order+1) observation clockOrigin time • product seed slots time) -
      (kernelWeight order observation clockOrigin finish • product seed slots finish -
        kernelWeight order observation clockOrigin start • product seed slots start) := by
  have base : IntervalIntegrable (product seed slots) volume start finish :=
    (product_ac seed slots start finish start0 finish0).continuousOn.intervalIntegrable
  have p (order : ℕ) := base.continuousOn_smul (kernelWeight_continuous order observation clockOrigin).continuousOn
  have q := (forcing_integrable seed slots start finish start0 finish0).continuousOn_smul
    (kernelWeight_continuous order observation clockOrigin).continuousOn
  have scaled : IntervalIntegrable (fun time => sumRate nu slots •
      (kernelWeight order observation clockOrigin time • product seed slots time)) volume start finish := by
    simpa only [Pi.smul_apply] using! (p order).smul (sumRate nu slots)
  have written := integral_of_ac_derivative
    (fun time => kernelWeight order observation clockOrigin time • product seed slots time)
    (fun time => kernelWeight order observation clockOrigin time • forcing seed slots time -
      kernelWeight (order+1) observation clockOrigin time • product seed slots time -
      sumRate nu slots • (kernelWeight order observation clockOrigin time • product seed slots time))
    ((kernel_ac order observation clockOrigin start finish).smul (product_ac seed slots start finish start0 finish0))
    ((q.sub (p (order+1))).sub scaled) (by
      filter_upwards [product_hasDerivAt_ae seed slots, productRate_split_ae seed slots, volume.ae_ne (0 : ℝ)] with time actual split nonzero
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
end SaturationMonoid.NavierStokes.NativeUnheatedTreeWindow
