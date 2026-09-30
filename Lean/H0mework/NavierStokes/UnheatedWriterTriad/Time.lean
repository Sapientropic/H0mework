import H0mework.NavierStokes.UnheatedWriterTriad.Rows

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeUnheatedTriadTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativeUnheatedTriadRows NativeUnheatedIntegralBilinear
noncomputable section
variable {nu : Viscosity}
abbrev Slot := IntegerWavevector × Coordinate

def product (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot) (time : ℝ) : ℂ :=
  velocity seed time a.1 a.2 * velocity seed time b.1 b.2 * velocity seed time c.1 c.2

def forcing (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot) (time : ℝ) : ℂ :=
  action seed time a.1 a.2 * velocity seed time b.1 b.2 * velocity seed time c.1 c.2 +
  velocity seed time a.1 a.2 * action seed time b.1 b.2 * velocity seed time c.1 c.2 +
  velocity seed time a.1 a.2 * velocity seed time b.1 b.2 * action seed time c.1 c.2

def sumRate (nu : Viscosity) (a b c : Slot) : ℝ :=
  nu.coeff * (integerWaveViscousMultiplier a.1 + integerWaveViscousMultiplier b.1 + integerWaveViscousMultiplier c.1)

def productRate (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot) (time : ℝ) : ℂ :=
  derivative seed time a.1 a.2 * velocity seed time b.1 b.2 * velocity seed time c.1 c.2 +
  velocity seed time a.1 a.2 * derivative seed time b.1 b.2 * velocity seed time c.1 c.2 +
  velocity seed time a.1 a.2 * velocity seed time b.1 b.2 * derivative seed time c.1 c.2

theorem productRate_split_ae (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot) :
    ∀ᵐ time : ℝ, 0 ≤ time → productRate seed a b c time =
      forcing seed a b c time - sumRate nu a b c • product seed a b c time := by
  filter_upwards [derivative_split_ae seed] with time actual nonnegative
  simp only [productRate, actual nonnegative, forcing, product, sumRate, Complex.real_smul]
  push_cast
  ring

theorem product_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (product seed a b c) (productRate seed a b c time) time := by
  filter_upwards [velocity_hasDerivAt_ae seed a.1 a.2, velocity_hasDerivAt_ae seed b.1 b.2,
    velocity_hasDerivAt_ae seed c.1 c.2] with time da db dc positive
  have actual := ((da positive).mul (db positive)).mul (dc positive)
  convert! actual using 1
  simp only [productRate, Pi.mul_apply]
  ring

theorem product_ac (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    AbsolutelyContinuousOnInterval (product seed a b c) start finish := by
  simpa only [product, Pi.smul_apply, smul_eq_mul] using!
    ((velocity_ac seed start finish start0 finish0 a.1 a.2).smul
      (velocity_ac seed start finish start0 finish0 b.1 b.2)).smul
      (velocity_ac seed start finish start0 finish0 c.1 c.2)

theorem productRate_integrable (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (productRate seed a b c) volume start finish := by
  have u (s : Slot) := (velocity_ac seed start finish start0 finish0 s.1 s.2).continuousOn
  have d (s : Slot) := derivative_integrable seed start finish start0 finish0 s.1 s.2
  have first := ((d a).mul_continuousOn (u b)).mul_continuousOn (u c)
  have second := ((d b).continuousOn_mul (u a)).mul_continuousOn (u c)
  have third := (d c).continuousOn_mul ((u a).mul (u b))
  simpa only [productRate, Pi.add_apply, Pi.mul_apply] using! (first.add second).add third

theorem product_write (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    product seed a b c finish - product seed a b c start =
      ∫ time in start..finish, forcing seed a b c time - sumRate nu a b c • product seed a b c time := by
  have paid := productRate_integrable seed a b c start finish start0 finish0
  have written := integral_of_ac_derivative (product seed a b c) (productRate seed a b c)
    (product_ac seed a b c start finish start0 finish0) paid (by
      filter_upwards [product_hasDerivAt_ae seed a b c, volume.ae_ne (0 : ℝ)] with time actual nonzero
      intro inside
      exact actual (lt_of_le_of_ne ((le_min start0 finish0).trans inside.1) (Ne.symm nonzero)))
  rw [written]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [productRate_split_ae seed a b c] with time actual inside
  exact actual ((le_min start0 finish0).trans (uIoc_subset_uIcc inside).1)

theorem product_next (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    product seed a b c (response.2.clockAdvance + time) = product response.1 a b c time := by
  simp only [product, velocity_next seed response generated time nonnegative]

theorem forcing_next (seed : GeneratedWholeRestartCurrent nu) (a b c : Slot)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    forcing seed a b c (response.2.clockAdvance + time) = forcing response.1 a b c time := by
  simp only [forcing, velocity_next seed response generated time nonnegative, action_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTriadTime
