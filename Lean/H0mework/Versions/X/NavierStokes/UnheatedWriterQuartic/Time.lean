import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Time

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedTriadRows NativeUnheatedIntegralBilinear
noncomputable section
variable {nu : Viscosity}
abbrev Slot := NativeUnheatedTriadTime.Slot

def product (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (time : ℝ) : ℂ :=
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2

def forcing (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (time : ℝ) : ℂ :=
  action seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2 +
  velocity seed time a.1 a.2*action seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*action seed time c.1 c.2*velocity seed time d.1 d.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*action seed time d.1 d.2

def sumRate (nu : Viscosity) (a b c d : Slot) : ℝ :=
  nu.coeff*(integerWaveViscousMultiplier a.1+integerWaveViscousMultiplier b.1+
    integerWaveViscousMultiplier c.1+integerWaveViscousMultiplier d.1)

def productRate (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (time : ℝ) : ℂ :=
  derivative seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2 +
  velocity seed time a.1 a.2*derivative seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*derivative seed time c.1 c.2*velocity seed time d.1 d.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*derivative seed time d.1 d.2

theorem productRate_split_ae (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) :
    ∀ᵐ time : ℝ, 0 ≤ time → productRate seed a b c d time =
      forcing seed a b c d time-sumRate nu a b c d • product seed a b c d time := by
  filter_upwards [derivative_split_ae seed] with time actual nonnegative
  simp only [productRate, actual nonnegative, forcing, product, sumRate, Complex.real_smul]
  push_cast
  ring

theorem productRate_grouped (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (time : ℝ) :
    productRate seed a b c d time = NativeUnheatedTriadTime.productRate seed a b c time*velocity seed time d.1 d.2 +
      NativeUnheatedTriadTime.product seed a b c time*derivative seed time d.1 d.2 := by
  simp only [productRate, NativeUnheatedTriadTime.productRate, NativeUnheatedTriadTime.product]
  ring

theorem product_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (product seed a b c d) (productRate seed a b c d time) time := by
  filter_upwards [NativeUnheatedTriadTime.product_hasDerivAt_ae seed a b c,
    velocity_hasDerivAt_ae seed d.1 d.2] with time triple last positive
  have actual := (triple positive).mul (last positive)
  convert! actual using 1
  exact productRate_grouped seed a b c d time

theorem product_ac (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    AbsolutelyContinuousOnInterval (product seed a b c d) start finish := by
  simpa only [product, NativeUnheatedTriadTime.product, Pi.smul_apply, smul_eq_mul] using!
    (NativeUnheatedTriadTime.product_ac seed a b c start finish start0 finish0).smul
      (velocity_ac seed start finish start0 finish0 d.1 d.2)

theorem productRate_integrable (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (productRate seed a b c d) volume start finish := by
  have first := (NativeUnheatedTriadTime.productRate_integrable seed a b c start finish start0 finish0).mul_continuousOn
    (velocity_ac seed start finish start0 finish0 d.1 d.2).continuousOn
  have last := (derivative_integrable seed start finish start0 finish0 d.1 d.2).continuousOn_mul
    (NativeUnheatedTriadTime.product_ac seed a b c start finish start0 finish0).continuousOn
  convert! first.add last using 1
  funext time
  exact productRate_grouped seed a b c d time

theorem product_write (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    product seed a b c d finish-product seed a b c d start =
      ∫ time in start..finish, forcing seed a b c d time-sumRate nu a b c d • product seed a b c d time := by
  have paid := productRate_integrable seed a b c d start finish start0 finish0
  have written := integral_of_ac_derivative (product seed a b c d) (productRate seed a b c d)
    (product_ac seed a b c d start finish start0 finish0) paid (by
      filter_upwards [product_hasDerivAt_ae seed a b c d, volume.ae_ne (0 : ℝ)] with time actual nonzero
      intro inside
      exact actual (lt_of_le_of_ne ((le_min start0 finish0).trans inside.1) (Ne.symm nonzero)))
  rw [written]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [productRate_split_ae seed a b c d] with time actual inside
  exact actual ((le_min start0 finish0).trans (uIoc_subset_uIcc inside).1)

theorem product_next (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    product seed a b c d (response.2.clockAdvance+time) = product response.1 a b c d time := by
  simp only [product, velocity_next seed response generated time nonnegative]

theorem forcing_next (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    forcing seed a b c d (response.2.clockAdvance+time) = forcing response.1 a b c d time := by
  simp only [forcing, velocity_next seed response generated time nonnegative, action_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticTime
