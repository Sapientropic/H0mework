import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.Time

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedTriadRows NativeUnheatedIntegralBilinear
noncomputable section
variable {nu : Viscosity}
abbrev Slot := NativeUnheatedQuarticTime.Slot

def product (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (time : ℝ) : ℂ :=
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2*velocity seed time e.1 e.2

def forcing (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (time : ℝ) : ℂ :=
  action seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2*velocity seed time e.1 e.2 +
  velocity seed time a.1 a.2*action seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2*velocity seed time e.1 e.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*action seed time c.1 c.2*velocity seed time d.1 d.2*velocity seed time e.1 e.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*action seed time d.1 d.2*velocity seed time e.1 e.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2*action seed time e.1 e.2

def sumRate (nu : Viscosity) (a b c d e : Slot) : ℝ :=
  nu.coeff*(integerWaveViscousMultiplier a.1+integerWaveViscousMultiplier b.1+
    integerWaveViscousMultiplier c.1+integerWaveViscousMultiplier d.1+integerWaveViscousMultiplier e.1)

def productRate (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (time : ℝ) : ℂ :=
  derivative seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2*velocity seed time e.1 e.2 +
  velocity seed time a.1 a.2*derivative seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2*velocity seed time e.1 e.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*derivative seed time c.1 c.2*velocity seed time d.1 d.2*velocity seed time e.1 e.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*derivative seed time d.1 d.2*velocity seed time e.1 e.2 +
  velocity seed time a.1 a.2*velocity seed time b.1 b.2*velocity seed time c.1 c.2*velocity seed time d.1 d.2*derivative seed time e.1 e.2

theorem productRate_split_ae (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) :
    ∀ᵐ time : ℝ, 0 ≤ time → productRate seed a b c d e time =
      forcing seed a b c d e time-sumRate nu a b c d e • product seed a b c d e time := by
  filter_upwards [derivative_split_ae seed] with time actual nonnegative
  simp only [productRate, actual nonnegative, forcing, product, sumRate, Complex.real_smul]
  push_cast
  ring

theorem productRate_grouped (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (time : ℝ) :
    productRate seed a b c d e time = NativeUnheatedQuarticTime.productRate seed a b c d time*velocity seed time e.1 e.2 +
      NativeUnheatedQuarticTime.product seed a b c d time*derivative seed time e.1 e.2 := by
  simp only [productRate, NativeUnheatedQuarticTime.productRate, NativeUnheatedQuarticTime.product]
  ring

theorem product_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (product seed a b c d e) (productRate seed a b c d e time) time := by
  filter_upwards [NativeUnheatedQuarticTime.product_hasDerivAt_ae seed a b c d,
    velocity_hasDerivAt_ae seed e.1 e.2] with time triple last positive
  have actual := (triple positive).mul (last positive)
  convert! actual using 1
  exact productRate_grouped seed a b c d e time

theorem product_ac (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    AbsolutelyContinuousOnInterval (product seed a b c d e) start finish := by
  simpa only [product, NativeUnheatedQuarticTime.product, Pi.smul_apply, smul_eq_mul] using!
    (NativeUnheatedQuarticTime.product_ac seed a b c d start finish start0 finish0).smul
      (velocity_ac seed start finish start0 finish0 e.1 e.2)

theorem productRate_integrable (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (productRate seed a b c d e) volume start finish := by
  have first := (NativeUnheatedQuarticTime.productRate_integrable seed a b c d start finish start0 finish0).mul_continuousOn
    (velocity_ac seed start finish start0 finish0 e.1 e.2).continuousOn
  have last := (derivative_integrable seed start finish start0 finish0 e.1 e.2).continuousOn_mul
    (NativeUnheatedQuarticTime.product_ac seed a b c d start finish start0 finish0).continuousOn
  convert! first.add last using 1
  funext time
  exact productRate_grouped seed a b c d e time

theorem product_write (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    product seed a b c d e finish-product seed a b c d e start =
      ∫ time in start..finish, forcing seed a b c d e time-sumRate nu a b c d e • product seed a b c d e time := by
  have paid := productRate_integrable seed a b c d e start finish start0 finish0
  have written := integral_of_ac_derivative (product seed a b c d e) (productRate seed a b c d e)
    (product_ac seed a b c d e start finish start0 finish0) paid (by
      filter_upwards [product_hasDerivAt_ae seed a b c d e, volume.ae_ne (0 : ℝ)] with time actual nonzero
      intro inside
      exact actual (lt_of_le_of_ne ((le_min start0 finish0).trans inside.1) (Ne.symm nonzero)))
  rw [written]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [productRate_split_ae seed a b c d e] with time actual inside
  exact actual ((le_min start0 finish0).trans (uIoc_subset_uIcc inside).1)

theorem product_next (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    product seed a b c d e (response.2.clockAdvance+time) = product response.1 a b c d e time := by
  simp only [product, velocity_next seed response generated time nonnegative]

theorem forcing_next (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    forcing seed a b c d e (response.2.clockAdvance+time) = forcing response.1 a b c d e time := by
  simp only [forcing, velocity_next seed response generated time nonnegative, action_next seed response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticTime
