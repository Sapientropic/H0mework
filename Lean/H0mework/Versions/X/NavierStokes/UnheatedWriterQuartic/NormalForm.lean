import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.Window
import H0mework.Versions.X.NavierStokes.UnheatedWriterQuartic.Kernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuarticNormalForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedQuarticTime NativeUnheatedQuarticKernel
open NativeUnheatedStressPairEvolution
noncomputable section
variable {nu : Viscosity}

def primitive (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (kernel : ℂ) (time : ℝ) : ℂ :=
  normalizer nu a b c d kernel*product seed a b c d time

def quintic (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (kernel : ℂ) (time : ℝ) : ℂ :=
  normalizer nu a b c d kernel*forcing seed a b c d time

theorem primitive_integrable (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (primitive seed a b c d kernel) volume start finish :=
  ((product_ac seed a b c d start finish start0 finish0).continuousOn.intervalIntegrable).const_mul _

theorem quintic_integrable (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (quintic seed a b c d kernel) volume start finish :=
  (NativeUnheatedQuarticWindow.forcing_integrable seed a b c d start finish start0 finish0).const_mul _

theorem primitive_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (kernel : ℂ) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (primitive seed a b c d kernel)
      (quintic seed a b c d kernel time-kernel*product seed a b c d time) time := by
  filter_upwards [product_hasDerivAt_ae seed a b c d, productRate_split_ae seed a b c d] with time actual split positive
  have derivative := (actual positive).const_mul (normalizer nu a b c d kernel)
  rw [split positive.le, mul_sub, normalizer_product seed a b c d kernel time] at derivative
  exact derivative

theorem row_write (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    primitive seed a b c d kernel finish-primitive seed a b c d kernel start =
      ∫ time in start..finish, quintic seed a b c d kernel time-kernel*product seed a b c d time := by
  rw [primitive, primitive, ← mul_sub, product_write seed a b c d start finish start0 finish0,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only
  rw [mul_sub, normalizer_product seed a b c d kernel time]
  rfl

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (kernel : ℂ) (order : ℕ)
    (observation origin start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    (∫ time in start..finish, kernelWeight order observation origin time • (kernel*product seed a b c d time)) =
    (∫ time in start..finish, kernelWeight order observation origin time • quintic seed a b c d kernel time) -
    (∫ time in start..finish, kernelWeight (order+1) observation origin time • primitive seed a b c d kernel time) -
    (kernelWeight order observation origin finish • primitive seed a b c d kernel finish -
      kernelWeight order observation origin start • primitive seed a b c d kernel start) := by
  calc
    _ = ∫ time in start..finish, normalizer nu a b c d kernel *
        (sumRate nu a b c d • (kernelWeight order observation origin time • product seed a b c d time)) := by
      apply intervalIntegral.integral_congr
      intro time _
      dsimp only
      rw [smul_comm (sumRate nu a b c d), mul_smul_comm, normalizer_product seed a b c d kernel time]
    _ = normalizer nu a b c d kernel*(sumRate nu a b c d •
        (∫ time in start..finish, kernelWeight order observation origin time • product seed a b c d time)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_smul]
    _ = _ := by
      rw [NativeUnheatedQuarticWindow.weighted_write seed a b c d order observation origin start finish start0 finish0]
      simp only [mul_sub, ← intervalIntegral.integral_const_mul, mul_smul_comm, primitive, quintic]

theorem primitive_next (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (kernel : ℂ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitive seed a b c d kernel (response.2.clockAdvance+time) = primitive response.1 a b c d kernel time := by
  rw [primitive, primitive, product_next seed a b c d response generated time nonnegative]

theorem quintic_next (seed : GeneratedWholeRestartCurrent nu) (a b c d : Slot) (kernel : ℂ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    quintic seed a b c d kernel (response.2.clockAdvance+time) = quintic response.1 a b c d kernel time := by
  rw [quintic, quintic, forcing_next seed a b c d response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuarticNormalForm
