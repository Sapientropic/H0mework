import H0mework.Versions.X.NavierStokes.UnheatedWriterQuintic.Window
import H0mework.Versions.X.NavierStokes.UnheatedWriterTriad.Kernel

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedQuinticNormalForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedQuinticTime NativeUnheatedTriadKernel NativeEndpointVelocityCarrier
open NativeUnheatedStressPairEvolution
noncomputable section
variable {nu : Viscosity}

theorem rate_nonnegative (a b c d e : Slot) : 0 ≤ sumRate nu a b c d e :=
  mul_nonneg nu.coeff_pos.le (add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (multiplier_nonnegative a.1) (multiplier_nonnegative b.1)) (multiplier_nonnegative c.1))
      (multiplier_nonnegative d.1)) (multiplier_nonnegative e.1))

theorem rate_zero_first (a b c d e : Slot) (zero : sumRate nu a b c d e = 0) : a.1 = 0 := by
  by_contra nonzero
  have positive : 0 < integerWaveViscousMultiplier a.1 := mul_pos (by positivity) (integerWaveNormSq_pos nonzero)
  unfold sumRate at zero
  nlinarith [nu.coeff_pos, multiplier_nonnegative b.1, multiplier_nonnegative c.1,
    multiplier_nonnegative d.1, multiplier_nonnegative e.1]

theorem product_zero_rate (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot)
    (zero : sumRate nu a b c d e = 0) (time : ℝ) : product seed a b c d e time = 0 := by
  have first := rate_zero_first a b c d e zero
  simp only [product, NativeUnheatedTriadRows.velocity, NativeUnheatedTriadRows.decode_apply,
    first, wholeVelocity_zero, Pi.zero_apply, smul_zero, zero_mul]

theorem forcing_zero_rate (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot)
    (zero : sumRate nu a b c d e = 0) (time : ℝ) : forcing seed a b c d e time = 0 := by
  have first := rate_zero_first a b c d e zero
  simp only [forcing, NativeUnheatedTriadRows.velocity, NativeUnheatedTriadRows.action,
    NativeUnheatedTriadRows.decode_apply, first, wholeVelocity_zero, Pi.zero_apply, smul_zero, zero_mul, add_zero]

def normalizer (nu : Viscosity) (a b c d e : Slot) (kernel : ℂ) : ℂ := (sumRate nu a b c d e)⁻¹ • kernel

theorem normalizer_product (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ) (time : ℝ) :
    normalizer nu a b c d e kernel*(sumRate nu a b c d e • product seed a b c d e time) = kernel*product seed a b c d e time := by
  by_cases zero : sumRate nu a b c d e = 0
  · rw [product_zero_rate seed a b c d e zero time, smul_zero, mul_zero, mul_zero]
  · simp only [normalizer, Complex.real_smul, ← mul_assoc, mul_right_comm _ kernel,
      ← Complex.ofReal_mul, inv_mul_cancel₀ zero, Complex.ofReal_one, one_mul]
    exact mul_comm _ _

def primitive (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ) (time : ℝ) : ℂ :=
  normalizer nu a b c d e kernel*product seed a b c d e time

def sextic (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ) (time : ℝ) : ℂ :=
  normalizer nu a b c d e kernel*forcing seed a b c d e time

theorem primitive_integrable (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (primitive seed a b c d e kernel) volume start finish :=
  ((product_ac seed a b c d e start finish start0 finish0).continuousOn.intervalIntegrable).const_mul _

theorem sextic_integrable (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (sextic seed a b c d e kernel) volume start finish :=
  (NativeUnheatedQuinticWindow.forcing_integrable seed a b c d e start finish start0 finish0).const_mul _

theorem primitive_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (primitive seed a b c d e kernel)
      (sextic seed a b c d e kernel time-kernel*product seed a b c d e time) time := by
  filter_upwards [product_hasDerivAt_ae seed a b c d e, productRate_split_ae seed a b c d e] with time actual split positive
  have derivative := (actual positive).const_mul (normalizer nu a b c d e kernel)
  rw [split positive.le, mul_sub, normalizer_product seed a b c d e kernel time] at derivative
  exact derivative

theorem row_write (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    primitive seed a b c d e kernel finish-primitive seed a b c d e kernel start =
      ∫ time in start..finish, sextic seed a b c d e kernel time-kernel*product seed a b c d e time := by
  rw [primitive, primitive, ← mul_sub, product_write seed a b c d e start finish start0 finish0,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only
  rw [mul_sub, normalizer_product seed a b c d e kernel time]
  rfl

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ) (order : ℕ)
    (observation origin start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    (∫ time in start..finish, kernelWeight order observation origin time • (kernel*product seed a b c d e time)) =
    (∫ time in start..finish, kernelWeight order observation origin time • sextic seed a b c d e kernel time) -
    (∫ time in start..finish, kernelWeight (order+1) observation origin time • primitive seed a b c d e kernel time) -
    (kernelWeight order observation origin finish • primitive seed a b c d e kernel finish -
      kernelWeight order observation origin start • primitive seed a b c d e kernel start) := by
  calc
    _ = ∫ time in start..finish, normalizer nu a b c d e kernel *
        (sumRate nu a b c d e • (kernelWeight order observation origin time • product seed a b c d e time)) := by
      apply intervalIntegral.integral_congr
      intro time _
      dsimp only
      rw [smul_comm (sumRate nu a b c d e), mul_smul_comm, normalizer_product seed a b c d e kernel time]
    _ = normalizer nu a b c d e kernel*(sumRate nu a b c d e •
        (∫ time in start..finish, kernelWeight order observation origin time • product seed a b c d e time)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_smul]
    _ = _ := by
      rw [NativeUnheatedQuinticWindow.weighted_write seed a b c d e order observation origin start finish start0 finish0]
      simp only [mul_sub, ← intervalIntegral.integral_const_mul, mul_smul_comm, primitive, sextic]

theorem primitive_next (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitive seed a b c d e kernel (response.2.clockAdvance+time) = primitive response.1 a b c d e kernel time := by
  rw [primitive, primitive, product_next seed a b c d e response generated time nonnegative]

theorem sextic_next (seed : GeneratedWholeRestartCurrent nu) (a b c d e : Slot) (kernel : ℂ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    sextic seed a b c d e kernel (response.2.clockAdvance+time) = sextic response.1 a b c d e kernel time := by
  rw [sextic, sextic, forcing_next seed a b c d e response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedQuinticNormalForm
