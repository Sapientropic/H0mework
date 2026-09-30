import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Window
import H0mework.Versions.X.NavierStokes.UnheatedWriterTree.Output

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeNormalForm
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeEndpointVelocityCarrier
open NativeUnheatedTreeTime NativeUnheatedTreeOutput NativeUnheatedStressPairEvolution
noncomputable section
variable {nu : Viscosity} {n : ℕ}

theorem product_zero_rate (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot)
    (zero : sumRate nu slots = 0) (time : ℝ) : product seed slots time = 0 := by
  unfold product
  apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (n+1)))
  simp only [NativeUnheatedTriadRows.velocity, NativeUnheatedTriadRows.decode_apply,
    rate_zero_wave slots zero 0, wholeVelocity_zero, Pi.zero_apply, smul_zero]

theorem forcing_zero_rate (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot)
    (zero : sumRate nu slots = 0) (time : ℝ) : forcing seed slots time = 0 := by
  unfold forcing
  apply Finset.sum_eq_zero
  intro number _
  simp only [NativeUnheatedTriadRows.action, NativeUnheatedTriadRows.decode_apply,
    rate_zero_wave slots zero number, wholeVelocity_zero, Pi.zero_apply, smul_zero, zero_mul]

def normalizer (nu : Viscosity) (slots : Fin (n+1) → Slot) (kernel : ℂ) : ℂ := (sumRate nu slots)⁻¹ • kernel

theorem normalizer_product (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ) (time : ℝ) :
    normalizer nu slots kernel*(sumRate nu slots • product seed slots time) = kernel*product seed slots time := by
  by_cases zero : sumRate nu slots = 0
  · rw [product_zero_rate seed slots zero time, smul_zero, mul_zero, mul_zero]
  · simp only [normalizer, Complex.real_smul, ← mul_assoc, mul_right_comm _ kernel,
      ← Complex.ofReal_mul, inv_mul_cancel₀ zero, Complex.ofReal_one, one_mul]
    exact mul_comm _ _

def primitive (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ) (time : ℝ) : ℂ :=
  normalizer nu slots kernel*product seed slots time

def nextForcing (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ) (time : ℝ) : ℂ :=
  normalizer nu slots kernel*forcing seed slots time

theorem primitive_original (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ) (time : ℝ) :
    primitive seed slots kernel time = (sumRate nu slots)⁻¹ • (kernel*product seed slots time) := by
  simp only [primitive, normalizer, smul_mul_assoc]

theorem primitive_ac (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    AbsolutelyContinuousOnInterval (primitive seed slots kernel) start finish := by
  simpa only [primitive, Pi.smul_apply, smul_eq_mul] using!
    (product_ac seed slots start finish start0 finish0).const_smul (normalizer nu slots kernel)

theorem primitive_integrable (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (primitive seed slots kernel) volume start finish :=
  (primitive_ac seed slots kernel start finish start0 finish0).continuousOn.intervalIntegrable

theorem nextForcing_integrable (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (nextForcing seed slots kernel) volume start finish :=
  (NativeUnheatedTreeWindow.forcing_integrable seed slots start finish start0 finish0).const_mul _

theorem primitive_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (primitive seed slots kernel)
      (nextForcing seed slots kernel time-kernel*product seed slots time) time := by
  filter_upwards [product_hasDerivAt_ae seed slots, productRate_split_ae seed slots] with time actual split positive
  have derivative := (actual positive).const_mul (normalizer nu slots kernel)
  rw [split positive.le, mul_sub, normalizer_product seed slots kernel time] at derivative
  exact derivative

theorem row_write (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ)
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    primitive seed slots kernel finish-primitive seed slots kernel start =
      ∫ time in start..finish, nextForcing seed slots kernel time-kernel*product seed slots time := by
  rw [primitive, primitive, ← mul_sub, product_write seed slots start finish start0 finish0,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro time _
  dsimp only
  rw [mul_sub, normalizer_product seed slots kernel time]
  rfl

theorem weighted_write (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ) (order : ℕ)
    (observation origin start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    (∫ time in start..finish, kernelWeight order observation origin time • (kernel*product seed slots time)) =
      (∫ time in start..finish, kernelWeight order observation origin time • nextForcing seed slots kernel time) -
      (∫ time in start..finish, kernelWeight (order+1) observation origin time • primitive seed slots kernel time) -
      (kernelWeight order observation origin finish • primitive seed slots kernel finish -
        kernelWeight order observation origin start • primitive seed slots kernel start) := by
  calc
    _ = ∫ time in start..finish, normalizer nu slots kernel *
        (sumRate nu slots • (kernelWeight order observation origin time • product seed slots time)) := by
      apply intervalIntegral.integral_congr
      intro time _
      dsimp only
      rw [smul_comm (sumRate nu slots), mul_smul_comm, normalizer_product seed slots kernel time]
    _ = normalizer nu slots kernel*(sumRate nu slots •
        (∫ time in start..finish, kernelWeight order observation origin time • product seed slots time)) := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_smul]
    _ = _ := by
      rw [NativeUnheatedTreeWindow.weighted_write seed slots order observation origin start finish start0 finish0]
      simp only [mul_sub, ← intervalIntegral.integral_const_mul, mul_smul_comm, primitive, nextForcing]

theorem primitive_next (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    primitive seed slots kernel (response.2.clockAdvance+time) = primitive response.1 slots kernel time := by
  rw [primitive, primitive, product_next seed slots response generated time nonnegative]

theorem nextForcing_next (seed : GeneratedWholeRestartCurrent nu) (slots : Fin (n+1) → Slot) (kernel : ℂ)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    nextForcing seed slots kernel (response.2.clockAdvance+time) = nextForcing response.1 slots kernel time := by
  rw [nextForcing, nextForcing, forcing_next seed slots response generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeNormalForm
