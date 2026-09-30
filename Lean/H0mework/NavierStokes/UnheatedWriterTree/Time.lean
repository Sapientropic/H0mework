import H0mework.NavierStokes.UnheatedWriterTriad.Rows

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeUnheatedTreeTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition NativeUnheatedTriadRows NativeUnheatedIntegralBilinear
noncomputable section
variable {nu : Viscosity} {n : ℕ}
abbrev Slot := IntegerWavevector × Coordinate

def product (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (time : ℝ) : ℂ :=
  ∏ number : Fin n, velocity seed time (slots number).1 (slots number).2

def cofactor (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (number : Fin n) (time : ℝ) : ℂ :=
  ∏ other ∈ Finset.univ.erase number, velocity seed time (slots other).1 (slots other).2

def forcing (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (time : ℝ) : ℂ :=
  ∑ number : Fin n, action seed time (slots number).1 (slots number).2*cofactor seed slots number time

def sumRate (nu : Viscosity) (slots : Fin n → Slot) : ℝ :=
  nu.coeff*∑ number : Fin n, integerWaveViscousMultiplier (slots number).1

def productRate (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (time : ℝ) : ℂ :=
  ∑ number : Fin n, derivative seed time (slots number).1 (slots number).2*cofactor seed slots number time

theorem velocity_cofactor (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (number : Fin n) (time : ℝ) :
    velocity seed time (slots number).1 (slots number).2*cofactor seed slots number time = product seed slots time :=
  Finset.mul_prod_erase Finset.univ (fun other => velocity seed time (slots other).1 (slots other).2) (Finset.mem_univ number)

theorem productRate_split_ae (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) :
    ∀ᵐ time : ℝ, 0 ≤ time → productRate seed slots time =
      forcing seed slots time-sumRate nu slots • product seed slots time := by
  filter_upwards [derivative_split_ae seed] with time actual nonnegative
  simp only [productRate, actual nonnegative, sub_mul, Finset.sum_sub_distrib, forcing]
  congr 1
  calc
    _ = ∑ number : Fin n, (nu.coeff*integerWaveViscousMultiplier (slots number).1) • product seed slots time := by
      apply Finset.sum_congr rfl
      intro number _
      rw [smul_mul_assoc, velocity_cofactor]
    _ = (∑ number : Fin n, nu.coeff*integerWaveViscousMultiplier (slots number).1) • product seed slots time := by rw [Finset.sum_smul]
    _ = _ := by rw [← Finset.mul_sum]; rfl

theorem partial_ac (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (selected : Finset (Fin n))
    (start finish : ℝ) (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    AbsolutelyContinuousOnInterval
      (fun time => ∏ number ∈ selected, velocity seed time (slots number).1 (slots number).2) start finish := by
  induction selected using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty] using
        (show ContDiffOn ℝ 1 (fun _ : ℝ => (1 : ℂ)) (uIcc start finish) from contDiffOn_const).absolutelyContinuousOnInterval
  | @insert number selected absent previous =>
      simpa only [Finset.prod_insert absent, Pi.smul_apply, smul_eq_mul] using!
        (velocity_ac seed start finish start0 finish0 (slots number).1 (slots number).2).smul previous

theorem product_ac (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    AbsolutelyContinuousOnInterval (product seed slots) start finish :=
  partial_ac seed slots Finset.univ start finish start0 finish0

theorem cofactor_ac (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (number : Fin n) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    AbsolutelyContinuousOnInterval (cofactor seed slots number) start finish :=
  partial_ac seed slots (Finset.univ.erase number) start finish start0 finish0

theorem product_hasDerivAt_ae (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) :
    ∀ᵐ time : ℝ, 0 < time → HasDerivAt (product seed slots) (productRate seed slots time) time := by
  have each : ∀ᵐ time : ℝ, ∀ number : Fin n, 0 < time →
      HasDerivAt (fun t => velocity seed t (slots number).1 (slots number).2)
        (derivative seed time (slots number).1 (slots number).2) time :=
    ae_all_iff.mpr (fun number => velocity_hasDerivAt_ae seed (slots number).1 (slots number).2)
  filter_upwards [each] with time actual positive
  have derived := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
    (fun number _ => actual number positive)
  simpa only [product, productRate, cofactor, smul_eq_mul, mul_comm] using! derived

theorem productRate_integrable (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    IntervalIntegrable (productRate seed slots) volume start finish := by
  have each (number : Fin n) := (derivative_integrable seed start finish start0 finish0 (slots number).1 (slots number).2).mul_continuousOn
    (cofactor_ac seed slots number start finish start0 finish0).continuousOn
  convert! IntervalIntegrable.sum Finset.univ (fun number _ => each number) using 1
  funext time
  simp only [productRate, Finset.sum_apply]

theorem product_write (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot) (start finish : ℝ)
    (start0 : 0 ≤ start) (finish0 : 0 ≤ finish) :
    product seed slots finish-product seed slots start =
      ∫ time in start..finish, forcing seed slots time-sumRate nu slots • product seed slots time := by
  have written := integral_of_ac_derivative (product seed slots) (productRate seed slots)
    (product_ac seed slots start finish start0 finish0) (productRate_integrable seed slots start finish start0 finish0) (by
      filter_upwards [product_hasDerivAt_ae seed slots, volume.ae_ne (0 : ℝ)] with time actual nonzero
      intro inside
      exact actual (lt_of_le_of_ne ((le_min start0 finish0).trans inside.1) (Ne.symm nonzero)))
  rw [written]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [productRate_split_ae seed slots] with time actual inside
  exact actual ((le_min start0 finish0).trans (uIoc_subset_uIcc inside).1)

theorem product_next (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    product seed slots (response.2.clockAdvance+time) = product response.1 slots time := by
  simp only [product, velocity_next seed response generated time nonnegative]

theorem forcing_next (seed : GeneratedWholeRestartCurrent nu) (slots : Fin n → Slot)
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some response) (time : ℝ) (nonnegative : 0 ≤ time) :
    forcing seed slots (response.2.clockAdvance+time) = forcing response.1 slots time := by
  simp only [forcing, cofactor, velocity_next seed response generated time nonnegative, action_next seed response generated time nonnegative]

theorem product_empty (seed : GeneratedWholeRestartCurrent nu) (slots : Fin 0 → Slot) (time : ℝ) : product seed slots time = 1 := by
  simp only [product, Finset.univ_eq_empty, Finset.prod_empty]

theorem forcing_empty (seed : GeneratedWholeRestartCurrent nu) (slots : Fin 0 → Slot) (time : ℝ) : forcing seed slots time = 0 := by
  simp only [forcing, Finset.univ_eq_empty, Finset.sum_empty]

theorem rate_empty (nu : Viscosity) (slots : Fin 0 → Slot) : sumRate nu slots = 0 := by
  simp only [sumRate, Finset.univ_eq_empty, Finset.sum_empty, mul_zero]

end
end SaturationMonoid.NavierStokes.NativeUnheatedTreeTime
