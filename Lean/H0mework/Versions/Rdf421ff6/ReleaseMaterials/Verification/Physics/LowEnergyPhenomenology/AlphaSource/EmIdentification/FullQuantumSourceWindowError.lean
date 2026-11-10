import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.CompleteSourceNoetherPrice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.ActualMixedNoetherTimePriceOwn
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumGaugeSourceInjection PreparationVacuumPhysicalHalfAxis GaussComposite.ActualDressedFullCoulomb GaussComposite.ActualDressedNoether
open GaussComposite.ActualDressedCubicPrice GaussComposite.ActualDressedFiniteStaticRead GaussComposite.ActualDressedSylvester
open Set MeasureTheory Filter
open scoped Topology BigOperators Matrix
attribute [local irreducible] dressedNoetherJet dressedStaticPolarization finiteConstantFieldSlope laplaceWeight

private theorem half_cubic_mass_price (sigma : ℝ) (positive : 0 < sigma) (small : sigma ≤ 2) :
    (∫ age : ℝ in Ioi 0, Real.exp (-((sigma/2)*age))*(1+age)^3) ≤ 896 / sigma^4 := by
  have h := cubic_laplace_sigma_four_price (sigma/2) (by positivity) (by linarith)
  apply (le_div_iff₀ (pow_pos positive 4)).mpr
  calc
    _ = 16*((sigma/2)^4*(∫ age : ℝ in Ioi 0, Real.exp (-((sigma/2)*age))*(1+age)^3)) := by ring
    _ ≤ 16*56 := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by norm_num

private theorem cubic_source_tail_price (sigma T : ℝ) (positive : 0 < sigma) (small : sigma ≤ 2) (future : 0 ≤ T) :
    (∫ age : ℝ in Ioi T, Real.exp (-(sigma*age))*(1+age)^3) ≤
      (896 / sigma^4) * Real.exp (-(sigma*T/2)) := by
  have subset : Ioi T ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi future
  have full := cubic_laplace_integrable sigma positive
  have half := cubic_laplace_integrable (sigma/2) (by positivity : 0 < sigma/2)
  calc
    _ ≤ ∫ age : ℝ in Ioi T, Real.exp (-(sigma*T/2)) * (Real.exp (-((sigma/2)*age))*(1+age)^3) := by
      apply integral_mono_ae (full.mono_set subset) ((half.mono_set subset).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with age after
      have age0 : 0 ≤ age := future.trans after.le
      have exponential : Real.exp (-(sigma*age)) ≤ Real.exp (-(sigma*T/2)) * Real.exp (-((sigma/2)*age)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have after0 : T ≤ age := after.le
        nlinarith [mul_nonneg positive.le (sub_nonneg.mpr after0)]
      exact (mul_le_mul_of_nonneg_right exponential (by positivity : 0 ≤ (1+age)^3)).trans_eq (by ring)
    _ = Real.exp (-(sigma*T/2)) * (∫ age : ℝ in Ioi T, Real.exp (-((sigma/2)*age))*(1+age)^3) := integral_const_mul _ _
    _ ≤ Real.exp (-(sigma*T/2)) * (∫ age : ℝ in Ioi 0, Real.exp (-((sigma/2)*age))*(1+age)^3) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      apply setIntegral_mono_set half _ (Filter.Eventually.of_forall (fun _ h => subset h))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with age after
      have age0 : 0 ≤ age := after.le
      positivity
    _ ≤ Real.exp (-(sigma*T/2)) * (896 / sigma^4) :=
      mul_le_mul_of_nonneg_left (half_cubic_mass_price sigma positive small) (Real.exp_nonneg _)
    _ = _ := mul_comm _ _

-- The finite approximation is the original complete Noether forcing, with the original constant field input.
def originalFullQuantumWindow (event : DressedEvent) (transfer : PhysicalMomentum) (lambda : ℂ) (T : ℝ) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => dressedNoetherForcing event transfer (fun _ => ⟨fieldUnit j,0,0⟩) lambda T i

private theorem original_window_finite_expression (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (T : ℝ) (i j : Fin 289) :
    originalFullQuantumWindow event transfer lambda T i j =
      ∫ age in (0:ℝ)..T, laplaceWeight lambda age * finiteConstantFieldSlope event transfer (fieldUnit j) age i := by
  unfold originalFullQuantumWindow dressedNoetherForcing
  simp_rw [finite_constant_field_slope_actual]

theorem actualFullQuantum_window_source_error (event : DressedEvent) (transfer : PhysicalMomentum)
    (lambda : ℂ) (positive : 0 < lambda.re) (small : lambda.re ≤ 2) (T : ℝ) (future : 0 ≤ T) (i j : Fin 289) :
    ‖dressedStaticPolarization event transfer lambda i j - originalFullQuantumWindow event transfer lambda T i j‖ ≤
      (896 * sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j) / lambda.re^4) *
        Real.exp (-(lambda.re*T/2)) := by
  let P := sourceCompleteCubicNoetherPrice event transfer (fieldUnit i) (fieldUnit j)
  have P0 : 0 ≤ P := sourceCompleteCubicNoetherPrice_nonnegative event transfer (fieldUnit i) (fieldUnit j)
  let f : ℝ → ℂ := fun age => laplaceWeight lambda age * finiteConstantFieldSlope event transfer (fieldUnit j) age i
  have full : IntegrableOn f (Ioi (0:ℝ)) := finite_static_integrand_integrable event transfer (fieldUnit j) lambda positive i
  have subset : Ioi T ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi future
  have decomposition : dressedStaticPolarization event transfer lambda i j - originalFullQuantumWindow event transfer lambda T i j =
      ∫ age in Ioi T, f age := by
    rw [dressed_static_polarization_finite event transfer lambda positive i j, original_window_finite_expression]
    have partition := intervalIntegral.integral_interval_add_Ioi full (full.mono_set subset)
    change (∫ age in Ioi (0:ℝ), f age) - (∫ age in (0:ℝ)..T, f age) = _
    rw [← partition, add_sub_cancel_left]
  rw [decomposition]
  calc
    _ ≤ ∫ age in Ioi T, ‖f age‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ age in Ioi T, P * (Real.exp (-(lambda.re*age))*(1+age)^3) := by
      apply integral_mono_ae (full.mono_set subset).norm
        (((cubic_laplace_integrable lambda.re positive).mono_set subset).const_mul P)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with age after
      have age0 : 0 ≤ age := future.trans after.le
      have bound := actual_complete_noether_source_price event transfer (fieldUnit j) age i
      rw [abs_of_nonneg age0] at bound
      dsimp only [f]
      rw [norm_mul, laplace_norm, finite_constant_field_slope_actual]
      exact (mul_le_mul_of_nonneg_left bound (Real.exp_nonneg _)).trans_eq (by dsimp only [P]; ring)
    _ = P * (∫ age : ℝ in Ioi T, Real.exp (-(lambda.re*age))*(1+age)^3) := integral_const_mul _ _
    _ ≤ P * ((896 / lambda.re^4) * Real.exp (-(lambda.re*T/2))) :=
      mul_le_mul_of_nonneg_left (cubic_source_tail_price lambda.re T positive small future) P0
    _ = _ := by dsimp only [P]; ring

end LowEnergy.ActualMixedNoetherTimePriceOwn
