import H0mework.NavierStokes.StressTimeControl.UnfilteredBudget
import H0mework.NavierStokes.StressEvolutionNegativeOne.Derivative
import H0mework.NavierStokes.StressEvolutionUnfiltered.Sliding

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeOriginalTimeVariation

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeResolventCompactness
open NativeOriginalNegativeOneWrite NativeOriginalNegativeOneDerivative NativeOriginalNegativeOneBudget

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

theorem action_on_interval (source : StressAt escape) (pointLe : point ≤ 1)
    {first last : ℝ} (firstInside : first ∈ Icc (0 : ℝ) 1) (lastInside : last ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (action source pointLe) volume first last :=
  (action_intervalIntegrable source pointLe).mono_set (by
    rw [uIcc_of_le zero_le_one]
    exact uIcc_subset_Icc firstInside lastInside)

theorem source_interval (source : StressAt escape) (pointLe : point ≤ 1)
    (first last : Icc (0 : ℝ) 1) :
    (∫ time in first.1..last.1, action source pointLe time) = state source pointLe last - state source pointLe first := by
  rw [← intervalIntegral.integral_interval_sub_left
    (action_on_interval source pointLe ⟨le_rfl, zero_le_one⟩ last.2)
    (action_on_interval source pointLe ⟨le_rfl, zero_le_one⟩ first.2), source_integral, source_integral]
  abel

def variation (source : StressAt escape) (pointLe : point ≤ 1) (time : ℝ) : ℝ :=
  ∫ actual in 0..time, ‖action source pointLe actual‖

theorem variation_continuousOn (source : StressAt escape) (pointLe : point ≤ 1) :
    ContinuousOn (variation source pointLe) (Icc 0 1) := by
  change ContinuousOn (fun time => ∫ actual in 0..time, ‖action source pointLe actual‖) (Icc 0 1)
  simpa only [uIcc_of_le zero_le_one] using
    intervalIntegral.continuousOn_primitive_interval' (action_intervalIntegrable source pointLe).norm left_mem_uIcc

theorem variation_range (source : StressAt escape) (pointLe : point ≤ 1)
    (time : ℝ) (inside : time ∈ Icc (0 : ℝ) 1) :
    0 ≤ variation source pointLe time ∧ variation source pointLe time ≤ budget receipt := by
  have total : variation source pointLe 1 ≤ budget receipt := by
    have same := commonTime_integral_eq_intervalIntegral 1 zero_le_one (fun actual => ‖action source pointLe actual‖)
    have actual := rate_integral_bound source pointLe
    rw [variation, ← same]
    simpa only [NativeOriginalNegativeOneWrite.action, projIcc_val] using actual
  refine ⟨intervalIntegral.integral_nonneg_of_forall inside.1 (fun _ => norm_nonneg _), ?_⟩
  have tail : 0 ≤ ∫ actual in time..1, ‖action source pointLe actual‖ :=
    intervalIntegral.integral_nonneg_of_forall inside.2 (fun _ => norm_nonneg _)
  have sum := intervalIntegral.integral_add_adjacent_intervals
    (action_on_interval source pointLe ⟨le_rfl, zero_le_one⟩ inside).norm
    (action_on_interval source pointLe inside ⟨zero_le_one, le_rfl⟩).norm
  change variation source pointLe time + _ = variation source pointLe 1 at sum
  linarith

theorem source_norm_increment_le (source : StressAt escape) (pointLe : point ≤ 1)
    (first last : Icc (0 : ℝ) 1) (ordered : first.1 ≤ last.1) :
    ‖state source pointLe last - state source pointLe first‖ ≤
      variation source pointLe last.1 - variation source pointLe first.1 := by
  rw [← source_interval]
  apply (intervalIntegral.norm_integral_le_integral_norm ordered).trans_eq
  exact (intervalIntegral.integral_interval_sub_left
    (action_on_interval source pointLe ⟨le_rfl, zero_le_one⟩ last.2).norm
    (action_on_interval source pointLe ⟨le_rfl, zero_le_one⟩ first.2).norm).symm

theorem stateAt_continuous (source : StressAt escape) (pointLe : point ≤ 1) :
    Continuous (stateAt source pointLe) := (source_continuous source pointLe).comp continuous_projIcc

theorem source_L1_difference_bound (source : StressAt escape) (pointLe : point ≤ 1)
    {left right shift : ℝ} (ordered : left ≤ right) (positive : 0 ≤ shift) (leftInside : 0 ≤ left)
    (rightInside : right + shift ≤ 1) :
    (∫ time in left..right, ‖stateAt source pointLe (time + shift) - stateAt source pointLe time‖) ≤ shift * budget receipt := by
  have within : Icc left right ⊆ Icc (0 : ℝ) 1 := fun time inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have shifted : MapsTo (fun time => time + shift) (Icc left right) (Icc (0 : ℝ) 1) :=
    fun time inside => ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have integrable : IntervalIntegrable (fun time => ‖stateAt source pointLe (time + shift) - stateAt source pointLe time‖)
      volume left right := (((stateAt_continuous source pointLe).comp (continuous_id.add continuous_const)).sub
    (stateAt_continuous source pointLe)).norm.intervalIntegrable (a := left) (b := right) (μ := volume)
  have variationIntegrable : IntervalIntegrable (fun time => variation source pointLe (time + shift) - variation source pointLe time)
      volume left right := (((variation_continuousOn source pointLe).comp
    (continuousOn_id.add continuousOn_const) shifted).sub
    ((variation_continuousOn source pointLe).mono within)).intervalIntegrable_of_Icc ordered (μ := volume)
  apply (intervalIntegral.integral_mono_on ordered integrable variationIntegrable ?_).trans
    (NativeSlidingPrimitive.integral_increment_le (variation_continuousOn source pointLe)
      (variation_range source pointLe) ordered positive leftInside rightInside)
  intro time inside
  simpa only [stateAt, projIcc_of_mem zero_le_one (shifted inside), projIcc_of_mem zero_le_one (within inside)] using
    source_norm_increment_le source pointLe ⟨time, within inside⟩ ⟨time + shift, shifted inside⟩ (by linarith)

end
end SaturationMonoid.NavierStokes.NativeOriginalTimeVariation
