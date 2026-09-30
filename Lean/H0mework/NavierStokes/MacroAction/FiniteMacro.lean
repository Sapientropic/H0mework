import H0mework.NavierStokes.MacroAction.MacroDecay
import H0mework.NavierStokes.MacroAction.MacroExecution
import H0mework.NavierStokes.SourceAction.SmallSeed

set_option autoImplicit false
open scoped BigOperators Topology

namespace SaturationMonoid.NavierStokes.NativeFiniteMacroControl

open Set Filter
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeRecoveryControlProducer NativeRecoverySmallK NativeSmallSeedControl NativeMacroKineticDecay

noncomputable section

variable {nu : Viscosity}

def debitBound (nu : Viscosity) (energy : ℝ) : ℝ :=
  criticalEnstrophyLatticeConstant * (2 * (((1 / 2 : ℝ) * energy) / nu.coeff))

def threshold (nu : Viscosity) : ℝ := (1 / 2 : ℝ) * nu.coeff ^ 2 * (2 * Real.pi) ^ 2

theorem threshold_pos : 0 < threshold nu := by
  have viscosity := nu.coeff_pos
  have piPositive := Real.pi_pos
  unfold threshold
  positivity

theorem smallK_of_kinetic_bound (current : GeneratedWholeRestartCurrent nu) (bound : ℝ)
    (bounded : kinetic current ≤ bound) (small : debitBound nu bound ≤ threshold nu) :
    smallK (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore current) := by
  unfold smallK kineticAllowance
  apply le_trans _ small
  unfold debitBound
  have endpoint := (endpoint_kinetic_le current).trans bounded
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left endpoint (by norm_num)) nu.coeff_pos.le)
      (by norm_num)) criticalEnstrophyLatticeConstant_nonneg

theorem exists_small_fuel (seed : GeneratedWholeRestartCurrent nu) :
    ∃ fuel : ℕ, debitBound nu (kinetic seed * contraction nu ^ fuel) ≤ threshold nu := by
  have decay := (tendsto_pow_atTop_nhds_zero_of_lt_one contraction_positive.le (contraction_lt_one (nu := nu))).const_mul (kinetic seed)
  have small := (((decay.const_mul (1 / 2 : ℝ)).div_const nu.coeff).const_mul 2).const_mul criticalEnstrophyLatticeConstant
  simp only [mul_zero, zero_div] at small
  have eventual := (tendsto_order.1 small).2 (threshold nu) (threshold_pos (nu := nu))
  obtain ⟨fuel, bound⟩ := eventual.exists
  exact ⟨fuel, bound.le⟩

theorem kinetic_at_arrival (seed : GeneratedWholeRestartCurrent nu) {current : GeneratedWholeRestartCurrent nu}
    (arrival : NativeReachable seed generatedWholeRestartEndpointMacroRespond current) :
    kinetic current ≤ kinetic seed * contraction nu ^ arrival.occurrence := by
  apply NativeMacroFiniteExecution.arrival_invariant seed
    (fun depth current => kinetic current ≤ kinetic seed * contraction nu ^ depth) _ _ arrival
  · simp only [pow_zero, mul_one, le_refl]
  · intro current response _ depth previous
    exact (macro_step_kinetic_le response.2).trans
      ((mul_le_mul_of_nonneg_right previous contraction_positive.le).trans_eq (by rw [pow_succ]; ring))

theorem small_source_response_stops_next (current : GeneratedWholeRestartCurrent nu)
    (small : smallK (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore current))
    (response : Response (GeneratedWholeRestartEndpointMacroStep nu) current) :
    generatedWholeRestartEndpointMacroRespond response.1 = none := by
  apply (generatedWholeRestartEndpointMacroRespond_eq_none_iff _).mpr
  rcases response with ⟨next, step⟩
  cases step
  dsimp only
  rw [nativeTemporalCofinalVisitAuthority_positiveTimeH1NextCurrent]
  exact source_next_unbounded current small

theorem source_finite_macro_terminal (seed : GeneratedWholeRestartCurrent nu) :
    Nonempty (GeneratedWholeRestartEndpointMacroTerminalRun seed) := by
  obtain ⟨fuel, thresholdPaid⟩ := exists_small_fuel seed
  rcases NativeMacroFiniteExecution.terminal_or_exact_arrival seed fuel with
    ⟨terminal, _⟩ | ⟨current, arrival, depth, response, generated⟩
  · exact ⟨terminal⟩
  · have kineticPaid := kinetic_at_arrival seed arrival
    rw [depth] at kineticPaid
    have small := smallK_of_kinetic_bound current (kinetic seed * contraction nu ^ fuel) kineticPaid thresholdPaid
    exact ⟨{
      terminal := response.1
      arrival := .step arrival generated
      stopped := small_source_response_stops_next current small response }⟩

end
end SaturationMonoid.NavierStokes.NativeFiniteMacroControl
