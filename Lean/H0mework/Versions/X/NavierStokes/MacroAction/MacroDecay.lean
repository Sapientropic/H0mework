import H0mework.Versions.X.NavierStokes.RecoveryAction.RecoveryDecay

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeMacroKineticDecay

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeRecoveryKineticDecay

noncomputable section

variable {nu : Viscosity}

def kinetic (current : GeneratedWholeRestartCurrent nu) : ℝ := ‖puncturedWholeVelocityEuclideanState current.initialState‖ ^ 2

theorem kinetic_nonnegative (current : GeneratedWholeRestartCurrent nu) : 0 ≤ kinetic current := sq_nonneg _

def contraction (nu : Viscosity) : ℝ := Real.exp (-rate nu / 2)

theorem contraction_positive : 0 < contraction nu := Real.exp_pos _

theorem contraction_lt_one : contraction nu < 1 := Real.exp_lt_one_iff.mpr (by have paid := rate_pos (nu := nu); linarith)

theorem cofinal_next_velocity_eq (initial : GeneratedWholeRestartCurrent nu) :
    puncturedWholeVelocityEuclideanState (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).initialState =
      ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity.puncturedEuclideanize
        ((sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial).wholePath
          (sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).time) := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  exact congrFun ((sourceGeneratedNativeTemporalPositiveTimeH1Slice initial).biotSavart_vorticityState wave.1) coordinate

theorem endpoint_kinetic_le (initial : GeneratedWholeRestartCurrent nu) :
    ‖(sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial).family.endpointReceipt.velocityEndpoint‖ ^ 2 ≤ kinetic initial :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint_norm_le.trans
      (NativeNormControl.contact_velocity_norm_le_initial initial))

theorem cofinal_next_kinetic_le (initial : GeneratedWholeRestartCurrent nu) :
    kinetic (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial) ≤ kinetic initial * contraction nu := by
  let receipt := sourceGeneratedNativeTemporalWholeMildReadWriteReceipt initial
  let slice := sourceGeneratedNativeTemporalPositiveTimeH1Slice initial
  have original := wholeMild_velocity_square_le_exp
    (sourceGeneratedNativeTemporalUniformKineticViscousLedgerCore initial) receipt slice.time
  have timeBound : Real.exp (-rate nu * slice.time.1) ≤ contraction nu := by
    apply Real.exp_le_exp.mpr
    have positive := rate_pos (nu := nu)
    have late := slice.time_half_lt
    nlinarith
  unfold kinetic
  rw [cofinal_next_velocity_eq]
  exact original.trans (mul_le_mul (endpoint_kinetic_le initial) timeBound (Real.exp_pos _).le (kinetic_nonnegative initial))

theorem macro_step_kinetic_le {initial next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu initial next) : kinetic next ≤ kinetic initial * contraction nu := by
  cases step
  rw [nativeTemporalCofinalVisitAuthority_positiveTimeH1NextCurrent]
  exact cofinal_next_kinetic_le _

theorem macro_initial_kinetic_le (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu) (index : ℕ) :
    kinetic (lineage.current index) ≤ kinetic (lineage.current 0) * contraction nu ^ index := by
  induction index with
  | zero => simp only [pow_zero, mul_one, le_refl]
  | succ index previous =>
      exact (macro_step_kinetic_le (lineage.step index)).trans
        ((mul_le_mul_of_nonneg_right previous contraction_positive.le).trans_eq (by rw [pow_succ]; ring))

theorem macro_initial_kinetic_tendsto_zero (lineage : GeneratedInfiniteWholeRestartEndpointMacroLineage nu) :
    Tendsto (fun index => kinetic (lineage.current index)) atTop (𝓝 0) := by
  have bound := (tendsto_pow_atTop_nhds_zero_of_lt_one contraction_positive.le (contraction_lt_one (nu := nu))).const_mul
    (kinetic (lineage.current 0))
  simp only [mul_zero] at bound
  exact squeeze_zero (fun index => kinetic_nonnegative (lineage.current index)) (macro_initial_kinetic_le lineage) bound

end
end SaturationMonoid.NavierStokes.NativeMacroKineticDecay
