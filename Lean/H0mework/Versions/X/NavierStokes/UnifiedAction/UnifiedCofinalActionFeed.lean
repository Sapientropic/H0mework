import H0mework.Versions.X.NavierStokes.CofinalAction.CofinalMomentum
import H0mework.Versions.X.NavierStokes.MomentumAction.NegativeFourMomentum

set_option autoImplicit false
open scoped Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeUnifiedCofinalActionFeed

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeCofinalStress NativeCofinalMomentumAction NativeEndpointVelocityCarrier NativePhysicalFourier
open NativeNegativeFourMomentum NativeStressSource NativeTimeJetCarrier NativeStressCurlAlgebra

noncomputable section

variable {nu : Viscosity}

def budget (initial : GeneratedWholeRestartCurrent nu) : ℝ :=
  actionBudget nu ‖wholeRestartContactVelocityState initial 0‖

private def finiteAction (initial : GeneratedWholeRestartCurrent nu) (index : ℕ) : WholeRestartVelocityEndpointState :=
  actionState nu (wholeRestartContactVelocityState initial ((sourceGeneratedCofinalStress initial).stage index))

private theorem finiteAction_bound (initial : GeneratedWholeRestartCurrent nu) (index : ℕ) :
    ‖finiteAction initial index‖ ≤ budget initial :=
  actionState_norm_le nu _ _ (wholeRestartContactVelocityState_norm_le_initial initial _)

private theorem contact_action (initial : GeneratedWholeRestartCurrent nu) (stage : ℕ) (wave : IntegerWavevector) :
    NativeMomentumIntegral.action nu (wholeRestartContactVelocityState initial stage) wave = actualMomentum initial stage wave := by
  rw [actualMomentum_eq_stress]
  simp only [NativeMomentumIntegral.action, NativeMomentumIntegral.row,
    wholeRestartContactVelocityState, wholeVelocity_punctured, contactStress]

private theorem finiteAction_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (fun index wave => finiteAction initial index wave) atTop
      (𝓝 fun wave : NonzeroIntegerWavevector => weightedRowCLM wave.1
        (momentum (sourceGeneratedCofinalStress initial) wave.1)) := by
  apply tendsto_pi_nhds.mpr
  intro wave
  have original := tendsto_pi_nhds.mp (momentum_tendsto (sourceGeneratedCofinalStress initial)) wave.1
  simpa only [finiteAction, actionState_apply, contact_action, Function.comp_def] using
    (weightedRowCLM wave.1).continuous.tendsto _ |>.comp original

/-- The original cofinal stress momentum, retained in the same full H⁻⁴ carrier. -/
def actionAt (initial : GeneratedWholeRestartCurrent nu) : WholeRestartVelocityEndpointState :=
  ⟨fun wave => weightedRowCLM wave.1 (momentum (sourceGeneratedCofinalStress initial) wave.1),
    lp.memℓp_of_tendsto
      (isBounded_iff_forall_norm_le.mpr ⟨budget initial, by
        rintro _ ⟨index, rfl⟩
        exact finiteAction_bound initial index⟩)
      (finiteAction_tendsto initial)⟩

theorem actionAt_norm_le (initial : GeneratedWholeRestartCurrent nu) :
    ‖actionAt initial‖ ≤ budget initial :=
  lp.norm_le_of_tendsto (Eventually.of_forall (finiteAction_bound initial)) (finiteAction_tendsto initial)

theorem actionAt_row (initial : GeneratedWholeRestartCurrent nu) (wave : NonzeroIntegerWavevector) :
    actionAt initial wave = weightedRowCLM wave.1 (momentum (sourceGeneratedCofinalStress initial) wave.1) := rfl

theorem source_action_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (fun index wave => actionState nu
      (wholeRestartContactVelocityState initial ((sourceGeneratedCofinalStress initial).stage index)) wave)
      atTop (𝓝 fun wave => actionAt initial wave) := finiteAction_tendsto initial

def read (value : WholeRestartVelocityEndpointState) (wave : IntegerWavevector) : ComplexCoordinateVector :=
  integerWaveNormSq wave ^ 2 • wholeVelocity value wave

theorem actionAt_read (initial : GeneratedWholeRestartCurrent nu) :
    read (actionAt initial) = momentum (sourceGeneratedCofinalStress initial) := by
  funext wave
  by_cases nonzero : wave ≠ 0
  · have scalar : integerWaveNormSq wave ^ 2 * weight wave = 1 := by
      rw [weight, ← mul_pow, mul_inv_cancel₀ (integerWaveNormSq_pos nonzero).ne', one_pow]
    funext coordinate
    change integerWaveNormSq wave ^ 2 • wholeVelocity (actionAt initial) wave coordinate = _
    rw [wholeVelocity_nonzero _ ⟨wave, nonzero⟩]
    change integerWaveNormSq wave ^ 2 • (weight wave • momentum (sourceGeneratedCofinalStress initial) wave coordinate) = _
    rw [smul_smul, scalar, one_smul]
  · have zero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    simp [read, momentum, projectedDivergenceCLM_apply, transverseProjection, integerWaveViscousMultiplier,
      integerWaveNormSq]

theorem actionAt_pressure (initial : GeneratedWholeRestartCurrent nu) (wave : IntegerWavevector) :
    read (actionAt initial) wave =
      nativeFluidStressDivergenceCoefficient (sourceGeneratedCofinalStress initial).stress wave -
        ((Complex.I * (((2 * Real.pi : ℝ) : ℂ))) *
          stressPressureCoefficient wave ((sourceGeneratedCofinalStress initial).stress wave)) • complexWavevector wave -
        (nu.coeff * integerWaveViscousMultiplier wave) • endpointVelocity initial wave := by
  rw [actionAt_read, momentum_pressure_identity]

theorem actionAt_complete_stress (initial : GeneratedWholeRestartCurrent nu) :
    read (actionAt initial) = resolvedMomentum initial + internalMomentum (sourceGeneratedCofinalStress initial) := by
  rw [actionAt_read, momentum_decomposition]

end
end SaturationMonoid.NavierStokes.NativeUnifiedCofinalActionFeed
