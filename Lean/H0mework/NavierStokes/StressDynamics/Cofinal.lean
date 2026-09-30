import Mathlib.Analysis.Normed.Group.Tannery
import H0mework.NavierStokes.StressAction.StressDynamicsBilinear
import H0mework.NavierStokes.UnifiedAction.UnifiedCompleteSource

/-! Complete stress and action at the original cofinal occurrence. The original
refinement converges in the full stress norm. The same recovery writer has a
strong right derivative; its exact relation to the retained cofinal action keeps
the complete stress residual. The original endpoint, clock and next are reused. -/

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeCompleteStressCofinal

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPhysicalRightTrace
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open NativeCompleteStressCarrier NativeCompleteStressAction NativeEndpointVelocityCarrier

noncomputable section

theorem lp_tendsto_of_sq_bound {Index E : Type*} [NormedAddCommGroup E]
    (path : ℕ → lp (fun _ : Index => E) 2) (target : lp (fun _ : Index => E) 2)
    {cap : Index → ℝ} (summable : Summable cap)
    (bounded : ∀ n i, ‖path n i‖ ^ 2 ≤ cap i)
    (rows : ∀ i, Tendsto (fun n => path n i) atTop (𝓝 (target i))) :
    Tendsto path atTop (𝓝 target) := by
  have targetBound (i : Index) : ‖target i‖ ^ 2 ≤ cap i :=
    le_of_tendsto ((rows i).norm.pow 2) (Eventually.of_forall (fun n => bounded n i))
  have dominated := tendsto_tsum_of_dominated_convergence (summable.mul_left 4)
    (fun i => (((rows i).sub_const (target i)).norm.pow 2))
    (Eventually.of_forall (fun n i => show ‖‖path n i - target i‖ ^ 2‖ ≤ 4 * cap i by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have triangle := norm_sub_le (path n i) (target i)
      have squared := pow_le_pow_left₀ (norm_nonneg _) triangle 2
      nlinarith [bounded n i, targetBound i,
        sq_nonneg (‖path n i‖ - ‖target i‖)]))
  have square : Tendsto (fun n => ‖path n - target‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have identity (n : ℕ) : ‖path n - target‖ ^ 2 =
        ∑' i, ‖path n i - target i‖ ^ 2 := by
      have actual := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (path n - target)
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply] using actual
    simpa only [← identity, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), tsum_zero]
      using dominated
  rw [Metric.tendsto_nhds]
  intro epsilon positive
  have near := Metric.tendsto_nhds.mp square (epsilon ^ 2) (sq_pos_of_pos positive)
  filter_upwards [near] with n small
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at small
  rw [dist_eq_norm]
  exact (sq_lt_sq₀ (norm_nonneg _) positive.le).mp small

theorem quadratic_continuous :
    Continuous (fun value : WholeRestartVelocityEndpointState =>
      NativeCompleteStressBilinear.mixed (wholeVelocity value) (wholeVelocity value)) := by
  change Continuous (fun value : WholeRestartVelocityEndpointState =>
    NativeCompleteStressBilinear.mixedCLM (wholeVelocityCLM value) (wholeVelocityCLM value))
  exact (NativeCompleteStressBilinear.mixedCLM.continuous.comp wholeVelocityCLM.continuous).clm_apply
    wholeVelocityCLM.continuous

theorem actionState_eq_full (nu : Viscosity) (velocity : WholeRestartVelocityEndpointState) :
    NativeNegativeFourMomentum.actionState nu velocity =
      momentumCLM nu (WithLp.toLp 2
        (velocity, NativeCompleteStressBilinear.mixed (wholeVelocity velocity) (wholeVelocity velocity))) := by
  apply lp.ext
  funext wave
  unfold NativeCompleteStressBilinear.mixed
  rw [NativeNegativeFourMomentum.actionState_apply, momentumCLM_source]
  rfl

theorem actionState_continuous (nu : Viscosity) :
    Continuous (NativeNegativeFourMomentum.actionState nu) := by
  rw [funext (actionState_eq_full nu)]
  exact (momentumCLM nu).continuous.comp
    ((WithLp.prod_continuous_toLp 2 WholeRestartVelocityEndpointState Space).comp
      (continuous_id.prodMk quadratic_continuous))

variable {nu : Viscosity}

theorem recoveryCurve_zero (initial : GeneratedWholeRestartCurrent nu) :
    NativeMacroMomentumIntegral.recoveryCurve (NativeRecoveryUnifiedCurrent.receipt initial) 0 =
      (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint := by
  apply lp.ext
  funext wave
  apply PiLp.ext
  intro coordinate
  change NativeRecoveryRowAction.velocity (NativeRecoveryUnifiedCurrent.receipt initial) 0
    wave.1 coordinate = _
  rw [NativeRecoveryRowAction.velocity_on_interval _ ⟨0, by norm_num⟩,
    (NativeRecoveryUnifiedCurrent.receipt initial).initial_row,
    wholeRestartVelocityEndpointCoefficient_of_ne _ wave.1 wave.2]
  rfl

theorem recoveryCurve_continuousAt_zero (initial : GeneratedWholeRestartCurrent nu) :
    ContinuousAt (NativeMacroMomentumIntegral.recoveryCurve
      (NativeRecoveryUnifiedCurrent.receipt initial)) 0 := by
  have original := sourceGeneratedNativeTemporalWholeMildReadWrite_physical_tendsto_initial initial
  have projection : Tendsto (projIcc (0 : ℝ) 1 zero_le_one) (𝓝 0)
      (𝓝 (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1)) := by
    simpa using (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).tendsto 0
  have actual := original.comp projection
  rw [ContinuousAt, recoveryCurve_zero]
  exact actual

theorem ordinaryAction_continuousAt_zero (initial : GeneratedWholeRestartCurrent nu) :
    ContinuousAt (NativeUnifiedRootActionFeed.ordinaryAction initial) 0 :=
  (actionState_continuous nu).continuousAt.comp (recoveryCurve_continuousAt_zero initial)

theorem recoveryWriter_hasDerivWithinAt_zero (initial : GeneratedWholeRestartCurrent nu) :
    HasDerivWithinAt (NativeUnifiedRootActionFeed.state initial)
      (NativeUnifiedRootActionFeed.ordinaryAction initial 0) (Icc (0 : ℝ) 1) 0 := by
  have measurable : StronglyMeasurableAtFilter
      (NativeUnifiedRootActionFeed.ordinaryAction initial) (𝓝[Ioi (0 : ℝ)] 0) volume := by
    refine ⟨Icc (0 : ℝ) 1, ?_, ?_⟩
    · exact (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self) (Icc_mem_nhdsGE zero_lt_one)
    · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
        (NativeUnifiedRootActionFeed.ordinaryAction_intervalIntegrable initial)).aestronglyMeasurable
  have primitive := (intervalIntegral.integral_hasDerivWithinAt_right
    (f := NativeUnifiedRootActionFeed.ordinaryAction initial) (a := (0 : ℝ)) (b := 0)
    (s := Ici (0 : ℝ)) (t := Ioi (0 : ℝ)) (by simp) measurable
    (ordinaryAction_continuousAt_zero initial).continuousWithinAt).const_add
      (NativeUnifiedRootActionFeed.state initial 0)
  apply (primitive.mono (show Icc (0 : ℝ) 1 ⊆ Ici 0 from fun _ member => member.1)).congr
  · intro time inside
    have written := NativeUnifiedRootActionFeed.source_integral initial ⟨time, inside⟩
    rw [intervalIntegral.integral_congr_ae
      ((NativeUnifiedRootActionFeed.action_ae_ordinary initial).mono fun _ same _ => same)] at written
    simpa only [add_comm] using eq_add_of_sub_eq written
  · simp

def cofinalStress (initial : GeneratedWholeRestartCurrent nu) : Space :=
  ofBound (NativeCofinalStress.sourceGeneratedCofinalStress initial).stress
    (‖wholeRestartContactVelocityState initial 0‖ ^ 2)
    (NativeCofinalStress.sourceGeneratedCofinalStress initial).stress_norm_le

def endpointStress (initial : GeneratedWholeRestartCurrent nu) : Space :=
  NativeCompleteStressBilinear.mixed
    (wholeVelocity (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint)
    (wholeVelocity (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint)

def retainedStress (initial : GeneratedWholeRestartCurrent nu) : Space :=
  cofinalStress initial - endpointStress initial

private theorem bounded_stress_row (stress : NativeFluidStressFourierState) (budget : ℝ)
    (bounded : ∀ wave output input, ‖stress wave output input‖ ≤ budget) (wave : IntegerWavevector) :
    ‖ofBound stress budget bounded wave‖ ^ 2 ≤
      9 * budget ^ 2 * weight wave ^ 2 := by
  have tensorBound : ‖tensor (stress wave)‖ ^ 2 ≤ 9 * budget ^ 2 := by
    rw [tensor_norm_sq]
    have bound := Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun output _ =>
      Finset.sum_le_sum (s := (Finset.univ : Finset Coordinate)) fun input _ =>
        pow_le_pow_left₀ (norm_nonneg _) (bounded wave output input) 2
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat, ← mul_assoc, show (3 : ℝ) * 3 = 9 by norm_num] using bound
  change ‖weight wave • tensor (stress wave)‖ ^ 2 ≤ _
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact (mul_le_mul_of_nonneg_left tensorBound (sq_nonneg _)).trans_eq (by ring)

theorem cofinalStress_strong_tendsto (initial : GeneratedWholeRestartCurrent nu) :
    Tendsto (fun index => ofBound
      (NativeCofinalStress.contactStress initial
        ((NativeCofinalStress.sourceGeneratedCofinalStress initial).stage index))
      (‖wholeRestartContactVelocityState initial 0‖ ^ 2)
      (NativeCofinalStress.contactStress_norm_le initial _)) atTop (𝓝 (cofinalStress initial)) := by
  apply lp_tendsto_of_sq_bound _ _ (weight_summable.mul_left
    (9 * (‖wholeRestartContactVelocityState initial 0‖ ^ 2) ^ 2))
  · intro index wave
    exact bounded_stress_row _ _ _ wave
  · intro wave
    have row := (NativeCofinalStress.sourceGeneratedCofinalStress initial).stress_tendsto
    have entries : Tendsto
        (fun index (pair : Coordinate × Coordinate) => NativeCofinalStress.contactStress initial
          ((NativeCofinalStress.sourceGeneratedCofinalStress initial).stage index) wave pair.1 pair.2)
        atTop (𝓝 (fun pair : Coordinate × Coordinate =>
          (NativeCofinalStress.sourceGeneratedCofinalStress initial).stress wave pair.1 pair.2)) := by
      apply tendsto_pi_nhds.mpr
      intro pair
      exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp row wave) pair.1) pair.2
    have converted := (PiLp.continuous_toLp (p := (2 : ℝ≥0∞))
      (β := fun _ : Coordinate × Coordinate => ℂ)).tendsto _ |>.comp entries
    exact converted.const_smul (weight wave)

theorem retainedStress_read (initial : GeneratedWholeRestartCurrent nu) :
    read (retainedStress initial) = NativeCofinalStressDefect.stressDefect
      (NativeCofinalStress.sourceGeneratedCofinalStress initial) := by
  funext wave output input
  change (readCLM wave output input) (cofinalStress initial - endpointStress initial) = _
  rw [map_sub, readCLM_apply, readCLM_apply]
  rw [cofinalStress, read_ofBound, endpointStress, NativeCompleteStressBilinear.mixed_read]
  rfl

theorem cofinal_action_split (initial : GeneratedWholeRestartCurrent nu) :
    NativeUnifiedCofinalActionFeed.actionAt initial =
      NativeUnifiedRootActionFeed.ordinaryAction initial 0 + divergenceCLM (retainedStress initial) := by
  have original : NativeUnifiedCofinalActionFeed.actionAt initial =
      momentumCLM nu (WithLp.toLp 2
        ((sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint,
          cofinalStress initial)) := by
    apply lp.ext
    funext wave
    unfold cofinalStress
    rw [NativeUnifiedCofinalActionFeed.actionAt_row, momentumCLM_source]
    rfl
  rw [original, NativeUnifiedRootActionFeed.ordinaryAction, recoveryCurve_zero, actionState_eq_full]
  change divergenceCLM (cofinalStress initial) - viscousCLM nu _ =
    (divergenceCLM (endpointStress initial) - viscousCLM nu _) +
      divergenceCLM (cofinalStress initial - endpointStress initial)
  rw [map_sub]
  abel

theorem recoveryWriter_retains_complete_action (initial : GeneratedWholeRestartCurrent nu) :
    HasDerivWithinAt (NativeUnifiedRootActionFeed.state initial)
      (NativeUnifiedCofinalActionFeed.actionAt initial - divergenceCLM (retainedStress initial))
      (Icc (0 : ℝ) 1) 0 := by
  rw [cofinal_action_split, add_sub_cancel_right]
  exact recoveryWriter_hasDerivWithinAt_zero initial

end
end SaturationMonoid.NavierStokes.NativeCompleteStressCofinal
