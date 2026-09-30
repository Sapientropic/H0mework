import H0mework.Versions.X.NavierStokes.WindowEnergyTrace.Distributed.Response
import H0mework.Versions.X.NavierStokes.WindowPhysics.Tail.Moments
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceWhole.Source

set_option autoImplicit false
open scoped Topology BigOperators
namespace SaturationMonoid.NavierStokes.NativeWindowDistributedAdjoint
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceAdjoint (value forward dual)
noncomputable section
variable {nu : Viscosity}

private def pairRead (M : ℕ) : physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (LinearMap.toContinuousLinearMap (coefficients (modes M)))
    (LinearMap.toContinuousLinearMap (coefficients (modes M)))

private theorem pair_ac (M : ℕ) {x y : ℝ → physicalSpace (modes M)} {a b : ℝ}
    (first : AbsolutelyContinuousOnInterval x a b) (last : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval (fun t => pairing (modes M) (x t) (y t)) a b := by
  have add := NativeUnheatedIntegralBilinear.diagonal_ac (pairRead M) (first.add last)
  have sub := NativeUnheatedIntegralBilinear.diagonal_ac (pairRead M) (first.sub last)
  have paid := (add.sub sub).const_mul (1/4 : ℝ)
  convert! paid using 1
  funext time
  change pairing (modes M) (x time) (y time) =
    (1/4 : ℝ) * (pairing (modes M) (x time + y time) (x time + y time) -
      pairing (modes M) (x time - y time) (x time - y time))
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply,
    pairing_symmetric (modes M) (y time) (x time)]
  ring

private theorem pair_integrable (M : ℕ) {x y : ℝ → physicalSpace (modes M)} {a b : ℝ}
    (paid : IntervalIntegrable x volume a b) (continuous : ContinuousOn y (uIcc a b)) :
    IntervalIntegrable (fun t => pairing (modes M) (x t) (y t)) volume a b := by
  let read (k : IntegerWavevector) (i : Coordinate) : physicalSpace (modes M) →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (NativeWindowAugmentedFixedOperator.rowRead (modes M) k i)
  have parts (k : IntegerWavevector) (i : Coordinate) (part : ℂ →L[ℝ] ℝ) :
      IntervalIntegrable (fun t => part (read k i (x t)) * part (read k i (y t))) volume a b := by
    have first : IntervalIntegrable (fun t => (part.comp (read k i)) (x t)) volume a b :=
      ⟨(part.comp (read k i)).integrable_comp paid.1, (part.comp (read k i)).integrable_comp paid.2⟩
    exact first.mul_continuousOn ((part.comp (read k i)).continuous.comp_continuousOn continuous)
  have rows (k : IntegerWavevector) (i : Coordinate) := (parts k i Complex.reCLM).add (parts k i Complex.imCLM)
  have summed := IntervalIntegrable.sum (s := modes M) fun k _ =>
    IntervalIntegrable.sum (s := Finset.univ) fun i _ => rows k i
  convert! summed using 1
  funext time
  rw [pairing_eq]
  simp only [Finset.sum_apply]
  rfl

theorem window_green_write (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (test : physicalSpace (modes M)) (a b : ℝ) (ab : a ≤ b) (a0 : 0 ≤ a) :
    (∫ time in a..b, NativeForwardWindowSource.kernel (observation-time) *
      pairing (modes M) (value seed M time) (testAction (nu := nu) M test)) =
      pairing (modes M) (value seed M a) (response seed M observation test a b ab a) +
        ∫ time in a..b, pairing (modes M) (NativeWindowStageNineSource.forcing seed M time)
          (response seed M observation test a b ab time) := by
  have pc := response_continuous seed M observation test a b ab
  rw [← uIcc_of_le ab] at pc
  have forcing := pair_integrable M
    (NativeWindowTraceAdjoint.forcing_integrable seed M a b a0 (a0.trans ab)) pc
  have observationPaid : IntervalIntegrable (fun time => NativeForwardWindowSource.kernel (observation-time) *
      pairing (modes M) (value seed M time) (testAction (nu := nu) M test)) volume a b := by
    have continuous : Continuous (fun time => NativeForwardWindowSource.kernel (observation-time) *
        pairRead M (value seed M time) (testAction (nu := nu) M test)) :=
      (NativeForwardWindowSource.kernel_smooth.continuous.comp (continuous_const.sub continuous_id)).mul
        (((pairRead M).continuous.comp (NativeWindowTraceAdjoint.value_continuous seed M)).clm_apply continuous_const)
    exact continuous.intervalIntegrable a b
  have written := NativeUnheatedIntegralBilinear.integral_of_ac_derivative _ _
    (pair_ac M (NativeWindowTraceAdjoint.value_ac seed M a b) (response_ac seed M observation test a b ab))
    (forcing.sub observationPaid) (by
      filter_upwards [source_green_derivative seed M observation test a b ab a0,
        (volume : Measure ℝ).ae_ne a, (volume : Measure ℝ).ae_ne b] with time actual first last inside
      rw [uIcc_of_le ab] at inside
      exact actual ⟨lt_of_le_of_ne inside.1 (Ne.symm first), lt_of_le_of_ne inside.2 last⟩)
  rw [response_terminal, map_zero, zero_sub, intervalIntegral.integral_sub forcing observationPaid] at written
  linarith only [written]

def window (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ) : physicalSpace (modes M) :=
  NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
    (∫ shift, NativeWindowTraceWholeHistory.history seed observation shift
      ∂NativeForwardWindowPairingReadout.averageMeasure)

theorem window_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ) :
    (window seed M observation).1 =
      ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.complexSharpSupportProjection (modes M)
        (NativeEndpointVelocityCarrier.wholeVelocity (NativeForwardWindowSource.source seed observation).fst) := by
  change ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory.complexSharpSupportProjection (modes M)
    (NativeEndpointVelocityCarrier.wholeVelocity
      (∫ shift, NativeWindowTraceWholeHistory.history seed observation shift
        ∂NativeForwardWindowPairingReadout.averageMeasure).1) = _
  rw [NativeWindowTraceWholeHistory.mean_original]

theorem value_restriction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (nonnegative : 0 ≤ time) :
    value seed M time =
      NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
        (NativeWindowTraceWholeHistory.original seed time) := by
  rw [value,NativeWindowStageNineSource.lift_load seed time nonnegative,
    NativeWindowStressOseenSource.load,NativeUnheatedSourceQuadraticApprox.physicalSource,dif_pos nonnegative]
  rfl

theorem window_integral (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (nonnegative : 0 ≤ observation) : window seed M observation =
      ∫ shift, NativeForwardWindowSource.kernel shift • value seed M (observation-shift) := by
  let read := NativeWholeResolvent.restrictCLM (modes M) (modes_zero M) (modes_closed M)
  have paid : Integrable (fun shift => NativeWindowTraceWholeHistory.history seed observation shift)
      NativeForwardWindowPairingReadout.averageMeasure :=
    ((NativeWindowTraceWholeHistory.sample_memLp seed observation 1).integrable le_rfl).congr
      (NativeWindowTraceWholeHistory.history_ae seed observation).symm
  rw [window,← read.integral_comp_comm paid]
  calc
    _ = ∫ shift, value seed M (observation-shift) ∂NativeForwardWindowPairingReadout.averageMeasure := by
      apply integral_congr_ae
      filter_upwards [NativeWindowTraceWholeHistory.history_ae seed observation,
        NativeWindowHistoryGNS.average_support] with shift actual inside
      rw [actual]
      exact (value_restriction seed M (observation-shift) (by linarith)).symm
    _ = _ := NativeForwardWindowPairingReadout.density_integral _

theorem window_pair_integral (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (nonnegative : 0 ≤ observation) (test : physicalSpace (modes M)) :
    pairing (modes M) (window seed M observation) (testAction (nu := nu) M test) =
      ∫ time in (0 : ℝ)..(observation+2), NativeForwardWindowSource.kernel (observation-time) *
        pairing (modes M) (value seed M time) (testAction (nu := nu) M test) := by
  let read := (pairRead M).flip (testAction (nu := nu) M test)
  have paid : Integrable (fun shift : ℝ => NativeForwardWindowSource.kernel shift •
      value seed M (observation-shift)) :=
    NativeForwardWindowSource.kernel_compact.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
      NativeForwardWindowSource.kernel_smooth.continuous
      (NativeWindowTraceAdjoint.value_continuous seed M).locallyIntegrable observation
  have written := read.integral_comp_comm paid
  change (∫ shift, read (NativeForwardWindowSource.kernel shift • value seed M (observation-shift))) =
      read (∫ shift, NativeForwardWindowSource.kernel shift • value seed M (observation-shift)) at written
  rw [← window_integral seed M observation nonnegative] at written
  simp only [map_smul] at written
  change (∫ shift, NativeForwardWindowSource.kernel shift *
    pairing (modes M) (value seed M (observation-shift)) (testAction (nu := nu) M test)) =
      pairing (modes M) (window seed M observation) (testAction (nu := nu) M test) at written
  rw [← written]
  have changed := (Measure.measurePreserving_sub_left (volume : Measure ℝ) observation).integral_comp
    (measurableEmbedding_subLeft observation) (fun time => NativeForwardWindowSource.kernel (observation-time) *
      pairing (modes M) (value seed M time) (testAction (nu := nu) M test))
  simp only [sub_sub_cancel] at changed
  rw [changed,intervalIntegral.integral_of_le (by linarith : 0 ≤ observation+2)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro time outside
  have zero : NativeForwardWindowSource.kernel (observation-time) = 0 := by
    by_contra nonzero
    have inside := NativeWindowTailMoments.kernelJet_interval 0 (observation-time)
      (by simpa only [NativeForwardWindowJets.kernelJet,iteratedDeriv_zero] using nonzero)
    exact outside ⟨by linarith [inside.2],by linarith [inside.1]⟩
  rw [zero,zero_mul]

theorem window_source_green (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (observation : ℝ)
    (nonnegative : 0 ≤ observation) (test : physicalSpace (modes M)) :
    pairing (modes M) (window seed M observation) (testAction (nu := nu) M test) =
      pairing (modes M) (value seed M 0)
        (response seed M observation test 0 (observation+2) (by linarith) 0) +
      ∫ time in (0 : ℝ)..(observation+2),
        pairing (modes M) (NativeWindowStageNineSource.forcing seed M time)
          (response seed M observation test 0 (observation+2) (by linarith) time) := by
  rw [window_pair_integral seed M observation nonnegative test]
  exact window_green_write seed M observation test 0 (observation+2) (by linarith) le_rfl


end
end SaturationMonoid.NavierStokes.NativeWindowDistributedAdjoint
