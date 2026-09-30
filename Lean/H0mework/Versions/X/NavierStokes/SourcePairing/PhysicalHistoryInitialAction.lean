import H0mework.Versions.X.NavierStokes.SourceAction.PhysicalHistoryCurrent

set_option autoImplicit false
open scoped Topology Matrix

namespace SaturationMonoid.NavierStokes.NativePhysicalHistoryInitialAction

open Set Filter
open PhysicsCore.ProofFreeRicherAnholonomicSource PhysicsCore.StageNineHolonomicField
open PhysicsCore.Stage9CU.Fluid.CurrentReadout
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeActionTube
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open Matrix NativeReceiptTimeProfile NativeMixedTimeSpace NativeTimeJetObservation
open NativeFullOrderSynthesis NativePhysicalHistory NativePhysicalHistoryCurrent
open NativeWholeHistoryField (receipt window)
open NativeWholeHistoryClock (duration duration_pos)
open NativeFluidSpatialOperators (slice slice_time slice_spatial)
open NativeFinitePrefixTimeChart (spatialRead)

noncomputable section

def momentum : ComplexVorticityHilbertState := NativeReceiptSpacetime.timeJet (window 0) 1 0

def vorticityAction : ComplexVorticityHilbertState := NativeUnifiedVorticityAction.rate (window 0) 0

theorem initial_interval_near : Icc (0 : ℝ) (duration 0) ∈ 𝓝[Ici (0 : ℝ)] 0 := by
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (duration_pos 0))] with sample after before
  exact ⟨after, before.le⟩

theorem slice_read (observation : ComplexVorticityHilbertState → PhysicalSpace → PhysicalSpace)
    (actual : ℝ) (inside : actual ∈ Icc (0 : ℝ) (duration 0)) (space : PhysicalSpace) :
    read observation (slice actual space) = observation (NativeReceiptSpacetime.state (receipt 0) actual) space := by
  have inSlab : slice actual space ∈ slab 0 := by
    change slice actual space 0 ∈ Icc (0 : ℝ) (duration 0)
    rw [slice_time]
    exact inside
  have source := state_read 0 (slice actual space) inSlab
  rw [slice_time] at source
  have spatial : spatialRead (slice actual space) = space := by
    apply PiLp.ext
    intro direction
    exact slice_spatial actual space direction
  unfold NativePhysicalHistory.read
  rw [slice_time, spatial, source]

theorem field_hasDerivWithinAt (space : PhysicalSpace) :
    HasDerivWithinAt (fun actual => field (slice actual space)) (spatialField momentum space) (Ici (0 : ℝ)) 0 := by
  have source := NativeTimeChartPhysicalAction.receipt_physical_hasDerivWithinAt (window 0) 0
    ⟨le_rfl, (duration_pos 0).le⟩ space
  apply (source.mono_of_mem_nhdsWithin initial_interval_near).congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [initial_interval_near] with actual inside
  exact slice_read _ actual inside space

theorem vorticity_hasDerivWithinAt (space : PhysicalSpace) :
    HasDerivWithinAt (fun actual => vorticityField (slice actual space))
      (spatialField vorticityAction space) (Ici (0 : ℝ)) 0 := by
  have source := NativeUnifiedVorticityAction.physical_hasDerivWithinAt (window 0) 0
    ⟨le_rfl, (duration_pos 0).le⟩ space
  apply (source.mono_of_mem_nhdsWithin initial_interval_near).congr_of_eventuallyEq_of_mem _ (by simp)
  filter_upwards [initial_interval_near] with actual inside
  exact slice_read _ actual inside space

theorem spatial_current_hasDerivWithinAt (space : PhysicalSpace) (direction : Fin 3) :
    HasDerivWithinAt (fun actual => current matter dual direction.succ (slice actual space))
      (spatialField momentum space direction) (Ici (0 : ℝ)) 0 := by
  rw [spatial_read]
  exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) direction).hasFDerivAt.comp_hasDerivWithinAt 0
    (field_hasDerivWithinAt space)

theorem temporal_current_hasDerivWithinAt (space : PhysicalSpace) :
    HasDerivWithinAt (fun actual => current matter dual 0 (slice actual space))
      (inner ℝ (field (slice 0 space)) (spatialField momentum space) / 4) (Ici (0 : ℝ)) 0 := by
  rw [temporal_read]
  convert! ((field_hasDerivWithinAt space).norm_sq.div_const 8).const_add 2 using 1
  ring

theorem momentum_row (wave : IntegerWavevector) : momentum wave =
    NativeStressSource.receiptMomentumAction (receipt 0) wave 0 :=
  NativeReceiptSpacetime.timeJet_one_row (window 0) 0 ⟨le_rfl, (duration_pos 0).le⟩ wave

theorem receipt_initial : NativeReceiptSpacetime.state (receipt 0) 0 =
    RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent.initialState := by
  rw [NativeReceiptSpacetime.state_on_interval (receipt 0) ⟨0, le_rfl, (duration_pos 0).le⟩,
    (receipt 0).wholePath_initial]

theorem momentum_source (wave : IntegerWavevector) : momentum wave =
    biotSavartVelocityCoefficient wave (wholeLatticeVorticityFourierTangentAt RationalVorticityEvaluator.butterflyGainViscosity.coeff
      RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent.initialState wave) := by
  rw [momentum_row]
  change biotSavartVelocityCoefficient wave (wholeLatticeVorticityFourierTangentAt _
    (NativeReceiptSpacetime.state (receipt 0) 0) wave) = _
  rw [receipt_initial]

private theorem rate_curl {nu : Viscosity} {initial : ComplexVorticityHilbertState} {horizon : ℝ}
    {sourceReceipt : WholeContinuousMildSerrinReceipt nu initial horizon} (sourceWindow : Window sourceReceipt)
    (actual : ℝ) (wave : IntegerWavevector) :
    NativeUnifiedVorticityAction.rate sourceWindow actual wave =
      fourierCurlCoefficient wave (NativeReceiptSpacetime.timeJet sourceWindow 1 actual wave) := by
  simp only [NativeUnifiedVorticityAction.rate, NativeReceiptSpacetime.timeJet,
    lp.coeFn_smul, Pi.smul_apply, pow_one, NativeReceiptSpacetime.vorticityFamily,
    NativePolynomialObservations.curl, readProfile, profileCurl_row]
  exact (((fourierCurlCoefficientContinuousLinearMap wave).restrictScalars ℝ).map_smul _ _).symm

theorem vorticityAction_curl (wave : IntegerWavevector) :
    vorticityAction wave = fourierCurlCoefficient wave (momentum wave) := rate_curl (window 0) 0 wave

theorem vorticityAction_row (wave : IntegerWavevector) :
    vorticityAction wave = wholeLatticeVorticityFourierTangentAt RationalVorticityEvaluator.butterflyGainViscosity.coeff
      (NativeReceiptSpacetime.state (receipt 0) 0) wave := by
  rw [vorticityAction_curl, momentum_row]
  let state := NativeReceiptSpacetime.state (receipt 0) 0
  have zero : state 0 = 0 := NativeReceiptSpacetime.state_zero (receipt 0) 0
  have transverse : WholeStateTransverse state := NativeReceiptSpacetime.state_transverse (receipt 0) 0
  change fourierCurlCoefficient wave (biotSavartVelocityCoefficient wave
    (wholeLatticeVorticityFourierTangentAt RationalVorticityEvaluator.butterflyGainViscosity.coeff state wave)) = _
  by_cases nonzero : wave ≠ 0
  · apply fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse _ _ nonzero
    unfold wholeLatticeVorticityFourierTangentAt
    rw [← NativeStressSource.quadraticFlux_biotSavart_action state zero transverse wave]
    simp [nativeFluidConstitutiveVorticityAction, fourierCurlCoefficient, dotProduct_sub,
      dotProduct_smul, dot_self_cross, transverse wave]
  · have waveZero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    rw [wholeLatticeVorticityFourierTangentAt_zero _ state transverse zero]
    simp [fourierCurlCoefficient]

theorem vorticityAction_source (wave : IntegerWavevector) :
    vorticityAction wave = wholeLatticeVorticityFourierTangentAt RationalVorticityEvaluator.butterflyGainViscosity.coeff
      RationalVorticityEvaluator.ButterflyStackedSourceCurrent.stackedShortCurrent.initialState wave := by
  rw [vorticityAction_row, receipt_initial]

end
end SaturationMonoid.NavierStokes.NativePhysicalHistoryInitialAction
