import H0mework.Versions.X.NavierStokes.PhysicalView.ZeroTail
import H0mework.Versions.X.NavierStokes.PhysicalView.ConsumerBalance
import H0mework.Versions.X.NavierStokes.SourceUnheated.Energy

/-! Preparation, canonical pairing, energy and prediction from the original zero-heat view.
The causal heat in the predictor is the source viscosity along physical time. -/

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal
namespace SaturationMonoid.NavierStokes.NativeZeroPhysicalContract
open Set MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeWindowRootCarrier NativeEndpointVelocityCarrier NativeCompleteStressAction
open NativeViewRuntime NativeViewConsumerNext
noncomputable section

abbrev viscosity := RationalVorticityEvaluator.butterflyGainViscosity

def measure (runtime : Runtime) (time : ℝ) : FullSpace := (payload runtime).view 0 time

def prepared (runtime : Runtime) : FullSpace := measure runtime 0

theorem measure_generated (runtime : Runtime) (time : ℝ) :
    measure runtime time = NativeWindowHeatEvolution.source initial 0
      (clockAt initial (visit (index runtime)).current + time) :=
  CarrierAt.view_generated _ _ _

theorem measure_original (runtime : Runtime) (time : ℝ) :
    measure runtime time = NativeForwardWindowSource.source initial
      (clockAt initial (visit (index runtime)).current + time) :=
  NativeWindowTailRootConsumer.source_read _ _

theorem measure_laboratory (runtime : Runtime) (time : ℝ) :
    measure runtime time = NativeViewPreparation.laboratoryRead viscosity 0
      (NativeUnifiedCompleteSource.source initial) (clock runtime time) :=
  NativeViewPreparation.view_laboratory_read _ _ _

theorem laboratory_time_rate (runtime : Runtime) (time : ℝ) :
    HasDerivAt (clock runtime) 1 time := NativeViewPreparation.rootClock_hasDerivAt _ _ _

theorem prepared_integral (runtime : Runtime) :
    prepared runtime = ∫ shift : ℝ, NativeForwardWindowSource.kernel shift •
      NativeUnifiedCompleteSource.source initial (clockAt initial (visit (index runtime)).current - shift) := by
  rw [prepared, measure_original, add_zero, NativeForwardWindowSource.source_integrand]

theorem prepared_seed : prepared NativeViewRuntime.seed = NativeForwardWindowSource.source initial 0 := by
  rw [prepared, measure_original, visit_current]
  change NativeForwardWindowSource.source initial (elapsedTime initial 0 + 0) = _
  rw [elapsedTime_zero, zero_add]

theorem samples_determine_measurement (runtime : Runtime) (time : ℝ)
    (samples : ℝ → FullSpace)
    (same : EqOn samples (NativeUnifiedCompleteSource.source initial)
      (Icc (clock runtime time - 1) (clock runtime time))) :
    NativeViewPreparation.predict viscosity 0
      (fun sample => samples (clockAt initial (visit (index runtime)).current + sample)) time =
      measure runtime time := NativeViewPreparation.view_past_local _ _ _ _ same

def pairing (runtime : Runtime) (time : ℝ) : NativeStressPairingCarrier.Data :=
  NativeForwardWindowPairing.data initial (clockAt initial (visit (index runtime)).current + time)

theorem pairing_mean (runtime : Runtime) (time : ℝ) :
    (pairing runtime time).mean = (measure runtime time).fst := by
  rw [measure_original]
  rfl

theorem pairing_stress (runtime : Runtime) (time : ℝ) :
    (pairing runtime time).stress = NativeCompleteStressCarrier.read (measure runtime time).snd := by
  rw [measure_original]
  rfl

theorem pairing_residual (runtime : Runtime) (time : ℝ) :
    (pairing runtime time).stress - NativeStressSource.quadraticFlux (wholeVelocity (pairing runtime time).mean) =
      NativeCompleteCorrectionRead.residual (measure runtime time) := by
  rw [pairing_mean, pairing_stress]
  rfl

theorem canonical_current (runtime : Runtime) (time : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    NativeHilbertDiracCurrent.diracCurrent (pairing runtime time) direction wave =
      NativePairedCurrentFourier.coefficient (wholeVelocity (measure runtime time).fst)
        (NativeCompleteStressCarrier.read (measure runtime time).snd) direction wave := by
  rw [NativeHilbertDiracCurrent.diracCurrent_eq _ direction wave
    (NativeForwardWindowPairingReadout.stress_symmetric initial _ wave),
    NativeStressPairingCarrier.pairedCurrent_eq, pairing_mean, pairing_stress]

theorem canonical_source_integral (runtime : Runtime) (time : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    NativeHilbertDiracCurrent.diracCurrent (pairing runtime time) direction wave =
      ∫ shift, NativeForwardWindowSource.kernel shift • NativeHilbertDiracCurrent.diracCurrent
        (NativeCompletePairedAction.source initial
          (clockAt initial (visit (index runtime)).current + time - shift)) direction wave :=
  NativeForwardWindowPairing.diracCurrent_average initial _ direction wave

def total (runtime : Runtime) (time : ℝ) : ℝ := NativeWordStressEnergy.kineticRead (measure runtime time).snd / 2

def resolved (runtime : Runtime) (time : ℝ) : ℝ :=
  ‖NativePhysicalFourier.realField (wholeVelocity (measure runtime time).fst)‖^2 / 2

def unresolved (runtime : Runtime) (time : ℝ) : ℝ :=
  NativeWordStressEnergy.kineticRead (NativeCompleteHeatTransport.residualValue (measure runtime time)) / 2

theorem resolved_generated (runtime : Runtime) (time : ℝ) :
    resolved runtime time = NativeViewEnergyContent.resolved initial 0
      (clockAt initial (visit (index runtime)).current + time) := by
  rw [resolved, measure_generated, NativeViewEnergyContent.resolved_physical]

theorem energy_readout (runtime : Runtime) (time : ℝ) :
    total runtime time = resolved runtime time + unresolved runtime time ∧
      0 ≤ unresolved runtime time ∧ resolved runtime time ≤ total runtime time ∧
      total runtime time ≤ ‖NativeWordStressEnergy.kineticRead‖ * NativeUnifiedCompleteSource.budget initial / 2 := by
  rw [resolved_generated]
  simp only [total, unresolved, measure_generated]
  exact ⟨NativeViewEnergyContent.split initial 0 _, NativeViewEnergyContent.unresolved_nonnegative initial 0 _,
    NativeViewEnergyContent.resolved_le_total initial 0 _, NativeViewEnergyContent.total_bound initial 0 _⟩

def work (runtime : Runtime) (time : ℝ) : ℝ :=
  NativeViewEnergyWork.residualWork initial 0 (clockAt initial (visit (index runtime)).current + time)

def dissipation (runtime : Runtime) (time : ℝ) : ℝ :=
  NativeViewEnergyWork.dissipation initial 0 (clockAt initial (visit (index runtime)).current + time)

theorem energy_integral (runtime : Runtime) (first last : ℝ)
    (first_nonnegative : 0 ≤ first) (last_nonnegative : 0 ≤ last) :
    resolved runtime last - resolved runtime first =
      ∫ time in first..last, work runtime time - viscosity.coeff * dissipation runtime time := by
  have actual := NativeUnheatedEnergy.energy_integral initial
    (clockAt initial (visit (index runtime)).current + first)
    (clockAt initial (visit (index runtime)).current + last)
    (by linarith [clockAt_nonnegative initial (visit (index runtime)).current])
    (by linarith [clockAt_nonnegative initial (visit (index runtime)).current])
  have shifted := intervalIntegral.integral_comp_add_left (a := first) (b := last)
    (fun time => NativeViewEnergyWork.residualWork initial 0 time -
      viscosity.coeff * NativeViewEnergyWork.dissipation initial 0 time)
    (clockAt initial (visit (index runtime)).current)
  rw [resolved_generated, resolved_generated]
  exact actual.trans shifted.symm

def kernel (runtime : Runtime) (target time : ℝ) : WholeRestartVelocityEndpointState :=
  NativeUnifiedHeatAction.heatCLM viscosity ⟨max (target - time) 0, le_max_right _ _⟩
    (divergenceCLM (measure runtime time).snd)

def forecast (runtime : Runtime) (target : ℝ) : WholeRestartVelocityEndpointState :=
  NativeUnifiedHeatAction.heatCLM viscosity ⟨max target 0, le_max_right _ _⟩
    (NativeNegativeFourMomentum.embed (prepared runtime).fst) +
      ∫ time in (0 : ℝ)..target, kernel runtime target time

theorem kernel_generated (runtime : Runtime) (target time : ℝ) :
    kernel runtime target time = NativeViewPrediction.heatForcing initial 0
      (clockAt initial (visit (index runtime)).current + target)
      (clockAt initial (visit (index runtime)).current + time) := by
  unfold kernel NativeViewPrediction.heatForcing NativeViewPrediction.forcing
  rw [measure_generated]
  simp only [add_sub_add_left_eq_sub]

theorem forecast_generated (runtime : Runtime) (target : ℝ) :
    forecast runtime target = NativeViewPrediction.prediction initial 0
      (clockAt initial (visit (index runtime)).current)
      (clockAt initial (visit (index runtime)).current + target) := by
  have shifted := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := target)
    (NativeViewPrediction.heatForcing initial 0 (clockAt initial (visit (index runtime)).current + target))
    (clockAt initial (visit (index runtime)).current)
  simp only [add_zero] at shifted
  unfold forecast NativeViewPrediction.prediction prepared
  rw [measure_generated, add_zero, NativeWindowHeatEvolution.state_embedded, ← shifted]
  simp only [add_sub_cancel_left]
  congr 1
  exact intervalIntegral.integral_congr fun time _ => kernel_generated runtime target time

theorem forecast_recovers (runtime : Runtime) (target : ℝ) (nonnegative : 0 ≤ target) :
    forecast runtime target = NativeNegativeFourMomentum.embed (measure runtime target).fst := by
  rw [forecast_generated, measure_generated]
  exact (NativeViewPrediction.prediction_physical initial 0 _ _
    (by linarith [clockAt_nonnegative initial (visit (index runtime)).current]) (by linarith)).symm

theorem forecast_unique (runtime : Runtime) (target : ℝ) (nonnegative : 0 ≤ target)
    (value : WholeRestartVelocityEndpointState)
    (predicted : NativeNegativeFourMomentum.embed value = forecast runtime target) :
    value = (measure runtime target).fst := by
  apply NativeNegativeFourMomentum.embed_injective
  exact predicted.trans (forecast_recovers runtime target nonnegative)

theorem measured_next (runtime : Runtime) (time : ℝ) :
    measure runtime.tick.next time = measure runtime (advance runtime + time) :=
  NativeWindowTailRootConsumer.measured_next runtime time

theorem prepared_next (runtime : Runtime) : prepared runtime.tick.next = measure runtime (advance runtime) := by
  simpa only [prepared, add_zero] using measured_next runtime 0

theorem pairing_next (runtime : Runtime) (time : ℝ) :
    pairing runtime.tick.next time = pairing runtime (advance runtime + time) := by
  apply NativeWindowRootPairing.data_ext
  · rw [pairing_mean, pairing_mean, measured_next]
  · rw [pairing_stress, pairing_stress, measured_next]

theorem forecast_next (runtime : Runtime) :
    forecast runtime (advance runtime) = NativeNegativeFourMomentum.embed (prepared runtime.tick.next).fst := by
  rw [forecast_recovers runtime _ (advance_nonnegative runtime), prepared_next]

theorem energy_write_next (runtime : Runtime) :
    resolved runtime.tick.next 0 - resolved runtime 0 =
      ∫ time in (0 : ℝ)..advance runtime, work runtime time - viscosity.coeff * dissipation runtime time := by
  have next : resolved runtime.tick.next 0 = resolved runtime (advance runtime) := by
    unfold resolved
    rw [measured_next, add_zero]
  rw [next]
  exact energy_integral runtime 0 _ le_rfl (advance_nonnegative runtime)

theorem controller_write_back (runtime : Runtime) :
    HEq (facade.readoutAt runtime PUnit.unit)
      (runtime.tick.generated.projectionOutcome ((installation initial).embed resolution)) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        ((nativeTemporalRoot initial).generatedLedgerAt (visit runtime.state).current) ∧
      runtime.tick.nextCurrent = process.stateAt (process.successor runtime.state) ∧
      forecast runtime (advance runtime) = NativeNegativeFourMomentum.embed (prepared runtime.tick.next).fst ∧
      (∀ time, measure runtime.tick.next time = measure runtime (advance runtime + time)) ∧
      (∀ time, clock runtime.tick.next time = clock runtime (advance runtime + time)) ∧
      (∀ time, pairing runtime.tick.next time = pairing runtime (advance runtime + time)) ∧
      resolved runtime.tick.next 0 - resolved runtime 0 =
        ∫ time in (0 : ℝ)..advance runtime, work runtime time - viscosity.coeff * dissipation runtime time :=
  ⟨(activated_readout runtime).1, (activated_readout runtime).2.1, (activated_readout runtime).2.2,
    forecast_next runtime, measured_next runtime, clock_next runtime, pairing_next runtime, energy_write_next runtime⟩

end
end SaturationMonoid.NavierStokes.NativeZeroPhysicalContract
