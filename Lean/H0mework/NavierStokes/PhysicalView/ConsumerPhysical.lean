import H0mework.NavierStokes.PhysicalView.ConsumerBalance

set_option autoImplicit false
open scoped Topology ENNReal NNReal ContDiff

namespace SaturationMonoid.NavierStokes.NativeViewPhysicalConsumer

open Set MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier NativeWindowRootControl NativeWindowSpacetimeFourier
open NativeViewRuntime NativeViewConsumerNext NativeViewObservation NativeViewObservedEnergy

noncomputable section

/-- This instrument consumes the fixed root's actual emitted payload and controls U, full σ, full R, curl U, and ∂t U. -/
def read (runtime : Runtime) (point : Spacetime) := outputs (payload runtime) resolution point

/-- Forecasts use the prepared velocity and the generated complete stress in Duhamel's formula. -/
def forecast (runtime : Runtime) (target : ℝ) := NativeViewRootPrediction.predict (payload runtime) resolution target

theorem measured_at_laboratory_time (runtime : Runtime) (time : ℝ) :
    measure (payload runtime) resolution time = NativeViewPreparation.laboratoryRead
      RationalVorticityEvaluator.butterflyGainViscosity resolution.1 (NativeUnifiedCompleteSource.source initial)
      (clock runtime time) := measure_laboratory _ _ _

theorem laboratory_time_rate (runtime : Runtime) (time : ℝ) :
    HasDerivAt (clock runtime) 1 time := NativeViewPreparation.rootClock_hasDerivAt _ _ _

theorem samples_determine_measurement (runtime : Runtime) (time : ℝ)
    (samples : ℝ → NativeCompleteStressAction.FullSpace)
    (same : EqOn samples (NativeUnifiedCompleteSource.source initial) (Icc (clock runtime time - 1) (clock runtime time))) :
    NativeViewPreparation.predict RationalVorticityEvaluator.butterflyGainViscosity resolution.1
      (fun sample => samples (clockAt initial (visit (index runtime)).current + sample)) time =
      measure (payload runtime) resolution time :=
  NativeViewPreparation.view_past_local _ _ _ samples same

theorem prepared_by_source (runtime : Runtime) :
    initialState runtime = NativeCompleteHeatTransport.fullHeatCLM RationalVorticityEvaluator.butterflyGainViscosity
      resolution.1 (∫ shift : ℝ, NativeForwardWindowSource.kernel shift •
        NativeUnifiedCompleteSource.source initial (clockAt initial (visit (index runtime)).current - shift)) :=
  NativeViewPreparation.prepared_integral _ _

theorem forecast_recovers (runtime : Runtime) (target : ℝ) (nonnegative : 0 ≤ target) :
    forecast runtime target = NativeNegativeFourMomentum.embed (measure (payload runtime) resolution target).fst :=
  NativeViewRootPrediction.prediction_recovers_velocity _ _ target nonnegative

theorem forecast_unique (runtime : Runtime) (target : ℝ) (nonnegative : 0 ≤ target)
    (value : ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint.WholeRestartVelocityEndpointState)
    (predicted : NativeNegativeFourMomentum.embed value = forecast runtime target) :
    value = (measure (payload runtime) resolution target).fst :=
  NativeViewRootPrediction.predicted_velocity_unique _ _ target nonnegative value predicted

theorem canonical_readout (runtime : Runtime) (time : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    NativeHilbertDiracCurrent.diracCurrent (NativeWindowRootPairing.data (payload runtime) resolution time) direction wave =
      NativePairedCurrentFourier.coefficient (NativeEndpointVelocityCarrier.wholeVelocity (measure (payload runtime) resolution time).fst)
        (NativeCompleteStressCarrier.read (measure (payload runtime) resolution time).snd) direction wave :=
  NativeWindowRootPairing.canonical_current _ _ _ _ _

theorem physical_time_action (runtime : Runtime) (time : ℝ) (nonnegative : 0 ≤ time)
    (space : ThreeDimensionalPeriodicCoarseFilterCore.PhysicalSpace) :
    HasDerivAt (fun sample => velocity (payload runtime) resolution (sample, space))
      (NativeViewPhysicalEquation.momentumField initial resolution.1
        (clockAt initial (visit (index runtime)).current + time, space)) time := by
  have actual := rate_actual (payload runtime) resolution time space
  erw [rate_momentum _ _ time nonnegative space] at actual
  exact actual

theorem native_channels (runtime : Runtime) (modes : Finset IntegerWavevector) (time : ℝ)
    (nonnegative : 0 ≤ time) (wave : IntegerWavevector) :
    NativeCompleteEvolution.nativeRow RationalVorticityEvaluator.butterflyGainViscosity modes
      (measure (payload runtime) resolution time) wave =
      if wave ∈ modes then NativeViewPhysicalCurl.vorticityJet initial resolution.1 resolution.2 1
        (clockAt initial (visit (index runtime)).current + time) wave else 0 := by
  erw [measure_view, CarrierAt.view_generated]
  exact NativeViewPhysicalEquation.native_channels initial resolution.1 resolution.2 modes _
    (by linarith [clockAt_nonnegative initial (visit (index runtime)).current]) wave

theorem all_order_control (runtime : Runtime) (order : ℕ) (exponent : ℝ≥0∞)
    {domain : Set Spacetime} (compact : IsCompact domain) :
    ∃ bound : ℝ, 0 ≤ bound ∧
      MemLp (iteratedFDeriv ℝ order (read runtime)) exponent (volume.restrict domain) ∧
      eLpNorm (iteratedFDeriv ℝ order (read runtime)) exponent (volume.restrict domain) ≤
        ENNReal.ofReal bound * volume domain ^ (1 / exponent.toReal) :=
  outputs_all_order_Lp (payload runtime) resolution order exponent compact

theorem energy_readout (runtime : Runtime) (time : ℝ) :
    total (payload runtime) resolution time = resolved (payload runtime) resolution time + unresolved (payload runtime) resolution time ∧
      0 ≤ unresolved (payload runtime) resolution time ∧
      resolved (payload runtime) resolution time ≤ total (payload runtime) resolution time ∧
      total (payload runtime) resolution time ≤
        ‖NativeWordStressEnergy.kineticRead‖ * NativeUnifiedCompleteSource.budget initial / 2 := by
  exact ⟨(split _ _ _).1, (split _ _ _).2, budget _ _ _⟩

/-- The same root disposes the whole ledger, writes the forecast and energy, and generates the next measured state. -/
theorem controller_write_back (runtime : Runtime) :
    HEq (facade.readoutAt runtime PUnit.unit)
      (runtime.tick.generated.projectionOutcome ((installation initial).embed resolution)) ∧
      HEq runtime.tick.generated.wholeLedgerWriteBack
        ((nativeTemporalRoot initial).generatedLedgerAt (visit runtime.state).current) ∧
      runtime.tick.nextCurrent = process.stateAt (process.successor runtime.state) ∧
      forecast runtime (advance runtime) = NativeNegativeFourMomentum.embed (initialState runtime.tick.next).fst ∧
      (∀ time, measure (payload runtime.tick.next) resolution time =
        measure (payload runtime) resolution (advance runtime + time)) ∧
      (∀ time, clock runtime.tick.next time = clock runtime (advance runtime + time)) ∧
      resolved (payload runtime.tick.next) resolution 0 - resolved (payload runtime) resolution 0 =
        ∫ time in (0 : ℝ)..advance runtime, work (payload runtime) resolution time -
          RationalVorticityEvaluator.butterflyGainViscosity.coeff * dissipation (payload runtime) resolution time :=
  ⟨(activated_readout runtime).1, (activated_readout runtime).2.1, (activated_readout runtime).2.2,
    forecast_next runtime, measured_next runtime, clock_next runtime, NativeViewConsumerBalance.energy_write_next runtime⟩

end
end SaturationMonoid.NavierStokes.NativeViewPhysicalConsumer
