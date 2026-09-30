import H0mework.NavierStokes.SourceHeat.TranslationData
import H0mework.NavierStokes.WindowPhysics.HeatCarrier
import H0mework.NavierStokes.SourceWindow.Pairing

set_option autoImplicit false
open scoped BigOperators Topology ENNReal NNReal ComplexOrder
namespace SaturationMonoid.NavierStokes.NativeHeatPairingAverage
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open NativeCompleteStressAction NativeEndpointVelocityCarrier NativeStressPairingCarrier
open NativeHeatGaussianPhase NativeHeatTranslationData NativeCompleteHeatTransport NativeUnifiedHeatAction
noncomputable section

def family (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) (sample : PhysicalSpace) : FullSpace :=
  translate (displacement nu lag sample) value

theorem family_measurable (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) :
    AEStronglyMeasurable (family nu lag value) gaussian :=
  (translate_measurable value (gaussian.map (displacement nu lag))).comp_measurable
    (by unfold displacement; fun_prop)

theorem family_integrable (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) :
    Integrable (family nu lag value) gaussian := by
  apply Integrable.of_bound (family_measurable nu lag value) ‖value‖
  exact Eventually.of_forall fun sample => (translate_norm (displacement nu lag sample) value).le

theorem family_square_integrable (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) :
    Integrable (fun sample => ‖family nu lag value sample‖ ^ 2) gaussian := by
  have same : (fun sample => ‖family nu lag value sample‖ ^ 2) = fun _ : PhysicalSpace => ‖value‖ ^ 2 := by
    funext sample
    rw [family, translate_norm]
  rw [same]
  exact integrable_const _

theorem average_original (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) :
    (∫ sample, family nu lag value sample ∂gaussian) = fullHeatCLM nu lag value := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space).injective
  apply Prod.ext
  · change (∫ sample, family nu lag value sample ∂gaussian).fst = heatCLM nu lag value.fst
    apply lp.ext
    funext wave
    let read := (lp.evalCLM ℝ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean) 2 wave).comp
      (WithLp.fstL 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space)
    calc
      _ = ∫ sample, (family nu lag value sample).fst wave ∂gaussian :=
        (read.integral_comp_comm (family_integrable nu lag value)).symm
      _ = ∫ sample, character (displacement nu lag sample) wave.1 • value.fst wave ∂gaussian := rfl
      _ = _ := by rw [integral_smul_const, heat_characteristic, heatCLM_row, Complex.coe_smul]
  · change (∫ sample, family nu lag value sample ∂gaussian).snd = tensorHeat nu lag value.snd
    apply lp.ext
    funext wave
    let read := (lp.evalCLM ℝ (fun _ : IntegerWavevector => NativeCompleteStressCarrier.Tensor) 2 wave).comp
      (WithLp.sndL 2 ℝ WholeRestartVelocityEndpointState NativeCompleteStressCarrier.Space)
    calc
      _ = ∫ sample, (family nu lag value sample).snd wave ∂gaussian :=
        (read.integral_comp_comm (family_integrable nu lag value)).symm
      _ = ∫ sample, character (displacement nu lag sample) wave • value.snd wave ∂gaussian := rfl
      _ = _ := by rw [integral_smul_const, heat_characteristic, tensorHeat_row, Complex.coe_smul]

def data (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) (original : NativeStressPairingCarrier.Data)
    (mean : original.mean = value.fst) (stress : original.stress = NativeCompleteStressCarrier.read value.snd) :
    NativeStressPairingCarrier.Data :=
  NativeForwardWindowPairingAverage.data gaussian (family nu lag value)
    (family_integrable nu lag value) (family_square_integrable nu lag value)
    (fun sample => NativeHeatTranslationData.mean_reality (displacement nu lag sample) value
      (by simpa only [mean] using original.reality))
    (fun sample => NativeHeatTranslationData.covariance_positive (displacement nu lag sample) value
      (by simpa only [mean, stress] using original.positive))

theorem data_mean (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) (original : NativeStressPairingCarrier.Data)
    (mean : original.mean = value.fst) (stress : original.stress = NativeCompleteStressCarrier.read value.snd) :
    (data nu lag value original mean stress).mean = (fullHeatCLM nu lag value).fst := by
  change (∫ sample, family nu lag value sample ∂gaussian).fst = _
  rw [average_original]

theorem data_stress (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) (original : NativeStressPairingCarrier.Data)
    (mean : original.mean = value.fst) (stress : original.stress = NativeCompleteStressCarrier.read value.snd) :
    (data nu lag value original mean stress).stress = NativeCompleteStressCarrier.read (fullHeatCLM nu lag value).snd := by
  change NativeCompleteStressCarrier.read (∫ sample, family nu lag value sample ∂gaussian).snd = _
  rw [average_original]

theorem heat_covariance_positive (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) (original : NativeStressPairingCarrier.Data)
    (mean : original.mean = value.fst) (stress : original.stress = NativeCompleteStressCarrier.read value.snd) :
    (covariance (fullHeatCLM nu lag value).fst (NativeCompleteStressCarrier.read (fullHeatCLM nu lag value).snd)).PosSemidef := by
  have generated := (data nu lag value original mean stress).positive
  rwa [data_mean, data_stress] at generated

theorem heat_mean_reality (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) (original : NativeStressPairingCarrier.Data)
    (mean : original.mean = value.fst) (stress : original.stress = NativeCompleteStressCarrier.read value.snd) :
    WholeRestartVelocityEndpointReality (fullHeatCLM nu lag value).fst := by
  have generated := (data nu lag value original mean stress).reality
  rwa [data_mean] at generated

theorem residual_read (value : FullSpace) :
    NativeCompleteStressCarrier.read (residualValue value) =
      NativeCompleteStressCarrier.read value.snd - NativeStressSource.quadraticFlux (wholeVelocity value.fst) := by
  funext wave output input
  change (NativeCompleteStressCarrier.weight wave)⁻¹ •
    (value.snd wave (output,input) -
      NativeCompleteStressBilinear.mixed (wholeVelocity value.fst) (wholeVelocity value.fst) wave (output,input)) = _
  rw [smul_sub]
  have original := congrArg (fun tensor => tensor wave output input)
    (NativeCompleteStressBilinear.mixed_read (wholeVelocity value.fst) (wholeVelocity value.fst))
  rw [NativeHigherTimeJets.mixedFlux_diagonal] at original
  change _ - NativeCompleteStressCarrier.read
    (NativeCompleteStressBilinear.mixed (wholeVelocity value.fst) (wholeVelocity value.fst)) wave output input = _
  rw [original]
  rfl

theorem data_residual (nu : Viscosity) (lag : ℝ≥0) (value : FullSpace) (original : NativeStressPairingCarrier.Data)
    (mean : original.mean = value.fst) (stress : original.stress = NativeCompleteStressCarrier.read value.snd) :
    (data nu lag value original mean stress).stress -
      NativeStressSource.quadraticFlux (wholeVelocity (data nu lag value original mean stress).mean) =
      NativeCompleteStressCarrier.read (tensorHeat nu lag (residualValue value) +
        (tensorHeat nu lag (NativeCompleteStressBilinear.mixed (wholeVelocity value.fst) (wholeVelocity value.fst)) -
          NativeCompleteStressBilinear.mixed (wholeVelocity (heatCLM nu lag value.fst))
            (wholeVelocity (heatCLM nu lag value.fst)))) := by
  rw [data_mean, data_stress, ← heat_residual_split, residual_read, fullHeatCLM_apply]

def sourceData {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    NativeStressPairingCarrier.Data :=
  data nu lag (NativeForwardWindowSource.source seed time) (NativeForwardWindowPairing.data seed time) rfl rfl

theorem source_mean {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    (sourceData seed lag time).mean = (fullHeatCLM nu lag (NativeForwardWindowSource.source seed time)).fst :=
  data_mean nu lag _ _ rfl rfl

theorem source_stress {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ) :
    (sourceData seed lag time).stress = NativeCompleteStressCarrier.read
      (fullHeatCLM nu lag (NativeForwardWindowSource.source seed time)).snd :=
  data_stress nu lag _ _ rfl rfl

theorem source_stress_symmetric {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0)
    (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    (sourceData seed lag time).stress wave output input = (sourceData seed lag time).stress wave input output := by
  rw [source_stress]
  change NativeCompleteStressCarrier.read (tensorHeat nu lag (NativeForwardWindowSource.source seed time).snd)
    wave output input = NativeCompleteStressCarrier.read (tensorHeat nu lag (NativeForwardWindowSource.source seed time).snd)
    wave input output
  rw [tensorHeat_read]
  exact congrArg (fun entry : ℂ =>
    ThreeDimensionalVorticityCoefficientFiniteGalerkinMildDuhamel.finiteStateVorticityHeatMultiplier nu.coeff lag wave • entry)
    (NativeForwardWindowPairingReadout.stress_symmetric seed time wave output input)

theorem source_current {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ)
    (direction : Fin 4) (wave : IntegerWavevector) :
    NativeStressPairingCarrier.pairedCurrent (sourceData seed lag time) direction wave =
      NativePairedCurrentFourier.coefficient
        (wholeVelocity (fullHeatCLM nu lag (NativeForwardWindowSource.source seed time)).fst)
        (NativeCompleteStressCarrier.read (fullHeatCLM nu lag (NativeForwardWindowSource.source seed time)).snd)
        direction wave := by
  rw [NativeStressPairingCarrier.pairedCurrent_eq, source_mean, source_stress]

theorem source_diracCurrent {nu : Viscosity} (seed : GeneratedWholeRestartCurrent nu) (lag : ℝ≥0) (time : ℝ)
    (direction : Fin 4) (wave : IntegerWavevector) :
    NativeHilbertDiracCurrent.diracCurrent (sourceData seed lag time) direction wave =
      NativePairedCurrentFourier.coefficient
        (wholeVelocity (fullHeatCLM nu lag (NativeForwardWindowSource.source seed time)).fst)
        (NativeCompleteStressCarrier.read (fullHeatCLM nu lag (NativeForwardWindowSource.source seed time)).snd)
        direction wave := by
  rw [NativeHilbertDiracCurrent.diracCurrent_eq _ direction wave (source_stress_symmetric seed lag time wave)]
  exact source_current seed lag time direction wave

end
end SaturationMonoid.NavierStokes.NativeHeatPairingAverage
