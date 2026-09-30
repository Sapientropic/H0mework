import H0mework.NavierStokes.WindowHistory.Realization

set_option autoImplicit false
open scoped BigOperators Topology ENNReal ComplexOrder
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryGNS
open Set Filter MeasureTheory
open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativePhysicalFourier NativeCofinalStressPositivity NativeEndpointVelocityCarrier
open NativeForwardWindowPairingReadout
noncomputable section
variable {nu : Viscosity}

theorem mean_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (coordinate : Coordinate) :
    inner ℂ (constant (lp.single 2 wave (1 : ℂ))) (history seed time (0,coordinate)) =
      wholeVelocity (NativeForwardWindowSource.source seed time).fst wave coordinate := by
  rw [← realization_background, ← realization_component, (realization seed time).inner_map_map,
    NativeStressPairingCarrier.background_component, sub_zero]
  rfl

theorem stress_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    inner ℂ (history seed time (wave,output)) (history seed time (0,input)) =
      -NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input := by
  rw [history_inner, sub_zero]
  rfl

theorem residual_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) (output input : Coordinate) :
    inner ℂ (vector seed time (wave,output)) (vector seed time (0,input)) =
      -(NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input-
        NativeStressSource.quadraticFlux (wholeVelocity (NativeForwardWindowSource.source seed time).fst) wave output input) := by
  rw [vector_inner]
  change -(NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd (wave-0) output input-
    NativeStressSource.quadraticFlux (wholeVelocity (NativeForwardWindowSource.source seed time).fst) (wave-0) output input) = _
  rw [sub_zero]

abbrev Spinor := Fin 4 → Fin 2 → HistoryHilbert

def mapSpinor (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (value : NativeHilbertDiracCurrent.Spinor (NativeForwardWindowPairing.data seed time)) : Spinor :=
  fun spin color => realization seed time (value spin color)

def action (matrix : DiracMatrix) (value : Spinor) : Spinor :=
  fun spin color => ∑ other : Fin 4, matrix spin other • value other color

def canonicalDual (value : Spinor) : Module.Dual ℂ Spinor where
  toFun candidate := ∑ spin : Fin 4, ∑ color : Fin 2,
    inner ℂ (action diracAdjointSpinSwap value spin color) (candidate spin color)
  map_add' first last := by simp only [Pi.add_apply, inner_add_right, Finset.sum_add_distrib]
  map_smul' scalar candidate := by
    simp only [Pi.smul_apply, inner_smul_right, Finset.mul_sum, RingHom.id_apply, smul_eq_mul]

theorem action_map (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (matrix : DiracMatrix)
    (value : NativeHilbertDiracCurrent.Spinor (NativeForwardWindowPairing.data seed time)) :
    action matrix (mapSpinor seed time value) =
      mapSpinor seed time (NativeHilbertDiracCurrent.action (NativeForwardWindowPairing.data seed time) matrix value) := by
  funext spin color
  change (∑ other : Fin 4, matrix spin other • realization seed time (value other color)) =
    realization seed time (∑ other : Fin 4, matrix spin other • value other color)
  rw [map_sum]
  simp only [map_smul]

theorem canonicalDual_map (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (first last : NativeHilbertDiracCurrent.Spinor (NativeForwardWindowPairing.data seed time)) :
    canonicalDual (mapSpinor seed time first) (mapSpinor seed time last) =
      NativeHilbertDiracCurrent.canonicalDual (NativeForwardWindowPairing.data seed time) first last := by
  change (∑ spin : Fin 4, ∑ color : Fin 2,
    inner ℂ (action diracAdjointSpinSwap (mapSpinor seed time first) spin color) (mapSpinor seed time last spin color)) = _
  rw [action_map]
  simp only [mapSpinor, (realization seed time).inner_map_map]
  rfl

def matter (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (wave : IntegerWavevector) : Spinor :=
  mapSpinor seed time (NativeHilbertDiracCurrent.matter (NativeForwardWindowPairing.data seed time) wave)

def current (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  canonicalDual (matter seed time wave) (action (diracGamma direction) (matter seed time 0))

theorem current_original (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    current seed time direction wave = NativeHilbertDiracCurrent.diracCurrent (NativeForwardWindowPairing.data seed time) direction wave := by
  unfold current matter
  rw [action_map, canonicalDual_map]
  rfl

theorem current_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    current seed time direction wave = NativePairedCurrentFourier.coefficient
      (wholeVelocity (NativeForwardWindowSource.source seed time).fst)
        (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd) direction wave := by
  rw [current_original, NativeHilbertDiracCurrent.diracCurrent_eq _ direction wave (NativeForwardWindowPairingReadout.stress_symmetric seed time wave),
    NativeStressPairingCarrier.pairedCurrent_eq]
  rfl

theorem current_average (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (direction : Fin 4) (wave : IntegerWavevector) :
    current seed time direction wave = ∫ shift, NativeForwardWindowSource.kernel shift •
      NativeHilbertDiracCurrent.diracCurrent (NativeCompletePairedAction.source seed (time-shift)) direction wave := by
  rw [current_original, NativeForwardWindowPairing.diracCurrent_average]

theorem average_support : ∀ᵐ shift : ℝ ∂averageMeasure, shift < -1 := by
  change ∀ᵐ shift : ℝ ∂volume.withDensity (fun shift => (density shift : ℝ≥0∞)), shift < -1
  rw [ae_withDensity_iff density_measurable.coe_nnreal_ennreal]
  filter_upwards with shift nonzero
  apply NativeForwardWindowSource.kernel_support shift
  intro zero
  apply nonzero
  simp only [density, zero]
  rfl

theorem history_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) (index : Index) :
    history seed (step.2.clockAdvance+time) index = history step.1 time index := by
  apply Lp.ext
  filter_upwards [history_ae seed (step.2.clockAdvance+time) index, history_ae step.1 time index, average_support]
    with shift first last inside
  rw [first,last,sample,sample,add_sub_assoc,
    NativeUnifiedCompleteSource.source_generated_next seed step generated (time-shift) (by linarith)]

theorem mean_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) (index : Index) :
    mean seed (step.2.clockAdvance+time) index = mean step.1 time index := by
  rw [mean,mean,NativeForwardWindowSource.source_next seed step generated time nonnegative]

theorem vector_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) (index : Index) :
    vector seed (step.2.clockAdvance+time) index = vector step.1 time index := by
  rw [vector,vector,history_next seed step generated time nonnegative,mean_next seed step generated time nonnegative]

theorem data_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    NativeForwardWindowPairing.data seed (step.2.clockAdvance+time) = NativeForwardWindowPairing.data step.1 time := by
  have ext (first last : NativeStressPairingCarrier.Data) (sameMean : first.mean=last.mean) (sameStress : first.stress=last.stress) : first=last := by
    cases first
    cases last
    cases sameMean
    cases sameStress
    rfl
  apply ext
  · change (NativeForwardWindowSource.source seed (step.2.clockAdvance+time)).fst = _
    rw [NativeForwardWindowSource.source_next seed step generated time nonnegative]
    rfl
  · change NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed (step.2.clockAdvance+time)).snd = _
    rw [NativeForwardWindowSource.source_next seed step generated time nonnegative]
    rfl

theorem current_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step)
    (time : ℝ) (nonnegative : 0 ≤ time) (direction : Fin 4) (wave : IntegerWavevector) :
    current seed (step.2.clockAdvance+time) direction wave = current step.1 time direction wave := by
  rw [current_original,current_original,data_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryGNS
