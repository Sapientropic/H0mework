import H0mework.NavierStokes.WindowHistory.Gradient
import H0mework.NavierStokes.PhysicalTranslation.Field

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryFirstJet
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition
open NativePhysicalFourier NativePhysicalGradient NativeCofinalStressPositivity NativeEndpointVelocityCarrier
open NativeWindowHistoryGNS NativeWindowHistoryGradient NativeForwardWindowPairingReadout
noncomputable section
variable {nu : Viscosity}

def meanJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) : ScalarSequence :=
  ∫ shift, jet seed time valid index direction shift ∂averageMeasure

def centeredJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) : HistoryHilbert :=
  jet seed time valid index direction-constant (meanJet seed time valid index direction)

theorem meanJet_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate)
    (wave : IntegerWavevector) : meanJet seed time valid index direction wave = multiplier (wave-index.1) direction*mean seed time index wave := by
  let evaluate := lp.evalCLM ℝ (fun _ : IntegerWavevector => ℂ) 2 wave
  have original := (Lp.memLp (jet seed time valid index direction)).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  change evaluate (∫ shift, jet seed time valid index direction shift ∂averageMeasure) = _
  rw [← evaluate.integral_comp_comm original]
  calc
    _ = ∫ shift, multiplier (wave-index.1) direction*sample seed time index shift wave ∂averageMeasure := by
      apply integral_congr_ae
      filter_upwards [jet_ae seed time valid index direction,sampleDerivative_read seed time valid index direction] with shift generated actual
      change jet seed time valid index direction shift wave = _
      rw [generated,actual]
    _ = _ := by
      rw [integral_const_mul]
      have same := evaluate.integral_comp_comm (sample_integrable seed time index)
      rw [sample_average] at same
      change (∫ shift, sample seed time index shift wave ∂averageMeasure) = mean seed time index wave at same
      rw [same]

theorem constant_pairing (value : ScalarSequence) (field : HistoryHilbert) :
    inner ℂ (constant value) field = inner ℂ value (∫ shift, field shift ∂averageMeasure) := by
  rw [L2.inner_def]
  calc
    _ = ∫ shift, inner ℂ value (field shift) ∂averageMeasure := by
      apply integral_congr_ae
      filter_upwards [constant_ae value] with shift same
      rw [same]
    _ = _ := integral_inner ((Lp.memLp field).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) value

theorem gradient_orthogonal (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate)
    (value : ScalarSequence) : inner ℂ (constant value) (centeredJet seed time valid index direction) = 0 := by
  rw [centeredJet,inner_sub_right,constant_pairing,constant_inner]
  rw [meanJet,sub_self]

theorem gradient_energy_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    ‖jet seed time valid index direction‖^2 = ‖meanJet seed time valid index direction‖^2+‖centeredJet seed time valid index direction‖^2 := by
  have sum : constant (meanJet seed time valid index direction)+centeredJet seed time valid index direction = jet seed time valid index direction := by
    unfold centeredJet
    abel
  have orthogonal := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    (gradient_orthogonal seed time valid index direction (meanJet seed time valid index direction))
  simp only [← pow_two,sum] at orthogonal
  have constantNorm : ‖constant (meanJet seed time valid index direction)‖ = ‖meanJet seed time valid index direction‖ := constantIsometry.norm_map _
  rwa [constantNorm] at orthogonal

theorem action_constant (external : IntegerWavevector) (direction : Coordinate) (displacement : ℝ) (value : ScalarSequence) :
    NativeWindowHistoryTranslation.action external direction displacement (constant value) =
      constant (NativeWindowHistoryTranslation.translation external direction displacement value) := by
  apply Lp.ext
  filter_upwards [NativeWindowHistoryTranslation.action_ae external direction displacement (constant value),constant_ae value,
    constant_ae (NativeWindowHistoryTranslation.translation external direction displacement value)] with shift translated original fixed
  rw [translated,original,fixed]

theorem mean_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    HasDerivAt (fun displacement => NativeWindowHistoryTranslation.translation index.1 direction displacement (mean seed time index))
      (meanJet seed time valid index direction) 0 :=
  NativeWindowHistoryTranslation.translation_hasDerivAt_zero index.1 direction _ _ (meanJet_read seed time valid index direction)

theorem constant_mean_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    HasDerivAt (fun displacement => NativeWindowHistoryTranslation.action index.1 direction displacement (constant (mean seed time index)))
      (constant (meanJet seed time valid index direction)) 0 := by
  have actual := (constantIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (mean_hasDerivAt seed time valid index direction)
  simpa only [action_constant] using! actual

theorem residual_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    HasDerivAt (fun displacement => NativeWindowHistoryTranslation.action index.1 direction displacement (vector seed time index))
      (centeredJet seed time valid index direction) 0 := by
  have actual := (source_hasDerivAt seed time valid index direction).sub (constant_mean_hasDerivAt seed time valid index direction)
  simpa only [vector,map_sub,centeredJet] using! actual

theorem component_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    HasDerivAt (fun displacement => NativeWindowHistoryTranslation.action index.1 direction displacement
      (realization seed time (NativeStressPairingCarrier.component (NativeForwardWindowPairing.data seed time) index)))
      (jet seed time valid index direction) 0 := by
  rw [realization_component]
  exact source_hasDerivAt seed time valid index direction

theorem residual_component_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    HasDerivAt (fun displacement => NativeWindowHistoryTranslation.action index.1 direction displacement
      (residual seed time (NativePositiveKernelCarrier.vector (NativeStressPairingCarrier.kernel (NativeForwardWindowPairing.data seed time)) index)))
      (centeredJet seed time valid index direction) 0 := by
  rw [residual_vector]
  exact residual_hasDerivAt seed time valid index direction

theorem two_leg_green (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (left right : Index) (direction : Coordinate) :
    inner ℂ (jet seed time valid left direction) (history seed time right)+
      inner ℂ (history seed time left) (jet seed time valid right direction) =
        multiplier (left.1-right.1) direction*inner ℂ (history seed time left) (history seed time right) := by
  have leftSide := (source_hasDerivAt seed time valid left direction).inner ℂ (source_hasDerivAt seed time valid right direction)
  simp only [NativeWindowHistoryTranslation.action_zero] at leftSide
  simp_rw [NativeWindowHistoryTranslation.action_relative_inner] at leftSide
  have rightSide := (NativeSpatialTranslation.phase_hasDerivAt direction (left.1-right.1) 0).mul_const
    (inner ℂ (history seed time left) (history seed time right))
  simp only [NativeSpatialTranslation.phase_zero,mul_one] at rightSide
  exact (add_comm _ _).trans (leftSide.unique rightSide)

theorem residual_green (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (left right : Index) (direction : Coordinate) :
    inner ℂ (centeredJet seed time valid left direction) (vector seed time right)+
      inner ℂ (vector seed time left) (centeredJet seed time valid right direction) =
        multiplier (left.1-right.1) direction*inner ℂ (vector seed time left) (vector seed time right) := by
  have leftSide := (residual_hasDerivAt seed time valid left direction).inner ℂ (residual_hasDerivAt seed time valid right direction)
  simp only [NativeWindowHistoryTranslation.action_zero] at leftSide
  simp_rw [NativeWindowHistoryTranslation.action_relative_inner] at leftSide
  have rightSide := (NativeSpatialTranslation.phase_hasDerivAt direction (left.1-right.1) 0).mul_const
    (inner ℂ (vector seed time left) (vector seed time right))
  simp only [NativeSpatialTranslation.phase_zero,mul_one] at rightSide
  exact (add_comm _ _).trans (leftSide.unique rightSide)

theorem stress_green (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (output input direction : Coordinate) :
    inner ℂ (jet seed time valid (wave,output) direction) (history seed time (0,input))+
      inner ℂ (history seed time (wave,output)) (jet seed time valid (0,input) direction) =
        -multiplier wave direction*NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input := by
  rw [two_leg_green,sub_zero,NativeWindowHistoryGNS.stress_read]
  ring

theorem covariance_green (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (wave : IntegerWavevector) (output input direction : Coordinate) :
    inner ℂ (centeredJet seed time valid (wave,output) direction) (vector seed time (0,input))+
      inner ℂ (vector seed time (wave,output)) (centeredJet seed time valid (0,input) direction) =
        -multiplier wave direction*(NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input-
          NativeStressSource.quadraticFlux (wholeVelocity (NativeForwardWindowSource.source seed time).fst) wave output input) := by
  rw [residual_green,sub_zero,NativeWindowHistoryGNS.residual_read]
  ring

theorem meanJet_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    ‖meanJet seed time valid index direction‖^2 ≤ (2*Real.pi)^2*ceiling*
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2) := by
  have paid := jet_bound seed time valid index direction
  rw [gradient_energy_split] at paid
  linarith [sq_nonneg ‖centeredJet seed time valid index direction‖]

theorem centeredJet_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (index : Index) (direction : Coordinate) :
    ‖centeredJet seed time valid index direction‖^2 ≤ (2*Real.pi)^2*ceiling*
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2) := by
  have paid := jet_bound seed time valid index direction
  rw [gradient_energy_split] at paid
  linarith [sq_nonneg ‖meanJet seed time valid index direction‖]

local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def physicalJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (direction output : Coordinate) : ScalarField :=
  (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (meanJet seed time valid (0,output) direction)

theorem physical_translation_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (direction output : Coordinate) :
    HasDerivAt (fun displacement => NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement direction displacement)
      (scalarField (wholeVelocity (NativeForwardWindowSource.source seed time).fst) output))
      (physicalJet seed time valid direction output) 0 := by
  let inverse : ScalarSequence →L[ℝ] ScalarField :=
    (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ
  have original := inverse.hasFDerivAt.comp_hasDerivAt 0 (mean_hasDerivAt seed time valid (0,output) direction)
  have source (displacement : ℝ) : NativePhysicalTranslation.translate (NativePhysicalTranslation.displacement direction displacement)
      (scalarField (wholeVelocity (NativeForwardWindowSource.source seed time).fst) output) =
      inverse (NativeWindowHistoryTranslation.translation 0 direction displacement (mean seed time (0,output))) := by
    rw [NativePhysicalTranslation.translate_eq_fourier,scalarField,LinearIsometryEquiv.apply_symm_apply]
    apply congrArg (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm
    apply lp.ext
    funext wave
    change NativeSpatialTranslation.phase direction displacement wave*wholeVelocity (NativeForwardWindowSource.source seed time).fst wave output =
      NativeSpatialTranslation.phase direction displacement (wave-0)*wholeVelocity (NativeForwardWindowSource.source seed time).fst (wave-0) output
    rw [sub_zero]
  simp only [source]
  convert! original using 1

theorem physicalJet_fourier (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (direction output : Coordinate)
    (wave : IntegerWavevector) : UnitAddTorus.mFourierCoeff (physicalJet seed time valid direction output) wave =
      multiplier wave direction*wholeVelocity (NativeForwardWindowSource.source seed time).fst wave output := by
  rw [← UnitAddTorus.mFourierBasis_repr,physicalJet,LinearIsometryEquiv.apply_symm_apply,meanJet_read]
  change multiplier (wave-0) direction*wholeVelocity (NativeForwardWindowSource.source seed time).fst (wave-0) output = _
  rw [sub_zero]

theorem physicalJet_bound (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time) (direction output : Coordinate) :
    ‖physicalJet seed time valid direction output‖^2 ≤ (2*Real.pi)^2*ceiling*
      NativeUnheatedGlobalGradient.budget (NativeEventualTailControl.terminal seed) (time+2) := by
  rw [physicalJet,LinearIsometryEquiv.norm_map]
  exact meanJet_bound seed time valid (0,output) direction

theorem jet_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (index : Index) (direction : Coordinate) :
    jet seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) index direction =
      jet step.1 time (by linarith) index direction := by
  have old := source_hasDerivAt seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) index direction
  rw [history_next seed step generated time nonnegative] at old
  exact old.unique (source_hasDerivAt step.1 time (by linarith) index direction)

theorem meanJet_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (index : Index) (direction : Coordinate) :
    meanJet seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) index direction =
      meanJet step.1 time (by linarith) index direction := by
  simp only [meanJet,jet_next seed step generated time nonnegative]

theorem centeredJet_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (index : Index) (direction : Coordinate) :
    centeredJet seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) index direction =
      centeredJet step.1 time (by linarith) index direction := by
  simp only [centeredJet,jet_next seed step generated time nonnegative,meanJet_next seed step generated time nonnegative]

theorem physicalJet_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (direction output : Coordinate) :
    physicalJet seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) direction output =
      physicalJet step.1 time (by linarith) direction output := by
  simp only [physicalJet,meanJet_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryFirstJet
