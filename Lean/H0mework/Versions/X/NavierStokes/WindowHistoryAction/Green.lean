import H0mework.Versions.X.NavierStokes.WindowHistoryAction.Matter

set_option autoImplicit false
open scoped BigOperators Matrix Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowWholeActionGreen
open MeasureTheory
open PhysicsCore.DiracCliffordRepresentation
open PhysicsCore.StageNineFullDiracAdjointMaterial (diracAdjointSpinSwap)
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativePhysicalGradient NativeEndpointVelocityCarrier
open NativeWindowHistoryGNS NativeWindowHistoryGradient NativeWindowHistoryFirstJet
open NativeWindowWholeActionMatter
noncomputable section
variable {nu : Viscosity}

theorem translate_zero (wave : IntegerWavevector) (direction : Coordinate) (field : Spinor) :
    translate wave direction 0 field = field := by
  funext spin color
  exact NativeWindowHistoryTranslation.action_zero wave direction _

theorem dual_translate (left right : IntegerWavevector) (direction : Coordinate) (displacement : ℝ)
    (first last : Spinor) :
    canonicalDual (translate left direction displacement first) (translate right direction displacement last) =
      NativeSpatialTranslation.phase direction displacement (left-right)*canonicalDual first last := by
  change (∑ spin, ∑ color, inner ℂ
    (action diracAdjointSpinSwap (translate left direction displacement first) spin color)
    (translate right direction displacement last spin color)) =
      NativeSpatialTranslation.phase direction displacement (left-right)*
        ∑ spin, ∑ color, inner ℂ (action diracAdjointSpinSwap first spin color) (last spin color)
  rw [← translate_action]
  simp only [NativeWindowWholeActionMatter.translate,NativeWindowHistoryTranslation.action_relative_inner,Finset.mul_sum]

theorem dual_hasDerivAt {first last : ℝ → Spinor} {firstJet lastJet : Spinor}
    (firstDerivative : HasDerivAt first firstJet 0) (lastDerivative : HasDerivAt last lastJet 0) :
    HasDerivAt (fun parameter => canonicalDual (first parameter) (last parameter))
      (canonicalDual firstJet (last 0)+canonicalDual (first 0) lastJet) 0 := by
  have adjoint := action_hasDerivAt firstDerivative diracAdjointSpinSwap
  have point (spin : Fin 4) (color : Fin 2) :=
    (hasDerivAt_pi.mp (hasDerivAt_pi.mp adjoint spin) color).inner ℂ
      (hasDerivAt_pi.mp (hasDerivAt_pi.mp lastDerivative spin) color)
  convert! HasDerivAt.sum (u := Finset.univ) (fun spin _ =>
    HasDerivAt.sum (u := Finset.univ) (fun color _ => point spin color)) using 1
  change (∑ spin, ∑ color, inner ℂ (action diracAdjointSpinSwap firstJet spin color) (last 0 spin color))+
    (∑ spin, ∑ color, inner ℂ (action diracAdjointSpinSwap (first 0) spin color) (lastJet spin color)) = _
  simp only [Finset.sum_add_distrib]
  exact add_comm _ _

def currentJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial : Coordinate) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  canonicalDual (matterJet seed time valid wave spatial) (action (diracGamma direction) (matter seed time 0))+
    canonicalDual (matter seed time wave) (action (diracGamma direction) (matterJet seed time valid 0 spatial))

theorem current_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial : Coordinate) (direction : Fin 4) (wave : IntegerWavevector) :
    HasDerivAt (fun displacement =>
      canonicalDual (translate wave spatial displacement (matter seed time wave))
        (action (diracGamma direction) (translate 0 spatial displacement (matter seed time 0))))
      (currentJet seed time valid spatial direction wave) 0 := by
  have actual := dual_hasDerivAt (matter_hasDerivAt seed time valid wave spatial)
    (action_hasDerivAt (matter_hasDerivAt seed time valid 0 spatial) (diracGamma direction))
  simpa only [translate_zero] using! actual

theorem currentJet_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial : Coordinate) (direction : Fin 4) (wave : IntegerWavevector) :
    currentJet seed time valid spatial direction wave = multiplier wave spatial*
      NativePairedCurrentFourier.coefficient (wholeVelocity (NativeForwardWindowSource.source seed time).fst)
        (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd) direction wave := by
  have actual := current_hasDerivAt seed time valid spatial direction wave
  simp_rw [← translate_action,dual_translate,sub_zero] at actual
  have phase := (NativeSpatialTranslation.phase_hasDerivAt spatial wave 0).mul_const (current seed time direction wave)
  simp only [NativeSpatialTranslation.phase_zero,mul_one] at phase
  exact (actual.unique phase).trans (by rw [current_read])

theorem velocity_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial coordinate : Coordinate) (wave : IntegerWavevector) :
    currentJet seed time valid spatial coordinate.succ wave =
      UnitAddTorus.mFourierCoeff (physicalJet seed time valid spatial coordinate) wave := by
  rw [currentJet_read,physicalJet_fourier]
  rfl

def stressJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial : Coordinate) (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  -(inner ℂ (jet seed time valid (wave,output) spatial) (history seed time (0,input))+
    inner ℂ (history seed time (wave,output)) (jet seed time valid (0,input) spatial))

def residualJet (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial : Coordinate) (wave : IntegerWavevector) (output input : Coordinate) : ℂ :=
  -(inner ℂ (centeredJet seed time valid (wave,output) spatial) (vector seed time (0,input))+
    inner ℂ (vector seed time (wave,output)) (centeredJet seed time valid (0,input) spatial))

theorem stressJet_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial : Coordinate) (wave : IntegerWavevector) (output input : Coordinate) :
    stressJet seed time valid spatial wave output input = multiplier wave spatial*
      NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input := by
  rw [stressJet,stress_green]
  ring

theorem residualJet_read (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial : Coordinate) (wave : IntegerWavevector) (output input : Coordinate) :
    residualJet seed time valid spatial wave output input = multiplier wave spatial*
      (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input-
        NativeStressSource.quadraticFlux (wholeVelocity (NativeForwardWindowSource.source seed time).fst) wave output input) := by
  rw [residualJet,covariance_green]
  ring

theorem multiplier_skew (wave : IntegerWavevector) (spatial : Coordinate) :
    star (multiplier wave spatial) = -multiplier wave spatial := by
  simp [multiplier]

theorem weak_action (field : IntegerWavevector → ℂ) (test : IntegerWavevector →₀ ℂ) (spatial : Coordinate) :
    (∑ wave ∈ test.support, star (test wave)*(multiplier wave spatial*field wave)) =
      -(∑ wave ∈ test.support, star (multiplier wave spatial*test wave)*field wave) := by
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro wave _
  simp only [star_mul,multiplier_skew]
  ring

theorem stress_weak_action (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial output input : Coordinate) (test : IntegerWavevector →₀ ℂ) :
    (∑ wave ∈ test.support, star (test wave)*stressJet seed time valid spatial wave output input) =
      -(∑ wave ∈ test.support, star (multiplier wave spatial*test wave)*
        NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input) := by
  simp_rw [stressJet_read]
  exact weak_action _ test spatial

theorem residual_weak_action (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial output input : Coordinate) (test : IntegerWavevector →₀ ℂ) :
    (∑ wave ∈ test.support, star (test wave)*residualJet seed time valid spatial wave output input) =
      -(∑ wave ∈ test.support, star (multiplier wave spatial*test wave)*
        (NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed time).snd wave output input-
          NativeStressSource.quadraticFlux (wholeVelocity (NativeForwardWindowSource.source seed time).fst) wave output input)) := by
  simp_rw [residualJet_read]
  exact weak_action _ test spatial

local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

def mode (wave : IntegerWavevector) (amplitude : ℂ) : ScalarField :=
  (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.symm (lp.single 2 wave amplitude)

theorem mode_inner (wave : IntegerWavevector) (amplitude : ℂ) (field : ScalarField) :
    inner ℂ (mode wave amplitude) field = star amplitude*UnitAddTorus.mFourierCoeff field wave := by
  rw [← (UnitAddTorus.mFourierBasis (d := Coordinate)).repr.inner_map_map,mode,
    LinearIsometryEquiv.apply_symm_apply,lp.inner_single_left,UnitAddTorus.mFourierBasis_repr]
  simp only [RCLike.inner_apply,starRingEnd_apply,mul_comm]

theorem physical_derivative_pairing (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (valid : -1 ≤ time)
    (spatial coordinate : Coordinate) (test : IntegerWavevector →₀ ℂ) :
    inner ℂ (∑ wave ∈ test.support, mode wave (test wave)) (physicalJet seed time valid spatial coordinate) =
      -inner ℂ (∑ wave ∈ test.support, mode wave (multiplier wave spatial*test wave))
        (scalarField (wholeVelocity (NativeForwardWindowSource.source seed time).fst) coordinate) := by
  simp only [sum_inner,mode_inner,physicalJet_fourier,scalarField_fourier]
  exact weak_action _ test spatial

open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open SourceGeneratedNativeResponseDisposition

theorem currentJet_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (spatial : Coordinate) (direction : Fin 4) (wave : IntegerWavevector) :
    currentJet seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) spatial direction wave =
      currentJet step.1 time (by linarith) spatial direction wave := by
  simp only [currentJet_read,NativeForwardWindowSource.source_next seed step generated time nonnegative]

theorem stressJet_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (spatial : Coordinate) (wave : IntegerWavevector) (output input : Coordinate) :
    stressJet seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) spatial wave output input =
      stressJet step.1 time (by linarith) spatial wave output input := by
  simp only [stressJet_read,NativeForwardWindowSource.source_next seed step generated time nonnegative]

theorem residualJet_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed = some step) (time : ℝ) (nonnegative : 0 ≤ time)
    (spatial : Coordinate) (wave : IntegerWavevector) (output input : Coordinate) :
    residualJet seed (step.2.clockAdvance+time) (by linarith [step.2.clockAdvance_pos]) spatial wave output input =
      residualJet step.1 time (by linarith) spatial wave output input := by
  simp only [residualJet_read,NativeForwardWindowSource.source_next seed step generated time nonnegative]

end
end SaturationMonoid.NavierStokes.NativeWindowWholeActionGreen
