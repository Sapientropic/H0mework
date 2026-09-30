import H0mework.Versions.X.NavierStokes.WindowEnergyTraceDual.Energy
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceOperator.Time
import H0mework.Versions.X.NavierStokes.WindowEnergyTraceAdjoint.Write
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowTraceDualEvolution
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeFiniteActionResolvent NativeWholeH1Mixed NativeResolventAdjoint
open NativeWindowTraceOperator (test test_pairing form_symmetric)
open NativeWindowTraceOperatorTime (traceJet traceJet_zero traceJet_hasDerivAt quadraticJet)
open NativeWindowStageNineSource (riesz)
noncomputable section
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {nu : Viscosity}

def mass (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :
    physicalSpace (modes M) →L[ℝ] physicalSpace (modes M) := LinearMap.toContinuousLinearMap (test seed time (modes M) (modes M) F radius)

def inverse (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) (time : ℝ) :=
  (mass seed M F radius time).inverse

def lifted (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (v : physicalSpace (modes M)) := inverse seed M F radius time v

def energy (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (v : physicalSpace (modes M)) : ℝ := pairing (modes M) (lifted seed M F radius time v) v

theorem mass_symmetric (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (x y : physicalSpace (modes M)) : pairing (modes M) x (mass seed M F radius time y)=
      pairing (modes M) y (mass seed M F radius time x) := by
  change pairing (modes M) x (test seed time (modes M) (modes M) F radius y)=_
  rw [test_pairing]
  change _=pairing (modes M) y (test seed time (modes M) (modes M) F radius x)
  rw [test_pairing,form_symmetric]

theorem field_contDiff (seed : GeneratedWholeRestartCurrent nu) (F : Finset IntegerWavevector) (radius : ℕ) :
    ContDiff ℝ 1 (fun t => NativeWindowTraceOperator.field seed t F radius) := by
  have derivative (time : ℝ) : HasDerivAt (fun t => NativeWindowTraceOperator.field seed t F radius)
      (traceJet seed F radius 1 time) time := by simpa only [traceJet_zero] using traceJet_hasDerivAt seed F radius 0 time
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun time => (derivative time).differentiableAt,?_⟩
  have same : deriv (fun t => NativeWindowTraceOperator.field seed t F radius)=traceJet seed F radius 1 :=
    funext fun time => (derivative time).deriv
  rw [same]
  exact continuous_iff_continuousAt.mpr fun time => (traceJet_hasDerivAt seed F radius 1 time).continuousAt

theorem mass_contDiff (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ) :
    ContDiff ℝ 1 (mass seed M F radius) := by
  rw [contDiff_clm_apply_iff]
  intro x
  have dual : ContDiff ℝ 1 (fun t => riesz (modes M) (mass seed M F radius t x)) := by
    rw [contDiff_clm_apply_iff]
    intro y
    have same (time : ℝ) : riesz (modes M) (mass seed M F radius time x) y=
        NativeWindowAugmentedFixedOperator.spectral nu (modes M) (modes M) y x+
          ∑ i : Coordinate,inner ℝ (NativeWindowTraceOperator.field seed time F radius)
            (NativeWindowStressHeatSource.physical (NativeWindowStressOseenTest.evaluate (modes M) F i y*
              NativeWindowStressOseenTest.evaluate (modes M) F i x)) := by
      change pairing (modes M) (test seed time (modes M) (modes M) F radius x) y=_
      rw [pairing_symmetric,test_pairing]
      rfl
    simp only [same]
    apply contDiff_const.add
    apply ContDiff.sum
    intro i _
    exact (field_contDiff seed F radius).inner ℝ contDiff_const
  have original := (riesz (modes M)).symm.contDiff.comp dual
  simpa only [Function.comp_def,ContinuousLinearEquiv.symm_apply_apply] using! original

theorem source_invertible (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃ low : ℕ,∀ radius≥low,∀ M : ℕ,∀ F : Finset IntegerWavevector,FiniteModeNegClosed F →
      ∀ time∈Icc 0 horizon,(mass seed M F radius time).IsInvertible := by
  obtain ⟨low,paid⟩ := NativeWindowTraceDualEnergy.source_inverse seed horizon nonnegative
  refine ⟨low,fun radius above M F closed time inside => ?_⟩
  obtain ⟨generated,same,_⟩ := paid radius above (modes M) F (modes_zero M) (modes_closed M) closed time inside
  refine ⟨generated.toContinuousLinearEquiv,?_⟩
  apply ContinuousLinearMap.ext
  intro v
  exact same v

theorem inverse_differentiableAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (actual : (mass seed M F radius time).IsInvertible) : DifferentiableAt ℝ (inverse seed M F radius) time := by
  have generated := (actual.contDiffAt_map_inverse (n := 1)).comp time (mass_contDiff seed M F radius).contDiffAt
  exact generated.differentiableAt (by norm_num)

theorem mass_rate_pair (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (time : ℝ) (v : physicalSpace (modes M)) :
    pairing (modes M) v (deriv (mass seed M F radius) time v)=quadraticJet seed (modes M) F radius 1 time v := by
  have derivative := ((mass_contDiff seed M F radius).differentiable (by norm_num) time).hasDerivAt
  have acted := derivative.clm_apply (hasDerivAt_const time v)
  have physical := (LinearMap.toContinuousLinearMap (coefficients (modes M))).hasFDerivAt.comp_hasDerivAt time acted
  have pair := (hasDerivAt_const time (coefficients (modes M) v)).inner ℝ physical
  have original := NativeWindowTraceOperatorTime.actual_hasDerivAt seed (modes M) F radius time v
  have equal := pair.unique original
  simpa only [map_zero,add_zero,inner_zero_left,zero_add] using! equal

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem mass_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    mass seed M F radius (step.2.clockAdvance+time)=mass step.1 M F radius time := by
  rw [mass,NativeWindowTraceOperatorAction.test_next seed step generated time nonnegative]
  rfl

theorem inverse_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    inverse seed M F radius (step.2.clockAdvance+time)=inverse step.1 M F radius time := by
  rw [inverse,mass_next seed M F radius step generated time nonnegative]
  rfl

theorem energy_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (F : Finset IntegerWavevector) (radius : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) (w : physicalSpace (modes M)) :
    energy seed M F radius (step.2.clockAdvance+time) w=energy step.1 M F radius time w := by
  rw [energy,lifted,inverse_next seed M F radius step generated time nonnegative]
  rfl

end
end SaturationMonoid.NavierStokes.NativeWindowTraceDualEvolution
