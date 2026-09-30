import H0mework.NavierStokes.InitialData.FinitePhysicalStateRestart
import H0mework.NavierStokes.GeneratedPaths.FiniteObservedCompactness

/-!
# Finite physical states as generated critical paths

The existing restart compiler regenerates every sharply supported,
transverse, Fourier-real finite state from primitive raw source data.  Here
that regenerated source is placed at the identity point of the native
integer-shell reachability graph.  A classical critical margin can therefore
be consumed by the already-generated common-time and strong compactness
machinery without storing a trajectory, target limit, or compactness witness
in the source.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFinitePhysicalStateGeneratedCriticalPath

open scoped BigOperators

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness

noncomputable section

/--
Compile a sharply supported finite physical state into an identity-reachable
source-generated critical path.  The primitive source regenerates support,
reality, and transversality; the path stores no trajectory or target limit.
-/
def generatedCriticalScalePathOfFinitePhysicalState
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (θ : ℝ)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ modes → state wave = 0)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (criticalMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy modes state ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    GeneratedCriticalScalePath ν θ where
  seed := rawSourceOfFiniteVorticityState modes state
  current := rawSourceOfFiniteVorticityState modes state
  arrival := .initial
  initialMargin := by
    have supportEq :=
      rawSourceOfFiniteVorticityState_generatedSupport
        modes zeroNotMem negClosed state
    have compiledEq :=
      generatedComplexVorticityState_rawSourceOfFinitePhysicalState
        modes zeroNotMem negClosed state supported transverse reality
    rw [supportEq] at compiledEq
    rw [supportEq, compiledEq]
    exact criticalMargin

@[simp] theorem
    generatedCriticalScalePathOfFinitePhysicalState_current
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (θ : ℝ)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ modes → state wave = 0)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (criticalMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy modes state ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    (generatedCriticalScalePathOfFinitePhysicalState
      modes zeroNotMem negClosed ν θ state
      supported transverse reality criticalMargin).current =
        rawSourceOfFiniteVorticityState modes state :=
  rfl

theorem
    generatedCriticalScalePathOfFinitePhysicalState_initialState
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : Viscosity)
    (θ : ℝ)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ modes → state wave = 0)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (criticalMargin :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy modes state ≤
        θ * ν.coeff ^ 2 * (2 * Real.pi) ^ 2) :
    generatedComplexVorticityState
        (generatedCriticalScalePathOfFinitePhysicalState
          modes zeroNotMem negClosed ν θ state
          supported transverse reality criticalMargin).current
        (generatedSupport
          (generatedCriticalScalePathOfFinitePhysicalState
            modes zeroNotMem negClosed ν θ state
            supported transverse reality criticalMargin).current) =
      state := by
  exact generatedComplexVorticityState_rawSourceOfFinitePhysicalState
    modes zeroNotMem negClosed state supported transverse reality

end

end ThreeDimensionalVorticityCoefficientFinitePhysicalStateGeneratedCriticalPath
end NavierStokes
end SaturationMonoid
