import H0mework.NavierStokes.InitialData.FinitePhysicalStateRestart
import H0mework.NavierStokes.ShellSources.TraceCumulative

/-!
# Support lift for a finite physical vorticity state

An actual finite physical state may have to start its next Galerkin segment on
a larger source-owned symbolic support.  This module proves that recompiling
the same state with `rawSourceOfFiniteVorticityState` on such a support is
exact zero extension: the whole Hilbert state and the flattened generated
coefficient carrier do not change.

The bridge is a transporter.  It consumes only a concrete support inclusion,
zero-freeness and negation closure of the larger support, and the physical
support/transversality/reality laws of the existing state.  It does not settle
an earlier symbolic trace, identify any old grammar receipt with the new
physical update, or carry a trajectory, branch, target, continuation, or debt
certificate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFinitePhysicalStateSupportLift

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative

noncomputable section

/-- Sharp support on a physical inventory remains sharp after enlarging the
inventory. -/
theorem finitePhysicalState_supported_on_superSupport
    {physicalModes symbolicModes : Finset IntegerWavevector}
    (supportSubset : physicalModes ⊆ symbolicModes)
    {state : ComplexVorticityHilbertState}
    (supported :
      ∀ wave, wave ∉ physicalModes → state wave = 0) :
    ∀ wave, wave ∉ symbolicModes → state wave = 0 := by
  intro wave waveNotMem
  exact supported wave (fun physicalMem =>
    waveNotMem (supportSubset physicalMem))

/-- A state transverse on its sharp physical support remains transverse on
every larger inventory because every added row is zero. -/
theorem finitePhysicalState_transverse_on_superSupport
    {physicalModes symbolicModes : Finset IntegerWavevector}
    {state : ComplexVorticityHilbertState}
    (supported :
      ∀ wave, wave ∉ physicalModes → state wave = 0)
    (transverse :
      ∀ wave ∈ physicalModes,
        complexWavevector wave ⬝ᵥ state wave = 0) :
    ∀ wave ∈ symbolicModes,
      complexWavevector wave ⬝ᵥ state wave = 0 := by
  intro wave _symbolicMem
  by_cases physicalMem : wave ∈ physicalModes
  · exact transverse wave physicalMem
  · rw [supported wave physicalMem]
    simp

/--
Zero-filled recompilation on a larger zero-free, negation-closed support
recovers the exact existing physical state on the whole Hilbert carrier.
-/
theorem generatedComplexVorticityState_rawSourceOfFinitePhysicalState_supportLift
    (physicalModes symbolicModes : Finset IntegerWavevector)
    (supportSubset : physicalModes ⊆ symbolicModes)
    (zeroNotMem : (0 : IntegerWavevector) ∉ symbolicModes)
    (negClosed :
      ∀ wave, wave ∈ symbolicModes → waveNeg wave ∈ symbolicModes)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ physicalModes → state wave = 0)
    (transverse :
      ∀ wave ∈ physicalModes,
        complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state) :
    generatedComplexVorticityState
        (rawSourceOfFiniteVorticityState symbolicModes state)
        (generatedSupport
          (rawSourceOfFiniteVorticityState symbolicModes state)) =
      state := by
  exact
    generatedComplexVorticityState_rawSourceOfFinitePhysicalState
      symbolicModes zeroNotMem negClosed state
      (finitePhysicalState_supported_on_superSupport
        supportSubset supported)
      (finitePhysicalState_transverse_on_superSupport
        supported transverse)
      reality

/-- The support-lifted compiler retains transversality on every Fourier row,
not only on the enlarged finite inventory. -/
theorem generatedComplexVorticityState_supportLift_transverse
    (physicalModes symbolicModes : Finset IntegerWavevector)
    (supportSubset : physicalModes ⊆ symbolicModes)
    (zeroNotMem : (0 : IntegerWavevector) ∉ symbolicModes)
    (negClosed :
      ∀ wave, wave ∈ symbolicModes → waveNeg wave ∈ symbolicModes)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ physicalModes → state wave = 0)
    (transverse :
      ∀ wave ∈ physicalModes,
        complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state)
    (wave : IntegerWavevector) :
    complexWavevector wave ⬝ᵥ
        generatedComplexVorticityState
          (rawSourceOfFiniteVorticityState symbolicModes state)
          (generatedSupport
            (rawSourceOfFiniteVorticityState symbolicModes state)) wave =
      0 := by
  rw [
    generatedComplexVorticityState_rawSourceOfFinitePhysicalState_supportLift
      physicalModes symbolicModes supportSubset zeroNotMem negClosed state
      supported transverse reality]
  by_cases physicalMem : wave ∈ physicalModes
  · exact transverse wave physicalMem
  · rw [supported wave physicalMem]
    simp

/-- The support-lifted compiler retains the same global Fourier-reality law. -/
theorem generatedComplexVorticityState_supportLift_reality
    (physicalModes symbolicModes : Finset IntegerWavevector)
    (supportSubset : physicalModes ⊆ symbolicModes)
    (zeroNotMem : (0 : IntegerWavevector) ∉ symbolicModes)
    (negClosed :
      ∀ wave, wave ∈ symbolicModes → waveNeg wave ∈ symbolicModes)
    (state : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ physicalModes → state wave = 0)
    (transverse :
      ∀ wave ∈ physicalModes,
        complexWavevector wave ⬝ᵥ state wave = 0)
    (reality : FiniteStateFourierReality state) :
    FiniteStateFourierReality
      (generatedComplexVorticityState
        (rawSourceOfFiniteVorticityState symbolicModes state)
        (generatedSupport
          (rawSourceOfFiniteVorticityState symbolicModes state))) := by
  rw [
    generatedComplexVorticityState_rawSourceOfFinitePhysicalState_supportLift
      physicalModes symbolicModes supportSubset zeroNotMem negClosed state
      supported transverse reality]
  exact reality

/-! ## Actual raw-source specialization -/

/--
For an actual raw source, every physical law needed by the support lift is
generated by that source.  The only new compatibility datum is inclusion of
its concrete generated support in the larger symbolic inventory.
-/
theorem rawSourceOfGeneratedPhysicalState_supportLift_generatedState
    (physicalSource : RawVorticityFourierSource)
    (symbolicModes : Finset IntegerWavevector)
    (supportSubset :
      generatedSupport physicalSource ⊆ symbolicModes)
    (zeroNotMem : (0 : IntegerWavevector) ∉ symbolicModes)
    (negClosed :
      ∀ wave, wave ∈ symbolicModes → waveNeg wave ∈ symbolicModes) :
    generatedComplexVorticityState
        (rawSourceOfFiniteVorticityState symbolicModes
          (generatedComplexVorticityState physicalSource
            (generatedSupport physicalSource)))
        (generatedSupport
          (rawSourceOfFiniteVorticityState symbolicModes
            (generatedComplexVorticityState physicalSource
              (generatedSupport physicalSource)))) =
      generatedComplexVorticityState physicalSource
        (generatedSupport physicalSource) := by
  let state :=
    generatedComplexVorticityState physicalSource
      (generatedSupport physicalSource)
  have supported :
      ∀ wave,
        wave ∉ generatedSupport physicalSource →
          state wave = 0 := by
    intro wave waveNotMem
    simp [state, waveNotMem]
  have transverse :
      ∀ wave ∈ generatedSupport physicalSource,
        complexWavevector wave ⬝ᵥ state wave = 0 := by
    intro wave waveMem
    simp only [state, generatedComplexVorticityState_apply,
      if_pos waveMem]
    exact generatedVorticityCoefficient_transverse
      physicalSource wave
  have reality : FiniteStateFourierReality state := by
    apply finiteStateFourierReality_of_reflection_fixed
      (fun {wave} waveMem =>
        generatedSupport_waveNeg_mem physicalSource waveMem)
      supported
    exact
      complexFourierRealityReflection_generatedSourceInitial
        physicalSource
  exact
    generatedComplexVorticityState_rawSourceOfFinitePhysicalState_supportLift
      (generatedSupport physicalSource) symbolicModes supportSubset
      zeroNotMem negClosed state supported transverse reality

private theorem generatedComplexVorticityState_fullSupport_apply
    (source : RawVorticityFourierSource)
    (wave : IntegerWavevector) :
    generatedComplexVorticityState source
        (generatedSupport source) wave =
      generatedVorticityCoefficient source wave := by
  by_cases waveMem : wave ∈ generatedSupport source
  · simp [waveMem]
  · rw [generatedComplexVorticityState_apply,
      if_neg waveMem,
      generatedVorticityCoefficient_eq_zero_of_not_mem
        source waveMem]

/--
The flattened generated coefficient carrier is also exactly invariant under
the same source-owned support lift.
-/
theorem generatedCoefficientCarrier_rawSourceOfGeneratedPhysicalState_supportLift
    (physicalSource : RawVorticityFourierSource)
    (symbolicModes : Finset IntegerWavevector)
    (supportSubset :
      generatedSupport physicalSource ⊆ symbolicModes)
    (zeroNotMem : (0 : IntegerWavevector) ∉ symbolicModes)
    (negClosed :
      ∀ wave, wave ∈ symbolicModes → waveNeg wave ∈ symbolicModes) :
    generatedCoefficientCarrier
        (rawSourceOfFiniteVorticityState symbolicModes
          (generatedComplexVorticityState physicalSource
            (generatedSupport physicalSource))) =
      generatedCoefficientCarrier physicalSource := by
  have wholeStateEquality :=
    rawSourceOfGeneratedPhysicalState_supportLift_generatedState
      physicalSource symbolicModes supportSubset zeroNotMem negClosed
  apply Finsupp.ext
  intro index
  have coordinateEquality :=
    congrArg
      (fun state : ComplexVorticityHilbertState =>
        state index.1 index.2)
      wholeStateEquality
  simpa only [generatedCoefficientCarrier_apply] using
    (show
      generatedVorticityCoefficient
          (rawSourceOfFiniteVorticityState symbolicModes
            (generatedComplexVorticityState physicalSource
              (generatedSupport physicalSource))) index.1 index.2 =
        generatedVorticityCoefficient physicalSource
          index.1 index.2 by
      simpa only [
        generatedComplexVorticityState_fullSupport_apply]
        using coordinateEquality)

end

end ThreeDimensionalVorticityCoefficientFinitePhysicalStateSupportLift
end NavierStokes
end SaturationMonoid
