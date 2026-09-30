import H0mework.NavierStokes.Crossing.FiniteCore
import H0mework.NavierStokes.Restart.HalfCriticalComponentGluing

/-!
# Source-native half-critical components of an actual whole crossing

The first canonical finite core of an actual whole half-critical crossing is
still above the fixed threshold.  The no-parameter component producer now
acts on that exact core, not on an alternate target state.  Because all
components retain the core's finite support, transversality, and Fourier
reality, each occurrence recompiles exactly to primitive
`RawVorticityFourierSource` data on the same source-generated inventory.

Thus one actual whole crossing generates, before quotienting occurrences:

```text
whole crossing state
  = sum (compiled finite half-critical component sources)
      + retained whole tail,
```

while the ordered cross nonlinear residual remains the responsibility
generated in the component-gluing carrier.  This module does not evolve the
components as independent Navier--Stokes solutions and does not identify any
finite component endpoint with the actual whole update.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteComponentSources

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFinitePhysicalStateRestart
open
  ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeKineticDifferenceCancellation
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCumulativeCriticalDissipation
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteCore
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing

noncomputable section

/-- Ordered half-critical occurrences generated from the exact finite core of
the actual whole crossing. -/
noncomputable def wholeRestartCrossingFiniteComponents
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    List ComplexVorticityHilbertState :=
  canonicalHalfCriticalComponents ν
    (wholeRestartCrossingFiniteCoreState initial index crossed)

/-- Primitive finite source attached to one canonical component occurrence.
Every occurrence uses the source-generated finite-core inventory. -/
noncomputable def wholeRestartCrossingFiniteComponentSource
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    RawVorticityFourierSource :=
  rawSourceOfFiniteVorticityState
    (wholeRestartCrossingFiniteCoreModes initial index crossed)
    (canonicalHalfCriticalComponent ν
      (wholeRestartCrossingFiniteCoreState initial index crossed))

/-- Ordered primitive-source occurrences.  Repetition is deliberate: each
occurrence remains independently addressable before any coefficient sum. -/
noncomputable def wholeRestartCrossingFiniteComponentSources
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    List RawVorticityFourierSource :=
  List.replicate
    (canonicalHalfCriticalComponentCount ν
      (wholeRestartCrossingFiniteCoreState initial index crossed))
    (wholeRestartCrossingFiniteComponentSource initial index crossed)

/-- The generated component state remains sharply supported on the same
finite-core inventory. -/
theorem wholeRestartCrossingFiniteComponent_supported
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    ∀ wave,
      wave ∉ wholeRestartCrossingFiniteCoreModes initial index crossed →
        canonicalHalfCriticalComponent ν
            (wholeRestartCrossingFiniteCoreState initial index crossed) wave =
          0 := by
  intro wave waveNotMem
  have coreZero :
      wholeRestartCrossingFiniteCoreState initial index crossed wave = 0 :=
    wholeRestartInitialState_supported
      (run initial index).contact
      (wholeRestartCrossingFiniteCoreRadius initial index crossed)
      wave waveNotMem
  change
    (canonicalHalfCriticalComponentCount ν
        (wholeRestartCrossingFiniteCoreState initial index crossed) : ℝ)⁻¹ •
        wholeRestartCrossingFiniteCoreState initial index crossed wave =
      0
  rw [coreZero]
  simp

/-- The generated component inherits whole-row transversality from the actual
crossing contact through the canonical sharp core. -/
theorem wholeRestartCrossingFiniteComponent_transverse
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    WholeStateTransverse
      (canonicalHalfCriticalComponent ν
        (wholeRestartCrossingFiniteCoreState initial index crossed)) := by
  exact wholeStateTransverse_real_smul _ _
    (wholeStateTransverse_sharpSupportProjection
      (wholeRestartCrossingFiniteCoreModes initial index crossed)
      (run initial index).contact.physicalState
      (run initial index).contact.transverse)

/-- Real amplitude splitting preserves the exact Fourier-reality law. -/
theorem finiteStateFourierReality_real_smul
    (scale : ℝ)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    FiniteStateFourierReality (scale • state) := by
  intro wave
  change scale • state (waveNeg wave) =
    vectorConj (scale • state wave)
  rw [reality wave]
  funext coordinate
  simp [vectorConj]

/-- The generated component inherits Fourier reality from the same sharp
finite core. -/
theorem wholeRestartCrossingFiniteComponent_reality
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    FiniteStateFourierReality
      (canonicalHalfCriticalComponent ν
        (wholeRestartCrossingFiniteCoreState initial index crossed)) := by
  exact finiteStateFourierReality_real_smul _ _
    (wholeRestartInitialState_reality
      (run initial index).contact
      (wholeRestartCrossingFiniteCoreRadius initial index crossed))

/-- Primitive support closure recovers exactly the finite-core inventory for
every canonical component source. -/
theorem wholeRestartCrossingFiniteComponentSource_generatedSupport
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    generatedSupport
        (wholeRestartCrossingFiniteComponentSource initial index crossed) =
      wholeRestartCrossingFiniteCoreModes initial index crossed := by
  exact rawSourceOfFiniteVorticityState_generatedSupport
    (wholeRestartCrossingFiniteCoreModes initial index crossed)
    (zero_not_mem_puncturedIntegerWaveFrequencyCube
      (wholeRestartCrossingFiniteCoreRadius initial index crossed))
    (fun _wave waveMem =>
      puncturedIntegerWaveFrequencyCube_waveNeg_mem
        (wholeRestartCrossingFiniteCoreRadius initial index crossed)
        waveMem)
    (canonicalHalfCriticalComponent ν
      (wholeRestartCrossingFiniteCoreState initial index crossed))

/-- The complete primitive compiler reconstructs every generated component
exactly on the whole Hilbert carrier. -/
theorem generatedComplexVorticityState_crossingFiniteComponentSource
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    generatedComplexVorticityState
        (wholeRestartCrossingFiniteComponentSource initial index crossed)
        (generatedSupport
          (wholeRestartCrossingFiniteComponentSource initial index crossed)) =
      canonicalHalfCriticalComponent ν
        (wholeRestartCrossingFiniteCoreState initial index crossed) := by
  exact generatedComplexVorticityState_rawSourceOfFinitePhysicalState
    (wholeRestartCrossingFiniteCoreModes initial index crossed)
    (zero_not_mem_puncturedIntegerWaveFrequencyCube
      (wholeRestartCrossingFiniteCoreRadius initial index crossed))
    (fun _wave waveMem =>
      puncturedIntegerWaveFrequencyCube_waveNeg_mem
        (wholeRestartCrossingFiniteCoreRadius initial index crossed)
        waveMem)
    (canonicalHalfCriticalComponent ν
      (wholeRestartCrossingFiniteCoreState initial index crossed))
    (wholeRestartCrossingFiniteComponent_supported initial index crossed)
    (fun wave _waveMem =>
      wholeRestartCrossingFiniteComponent_transverse
        initial index crossed wave)
    (wholeRestartCrossingFiniteComponent_reality initial index crossed)

/-- Every generated primitive source occurrence compiles to the corresponding
ordered half-critical component occurrence. -/
theorem wholeRestartCrossingFiniteComponentSources_map_compiled
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (wholeRestartCrossingFiniteComponentSources initial index crossed).map
        (fun source =>
          generatedComplexVorticityState source (generatedSupport source)) =
      wholeRestartCrossingFiniteComponents initial index crossed := by
  simp [wholeRestartCrossingFiniteComponentSources,
    wholeRestartCrossingFiniteComponents,
    canonicalHalfCriticalComponents,
    generatedComplexVorticityState_crossingFiniteComponentSource]

/-- The compiled primitive component occurrences reconstruct the exact finite
core, with no caller-supplied coefficient or component count. -/
theorem wholeRestartCrossingFiniteComponentSources_sum_compiled
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    ((wholeRestartCrossingFiniteComponentSources initial index crossed).map
        fun source =>
          generatedComplexVorticityState source
            (generatedSupport source)).sum =
      wholeRestartCrossingFiniteCoreState initial index crossed := by
  rw [wholeRestartCrossingFiniteComponentSources_map_compiled]
  exact canonicalHalfCriticalComponents_sum _ _

/-- Each compiled primitive occurrence is strictly half-critical. -/
theorem wholeRestartCrossingFiniteComponentSources_forall_halfCritical
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index)
    (source : RawVorticityFourierSource)
    (sourceMem :
      source ∈
        wholeRestartCrossingFiniteComponentSources initial index crossed) :
    criticalEnstrophyLatticeConstant *
        wholeVorticityEuclideanMass
          (generatedComplexVorticityState source
            (generatedSupport source)) <
      (1 / 2 : ℝ) * ν.coeff ^ 2 * (2 * Real.pi) ^ 2 := by
  have sourceEq :
      source =
        wholeRestartCrossingFiniteComponentSource initial index crossed := by
    exact (List.mem_replicate.mp sourceMem).2
  subst source
  rw [generatedComplexVorticityState_crossingFiniteComponentSource]
  exact canonicalHalfCriticalComponent_strictly_halfCritical _ _

/-- The original actual whole crossing state is exactly the sum of compiled
finite half-critical source occurrences plus the retained whole tail. -/
theorem wholeRestartCrossingPhysicalState_eq_componentSources_add_tail
    {ν : Viscosity}
    (initial : GeneratedWholeRestartCurrent ν)
    (index : ℕ)
    (crossed : wholeRestartHalfCriticalCrossed initial index) :
    (run initial index).contact.physicalState =
      ((wholeRestartCrossingFiniteComponentSources initial index crossed).map
        fun source =>
          generatedComplexVorticityState source
            (generatedSupport source)).sum +
        wholeRestartCrossingFiniteTail initial index crossed := by
  rw [wholeRestartCrossingFiniteComponentSources_sum_compiled]
  exact wholeRestartCrossingPhysicalState_eq_core_add_tail
    initial index crossed

end

end
    ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingFiniteComponentSources
end NavierStokes
end SaturationMonoid
