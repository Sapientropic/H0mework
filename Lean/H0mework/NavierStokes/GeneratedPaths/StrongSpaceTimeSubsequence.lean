import H0mework.NavierStokes.GeneratedPaths.StrongSpaceTimeCompactness

/-!
# Strong generated-path subsequences and fixed Fourier rows

This module turns whole-carrier compact closure into the sequential limit
interface needed by later Navier--Stokes consumers.  Every sequence of actual
source-generated critical scale paths has one strictly monotone subsequence
which converges strongly in

`L²([0,T]; ℓ²(ℤ³; ℂ³))`.

The limit remains in the closure of the actual generated family.  The same
subsequence converges strongly in `L²([0,T]; ℂ³)` after evaluation at every
fixed Fourier wave.  Thus a fixed-row Duhamel or nonlinear consumer can use
the common whole-carrier limit directly; no row-dependent diagonal
subsequence is introduced.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence

open scoped Topology

open Set
open Filter
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedPathCriticalAbsorption
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness

noncomputable section

abbrev FixedWaveSpaceTimeState (requestedTime : ℝ) :=
  ↥(MeasureTheory.Lp ComplexCoordinateVector 2
    (commonTimeMeasure requestedTime))

/-- Evaluation at one Fourier wave, lifted to the common time `L²` carrier. -/
def fixedWaveSpaceTimeRestriction
    (requestedTime : ℝ)
    (wave : IntegerWavevector) :
    SpaceTimeState requestedTime →L[ℂ]
      FixedWaveSpaceTimeState requestedTime :=
  (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).compLpL 2 (commonTimeMeasure requestedTime)

/--
The lifted fixed-wave restriction is the actual Fourier coefficient almost
everywhere in time, rather than an unrelated finite-dimensional readout.
-/
theorem fixedWaveSpaceTimeRestriction_coeFn
    (requestedTime : ℝ)
    (wave : IntegerWavevector)
    (state : SpaceTimeState requestedTime) :
    ∀ᵐ time ∂(commonTimeMeasure requestedTime),
      fixedWaveSpaceTimeRestriction requestedTime wave state time =
        state time wave := by
  filter_upwards [
    (lp.evalCLM ℂ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave).coeFn_compLpL state] with time timeRestriction
  change
    fixedWaveSpaceTimeRestriction requestedTime wave state time =
      state time wave
  rw [show
    fixedWaveSpaceTimeRestriction requestedTime wave state time =
      (lp.evalCLM ℂ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 wave) (state time) from timeRestriction]
  rfl

/--
Every sequence of actual generated critical paths admits one common strictly
monotone subsequence with:

* a limit in the closure of the generated whole-carrier family;
* strong whole-carrier `L²` convergence; and
* strong time-`L²` convergence of every fixed Fourier coefficient along the
  same subsequence.

This is the sequential interface for a later fixed-row Duhamel limit.
-/
theorem generatedCriticalSpaceTimePath_strong_subsequence_with_fixed_wave_rows
    {ν : Viscosity}
    {θ requestedTime : ℝ}
    (θLtOne : θ < 1)
    (requestedTimePos : 0 < requestedTime)
    (paths : ℕ → GeneratedCriticalScalePath ν θ) :
    ∃ limit : SpaceTimeState requestedTime,
      limit ∈
          closure
            (generatedCriticalSpaceTimePathFamily
              (ν := ν) θLtOne requestedTimePos) ∧
      ∃ subsequence : ℕ → ℕ,
        StrictMono subsequence ∧
        Tendsto
            (fun index =>
              generatedCriticalSpaceTimePath
                θLtOne requestedTimePos
                (paths (subsequence index)))
            atTop
            (𝓝 limit) ∧
        Tendsto
            (fun index =>
              ‖generatedCriticalSpaceTimePath
                    θLtOne requestedTimePos
                    (paths (subsequence index)) -
                  limit‖)
            atTop
            (𝓝 0) ∧
        (∀ wave : IntegerWavevector,
          Tendsto
              (fun index =>
                fixedWaveSpaceTimeRestriction requestedTime wave
                  (generatedCriticalSpaceTimePath
                    θLtOne requestedTimePos
                    (paths (subsequence index))))
              atTop
              (𝓝
                (fixedWaveSpaceTimeRestriction requestedTime wave
                  limit))) ∧
        (∀ wave : IntegerWavevector,
          Tendsto
              (fun index =>
                ‖fixedWaveSpaceTimeRestriction requestedTime wave
                      (generatedCriticalSpaceTimePath
                        θLtOne requestedTimePos
                        (paths (subsequence index))) -
                    fixedWaveSpaceTimeRestriction requestedTime wave
                      limit‖)
              atTop
              (𝓝 0)) := by
  let family : Set (SpaceTimeState requestedTime) :=
    generatedCriticalSpaceTimePathFamily
      (ν := ν) θLtOne requestedTimePos
  let sequence : ℕ → SpaceTimeState requestedTime :=
    fun index =>
      generatedCriticalSpaceTimePath
        θLtOne requestedTimePos (paths index)
  have sequenceMem (index : ℕ) :
      sequence index ∈ closure family := by
    apply subset_closure
    exact ⟨paths index, rfl⟩
  obtain ⟨limit, limitMem, subsequence, subsequenceMono,
      subsequenceTendsto⟩ :=
    (generatedCriticalSpaceTimePathFamily_isCompact_closure
      (ν := ν) θLtOne requestedTimePos).tendsto_subseq sequenceMem
  have wholeTendsto :
      Tendsto
          (fun index =>
            generatedCriticalSpaceTimePath
              θLtOne requestedTimePos
              (paths (subsequence index)))
          atTop
          (𝓝 limit) := by
    simpa [sequence, Function.comp_def] using subsequenceTendsto
  have wholeStrong :
      Tendsto
          (fun index =>
            ‖generatedCriticalSpaceTimePath
                  θLtOne requestedTimePos
                  (paths (subsequence index)) -
                limit‖)
          atTop
          (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp wholeTendsto
  have fixedWaveTendsto (wave : IntegerWavevector) :
      Tendsto
          (fun index =>
            fixedWaveSpaceTimeRestriction requestedTime wave
              (generatedCriticalSpaceTimePath
                θLtOne requestedTimePos
                (paths (subsequence index))))
          atTop
          (𝓝
            (fixedWaveSpaceTimeRestriction requestedTime wave
              limit)) := by
    exact
      ((fixedWaveSpaceTimeRestriction requestedTime wave).continuous.tendsto
        limit).comp wholeTendsto
  have fixedWaveStrong (wave : IntegerWavevector) :
      Tendsto
          (fun index =>
            ‖fixedWaveSpaceTimeRestriction requestedTime wave
                  (generatedCriticalSpaceTimePath
                    θLtOne requestedTimePos
                    (paths (subsequence index))) -
                fixedWaveSpaceTimeRestriction requestedTime wave
                  limit‖)
          atTop
          (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (fixedWaveTendsto wave)
  exact
    ⟨limit, by simpa [family] using limitMem,
      subsequence, subsequenceMono, wholeTendsto, wholeStrong,
      fixedWaveTendsto, fixedWaveStrong⟩

end

end ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeSubsequence
end NavierStokes
end SaturationMonoid
