import H0mework.NavierStokes.SourceAction.EventualTail
import H0mework.NavierStokes.MacroAction.FiniteMacroGlobal
import H0mework.NavierStokes.SourceAction.WholeVelocityFilter

set_option autoImplicit false
open scoped ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeAbsoluteEventualControl

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartGlobalPhysicalTrajectory
open NativeEventualTailControl NativeEndpointVelocityCarrier NativeFullOrderSynthesis NativeSpacetimeControl

noncomputable section

variable {nu : Viscosity}

def velocity (seed : GeneratedWholeRestartCurrent nu) : ℝ → WholeRestartVelocityEndpointState :=
  NativeFiniteMacroGlobal.globalPath (terminal seed)

theorem velocity_initial (seed : GeneratedWholeRestartCurrent nu) :
    velocity seed 0 = puncturedWholeVelocityEuclideanState seed.initialState := NativeFiniteMacroGlobal.initial _

theorem velocity_norm_le (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) :
    ‖velocity seed time‖ ≤ ‖puncturedWholeVelocityEuclideanState seed.initialState‖ := NativeFiniteMacroGlobal.norm_le _ time

def startTime (seed : GeneratedWholeRestartCurrent nu) : ℝ :=
  NativeFiniteMacroPhysical.clock (terminal seed).arrival + offset seed

theorem offset_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ offset seed := by
  have source := (elapsedTime_strictMono (terminal seed).terminal).monotone (Nat.zero_le 2)
  simpa only [offset, elapsedTime_zero] using source

theorem startTime_nonnegative (seed : GeneratedWholeRestartCurrent nu) : 0 ≤ startTime seed :=
  add_nonneg (NativeFiniteMacroPhysical.clock_nonnegative _) (offset_nonnegative seed)

theorem velocity_tail (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    velocity seed (startTime seed + time) = puncturedWholeVelocityEuclideanState ((sourceTail seed).physicalPath time) := by
  rw [velocity, startTime, add_assoc,
    NativeFiniteMacroGlobal.tail_chart (terminal seed) (offset seed + time) (add_nonneg (offset_nonnegative seed) nonnegative),
    ← sourceTail_reads_original seed time nonnegative]

def support (seed : GeneratedWholeRestartCurrent nu) : Set Spacetime := Ici (startTime seed) ×ˢ univ

def toTail (seed : GeneratedWholeRestartCurrent nu) (pair : Spacetime) : Spacetime := (pair.1 - startTime seed, pair.2)

def field (seed : GeneratedWholeRestartCurrent nu) (pair : Spacetime) : PhysicalSpace :=
  spatialField (wholeVelocity (velocity seed pair.1)) pair.2

def vorticityField (seed : GeneratedWholeRestartCurrent nu) (pair : Spacetime) : PhysicalSpace :=
  NativeGeneratedGlobalSpacetime.vorticityField (sourceTail seed) (toTail seed pair)

def correctionField (seed : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector) (pair : Spacetime) : PhysicalSpace :=
  NativeWholeVelocityFilterControl.physicalField modes (wholeVelocity (velocity seed pair.1)) pair.2

theorem velocity_reads_tail (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (later : startTime seed ≤ time) :
    wholeVelocity (velocity seed time) = wholeBiotSavartVelocityState ((sourceTail seed).physicalPath (time - startTime seed)) := by
  have actual := velocity_tail seed (time - startTime seed) (sub_nonneg.mpr later)
  rw [add_sub_cancel] at actual
  rw [actual, wholeVelocity_punctured]

theorem tail_zero (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    (sourceTail seed).physicalPath time 0 = 0 := by
  have positive : 0 < time + 1 := by linarith
  rw [← NativeGeneratedGlobalSpacetime.state_reads_original (sourceTail seed) (time + 1) positive ⟨time, nonnegative, by linarith⟩]
  exact NativeReceiptSpacetime.state_zero _ _

theorem tail_transverse (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (nonnegative : 0 ≤ time) :
    WholeStateTransverse ((sourceTail seed).physicalPath time) := by
  have positive : 0 < time + 1 := by linarith
  rw [← NativeGeneratedGlobalSpacetime.state_reads_original (sourceTail seed) (time + 1) positive ⟨time, nonnegative, by linarith⟩]
  exact NativeReceiptSpacetime.state_transverse _ _

theorem vorticity_reads_actual_velocity (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (later : startTime seed ≤ time) (wave : IntegerWavevector) :
    fourierCurlCoefficient wave (wholeVelocity (velocity seed time) wave) =
      (sourceTail seed).physicalPath (time - startTime seed) wave := by
  rw [velocity_reads_tail seed time later]
  change fourierCurlCoefficient wave (biotSavartVelocityCoefficient wave ((sourceTail seed).physicalPath (time - startTime seed) wave)) = _
  by_cases nonzero : wave ≠ 0
  · exact fourierCurlCoefficient_biotSavartVelocityCoefficient_of_transverse wave _ nonzero
      (tail_transverse seed _ (sub_nonneg.mpr later) wave)
  · have atZero : wave = 0 := not_ne_iff.mp nonzero
    subst wave
    rw [tail_zero seed _ (sub_nonneg.mpr later)]
    simp [fourierCurlCoefficient]

theorem field_reads_tail (seed : GeneratedWholeRestartCurrent nu) (pair : Spacetime) (inside : pair ∈ support seed) :
    field seed pair = NativeGeneratedGlobalSpacetime.field (sourceTail seed) (toTail seed pair) := by
  unfold field NativeGeneratedGlobalSpacetime.field toTail
  rw [velocity_reads_tail seed pair.1 inside.1]

theorem correction_reads_tail (seed : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector)
    (pair : Spacetime) (inside : pair ∈ support seed) :
    correctionField seed modes pair = NativeGeneratedGlobalSpacetime.correctionField (sourceTail seed) modes (toTail seed pair) := by
  unfold correctionField NativeGeneratedGlobalSpacetime.correctionField toTail
  rw [velocity_reads_tail seed pair.1 inside.1,
    NativeWholeVelocityFilterControl.physicalField_eq_original modes _ (tail_zero seed _ (sub_nonneg.mpr inside.1))
      (tail_transverse seed _ (sub_nonneg.mpr inside.1))]

theorem source_absolute_spacetime_control (seed : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector) :
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field seed) (support seed) ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField seed) (support seed) ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField seed modes) (support seed) := by
  have source := source_tail_spacetime_control seed modes
  have coordinates : ContDiff ℝ (↑(⊤ : ℕ∞)) (toTail seed) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have mapped : MapsTo (toTail seed) (support seed) NativeGeneratedGlobalSpacetime.halfspace := by
    intro pair inside
    refine ⟨?_, trivial⟩
    change 0 ≤ pair.1 - startTime seed
    exact sub_nonneg.mpr inside.1
  exact ⟨(source.1.comp coordinates.contDiffOn mapped).congr (field_reads_tail seed),
    source.2.1.comp coordinates.contDiffOn mapped,
    (source.2.2.comp coordinates.contDiffOn mapped).congr (correction_reads_tail seed modes)⟩

theorem source_absolute_all_order_Lp (seed : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain) (contained : domain ⊆ support seed) :
    ∀ observation ∈ ({field seed, vorticityField seed, correctionField seed modes} : Set (Spacetime → PhysicalSpace)),
      ∃ budget : ℝ, 0 ≤ budget ∧
        MemLp (iteratedFDerivWithin ℝ order observation (support seed)) exponent (volume.restrict domain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order observation (support seed)) exponent (volume.restrict domain) ≤
          ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) := by
  intro observation member
  have source := source_absolute_spacetime_control seed modes
  have smooth : ContDiffOn ℝ (↑(⊤ : ℕ∞)) observation (support seed) := by
    simp only [mem_insert_iff, mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl
    · exact source.1
    · exact source.2.1
    · exact source.2.2
  exact NativeRecoveryTimeJets.spacetime_frechet_Lp_of_smooth _ _ smooth
    ((uniqueDiffOn_Ici _).prod uniqueDiffOn_univ) order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativeAbsoluteEventualControl
