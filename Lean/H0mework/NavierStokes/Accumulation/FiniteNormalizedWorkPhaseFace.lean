import H0mework.NavierStokes.Accumulation.ActualFourierConeAdvance
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# General-current normalized-work phase face

This module works over an arbitrary finite Fourier carrier, viscosity,
and actual Galerkin state.  No fixed source coefficients, Taylor table, future
recurrence, contact branch, or summability witness enters the definitions.
-/

set_option autoImplicit false

open scoped BigOperators Matrix Topology

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkPhaseFace

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance

noncomputable section

/-! ## State-parametric finite normalized work -/

/-- Complete finite Galerkin work at an arbitrary actual state. -/
def finiteGeneratorRealWork
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState) : Real :=
  ∑ wave ∈ modes,
    complexCoordinateRealInner (state wave)
      (finiteStateVorticityGenerator modes viscosity state wave)

/-- Strictly positive mass coordinate; the added unit removes the zero-state
singularity without adding any future or target information. -/
def finiteAugmentedCoefficientMass
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : Real :=
  finiteStateVorticityCoefficientEnstrophy modes state + 1

theorem finiteAugmentedCoefficientMass_pos
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 < finiteAugmentedCoefficientMass modes state := by
  have massNonneg :
      0 ≤ finiteStateVorticityCoefficientEnstrophy modes state := by
    unfold finiteStateVorticityCoefficientEnstrophy
    exact Finset.sum_nonneg fun wave _ =>
      complexCoordinateAmplitudeSq_nonneg (state wave)
  unfold finiteAugmentedCoefficientMass
  linarith

/-- The `5/4` normalized complete work used by the current phase-rich clock
frontier, now defined on every finite actual state. -/
def finiteNormalizedGeneratorWork
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState) : Real :=
  finiteGeneratorRealWork modes viscosity state /
    finiteAugmentedCoefficientMass modes state ^ (5 / 4 : Real)

theorem finiteCoefficientMass_contDiff
    (modes : Finset IntegerWavevector) :
    ContDiff Real 1
      (finiteStateVorticityCoefficientEnstrophy modes) := by
  unfold finiteStateVorticityCoefficientEnstrophy
    complexCoordinateAmplitudeSq
  apply ContDiff.sum
  intro wave waveMem
  apply ContDiff.sum
  intro coordinate coordinateMem
  have row : ContDiff Real 1
      (fun state : ComplexVorticityHilbertState =>
        state wave coordinate) :=
    complexVorticityCoordinateEvaluation_contDiff wave coordinate
  have realPart : ContDiff Real 1
      (fun state : ComplexVorticityHilbertState =>
        (state wave coordinate).re) :=
    Complex.reCLM.contDiff.comp row
  have imaginaryPart : ContDiff Real 1
      (fun state : ComplexVorticityHilbertState =>
        (state wave coordinate).im) :=
    Complex.imCLM.contDiff.comp row
  simpa [Complex.normSq_apply] using
    realPart.mul realPart |>.add (imaginaryPart.mul imaginaryPart)

theorem finiteGeneratorRealWork_contDiff
    (modes : Finset IntegerWavevector)
    (viscosity : Real) :
    ContDiff Real 1 (finiteGeneratorRealWork modes viscosity) := by
  unfold finiteGeneratorRealWork complexCoordinateRealInner
  apply ContDiff.sum
  intro wave waveMem
  apply ContDiff.sum
  intro coordinate coordinateMem
  have stateRow : ContDiff Real 1
      (fun state : ComplexVorticityHilbertState =>
        state wave coordinate) :=
    complexVorticityCoordinateEvaluation_contDiff wave coordinate
  have generatorRow : ContDiff Real 1
      (fun state : ComplexVorticityHilbertState =>
        finiteStateVorticityGenerator modes viscosity state wave coordinate) :=
    (complexVorticityCoordinateEvaluation_contDiff wave coordinate).comp
      (finiteStateVorticityGenerator_contDiff modes viscosity)
  have stateRe := Complex.reCLM.contDiff.comp stateRow
  have stateIm := Complex.imCLM.contDiff.comp stateRow
  have generatorRe := Complex.reCLM.contDiff.comp generatorRow
  have generatorIm := Complex.imCLM.contDiff.comp generatorRow
  exact (stateRe.mul generatorRe).add (stateIm.mul generatorIm)

theorem finiteNormalizedGeneratorWork_contDiff
    (modes : Finset IntegerWavevector)
    (viscosity : Real) :
    ContDiff Real 1 (finiteNormalizedGeneratorWork modes viscosity) := by
  have massSmooth : ContDiff Real 1
      (finiteAugmentedCoefficientMass modes) :=
    (finiteCoefficientMass_contDiff modes).add contDiff_const
  have massPowerSmooth : ContDiff Real 1
      (fun state : ComplexVorticityHilbertState =>
        finiteAugmentedCoefficientMass modes state ^ (5 / 4 : Real)) :=
    massSmooth.rpow_const_of_ne fun state =>
      (finiteAugmentedCoefficientMass_pos modes state).ne'
  exact (finiteGeneratorRealWork_contDiff modes viscosity).div
    massPowerSmooth fun state =>
      (Real.rpow_pos_of_pos
        (finiteAugmentedCoefficientMass_pos modes state) _).ne'

/-- Directional derivative selected by the actual finite NS vector field at
the same state.  The direction is computed internally from `state`. -/
def finiteNormalizedWorkDirectionalDerivative
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState) : Real :=
  (fderiv Real (finiteNormalizedGeneratorWork modes viscosity) state)
    (finiteStateVorticityGenerator modes viscosity state)

theorem finiteNormalizedWorkDirectionalDerivative_continuous
    (modes : Finset IntegerWavevector)
    (viscosity : Real) :
    Continuous
      (finiteNormalizedWorkDirectionalDerivative modes viscosity) := by
  let normalized := finiteNormalizedGeneratorWork modes viscosity
  let generator := finiteStateVorticityGenerator modes viscosity
  have bundledDerivative : Continuous
      (fun pair : ComplexVorticityHilbertState ×
          ComplexVorticityHilbertState =>
        (fderiv Real normalized pair.1) pair.2) :=
    (finiteNormalizedGeneratorWork_contDiff modes viscosity)
      |>.continuous_fderiv_apply one_ne_zero
  have stateAndDirection : Continuous
      (fun state : ComplexVorticityHilbertState =>
        (state, generator state)) :=
    continuous_id.prodMk
      (finiteStateVorticityGenerator_contDiff modes viscosity).continuous
  exact bundledDerivative.comp stateAndDirection

/-- Every actual finite Galerkin update differentiates the normalized work
by the state-owned directional derivative above. -/
theorem finiteNormalizedGeneratorWork_hasDerivAt_of_actual
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (trajectory : Real → ComplexVorticityHilbertState)
    (time : Real)
    (actual : HasDerivAt trajectory
      (finiteStateVorticityGenerator modes viscosity (trajectory time))
      time) :
    HasDerivAt
      (fun moment =>
        finiteNormalizedGeneratorWork modes viscosity (trajectory moment))
      (finiteNormalizedWorkDirectionalDerivative
        modes viscosity (trajectory time))
      time := by
  have normalizedDerivative :=
    (finiteNormalizedGeneratorWork_contDiff modes viscosity)
      |>.differentiable (by norm_num) (trajectory time)
      |>.hasFDerivAt
  exact normalizedDerivative.comp_hasDerivAt time actual

/-- Algebraic quotient-rule readout when the finite generator work itself
has a named derivative along an actual trajectory. -/
def finiteNormalizedWorkRawDerivative
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : ComplexVorticityHilbertState)
    (workDerivative : Real) : Real :=
  let mass := finiteAugmentedCoefficientMass modes state
  let work := finiteGeneratorRealWork modes viscosity state
  let massPower := mass ^ (5 / 4 : Real)
  let massPowerDerivative :=
    (2 * work) * (5 / 4 : Real) * mass ^ (5 / 4 - 1 : Real)
  (workDerivative * massPower - work * massPowerDerivative) /
    massPower ^ 2

theorem finiteNormalizedWorkDirectionalDerivative_eq_raw
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (trajectory : Real → ComplexVorticityHilbertState)
    (time workDerivative : Real)
    (actual : HasDerivAt trajectory
      (finiteStateVorticityGenerator modes viscosity (trajectory time))
      time)
    (workHasDerivative : HasDerivAt
      (fun moment => finiteGeneratorRealWork modes viscosity
        (trajectory moment)) workDerivative time) :
    finiteNormalizedWorkDirectionalDerivative
        modes viscosity (trajectory time) =
      finiteNormalizedWorkRawDerivative
        modes viscosity (trajectory time) workDerivative := by
  have massDerivative :=
    finiteStateVorticityCoefficientEnstrophy_hasDerivAt
      modes trajectory time
      (finiteStateVorticityGenerator modes viscosity (trajectory time))
      actual
  have augmentedMassDerivative : HasDerivAt
      (fun moment => finiteAugmentedCoefficientMass modes
        (trajectory moment))
      (2 * finiteGeneratorRealWork modes viscosity (trajectory time))
      time := by
    simpa only [finiteAugmentedCoefficientMass, finiteGeneratorRealWork]
      using massDerivative.add_const 1
  have massNe :
      finiteAugmentedCoefficientMass modes (trajectory time) ≠ 0 :=
    (finiteAugmentedCoefficientMass_pos modes (trajectory time)).ne'
  have massPowerDerivative :=
    augmentedMassDerivative.rpow_const (p := (5 / 4 : Real))
      (Or.inl massNe)
  have massPowerNe :
      finiteAugmentedCoefficientMass modes (trajectory time) ^
          (5 / 4 : Real) ≠ 0 :=
    (Real.rpow_pos_of_pos
      (finiteAugmentedCoefficientMass_pos modes (trajectory time)) _).ne'
  have quotientDerivative :=
    workHasDerivative.div massPowerDerivative massPowerNe
  have rawDerivative : HasDerivAt
      (fun moment => finiteNormalizedGeneratorWork modes viscosity
        (trajectory moment))
      (finiteNormalizedWorkRawDerivative
        modes viscosity (trajectory time) workDerivative)
      time := by
    refine (quotientDerivative.congr_of_eventuallyEq ?_).congr_deriv ?_
    · filter_upwards [] with moment
      rfl
    · rfl
  exact (finiteNormalizedGeneratorWork_hasDerivAt_of_actual
    modes viscosity trajectory time actual).unique rawDerivative

/-- Direct splice to the canonical finite restriction generated by an
arbitrary actual whole-restart current. -/
theorem generatedCurrentCanonicalStage_normalizedWork_hasDerivAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (radius : Nat)
    (time : Real)
    (timeMem : time ∈ Set.Icc (0 : Real)
      (wholeRestartDuration current.contact)) :
    HasDerivAt
      (fun moment =>
        finiteNormalizedGeneratorWork (wholeRestartModes radius) nu.coeff
          ((generatedWholeRestartCanonicalStage
            current.contact radius).trajectory moment))
      (finiteNormalizedWorkDirectionalDerivative
        (wholeRestartModes radius) nu.coeff
        ((generatedWholeRestartCanonicalStage
          current.contact radius).trajectory time))
      time := by
  apply finiteNormalizedGeneratorWork_hasDerivAt_of_actual
  exact ((generatedWholeRestartCanonicalStage
    current.contact radius).physical time timeMem).1

/-! ## Compact phase-cone inwardness -/

/-- A compact coefficient/phase face on one fixed finite carrier.  It stores
only current-state geometry; no trajectory, future recurrence, or payment is
part of the carrier. -/
structure CompactFinitePhaseFace
    (modes : Finset IntegerWavevector) where
  phase : FiniteFourierPhaseCone
  phase_modes : phase.modes = modes
  carrier : Set ComplexVorticityHilbertState
  carrier_compact : IsCompact carrier
  carrier_nonempty : carrier.Nonempty
  phase_holds : ∀ state ∈ carrier, phase.Holds state

/-- Pointwise strict inwardness becomes one uniform positive margin on a
compact current-state phase face. -/
theorem CompactFinitePhaseFace.exists_uniform_normalizedWork_inward_margin
    {modes : Finset IntegerWavevector}
    (face : CompactFinitePhaseFace modes)
    (viscosity : Real)
    (inward : ∀ state ∈ face.carrier,
      0 < finiteNormalizedWorkDirectionalDerivative
        modes viscosity state) :
    ∃ margin : Real, 0 < margin ∧
      ∀ state ∈ face.carrier,
        margin ≤ finiteNormalizedWorkDirectionalDerivative
          modes viscosity state := by
  exact face.carrier_compact.exists_forall_le'
    (finiteNormalizedWorkDirectionalDerivative_continuous
      modes viscosity).continuousOn inward

private theorem exists_pos_time_increase_of_hasDerivAt_pos
    (f : Real → Real)
    (derivative time : Real)
    (derivativePos : 0 < derivative)
    (hasDerivative : HasDerivAt f derivative time) :
    ∃ later : Real, time < later ∧ f time < f later := by
  have eventuallyPositiveSlope :
      ∀ᶠ step in nhdsWithin (0 : Real) (Set.Ioi 0),
        0 < step⁻¹ • (f (time + step) - f time) :=
    hasDerivative.tendsto_slope_zero_right.eventually
      (eventually_gt_nhds derivativePos)
  obtain ⟨step, slopePositive, stepPos⟩ :=
    (eventuallyPositiveSlope.and self_mem_nhdsWithin).exists
  refine ⟨time + step, by linarith, ?_⟩
  have stepInvPos : 0 < step⁻¹ := inv_pos.mpr stepPos
  have differencePos : 0 < f (time + step) - f time :=
    pos_of_mul_pos_right (by simpa [smul_eq_mul] using slopePositive)
      stepInvPos.le
  linarith

/-- At every boundary state with positive state-owned directional derivative,
any actual finite update immediately generates an interior normalized-work
state.  This is pointwise and makes no uniform-time claim. -/
theorem finiteNormalizedWork_enters_interior_of_actual_inward
    (modes : Finset IntegerWavevector)
    (viscosity threshold : Real)
    (trajectory : Real → ComplexVorticityHilbertState)
    (time : Real)
    (onBoundary :
      finiteNormalizedGeneratorWork modes viscosity (trajectory time) =
        threshold)
    (actual : HasDerivAt trajectory
      (finiteStateVorticityGenerator modes viscosity (trajectory time))
      time)
    (inward : 0 < finiteNormalizedWorkDirectionalDerivative
      modes viscosity (trajectory time)) :
    ∃ later : Real, time < later ∧
      threshold <
        finiteNormalizedGeneratorWork modes viscosity (trajectory later) := by
  obtain ⟨later, laterTime, increase⟩ :=
    exists_pos_time_increase_of_hasDerivAt_pos
      (fun moment =>
        finiteNormalizedGeneratorWork modes viscosity (trajectory moment))
      (finiteNormalizedWorkDirectionalDerivative
        modes viscosity (trajectory time))
      time inward
      (finiteNormalizedGeneratorWork_hasDerivAt_of_actual
        modes viscosity trajectory time actual)
  exact ⟨later, laterTime, by simpa [onBoundary] using increase⟩

end

end ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkPhaseFace
end NavierStokes
end SaturationMonoid
