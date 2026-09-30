import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import H0mework.NavierStokes.InitialData.FiniteSupportCriticalSobolev
import H0mework.NavierStokes.InitialData.FiniteSupportRealityTrajectory

/-!
# Exact enstrophy balance for finite three-dimensional vorticity Galerkin flow

This module proves the coefficient-space enstrophy balance for the complete
finite three-dimensional vorticity generator.  The first theorem is uniform
in an arbitrary finite mode set and arbitrary differentiable trajectory:

```text
d/dt (1/2 * sum_k |omega_k|^2)
  = complete nonlinear work
      - nu * (2*pi)^2 * sum_k |k|^2 |omega_k|^2.
```

The factor `(2*pi)^2` is not optional: it is already present in
`integerWaveViscousMultiplier`, while
`finiteStateVorticityEnstrophyMass` deliberately omits it.

On a negation-closed Fourier inventory, the advection part of complete
nonlinear work cancels by the source-free involution

```text
(output, first, second)
  |-> (-second, first, -output).
```

For the source-generated transverse and reality-preserving trajectory this
turns the nonlinear work into genuine vortex-stretching work and integrates
to an exact finite-time ledger.  The source theorem accepts only the raw
source and viscosity; trajectory, lifespan, support, transversality, reality,
pointwise balance, and integrated ledger are all conclusions.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance

open scoped BigOperators Matrix Topology Interval

open Set
open Matrix
open MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev

noncomputable section

/-! ## Finite coefficient enstrophy and real pairing calculus -/

/-- Full coefficient enstrophy on an arbitrary finite Fourier inventory. -/
def finiteStateVorticityCoefficientEnstrophy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes,
    complexCoordinateAmplitudeSq (state wave)

/-- The conventional half-enstrophy whose derivative is the real Hermitian
pairing with the vorticity tangent. -/
def finiteStateVorticityHalfEnstrophy
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  (1 / 2 : ℝ) *
    finiteStateVorticityCoefficientEnstrophy modes state

private theorem complexCoordinateRealInner_zero_right
    (left : ComplexCoordinateVector) :
    complexCoordinateRealInner left 0 = 0 := by
  simp [complexCoordinateRealInner]

private theorem complexCoordinateRealInner_sub_right
    (left right₁ right₂ : ComplexCoordinateVector) :
    complexCoordinateRealInner left (right₁ - right₂) =
      complexCoordinateRealInner left right₁ -
        complexCoordinateRealInner left right₂ := by
  unfold complexCoordinateRealInner
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  ring

private theorem complexCoordinateRealInner_add_right
    (left right₁ right₂ : ComplexCoordinateVector) :
    complexCoordinateRealInner left (right₁ + right₂) =
      complexCoordinateRealInner left right₁ +
        complexCoordinateRealInner left right₂ := by
  unfold complexCoordinateRealInner
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.add_apply, Complex.add_re, Complex.add_im]
  ring

private theorem complexCoordinateRealInner_sum_right
    {ι : Type*}
    (indices : Finset ι)
    (left : ComplexCoordinateVector)
    (right : ι → ComplexCoordinateVector) :
    complexCoordinateRealInner left (∑ index ∈ indices, right index) =
      ∑ index ∈ indices,
        complexCoordinateRealInner left (right index) := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
      simp [complexCoordinateRealInner_zero_right]
  | @insert index tail indexNotMem inductionHypothesis =>
      rw [Finset.sum_insert indexNotMem,
        complexCoordinateRealInner_add_right,
        inductionHypothesis,
        Finset.sum_insert indexNotMem]

private theorem complexCoordinateRealInner_real_smul_right
    (left right : ComplexCoordinateVector)
    (scalar : ℝ) :
    complexCoordinateRealInner left (scalar • right) =
      scalar * complexCoordinateRealInner left right := by
  unfold complexCoordinateRealInner
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp only [Pi.smul_apply, Complex.smul_re, Complex.smul_im]
  ring

/-- Derivative of the exact coordinate amplitude along an arbitrary
differentiable complex-vector path. -/
theorem complexCoordinateAmplitudeSq_hasDerivAt
    (path : ℝ → ComplexCoordinateVector)
    (t : ℝ)
    (tangent : ComplexCoordinateVector)
    (evolves : HasDerivAt path tangent t) :
    HasDerivAt
      (fun time => complexCoordinateAmplitudeSq (path time))
      (2 * complexCoordinateRealInner (path t) tangent) t := by
  unfold complexCoordinateAmplitudeSq
  have coordinateDerivative :
      ∀ coordinate ∈ (Finset.univ : Finset Coordinate),
        HasDerivAt
          (fun time => Complex.normSq (path time coordinate))
          (2 *
            ((path t coordinate).re * (tangent coordinate).re +
              (path t coordinate).im * (tangent coordinate).im)) t := by
    intro coordinate coordinateMem
    have coordinateEvolves :
        HasDerivAt
          (fun time => path time coordinate)
          (tangent coordinate) t := by
      have projected :=
        (ContinuousLinearMap.proj coordinate :
          ComplexCoordinateVector →L[ℝ] ℂ).hasFDerivAt
          |>.comp_hasDerivAt t evolves
      change
        HasDerivAt
          (fun time => path time coordinate)
          (tangent coordinate) t at projected
      exact projected
    have normDerivative := coordinateEvolves.norm_sq
    simpa [Complex.sq_norm, mul_comm] using normDerivative
  have summed := HasDerivAt.fun_sum coordinateDerivative
  rw [← Finset.mul_sum] at summed
  simpa [complexCoordinateRealInner] using summed

/-! ## Complete nonlinear work and the arbitrary-trajectory balance -/

/-- Complete real nonlinear work of the finite vorticity generator. -/
def finiteStateVorticityNonlinearWork
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ wave ∈ modes,
    complexCoordinateRealInner (state wave)
      (finiteStateVorticityNonlinearCoefficientAt modes state wave)

/-- Full coefficient enstrophy has derivative twice the real pairing with an
arbitrary supplied tangent. -/
theorem finiteStateVorticityCoefficientEnstrophy_hasDerivAt
    (modes : Finset IntegerWavevector)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    HasDerivAt
      (fun time =>
        finiteStateVorticityCoefficientEnstrophy modes
          (trajectory time))
      (2 * ∑ wave ∈ modes,
        complexCoordinateRealInner
          (trajectory t wave) (tangent wave)) t := by
  unfold finiteStateVorticityCoefficientEnstrophy
  have waveDerivative :
      ∀ wave ∈ modes,
        HasDerivAt
          (fun time =>
            complexCoordinateAmplitudeSq (trajectory time wave))
          (2 * complexCoordinateRealInner
            (trajectory t wave) (tangent wave)) t := by
    intro wave waveMem
    exact
      complexCoordinateAmplitudeSq_hasDerivAt
        (fun time => trajectory time wave) t (tangent wave)
        (complexVorticityTrajectoryWave_hasDerivAt
          trajectory t tangent wave evolves)
  have summed := HasDerivAt.fun_sum waveDerivative
  rw [← Finset.mul_sum] at summed
  exact summed

/-- The viscous real pairing has the exact physical `(2*pi)^2`
normalization carried by the generator. -/
theorem finiteStateVorticityViscousWork_eq
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner (state wave)
        ((ν * integerWaveViscousMultiplier wave) • state wave)) =
      ν * (2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass modes state := by
  unfold finiteStateVorticityEnstrophyMass
  simp_rw [complexCoordinateRealInner_real_smul_right,
    complexCoordinateRealInner_self,
    ← complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  unfold integerWaveViscousMultiplier
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave waveMem
  ring

/-- Pairing the actual finite generator with the current vorticity splits
exactly into complete nonlinear work minus viscous enstrophy mass. -/
theorem finiteStateVorticityGenerator_realWork
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    (∑ wave ∈ modes,
      complexCoordinateRealInner (state wave)
        (finiteStateVorticityGenerator modes ν state wave)) =
      finiteStateVorticityNonlinearWork modes state -
        ν * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes state := by
  unfold finiteStateVorticityNonlinearWork
  calc
    (∑ wave ∈ modes,
        complexCoordinateRealInner (state wave)
          (finiteStateVorticityGenerator modes ν state wave)) =
        ∑ wave ∈ modes,
          (complexCoordinateRealInner (state wave)
              (finiteStateVorticityNonlinearCoefficientAt
                modes state wave) -
            complexCoordinateRealInner (state wave)
              ((ν * integerWaveViscousMultiplier wave) •
                state wave)) := by
      apply Finset.sum_congr rfl
      intro wave waveMem
      rw [finiteStateVorticityGenerator_apply,
        if_pos waveMem,
        complexCoordinateRealInner_sub_right]
    _ =
        (∑ wave ∈ modes,
          complexCoordinateRealInner (state wave)
            (finiteStateVorticityNonlinearCoefficientAt
              modes state wave)) -
          ∑ wave ∈ modes,
            complexCoordinateRealInner (state wave)
              ((ν * integerWaveViscousMultiplier wave) •
                state wave) := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by
      rw [finiteStateVorticityViscousWork_eq]

/-- Exact pointwise half-enstrophy balance for an arbitrary differentiable
trajectory satisfying the actual finite Galerkin update.  No reality,
transversality, support, cutoff, or nonvanishing premise is used. -/
theorem finiteStateVorticityHalfEnstrophy_hasDerivAt_nonlinearWork
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          modes ν (trajectory t)) t) :
    HasDerivAt
      (fun time =>
        finiteStateVorticityHalfEnstrophy modes
          (trajectory time))
      (finiteStateVorticityNonlinearWork modes (trajectory t) -
        ν * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes (trajectory t)) t := by
  have fullDerivative :=
    finiteStateVorticityCoefficientEnstrophy_hasDerivAt
      modes trajectory t
      (finiteStateVorticityGenerator modes ν (trajectory t))
      evolves
  have halfDerivative := fullDerivative.const_mul (1 / 2 : ℝ)
  rw [finiteStateVorticityGenerator_realWork] at halfDerivative
  simpa [finiteStateVorticityHalfEnstrophy] using halfDerivative

private theorem continuousAt_finset_sum
    {ι : Type*}
    [DecidableEq ι]
    (indices : Finset ι)
    {f : ι → ℝ → ℝ}
    {t : ℝ}
    (continuous :
      ∀ index ∈ indices, ContinuousAt (f index) t) :
    ContinuousAt
      (fun time => ∑ index ∈ indices, f index time) t := by
  induction indices using Finset.induction_on with
  | empty =>
      simpa using
        (continuousAt_const :
          ContinuousAt (fun _ : ℝ => (0 : ℝ)) t)
  | @insert index tail indexNotMem inductionHypothesis =>
      simp only [Finset.sum_insert indexNotMem]
      exact
        (continuous index (by simp)).add
          (inductionHypothesis fun later laterMem =>
            continuous later (by simp [laterMem]))

private theorem complexCoordinateRealInner_continuousAt
    {left right : ℝ → ComplexCoordinateVector}
    {t : ℝ}
    (leftContinuous : ContinuousAt left t)
    (rightContinuous : ContinuousAt right t) :
    ContinuousAt
      (fun time =>
        complexCoordinateRealInner (left time) (right time)) t := by
  unfold complexCoordinateRealInner
  apply continuousAt_finset_sum
  intro coordinate coordinateMem
  have leftCoordinate :
      ContinuousAt (fun time => left time coordinate) t :=
    (continuous_apply coordinate).continuousAt.comp leftContinuous
  have rightCoordinate :
      ContinuousAt (fun time => right time coordinate) t :=
    (continuous_apply coordinate).continuousAt.comp rightContinuous
  exact
    ((Complex.continuous_re.continuousAt.comp leftCoordinate).mul
      (Complex.continuous_re.continuousAt.comp rightCoordinate)).add
      ((Complex.continuous_im.continuousAt.comp leftCoordinate).mul
        (Complex.continuous_im.continuousAt.comp rightCoordinate))

/-- Complete nonlinear work is continuous at every time where the coefficient
trajectory is differentiable. -/
theorem finiteStateVorticityNonlinearWork_continuousAt_of_hasDerivAt
    (modes : Finset IntegerWavevector)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (tangent : ComplexVorticityHilbertState)
    (evolves : HasDerivAt trajectory tangent t) :
    ContinuousAt
      (fun time =>
        finiteStateVorticityNonlinearWork modes (trajectory time)) t := by
  unfold finiteStateVorticityNonlinearWork
  apply continuousAt_finset_sum
  intro wave waveMem
  have trajectoryContinuous : ContinuousAt trajectory t :=
    evolves.continuousAt
  have rowContinuous :
      ContinuousAt (fun time => trajectory time wave) t :=
    (complexVorticityTrajectoryWave_hasDerivAt
      trajectory t tangent wave evolves).continuousAt
  have nonlinearContinuous :
      ContinuousAt
        (fun time =>
          finiteStateVorticityNonlinearCoefficientAt
            modes (trajectory time) wave) t :=
    (finiteStateVorticityNonlinearCoefficientAt_contDiff modes wave)
      |>.continuous.continuousAt.comp trajectoryContinuous
  exact
    complexCoordinateRealInner_continuousAt
      rowContinuous nonlinearContinuous

/-- Exact integrated half-enstrophy ledger for an arbitrary differentiable
trajectory satisfying the actual finite Galerkin update.  At this ambient
level the nonlinear term has not yet been reduced to stretching work. -/
theorem finiteStateVorticityHalfEnstrophy_integral_nonlinearWork
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t) :
    (∫ t in a..b,
      (finiteStateVorticityNonlinearWork modes (trajectory t) -
        ν * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass
            modes (trajectory t))) =
      finiteStateVorticityHalfEnstrophy modes (trajectory b) -
        finiteStateVorticityHalfEnstrophy modes (trajectory a) := by
  let rate : ℝ → ℝ :=
    fun t =>
      finiteStateVorticityNonlinearWork modes (trajectory t) -
        ν * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes (trajectory t)
  have rateContinuousOn :
      ContinuousOn rate (Icc a b) := by
    intro t timeMem
    have actual := evolves t timeMem
    have nonlinearContinuous :=
      finiteStateVorticityNonlinearWork_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator modes ν (trajectory t))
        actual
    have massContinuous :=
      finiteStateVorticityEnstrophyMass_continuousAt_of_hasDerivAt
        modes trajectory t
        (finiteStateVorticityGenerator modes ν (trajectory t))
        actual
    exact
      (nonlinearContinuous.sub
        (massContinuous.const_mul
          (ν * (2 * Real.pi) ^ 2))).continuousWithinAt
  have rateContinuousOnU :
      ContinuousOn rate (uIcc a b) := by
    simpa [uIcc_of_le hab] using rateContinuousOn
  have derivative :
      ∀ t ∈ uIcc a b,
        HasDerivAt
          (fun time =>
            finiteStateVorticityHalfEnstrophy modes
              (trajectory time))
          (rate t) t := by
    intro t timeMem
    apply
      finiteStateVorticityHalfEnstrophy_hasDerivAt_nonlinearWork
        modes ν trajectory t
    apply evolves t
    simpa [uIcc_of_le hab] using timeMem
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      derivative rateContinuousOnU.intervalIntegrable

/-! ## Advection cancellation and genuine stretching work -/

/-- Vortex-stretching part of one arbitrary-state ordered Fourier row. -/
def finiteStateVorticityStretchingPairContribution
    (state : ComplexVorticityHilbertState)
    (pair : StretchingPair) : ComplexCoordinateVector :=
  (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (complexWavevector pair.2 ⬝ᵥ state pair.1)) •
    finiteStateVelocityCoefficient state pair.2

/-- Vorticity-advection part of one arbitrary-state ordered Fourier row. -/
def finiteStateVorticityAdvectionPairContribution
    (state : ComplexVorticityHilbertState)
    (pair : StretchingPair) : ComplexCoordinateVector :=
  (Complex.I * (((2 * Real.pi : ℝ) : ℂ)) *
      (complexWavevector pair.2 ⬝ᵥ
        finiteStateVelocityCoefficient state pair.1)) •
    state pair.2

theorem finiteStateVorticityNonlinearPairContribution_eq
    (state : ComplexVorticityHilbertState)
    (pair : StretchingPair) :
    finiteStateVorticityNonlinearPairContribution state pair =
      finiteStateVorticityStretchingPairContribution state pair -
        finiteStateVorticityAdvectionPairContribution state pair :=
  rfl

/-- An output-indexed ordered Fourier interaction.  The finite inventory
below imposes `first + second = output`. -/
abbrev FiniteVorticityInteractionOccurrence :=
  (IntegerWavevector × IntegerWavevector) × IntegerWavevector

def finiteVorticityInteractionOutput
    (occurrence : FiniteVorticityInteractionOccurrence) :
    IntegerWavevector :=
  occurrence.1.1

def finiteVorticityInteractionFirst
    (occurrence : FiniteVorticityInteractionOccurrence) :
    IntegerWavevector :=
  occurrence.1.2

def finiteVorticityInteractionSecond
    (occurrence : FiniteVorticityInteractionOccurrence) :
    IntegerWavevector :=
  occurrence.2

/-- Complete finite interaction inventory with output incidence internal. -/
def finiteVorticityInteractionInventory
    (modes : Finset IntegerWavevector) :
    Finset FiniteVorticityInteractionOccurrence :=
  (((modes ×ˢ modes) ×ˢ modes).filter fun occurrence =>
    finiteVorticityInteractionFirst occurrence +
        finiteVorticityInteractionSecond occurrence =
      finiteVorticityInteractionOutput occurrence)

/-- Real vortex-stretching work carried by one interaction occurrence. -/
def finiteStateVorticityStretchingOccurrenceWork
    (state : ComplexVorticityHilbertState)
    (occurrence : FiniteVorticityInteractionOccurrence) : ℝ :=
  complexCoordinateRealInner
    (state (finiteVorticityInteractionOutput occurrence))
    (finiteStateVorticityStretchingPairContribution state
      (finiteVorticityInteractionFirst occurrence,
        finiteVorticityInteractionSecond occurrence))

/-- Real vorticity-advection work carried by one interaction occurrence. -/
def finiteStateVorticityAdvectionOccurrenceWork
    (state : ComplexVorticityHilbertState)
    (occurrence : FiniteVorticityInteractionOccurrence) : ℝ :=
  complexCoordinateRealInner
    (state (finiteVorticityInteractionOutput occurrence))
    (finiteStateVorticityAdvectionPairContribution state
      (finiteVorticityInteractionFirst occurrence,
        finiteVorticityInteractionSecond occurrence))

/-- Real vortex-stretching work of the complete finite interaction table. -/
def finiteStateVorticityStretchingWork
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ occurrence ∈ finiteVorticityInteractionInventory modes,
    finiteStateVorticityStretchingOccurrenceWork state occurrence

/-- Real vorticity-advection work of the complete finite interaction table. -/
def finiteStateVorticityAdvectionWork
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : ℝ :=
  ∑ occurrence ∈ finiteVorticityInteractionInventory modes,
    finiteStateVorticityAdvectionOccurrenceWork state occurrence

private theorem
    complexCoordinateRealInner_finiteStateVorticityNonlinearCoefficientAt
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    complexCoordinateRealInner (state output)
        (finiteStateVorticityNonlinearCoefficientAt
          modes state output) =
      ∑ first ∈ modes,
        ∑ second ∈ modes,
          if first + second = output then
            complexCoordinateRealInner (state output)
              (finiteStateVorticityNonlinearPairContribution
                state (first, second))
          else 0 := by
  unfold finiteStateVorticityNonlinearCoefficientAt
  rw [complexCoordinateRealInner_sum_right]
  apply Finset.sum_congr rfl
  intro first firstMem
  rw [complexCoordinateRealInner_sum_right]
  apply Finset.sum_congr rfl
  intro second secondMem
  by_cases pairSum : first + second = output
  · rw [if_pos pairSum, if_pos pairSum]
  · rw [if_neg pairSum, if_neg pairSum,
      complexCoordinateRealInner_zero_right]

/-- Complete nonlinear work is exactly the finite occurrence sum over the
same output incidence table. -/
theorem finiteStateVorticityNonlinearWork_eq_occurrenceSum
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityNonlinearWork modes state =
      ∑ occurrence ∈ finiteVorticityInteractionInventory modes,
        complexCoordinateRealInner
          (state (finiteVorticityInteractionOutput occurrence))
          (finiteStateVorticityNonlinearPairContribution state
            (finiteVorticityInteractionFirst occurrence,
              finiteVorticityInteractionSecond occurrence)) := by
  classical
  unfold finiteStateVorticityNonlinearWork
  simp_rw [
    complexCoordinateRealInner_finiteStateVorticityNonlinearCoefficientAt]
  unfold finiteVorticityInteractionInventory
  rw [Finset.sum_filter]
  simp only [Finset.sum_product]
  rfl

/-- Before advection cancellation, complete nonlinear work splits exactly
into stretching work minus advection work. -/
theorem finiteStateVorticityNonlinearWork_eq_stretching_sub_advection
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityNonlinearWork modes state =
      finiteStateVorticityStretchingWork modes state -
        finiteStateVorticityAdvectionWork modes state := by
  rw [finiteStateVorticityNonlinearWork_eq_occurrenceSum]
  unfold finiteStateVorticityStretchingWork
    finiteStateVorticityAdvectionWork
    finiteStateVorticityStretchingOccurrenceWork
    finiteStateVorticityAdvectionOccurrenceWork
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro occurrence occurrenceMem
  rw [← complexCoordinateRealInner_sub_right,
    ← finiteStateVorticityNonlinearPairContribution_eq]

/-- The advection pairing involution keeps the advecting wave and exchanges
the testing/output row with the transported row. -/
def finiteVorticityAdvectionSwap
    (occurrence : FiniteVorticityInteractionOccurrence) :
    FiniteVorticityInteractionOccurrence :=
  ((waveNeg (finiteVorticityInteractionSecond occurrence),
      finiteVorticityInteractionFirst occurrence),
    waveNeg (finiteVorticityInteractionOutput occurrence))

@[simp] theorem finiteVorticityAdvectionSwap_involutive
    (occurrence : FiniteVorticityInteractionOccurrence) :
    finiteVorticityAdvectionSwap
        (finiteVorticityAdvectionSwap occurrence) =
      occurrence := by
  rcases occurrence with ⟨⟨output, first⟩, second⟩
  simp [finiteVorticityAdvectionSwap,
    finiteVorticityInteractionOutput,
    finiteVorticityInteractionFirst,
    finiteVorticityInteractionSecond]

/-- Advection swap as an involution of the ambient interaction carrier. -/
def finiteVorticityAdvectionSwapEquiv :
    FiniteVorticityInteractionOccurrence ≃
      FiniteVorticityInteractionOccurrence where
  toFun := finiteVorticityAdvectionSwap
  invFun := finiteVorticityAdvectionSwap
  left_inv := finiteVorticityAdvectionSwap_involutive
  right_inv := finiteVorticityAdvectionSwap_involutive

@[simp] theorem finiteVorticityAdvectionSwapEquiv_apply
    (occurrence : FiniteVorticityInteractionOccurrence) :
    finiteVorticityAdvectionSwapEquiv occurrence =
      finiteVorticityAdvectionSwap occurrence :=
  rfl

/-- On a negation-closed finite inventory, the advection swap preserves the
complete output-incidence table. -/
theorem mem_finiteVorticityInteractionInventory_advectionSwap_iff
    {modes : Finset IntegerWavevector}
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (occurrence : FiniteVorticityInteractionOccurrence) :
    finiteVorticityAdvectionSwap occurrence ∈
        finiteVorticityInteractionInventory modes ↔
      occurrence ∈ finiteVorticityInteractionInventory modes := by
  rcases occurrence with ⟨⟨output, first⟩, second⟩
  unfold finiteVorticityInteractionInventory
  constructor
  · intro swappedMem
    rcases Finset.mem_filter.mp swappedMem with
      ⟨swappedProductMem, swappedIncidence⟩
    rcases Finset.mem_product.mp swappedProductMem with
      ⟨swappedPairMem, negOutputMem⟩
    rcases Finset.mem_product.mp swappedPairMem with
      ⟨negSecondMem, firstMem⟩
    have secondMem : second ∈ modes := by
      simpa using negClosed (waveNeg second) negSecondMem
    have outputMem : output ∈ modes := by
      simpa using negClosed (waveNeg output) negOutputMem
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨outputMem, firstMem⟩, secondMem⟩, ?_⟩
    funext coordinate
    have coordinateIncidence :=
      congrFun swappedIncidence coordinate
    simp [finiteVorticityAdvectionSwap,
      finiteVorticityInteractionOutput,
      finiteVorticityInteractionFirst,
      finiteVorticityInteractionSecond, waveNeg] at coordinateIncidence ⊢
    omega
  · intro occurrenceMem
    rcases Finset.mem_filter.mp occurrenceMem with
      ⟨productMem, incidence⟩
    rcases Finset.mem_product.mp productMem with
      ⟨pairMem, secondMem⟩
    rcases Finset.mem_product.mp pairMem with
      ⟨outputMem, firstMem⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨negClosed second secondMem, firstMem⟩,
        negClosed output outputMem⟩, ?_⟩
    funext coordinate
    have coordinateIncidence :=
      congrFun incidence coordinate
    simp [finiteVorticityAdvectionSwap,
      finiteVorticityInteractionOutput,
      finiteVorticityInteractionFirst,
      finiteVorticityInteractionSecond, waveNeg] at coordinateIncidence ⊢
    omega

private theorem complexCoordinateRealInner_eq_re_dot
    (left right : ComplexCoordinateVector) :
    complexCoordinateRealInner left right =
      (vectorConj left ⬝ᵥ right).re := by
  unfold complexCoordinateRealInner dotProduct
  change
    (∑ coordinate : Coordinate,
      ((left coordinate).re * (right coordinate).re +
        (left coordinate).im * (right coordinate).im)) =
      ∑ coordinate : Coordinate,
        (vectorConj left coordinate * right coordinate).re
  apply Finset.sum_congr rfl
  intro coordinate _
  simp [vectorConj]

private theorem complexWavevector_add
    (first second : IntegerWavevector) :
    complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
  funext coordinate
  simp [complexWavevector]

/-- One incidence row and its advection swap carry opposite real work.
Reality is consumed here as a state invariant; the public source theorem
below generates it along the trajectory. -/
theorem finiteStateVorticityAdvectionOccurrenceWork_swap
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state)
    (occurrence : FiniteVorticityInteractionOccurrence)
    (incidence :
      finiteVorticityInteractionFirst occurrence +
        finiteVorticityInteractionSecond occurrence =
        finiteVorticityInteractionOutput occurrence) :
    finiteStateVorticityAdvectionOccurrenceWork state
        (finiteVorticityAdvectionSwap occurrence) =
      -finiteStateVorticityAdvectionOccurrenceWork state occurrence := by
  unfold finiteStateVorticityAdvectionOccurrenceWork
  rcases occurrence with ⟨⟨output, first⟩, second⟩
  simp only [finiteVorticityInteractionOutput,
    finiteVorticityInteractionFirst,
    finiteVorticityInteractionSecond] at incidence ⊢
  have coefficientNeg :
      complexWavevector (waveNeg output) ⬝ᵥ
          finiteStateVelocityCoefficient state first =
        -(complexWavevector second ⬝ᵥ
          finiteStateVelocityCoefficient state first) := by
    rw [complexWavevector_waveNeg, neg_dotProduct,
      ← incidence, complexWavevector_add, add_dotProduct,
      finiteStateVelocityCoefficient,
      complexWavevector_dot_biotSavartVelocityCoefficient]
    simp
  have complexPairingNeg :
      vectorConj (state (waveNeg second)) ⬝ᵥ
          finiteStateVorticityAdvectionPairContribution state
            (first, waveNeg output) =
        -(vectorConj (state output) ⬝ᵥ
          finiteStateVorticityAdvectionPairContribution state
            (first, second)) := by
    unfold finiteStateVorticityAdvectionPairContribution
    rw [reality second, reality output,
      vectorConj_involutive]
    rw [coefficientNeg, dotProduct_smul, dotProduct_smul,
      dotProduct_comm (state second) (vectorConj (state output))]
    module
  rw [finiteVorticityAdvectionSwap,
    finiteVorticityInteractionOutput,
    finiteVorticityInteractionFirst,
    finiteVorticityInteractionSecond,
    complexCoordinateRealInner_eq_re_dot,
    complexCoordinateRealInner_eq_re_dot,
    complexPairingNeg]
  simp

/-- On a negation-closed inventory, the complete advection contribution is
exactly zero.  The cancellation is internal to the actual finite interaction
table; no trajectory or source premise is used. -/
theorem finiteStateVorticityAdvectionWork_eq_zero
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    finiteStateVorticityAdvectionWork modes state = 0 := by
  unfold finiteStateVorticityAdvectionWork
  apply Finset.sum_involution
    (fun occurrence _ =>
      finiteVorticityAdvectionSwap occurrence)
  · intro occurrence occurrenceMem
    have incidence :=
      (Finset.mem_filter.mp occurrenceMem).2
    rw [finiteStateVorticityAdvectionOccurrenceWork_swap
      state reality occurrence incidence]
    ring
  · intro occurrence occurrenceMem workNonzero swapFixed
    have incidence :=
      (Finset.mem_filter.mp occurrenceMem).2
    have opposite :=
      finiteStateVorticityAdvectionOccurrenceWork_swap
        state reality occurrence incidence
    rw [swapFixed] at opposite
    apply workNonzero
    linarith
  · intro occurrence occurrenceMem
    exact
      (mem_finiteVorticityInteractionInventory_advectionSwap_iff
        negClosed occurrence).2 occurrenceMem
  · intro occurrence occurrenceMem
    exact finiteVorticityAdvectionSwap_involutive occurrence

/-- For a reality-symmetric state on a negation-closed inventory, complete
nonlinear work is exactly genuine vortex-stretching work. -/
theorem finiteStateVorticityNonlinearWork_eq_stretchingWork
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality state) :
    finiteStateVorticityNonlinearWork modes state =
      finiteStateVorticityStretchingWork modes state := by
  rw [finiteStateVorticityNonlinearWork_eq_stretching_sub_advection,
    finiteStateVorticityAdvectionWork_eq_zero
      modes negClosed state reality,
    sub_zero]

/-! ## Stretching-form pointwise and integrated ledgers -/

/-- Exact pointwise enstrophy balance in genuine stretching form.  Reality
and negation closure are consumed only to identify complete nonlinear work
with stretching; the actual update remains the sole dynamical premise. -/
theorem finiteStateVorticityHalfEnstrophy_hasDerivAt_stretchingWork
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator
          modes ν (trajectory t)) t)
    (reality : FiniteStateFourierReality (trajectory t)) :
    HasDerivAt
      (fun time =>
        finiteStateVorticityHalfEnstrophy modes
          (trajectory time))
      (finiteStateVorticityStretchingWork modes (trajectory t) -
        ν * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass modes (trajectory t)) t := by
  have balance :=
    finiteStateVorticityHalfEnstrophy_hasDerivAt_nonlinearWork
      modes ν trajectory t evolves
  rw [finiteStateVorticityNonlinearWork_eq_stretchingWork
    modes negClosed (trajectory t) reality] at balance
  exact balance

/-- Exact finite-time enstrophy ledger in genuine stretching form for every
actual reality-preserving trajectory on a negation-closed inventory. -/
theorem finiteStateVorticityHalfEnstrophy_integral_stretchingWork
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (hab : a ≤ b)
    (evolves :
      ∀ t ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t)
    (reality :
      ∀ t ∈ Icc a b,
        FiniteStateFourierReality (trajectory t)) :
    (∫ t in a..b,
      (finiteStateVorticityStretchingWork modes (trajectory t) -
        ν * (2 * Real.pi) ^ 2 *
          finiteStateVorticityEnstrophyMass
            modes (trajectory t))) =
      finiteStateVorticityHalfEnstrophy modes (trajectory b) -
        finiteStateVorticityHalfEnstrophy modes (trajectory a) := by
  calc
    (∫ t in a..b,
        (finiteStateVorticityStretchingWork modes (trajectory t) -
          ν * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass
              modes (trajectory t))) =
        ∫ t in a..b,
          (finiteStateVorticityNonlinearWork modes (trajectory t) -
            ν * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass
                modes (trajectory t)) := by
          apply intervalIntegral.integral_congr
          intro t timeMem
          have intervalMem : t ∈ Icc a b := by
            simpa [uIcc_of_le hab] using timeMem
          change
            finiteStateVorticityStretchingWork modes (trajectory t) -
                  ν * (2 * Real.pi) ^ 2 *
                    finiteStateVorticityEnstrophyMass
                      modes (trajectory t) =
              finiteStateVorticityNonlinearWork modes (trajectory t) -
                  ν * (2 * Real.pi) ^ 2 *
                    finiteStateVorticityEnstrophyMass
                      modes (trajectory t)
          rw [finiteStateVorticityNonlinearWork_eq_stretchingWork
            modes negClosed (trajectory t) (reality t intervalMem)]
    _ =
        finiteStateVorticityHalfEnstrophy modes (trajectory b) -
          finiteStateVorticityHalfEnstrophy modes (trajectory a) :=
      finiteStateVorticityHalfEnstrophy_integral_nonlinearWork
        modes ν trajectory a b hab evolves

/-! ## Source-generated physical balance -/

/-- Every raw source generates one positive-time physical Galerkin
trajectory carrying both the pointwise stretching balance and its exact
finite-time write-back ledger.

The theorem mouth contains only the raw source and viscosity.  The actual
trajectory, lifespan, sharp support, transversality, Fourier reality,
pointwise balance, and integrated balance are all generated conclusions. -/
theorem generatedSource_transverseRealityEnstrophyBalanceLocalTrajectory
    (source : RawVorticityFourierSource)
    (ν : ℝ) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (physicalTime : ℝ),
      0 < physicalTime ∧
        trajectory 0 =
          generatedComplexVorticityState source
            (generatedSupport source) ∧
        ∀ t ∈ Icc (0 : ℝ) physicalTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                (generatedSupport source) ν (trajectory t)) t ∧
            (∀ wave,
              wave ∉ generatedSupport source →
                trajectory t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
            FiniteStateFourierReality (trajectory t) ∧
            HasDerivAt
              (fun time =>
                finiteStateVorticityHalfEnstrophy
                  (generatedSupport source) (trajectory time))
              (finiteStateVorticityStretchingWork
                  (generatedSupport source) (trajectory t) -
                ν * (2 * Real.pi) ^ 2 *
                  finiteStateVorticityEnstrophyMass
                    (generatedSupport source) (trajectory t)) t ∧
            (∫ time in (0 : ℝ)..t,
              (finiteStateVorticityStretchingWork
                  (generatedSupport source) (trajectory time) -
                ν * (2 * Real.pi) ^ 2 *
                  finiteStateVorticityEnstrophyMass
                    (generatedSupport source) (trajectory time))) =
              finiteStateVorticityHalfEnstrophy
                  (generatedSupport source) (trajectory t) -
                finiteStateVorticityHalfEnstrophy
                  (generatedSupport source) (trajectory 0) := by
  obtain
      ⟨trajectory, physicalTime, physicalTimePos, initial,
        physicalProperties⟩ :=
    generatedSource_transverseRealityLocalTrajectory source ν
  have negClosed :
      ∀ wave, wave ∈ generatedSupport source →
        waveNeg wave ∈ generatedSupport source := by
    intro wave waveMem
    exact generatedSupport_waveNeg_mem source waveMem
  refine
    ⟨trajectory, physicalTime, physicalTimePos, initial, ?_⟩
  intro t timeMem
  obtain
      ⟨actual, supported, transverse, reality⟩ :=
    physicalProperties t timeMem
  refine
    ⟨actual, supported, transverse, reality, ?_, ?_⟩
  · exact
      finiteStateVorticityHalfEnstrophy_hasDerivAt_stretchingWork
        (generatedSupport source) negClosed ν trajectory t
        actual reality
  · apply
      finiteStateVorticityHalfEnstrophy_integral_stretchingWork
        (generatedSupport source) negClosed ν trajectory
        0 t timeMem.1
    · intro time timeWithin
      exact
        (physicalProperties time
          ⟨timeWithin.1, timeWithin.2.trans timeMem.2⟩).1
    · intro time timeWithin
      exact
        (physicalProperties time
          ⟨timeWithin.1, timeWithin.2.trans timeMem.2⟩).2.2.2

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
end NavierStokes
end SaturationMonoid
