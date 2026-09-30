import Mathlib.Analysis.Calculus.MeanValue
import H0mework.NavierStokes.Fourier.CoarseFilterProcess
import H0mework.NavierStokes.InitialData.FiniteSupportComplexTrajectory
import H0mework.NavierStokes.Fourier.ShellSerrinGeometry

/-!
# Physical invariants of finite three-dimensional vorticity trajectories

The ambient complex Galerkin vector field is defined on every square-summable
coefficient state, but physical source states occupy the finite transverse
subspace.  This module proves that the complete ordered-pair nonlinearity is
tangent to that subspace, packages the existing rowwise transverse projection
as an actual finite-rank continuous linear projection, and uses Picard--
Lindelöf on the projected vector field to generate a trajectory which then
satisfies the original Galerkin update.

The public source theorem generates the trajectory, positive time window,
support, and transversality as conclusions.  None is accepted as a source
field or theorem premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory

open scoped BigOperators Matrix Topology

open Set
open Matrix
open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry

noncomputable section

/-! ## Arbitrary-state transverse pair algebra -/

/-- Transversality of an ambient coefficient state on one finite mode set. -/
def FiniteStateTransverseOn
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) : Prop :=
  ∀ wave ∈ modes,
    complexWavevector wave ⬝ᵥ state wave = 0

private theorem complexWavevector_stretchingPairOutput
    (pair : StretchingPair) :
    complexWavevector (stretchingPairOutput pair) =
      complexWavevector pair.1 + complexWavevector pair.2 := by
  funext coordinate
  simp [complexWavevector, stretchingPairOutput]

private theorem stretchingPairOutput_dot_finiteStateVelocityCoefficient_second
    (state : ComplexVorticityHilbertState)
    (pair : StretchingPair) :
    complexWavevector (stretchingPairOutput pair) ⬝ᵥ
        finiteStateVelocityCoefficient state pair.2 =
      complexWavevector pair.1 ⬝ᵥ
        finiteStateVelocityCoefficient state pair.2 := by
  rw [complexWavevector_stretchingPairOutput,
    add_dotProduct,
    finiteStateVelocityCoefficient,
    complexWavevector_dot_biotSavartVelocityCoefficient,
    add_zero]

private theorem stretchingPairOutput_dot_state_second
    (state : ComplexVorticityHilbertState)
    (pair : StretchingPair)
    (secondTransverse :
      complexWavevector pair.2 ⬝ᵥ state pair.2 = 0) :
    complexWavevector (stretchingPairOutput pair) ⬝ᵥ state pair.2 =
      complexWavevector pair.1 ⬝ᵥ state pair.2 := by
  rw [complexWavevector_stretchingPairOutput,
    add_dotProduct, secondTransverse, add_zero]

/-- Exact longitudinal coefficient of one arbitrary-state nonlinear pair.
The row itself need not be transverse. -/
theorem complexWavevector_output_dot_finiteStateVorticityNonlinearPairContribution
    (state : ComplexVorticityHilbertState)
    (pair : StretchingPair)
    (secondTransverse :
      complexWavevector pair.2 ⬝ᵥ state pair.2 = 0) :
    complexWavevector (stretchingPairOutput pair) ⬝ᵥ
        finiteStateVorticityNonlinearPairContribution state pair =
      (Complex.I * (((2 * Real.pi : ℝ) : ℂ))) *
        ((complexWavevector pair.2 ⬝ᵥ state pair.1) *
          (complexWavevector pair.1 ⬝ᵥ
            finiteStateVelocityCoefficient state pair.2) -
        (complexWavevector pair.2 ⬝ᵥ
            finiteStateVelocityCoefficient state pair.1) *
          (complexWavevector pair.1 ⬝ᵥ state pair.2)) := by
  rw [finiteStateVorticityNonlinearPairContribution,
    dotProduct_sub, dotProduct_smul, dotProduct_smul,
    stretchingPairOutput_dot_finiteStateVelocityCoefficient_second,
    stretchingPairOutput_dot_state_second state pair secondTransverse]
  simp only [smul_eq_mul]
  ring

/-- Swapping two transverse input rows reverses the longitudinal coefficient
while preserving their output frequency. -/
theorem finiteStateVorticityNonlinearPairDivergence_swap
    (state : ComplexVorticityHilbertState)
    (pair : StretchingPair)
    (firstTransverse :
      complexWavevector pair.1 ⬝ᵥ state pair.1 = 0)
    (secondTransverse :
      complexWavevector pair.2 ⬝ᵥ state pair.2 = 0) :
    complexWavevector
          (stretchingPairOutput (stretchingPairSwap pair)) ⬝ᵥ
        finiteStateVorticityNonlinearPairContribution state
          (stretchingPairSwap pair) =
      -(complexWavevector (stretchingPairOutput pair) ⬝ᵥ
        finiteStateVorticityNonlinearPairContribution state pair) := by
  rw [
    complexWavevector_output_dot_finiteStateVorticityNonlinearPairContribution
      state (stretchingPairSwap pair) firstTransverse,
    complexWavevector_output_dot_finiteStateVorticityNonlinearPairContribution
      state pair secondTransverse]
  simp only [stretchingPairSwap]
  ring

/-- The complete arbitrary-state ordered-pair aggregate is transverse whenever
all of its finite input rows are transverse. -/
theorem finiteStateVorticityNonlinearCoefficientAt_transverse
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state)
    (output : IntegerWavevector) :
    complexWavevector output ⬝ᵥ
        finiteStateVorticityNonlinearCoefficientAt modes state output = 0 := by
  classical
  let longitudinalSum : ℂ :=
    ∑ first ∈ modes,
      ∑ second ∈ modes,
        if first + second = output then
          complexWavevector output ⬝ᵥ
            finiteStateVorticityNonlinearPairContribution
              state (first, second)
        else 0
  have dotEquality :
      complexWavevector output ⬝ᵥ
          finiteStateVorticityNonlinearCoefficientAt modes state output =
        longitudinalSum := by
    simp only [finiteStateVorticityNonlinearCoefficientAt,
      longitudinalSum, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro first firstMem
    apply Finset.sum_congr rfl
    intro second secondMem
    by_cases pairSum : first + second = output
    · simp [pairSum]
    · simp [pairSum]
  have sumEqNeg : longitudinalSum = -longitudinalSum := by
    calc
      longitudinalSum =
          ∑ first ∈ modes,
            ∑ second ∈ modes,
              if first + second = output then
                complexWavevector output ⬝ᵥ
                  finiteStateVorticityNonlinearPairContribution
                    state (second, first)
              else 0 := by
          simp only [longitudinalSum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro first firstMem
          apply Finset.sum_congr rfl
          intro second secondMem
          rw [add_comm]
      _ =
          ∑ first ∈ modes,
            ∑ second ∈ modes,
              -(if first + second = output then
                  complexWavevector output ⬝ᵥ
                    finiteStateVorticityNonlinearPairContribution
                      state (first, second)
                else 0) := by
          apply Finset.sum_congr rfl
          intro first firstMem
          apply Finset.sum_congr rfl
          intro second secondMem
          by_cases pairSum : first + second = output
          · rw [if_pos pairSum, if_pos pairSum]
            have swapped :=
              finiteStateVorticityNonlinearPairDivergence_swap
                state (first, second)
                (stateTransverse first firstMem)
                (stateTransverse second secondMem)
            have swappedOutput : second + first = output := by
              simpa [add_comm] using pairSum
            simp only [stretchingPairOutput, stretchingPairSwap] at swapped
            rw [swappedOutput, pairSum] at swapped
            exact swapped
          · simp [pairSum]
      _ = -longitudinalSum := by
          simp only [Finset.sum_neg_distrib, longitudinalSum]
  have twiceSumZero : (2 : ℂ) * longitudinalSum = 0 := by
    calc
      (2 : ℂ) * longitudinalSum =
          longitudinalSum + longitudinalSum := by ring
      _ = -longitudinalSum + longitudinalSum := by
          exact
            congrArg (fun value : ℂ => value + longitudinalSum)
              sumEqNeg
      _ = 0 := neg_add_cancel _
  rw [dotEquality]
  exact
    (mul_eq_zero.mp twiceSumZero).resolve_left (by norm_num)

/-- The complete finite Galerkin generator is tangent to the transverse
finite-support carrier. -/
theorem finiteStateVorticityGenerator_transverse
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState)
    (stateTransverse : FiniteStateTransverseOn modes state)
    (output : IntegerWavevector) :
    complexWavevector output ⬝ᵥ
        finiteStateVorticityGenerator modes ν state output = 0 := by
  by_cases outputMem : output ∈ modes
  · rw [finiteStateVorticityGenerator_apply, if_pos outputMem,
      dotProduct_sub, dotProduct_smul,
      finiteStateVorticityNonlinearCoefficientAt_transverse
        modes state stateTransverse output,
      stateTransverse output outputMem]
    simp
  · rw [finiteStateVorticityGenerator_apply, if_neg outputMem]
    simp

/-! ## Finite transverse-support projection -/

/-- The existing rowwise transverse projection as a complex-linear map. -/
def transverseProjectionLinearMap
    (wave : IntegerWavevector) :
    ComplexCoordinateVector →ₗ[ℂ] ComplexCoordinateVector where
  toFun := transverseProjection wave
  map_add' := by
    intro left right
    by_cases waveZero : wave = 0
    · simp [transverseProjection, waveZero]
    · rw [transverseProjection, if_neg waveZero,
        transverseProjection, if_neg waveZero,
        transverseProjection, if_neg waveZero,
        dotProduct_add]
      module
  map_smul' := by
    intro scalar vector
    exact transverseProjection_smul wave scalar vector

/-- Continuous real-linear form of one rowwise transverse projection. -/
def transverseProjectionCLM
    (wave : IntegerWavevector) :
    ComplexCoordinateVector →L[ℝ] ComplexCoordinateVector :=
  (transverseProjectionLinearMap wave).toContinuousLinearMap.restrictScalars ℝ

@[simp] theorem transverseProjectionCLM_apply
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    transverseProjectionCLM wave vector =
      transverseProjection wave vector :=
  rfl

@[simp] theorem transverseProjection_idempotent
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    transverseProjection wave (transverseProjection wave vector) =
      transverseProjection wave vector := by
  by_cases waveZero : wave = 0
  · simp [transverseProjection, waveZero]
  · rw [transverseProjection, if_neg waveZero,
      complexWavevector_dot_transverseProjection]
    simp

/-- A nonzero transverse row is fixed by its rowwise projection. -/
theorem transverseProjection_eq_self_of_transverse
    {wave : IntegerWavevector}
    {vector : ComplexCoordinateVector}
    (waveNonzero : wave ≠ 0)
    (transverse :
      complexWavevector wave ⬝ᵥ vector = 0) :
    transverseProjection wave vector = vector := by
  rw [transverseProjection, if_neg waveNonzero, transverse]
  simp

/-- Sharp finite support followed by rowwise transverse projection. -/
def finiteTransverseSupportProjection
    (modes : Finset IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState :=
  ∑ wave ∈ modes,
    (lp.singleContinuousLinearMap
      ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp
      ((transverseProjectionCLM wave).comp
        (lp.evalCLM
          ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave))

@[simp] theorem finiteTransverseSupportProjection_apply
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    finiteTransverseSupportProjection modes state wave =
      if wave ∈ modes
      then transverseProjection wave (state wave)
      else 0 := by
  classical
  simp only [finiteTransverseSupportProjection, _root_.sum_apply,
    ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rw [lp.coeFn_sum]
  simp [lp.single_apply, lp.evalCLM, lp.evalₗ_apply,
    transverseProjectionCLM, transverseProjectionLinearMap]

@[simp] theorem finiteTransverseSupportProjection_idempotent
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteTransverseSupportProjection modes
        (finiteTransverseSupportProjection modes state) =
      finiteTransverseSupportProjection modes state := by
  apply Subtype.ext
  funext wave
  by_cases waveMem : wave ∈ modes
  · simp [waveMem, transverseProjection_idempotent]
  · simp [waveMem]

/-- A projection-fixed state vanishes outside the owned finite support. -/
theorem finiteTransverseSupportProjection_fixed_support
    {modes : Finset IntegerWavevector}
    {state : ComplexVorticityHilbertState}
    (fixed :
      finiteTransverseSupportProjection modes state = state)
    {wave : IntegerWavevector}
    (outside : wave ∉ modes) :
    state wave = 0 := by
  have rowEquality := congrArg (fun value => value wave) fixed
  simpa [outside] using rowEquality.symm

/-- A projection-fixed state is transverse at every frequency. -/
theorem finiteTransverseSupportProjection_fixed_transverse
    {modes : Finset IntegerWavevector}
    {state : ComplexVorticityHilbertState}
    (fixed :
      finiteTransverseSupportProjection modes state = state) :
    ∀ wave,
      complexWavevector wave ⬝ᵥ state wave = 0 := by
  intro wave
  have rowEquality := congrArg (fun value => value wave) fixed
  by_cases waveMem : wave ∈ modes
  · rw [finiteTransverseSupportProjection_apply,
      if_pos waveMem] at rowEquality
    rw [← rowEquality]
    exact complexWavevector_dot_transverseProjection _ _
  · rw [finiteTransverseSupportProjection_apply,
      if_neg waveMem] at rowEquality
    rw [← rowEquality]
    simp

/-! ## Projected Picard construction and original update recovery -/

/-- The finite transverse projection of the actual Galerkin vector field. -/
def finiteStateTransverseProjectedGenerator
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteTransverseSupportProjection modes
    (finiteStateVorticityGenerator modes ν state)

/-- The projected finite-rank vector field remains continuously
differentiable on the common ambient carrier. -/
theorem finiteStateTransverseProjectedGenerator_contDiff
    (modes : Finset IntegerWavevector)
    (ν : ℝ) :
    ContDiff ℝ 1
      (finiteStateTransverseProjectedGenerator modes ν) := by
  exact
    (finiteTransverseSupportProjection modes).contDiff.comp
      (finiteStateVorticityGenerator_contDiff modes ν)

/-- Once a zero-free finite state is projection-fixed, its actual Galerkin
tangent is fixed by the same transverse-support projection. -/
theorem finiteTransverseSupportProjection_generator_of_fixed
    {modes : Finset IntegerWavevector}
    (zeroNotMem : 0 ∉ modes)
    (ν : ℝ)
    {state : ComplexVorticityHilbertState}
    (fixed :
      finiteTransverseSupportProjection modes state = state) :
    finiteTransverseSupportProjection modes
        (finiteStateVorticityGenerator modes ν state) =
      finiteStateVorticityGenerator modes ν state := by
  have stateTransverse :
      FiniteStateTransverseOn modes state := by
    intro wave waveMem
    exact
      finiteTransverseSupportProjection_fixed_transverse
        fixed wave
  apply Subtype.ext
  funext wave
  by_cases waveMem : wave ∈ modes
  · rw [finiteTransverseSupportProjection_apply, if_pos waveMem]
    apply transverseProjection_eq_self_of_transverse
    · intro waveZero
      subst wave
      exact zeroNotMem waveMem
    · exact
        finiteStateVorticityGenerator_transverse
          modes ν state stateTransverse wave
  · rw [finiteTransverseSupportProjection_apply, if_neg waveMem,
      finiteStateVorticityGenerator_apply, if_neg waveMem]

@[simp] theorem zero_not_mem_generatedIntegerShellGalerkinModes
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current) :
    0 ∉ generatedIntegerShellGalerkinModes current response := by
  simp [generatedIntegerShellGalerkinModes]

/-- The actual source coefficient table is fixed by transverse projection on
the response-owned Galerkin support. -/
theorem finiteTransverseSupportProjection_generatedIntegerShellInitial
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current) :
    finiteTransverseSupportProjection
        (generatedIntegerShellGalerkinModes current response)
        (generatedIntegerShellGalerkinInitialState current response) =
      generatedIntegerShellGalerkinInitialState current response := by
  apply Subtype.ext
  funext wave
  rw [finiteTransverseSupportProjection_apply,
    generatedIntegerShellGalerkinInitialState_apply]
  by_cases waveMem :
      wave ∈ generatedIntegerShellGalerkinModes current response
  · rw [if_pos waveMem, if_pos waveMem]
    apply transverseProjection_eq_self_of_transverse
    · intro waveZero
      subst wave
      exact
        zero_not_mem_generatedIntegerShellGalerkinModes
          current response waveMem
    · exact generatedVorticityCoefficient_transverse current wave
  · rw [if_neg waveMem, if_neg waveMem]

/-- The complete coefficient table generated by any raw source is fixed by
the transverse-support projection on its own exact support. -/
theorem finiteTransverseSupportProjection_generatedSourceInitial
    (source : RawVorticityFourierSource) :
    finiteTransverseSupportProjection (generatedSupport source)
        (generatedComplexVorticityState source (generatedSupport source)) =
      generatedComplexVorticityState source (generatedSupport source) := by
  apply Subtype.ext
  funext wave
  rw [finiteTransverseSupportProjection_apply,
    generatedComplexVorticityState_apply]
  by_cases waveMem : wave ∈ generatedSupport source
  · rw [if_pos waveMem, if_pos waveMem]
    apply transverseProjection_eq_self_of_transverse
    · intro waveZero
      subst wave
      exact zero_not_mem_generatedSupport source waveMem
    · exact generatedVorticityCoefficient_transverse source wave
  · rw [if_neg waveMem, if_neg waveMem]

/-- Picard--Lindelöf applied to the finite transverse projection.  This is an
internal construction lemma; the public theorem below discharges its fixed
initial-state premise from the source. -/
theorem exists_finiteStateVorticity_transverseLocalTrajectory
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (ν : ℝ)
    (initialState : ComplexVorticityHilbertState)
    (initialFixed :
      finiteTransverseSupportProjection modes initialState =
        initialState) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (physicalTime : ℝ),
      0 < physicalTime ∧
        trajectory 0 = initialState ∧
        ∀ t ∈ Icc (0 : ℝ) physicalTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                modes ν (trajectory t)) t ∧
            finiteTransverseSupportProjection modes (trajectory t) =
              trajectory t := by
  obtain ⟨trajectory, initial, radius, radiusPos, evolves⟩ :=
    (finiteStateTransverseProjectedGenerator_contDiff modes ν).contDiffAt
      |>.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀
        0
  let physicalTime := radius / 2
  have physicalTimePos : 0 < physicalTime := by
    dsimp [physicalTime]
    linarith
  have physicalTimeLtRadius : physicalTime < radius := by
    dsimp [physicalTime]
    linarith
  have timeInRadius :
      ∀ t ∈ Icc (0 : ℝ) physicalTime,
        t ∈ Ioo (-radius) radius := by
    intro t timeMem
    constructor
    · linarith [timeMem.1]
    · exact lt_of_le_of_lt timeMem.2 physicalTimeLtRadius
  have projectedLaw :
      ∀ t ∈ Icc (0 : ℝ) physicalTime,
        HasDerivAt trajectory
          (finiteStateTransverseProjectedGenerator
            modes ν (trajectory t)) t := by
    intro t timeMem
    exact evolves t (by simpa using timeInRadius t timeMem)
  have projectedPathLaw :
      ∀ t ∈ Icc (0 : ℝ) physicalTime,
        HasDerivAt
          ((finiteTransverseSupportProjection modes) ∘ trajectory)
          (finiteStateTransverseProjectedGenerator
            modes ν (trajectory t)) t := by
    intro t timeMem
    have projected :=
      (finiteTransverseSupportProjection modes).hasFDerivAt
        |>.comp_hasDerivAt t (projectedLaw t timeMem)
    simpa [finiteStateTransverseProjectedGenerator,
      finiteTransverseSupportProjection_idempotent] using projected
  have trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) physicalTime) :=
    HasDerivAt.continuousOn projectedLaw
  have projectedPathContinuous :
      ContinuousOn
        ((finiteTransverseSupportProjection modes) ∘ trajectory)
        (Icc (0 : ℝ) physicalTime) :=
    HasDerivAt.continuousOn projectedPathLaw
  have sameInitial :
      trajectory 0 =
        finiteTransverseSupportProjection modes (trajectory 0) := by
    rw [initial, initialFixed]
  have fixedForward :
      ∀ t ∈ Icc (0 : ℝ) physicalTime,
        trajectory t =
          finiteTransverseSupportProjection modes (trajectory t) := by
    apply eq_of_has_deriv_right_eq
      (f' := fun t =>
        finiteStateTransverseProjectedGenerator
          modes ν (trajectory t))
    · intro t timeMem
      exact
        (projectedLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · intro t timeMem
      exact
        (projectedPathLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · exact trajectoryContinuous
    · exact projectedPathContinuous
    · exact sameInitial
  refine
    ⟨trajectory, physicalTime, physicalTimePos, initial, ?_⟩
  intro t timeMem
  have fixed :
      finiteTransverseSupportProjection modes (trajectory t) =
        trajectory t :=
    (fixedForward t timeMem).symm
  have generatorFixed :=
    finiteTransverseSupportProjection_generator_of_fixed
      zeroNotMem ν fixed
  have actualLaw := projectedLaw t timeMem
  rw [finiteStateTransverseProjectedGenerator,
    generatorFixed] at actualLaw
  exact ⟨actualLaw, fixed⟩

/-! ## Source-specialized physical trajectory -/

/-- Every actual raw source generates a positive-time trajectory on its own
exact finite support.  The returned trajectory satisfies the original
Galerkin generator, remains sharply supported, and is transverse at every
frequency. -/
theorem generatedSource_transverseLocalTrajectory
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
            ∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0 := by
  obtain ⟨trajectory, physicalTime, physicalTimePos, initial, evolves⟩ :=
    exists_finiteStateVorticity_transverseLocalTrajectory
      (generatedSupport source)
      (zero_not_mem_generatedSupport source)
      ν
      (generatedComplexVorticityState source (generatedSupport source))
      (finiteTransverseSupportProjection_generatedSourceInitial source)
  refine ⟨trajectory, physicalTime, physicalTimePos, initial, ?_⟩
  intro t timeMem
  obtain ⟨actualLaw, fixed⟩ := evolves t timeMem
  refine ⟨actualLaw, ?_, ?_⟩
  · intro wave outside
    exact finiteTransverseSupportProjection_fixed_support fixed outside
  · exact finiteTransverseSupportProjection_fixed_transverse fixed

/-- A literal successful source response generates a positive physical-time
Galerkin trajectory on which the original finite vorticity update, exact
finite support, and rowwise transversality hold simultaneously.

The source-owned branch equality is used only to recover its internally
selected shell.  The trajectory, time window, support law, and transverse law
are all conclusions. -/
theorem generatedIntegerShellRespond_transverseLocalTrajectory
    (current : RawVorticityFourierSource)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response)
    (ν : ℝ) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (physicalTime : ℝ),
      0 < physicalTime ∧
        trajectory 0 =
          generatedIntegerShellGalerkinInitialState current response ∧
        generatedNextOuterNonlinearShellSq? current =
          some response.2.shellSq ∧
        ∀ t ∈ Icc (0 : ℝ) physicalTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                (generatedIntegerShellGalerkinModes current response)
                ν (trajectory t)) t ∧
            (∀ wave,
              wave ∉ generatedIntegerShellGalerkinModes current response →
                trajectory t wave = 0) ∧
            ∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0 := by
  obtain
      ⟨trajectory, physicalTime, physicalTimePos, initial, evolves⟩ :=
    exists_finiteStateVorticity_transverseLocalTrajectory
      (generatedIntegerShellGalerkinModes current response)
      (zero_not_mem_generatedIntegerShellGalerkinModes current response)
      ν
      (generatedIntegerShellGalerkinInitialState current response)
      (finiteTransverseSupportProjection_generatedIntegerShellInitial
        current response)
  refine
    ⟨trajectory, physicalTime, physicalTimePos, initial,
      generatedIntegerShellRespond_selectedShell
        current response generated, ?_⟩
  intro t timeMem
  obtain ⟨actualLaw, fixed⟩ := evolves t timeMem
  refine ⟨actualLaw, ?_, ?_⟩
  · intro wave outside
    exact
      finiteTransverseSupportProjection_fixed_support
        fixed outside
  · exact
      finiteTransverseSupportProjection_fixed_transverse fixed

/-- Along an actual generated shell path, the source-specialized transverse
trajectory above is immediately a state-generic Serrin-geometry input.  The
path owns the physical shell compiler and reciprocal shell weight; the next
literal source response owns the local trajectory. -/
theorem
    generatedIntegerShellReachable_transverseLocalTrajectory_wholeShellSerrinGeometry
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response)
    (ν : ℝ) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (physicalTime : ℝ),
      0 < physicalTime ∧
        trajectory 0 =
          generatedIntegerShellGalerkinInitialState current response ∧
        generatedNextOuterNonlinearShellSq? current =
          some response.2.shellSq ∧
        (∀ t ∈ Icc (0 : ℝ) physicalTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                (generatedIntegerShellGalerkinModes current response)
                ν (trajectory t)) t ∧
            (∀ wave,
              wave ∉ generatedIntegerShellGalerkinModes current response →
                trajectory t wave = 0) ∧
            ∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
        ∀ t ∈ Icc (0 : ℝ) physicalTime,
          ∀ x : PhysicalSpace,
            ‖generatedIntegerShellReachableStatePhysicalVelocityField
                arrival (fun wave => trajectory t wave) x‖ ^ 2 ≤
              biotSavartSerrinConstant *
                generatedIntegerShellReachableReciprocalCardWeight arrival *
                pathWholeShellVorticityMass
                  arrival (fun wave => trajectory t wave) := by
  obtain
      ⟨trajectory, physicalTime, physicalTimePos, initial,
        selectedShell, evolves⟩ :=
    generatedIntegerShellRespond_transverseLocalTrajectory
      current response generated ν
  refine
    ⟨trajectory, physicalTime, physicalTimePos, initial,
      selectedShell, evolves, ?_⟩
  intro t timeMem x
  exact
    generatedIntegerShellReachable_wholeShellStateSerrinGeometry
      arrival (fun wave => trajectory t wave) x

end

end ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
end NavierStokes
end SaturationMonoid
