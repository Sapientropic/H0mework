import H0mework.NavierStokes.Accumulation.FullReceiptFourierConeAdvance
import H0mework.NavierStokes.NativeWork.FullReceiptNativeFluxSettlement
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Full-receipt normalized-work Euler escrow

The full-receipt rowwise Euler tube is assembled on one fixed finite
observation.  A finite-dimensional source-generated compact ball then turns
the `C¹` normalized-work readout into an internally selected Lipschitz bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

open scoped BigOperators Topology

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFullReceiptNormalizedWorkEulerEscrow

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedPathFiniteObservedCompactness
open ThreeDimensionalVorticityCoefficientGeneratedPathStrongSpaceTimeCompactness
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellInfiniteLineageHilbertCompletion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartEnstrophyWork
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartSourcePairOccurrence
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinOverlap
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeTemporalEnstrophyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationNativeTurbulenceLaw
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartActualFourierConeAdvance
open ThreeDimensionalVorticityCoefficientWholeStateSourceOwnedLocalBarrier
open ThreeDimensionalVorticityCoefficientFiniteNormalizedWorkPhaseFace
open ThreeDimensionalVorticityCoefficientFullReceiptFourierConeAdvance
open ThreeDimensionalVorticityCoefficientFullReceiptNativeFluxSettlement
open ThreeDimensionalVorticityCoefficientNativeFluxValueEscrow

noncomputable section

/-! ## Finite-coordinate compact escrow -/

def fullReplayActualObservedState
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    FiniteObservedCoefficientState modes :=
  finiteObservedCoefficientState modes (current.nextReceipt.wholePath time)

def fullReplayEulerObservedState
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    FiniteObservedCoefficientState modes :=
  fun wave => fullReplayEulerRow current time.1 wave.1

theorem finiteObservedEmbedding_fullReplayEulerObservedState
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    finiteObservedEmbedding modes
        (fullReplayEulerObservedState current modes time) =
      fullReplayFiniteEulerState current modes time.1 := by
  apply lp.ext
  funext wave
  by_cases waveMem : wave ∈ modes
  · rw [finiteObservedEmbedding_apply, dif_pos waveMem,
      fullReplayFiniteEulerState, finiteComplexVorticityState_apply,
      if_pos waveMem]
    rfl
  · rw [finiteObservedEmbedding_apply, dif_neg waveMem,
      fullReplayFiniteEulerState, finiteComplexVorticityState_apply,
      if_neg waveMem]

theorem fullReplayActualObservedState_continuous
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    Continuous (fullReplayActualObservedState current modes) := by
  unfold fullReplayActualObservedState finiteObservedCoefficientState
  exact (finiteObservedRestriction modes).continuous.comp
    current.nextReceipt.wholePath.continuous

theorem fullReplayEulerObservedState_continuous
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    Continuous (fullReplayEulerObservedState current modes) := by
  unfold fullReplayEulerObservedState fullReplayEulerRow
  apply continuous_pi
  intro wave
  exact continuous_const.add
    (continuous_subtype_val.smul continuous_const)

/-- Explicit source-only ball radius.  It uses the current coefficient
ceiling and the finite sum of inverse-sixth Euler allowances; no completed
path range is inspected. -/
def fullReplayNormalizedWorkEulerBallRadius
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  Real.sqrt (wholeRestartCoefficientCeiling current.contact) +
    (∑ wave ∈ modes,
      fullReplayEulerTubePaymentUpper current wave) + 1

theorem fullReplayNormalizedWorkEulerBallRadius_pos
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    0 < fullReplayNormalizedWorkEulerBallRadius current modes := by
  unfold fullReplayNormalizedWorkEulerBallRadius
  have paymentNonneg : 0 ≤ ∑ wave ∈ modes,
      fullReplayEulerTubePaymentUpper current wave :=
    Finset.sum_nonneg fun wave _ =>
      fullReplayEulerTubePaymentUpper_nonneg current wave
  positivity

theorem fullReplayActualObservedState_mem_ball
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    fullReplayActualObservedState current modes time ∈
      Metric.closedBall (0 : FiniteObservedCoefficientState modes)
        (fullReplayNormalizedWorkEulerBallRadius current modes) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg
    (fullReplayNormalizedWorkEulerBallRadius_pos current modes).le).2
  intro wave
  have rowLeState :
      ‖current.nextReceipt.wholePath time wave.1‖ ≤
        ‖current.nextReceipt.wholePath time‖ :=
    lp.norm_apply_le_norm (by norm_num)
      (current.nextReceipt.wholePath time) wave.1
  have stateLePath :
      ‖current.nextReceipt.wholePath time‖ ≤
        ‖current.nextReceipt.wholePath‖ :=
    current.nextReceipt.wholePath.norm_coe_le_norm time
  have pathLe :=
    fullReplay_wholePath_norm_le_sqrt_coefficientCeiling current
  unfold fullReplayActualObservedState finiteObservedCoefficientState
  unfold fullReplayNormalizedWorkEulerBallRadius
  have paymentsNonneg : 0 ≤ ∑ output ∈ modes,
      fullReplayEulerTubePaymentUpper current output :=
    Finset.sum_nonneg fun output _ =>
      fullReplayEulerTubePaymentUpper_nonneg current output
  exact (rowLeState.trans (stateLePath.trans pathLe)).trans
    (by linarith)

theorem fullReplayEulerObservedState_mem_ball
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    fullReplayEulerObservedState current modes time ∈
      Metric.closedBall (0 : FiniteObservedCoefficientState modes)
        (fullReplayNormalizedWorkEulerBallRadius current modes) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg
    (fullReplayNormalizedWorkEulerBallRadius_pos current modes).le).2
  intro wave
  have waveNe : wave.1 ≠ 0 := fun waveZero =>
    zeroNotMem (waveZero ▸ wave.2)
  have rowError := fullReplay_row_sub_euler_norm_le
    current wave.1 waveNe time
  have timeSlopeLe :
      time.1 * fullReplayEulerRemainderSlope current wave.1 ≤
        wholeRestartDuration current.contact *
          fullReplayEulerRemainderSlope current wave.1 := by
    exact mul_le_mul_of_nonneg_right time.2.2
      (fullReplayEulerRemainderSlope_nonneg current wave.1)
  have rowErrorSource := timeSlopeLe.trans
    (fullReplay_duration_mul_remainderSlope_le_sourceUpper
      current wave.1)
  have actualRowLe :
      ‖current.nextReceipt.wholePath time wave.1‖ ≤
        Real.sqrt (wholeRestartCoefficientCeiling current.contact) :=
    (lp.norm_apply_le_norm (by norm_num)
      (current.nextReceipt.wholePath time) wave.1).trans
      ((current.nextReceipt.wholePath.norm_coe_le_norm time).trans
        (fullReplay_wholePath_norm_le_sqrt_coefficientCeiling current))
  have eulerRowLe :
      ‖fullReplayEulerRow current time.1 wave.1‖ ≤
        Real.sqrt (wholeRestartCoefficientCeiling current.contact) +
          fullReplayEulerTubePaymentUpper current wave.1 := by
    have triangle := norm_sub_le
      (current.nextReceipt.wholePath time wave.1)
      (current.nextReceipt.wholePath time wave.1 -
        fullReplayEulerRow current time.1 wave.1)
    have identity :
        current.nextReceipt.wholePath time wave.1 -
            (current.nextReceipt.wholePath time wave.1 -
              fullReplayEulerRow current time.1 wave.1) =
          fullReplayEulerRow current time.1 wave.1 := by abel
    rw [identity] at triangle
    exact triangle.trans
      (add_le_add actualRowLe (rowError.trans rowErrorSource))
  have singleLe :
      fullReplayEulerTubePaymentUpper current wave.1 ≤
        ∑ output ∈ modes,
          fullReplayEulerTubePaymentUpper current output :=
    Finset.single_le_sum
      (fun output _ => fullReplayEulerTubePaymentUpper_nonneg current output)
      wave.2
  unfold fullReplayEulerObservedState
    fullReplayNormalizedWorkEulerBallRadius
  linarith

def fullReplayObservedNormalizedWork
    (modes : Finset IntegerWavevector)
    (viscosity : Real)
    (state : FiniteObservedCoefficientState modes) : Real :=
  finiteNormalizedGeneratorWork modes viscosity
    (finiteObservedEmbedding modes state)

theorem fullReplayObservedNormalizedWork_contDiff
    (modes : Finset IntegerWavevector)
    (viscosity : Real) :
    ContDiff Real 1 (fullReplayObservedNormalizedWork modes viscosity) := by
  unfold fullReplayObservedNormalizedWork
  exact (finiteNormalizedGeneratorWork_contDiff modes viscosity).comp
    ((finiteObservedEmbedding modes).restrictScalars Real).contDiff

private def fullReplayObservedNormalizedWorkDerivativeNormImage
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Set Real :=
  (fun state : FiniteObservedCoefficientState modes =>
      ‖fderiv Real
        (fullReplayObservedNormalizedWork modes nu.coeff) state‖) ''
    Metric.closedBall (0 : FiniteObservedCoefficientState modes)
      (fullReplayNormalizedWorkEulerBallRadius current modes)

private theorem fullReplayObservedNormalizedWorkDerivativeNormImage_bddAbove
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    BddAbove
      (fullReplayObservedNormalizedWorkDerivativeNormImage current modes) := by
  apply IsCompact.bddAbove_image
    (isCompact_closedBall
      (0 : FiniteObservedCoefficientState modes)
      (fullReplayNormalizedWorkEulerBallRadius current modes))
  exact ((fullReplayObservedNormalizedWork_contDiff modes nu.coeff
    ).continuous_fderiv one_ne_zero).norm.continuousOn

private theorem fullReplayObservedNormalizedWorkDerivativeNormImage_nonempty
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    (fullReplayObservedNormalizedWorkDerivativeNormImage current modes
      ).Nonempty := by
  refine ⟨‖fderiv Real
      (fullReplayObservedNormalizedWork modes nu.coeff)
      (0 : FiniteObservedCoefficientState modes)‖, ?_⟩
  refine ⟨0, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_self]
  exact (fullReplayNormalizedWorkEulerBallRadius_pos current modes).le

/-- Canonical source-owned Lipschitz readout.  Its value is the supremum of
the actual derivative norm on the generated compact ball; no arbitrary
numeric witness survives from compactness. -/
noncomputable def fullReplayObservedNormalizedWorkLipschitzConstant
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : NNReal :=
  ⟨sSup (fullReplayObservedNormalizedWorkDerivativeNormImage current modes), by
    obtain ⟨value, valueMem⟩ :=
      fullReplayObservedNormalizedWorkDerivativeNormImage_nonempty
        current modes
    have valueNonneg : 0 ≤ value := by
      rcases valueMem with ⟨state, _stateMem, rfl⟩
      exact norm_nonneg _
    exact valueNonneg.trans
      (le_csSup
        (fullReplayObservedNormalizedWorkDerivativeNormImage_bddAbove
          current modes)
        valueMem)⟩

theorem fullReplayObservedNormalizedWorkLipschitzConstant_spec
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    LipschitzOnWith
      (fullReplayObservedNormalizedWorkLipschitzConstant current modes)
      (fullReplayObservedNormalizedWork modes nu.coeff)
      (Metric.closedBall
        (0 : FiniteObservedCoefficientState modes)
        (fullReplayNormalizedWorkEulerBallRadius current modes)) :=
  by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := Real)
    · intro state _stateMem
      exact (fullReplayObservedNormalizedWork_contDiff modes nu.coeff
        ).differentiable one_ne_zero state
    · intro state stateMem
      apply NNReal.coe_le_coe.mp
      change ‖fderiv Real
          (fullReplayObservedNormalizedWork modes nu.coeff) state‖ ≤
        sSup
          (fullReplayObservedNormalizedWorkDerivativeNormImage current modes)
      apply le_csSup
        (fullReplayObservedNormalizedWorkDerivativeNormImage_bddAbove
          current modes)
      exact ⟨state, stateMem, rfl⟩
    · exact convex_closedBall _ _

/-- Any source calculation bounding the differential on the generated ball
automatically bounds the canonical supremum used by the Euler escrow.  This
is the quantitative producer mouth; no chosen Lipschitz witness remains. -/
theorem fullReplayObservedNormalizedWorkLipschitzConstant_le_of_fderiv_norm_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (bound : Real)
    (derivativeBound :
      ∀ state ∈ Metric.closedBall
          (0 : FiniteObservedCoefficientState modes)
          (fullReplayNormalizedWorkEulerBallRadius current modes),
        ‖fderiv Real
          (fullReplayObservedNormalizedWork modes nu.coeff) state‖ ≤ bound) :
    (fullReplayObservedNormalizedWorkLipschitzConstant current modes : Real) ≤
      bound := by
  change sSup
      (fullReplayObservedNormalizedWorkDerivativeNormImage current modes) ≤
    bound
  apply csSup_le
    (fullReplayObservedNormalizedWorkDerivativeNormImage_nonempty
      current modes)
  intro value valueMem
  rcases valueMem with ⟨state, stateMem, rfl⟩
  exact derivativeBound state stateMem

theorem fullReplay_observedState_dist_le_eulerError
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    dist (fullReplayActualObservedState current modes time)
        (fullReplayEulerObservedState current modes time) ≤
      Real.sqrt (fullReplayFiniteEulerErrorEnergy
        current modes time.1) := by
  rw [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro wave
  change ‖current.nextReceipt.wholePath time wave.1 -
      fullReplayEulerRow current time.1 wave.1‖ ≤ _
  have waveNe : wave.1 ≠ 0 := fun waveZero =>
    zeroNotMem (waveZero ▸ wave.2)
  have rowBound := fullReplay_row_sub_euler_norm_le
    current wave.1 waveNe time
  apply rowBound.trans
  apply Real.le_sqrt_of_sq_le
  have singleLe :
      3 * (time.1 * fullReplayEulerRemainderSlope current wave.1) ^ 2 ≤
        ∑ output ∈ modes,
          3 * (time.1 *
            fullReplayEulerRemainderSlope current output) ^ 2 :=
    Finset.single_le_sum
      (f := fun output : IntegerWavevector =>
        3 * (time.1 *
          fullReplayEulerRemainderSlope current output) ^ 2)
      (fun output _ => mul_nonneg (by norm_num) (sq_nonneg _)) wave.2
  unfold fullReplayFiniteEulerErrorEnergy
  nlinarith

/-- The internally selected finite-dimensional Lipschitz constant turns the
full-replay Euler tube into an explicit normalized-work value escrow. -/
theorem fullReplay_normalizedWork_sub_euler_abs_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    |finiteNormalizedGeneratorWork modes nu.coeff
          (complexSharpSupportProjection modes
            (current.nextReceipt.wholePath time)) -
        finiteNormalizedGeneratorWork modes nu.coeff
          (fullReplayFiniteEulerState current modes time.1)| ≤
      (fullReplayObservedNormalizedWorkLipschitzConstant current modes : Real) *
        Real.sqrt (fullReplayFiniteEulerErrorEnergy
          current modes time.1) := by
  have lipschitz :=
    fullReplayObservedNormalizedWorkLipschitzConstant_spec current modes
  have distanceBound := lipschitz.dist_le_mul
    (fullReplayActualObservedState current modes time)
    (fullReplayActualObservedState_mem_ball current modes time)
    (fullReplayEulerObservedState current modes time)
    (fullReplayEulerObservedState_mem_ball current modes zeroNotMem time)
  have observedDistance := fullReplay_observedState_dist_le_eulerError
    current modes zeroNotMem time
  have combined := distanceBound.trans
    (mul_le_mul_of_nonneg_left observedDistance (by positivity))
  rw [Real.dist_eq] at combined
  unfold fullReplayObservedNormalizedWork at combined
  have actualEmbeddingEq :
      finiteObservedEmbedding modes
          (fullReplayActualObservedState current modes time) =
        complexSharpSupportProjection modes
          (current.nextReceipt.wholePath time) := by
    simpa only [fullReplayActualObservedState] using
      finiteObservedEmbedding_finiteObservedCoefficientState modes
        (current.nextReceipt.wholePath time)
  rw [actualEmbeddingEq,
    finiteObservedEmbedding_fullReplayEulerObservedState] at combined
  exact combined

/-! ## Source-side finite margin mouth -/

/-- Entirely finite current-side condition ensuring that the Euler value
pays its own generated tube error.  The actual target path is not a field. -/
def fullReplayNormalizedWorkEulerMarginAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (floor : Real) : Prop :=
  ∀ time : Icc (0 : Real) (wholeRestartDuration current.contact),
    floor +
        (fullReplayObservedNormalizedWorkLipschitzConstant
          current modes : Real) *
          Real.sqrt
            (fullReplayFiniteEulerErrorEnergy current modes time.1) ≤
      finiteNormalizedGeneratorWork modes nu.coeff
        (fullReplayFiniteEulerState current modes time.1)

/-- Finite current-side tangent used by the exact Euler line. -/
def fullReplayEulerObservedTangent
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    FiniteObservedCoefficientState modes :=
  fun wave => wholeLatticeVorticityFourierTangentAt nu.coeff
    current.contact.physicalState wave.1

private theorem fullReplayEulerObservedState_eq_zero_add_smul
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    fullReplayEulerObservedState current modes time =
      fullReplayEulerObservedState current modes
          ⟨0, ⟨le_rfl, (wholeRestartDuration_pos current.contact).le⟩⟩ +
        time.1 • fullReplayEulerObservedTangent current modes := by
  ext wave
  simp [fullReplayEulerObservedState, fullReplayEulerRow,
    fullReplayEulerObservedTangent]

private theorem fullReplayEulerObservedState_dist_zero_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    dist (fullReplayEulerObservedState current modes time)
        (fullReplayEulerObservedState current modes
          ⟨0, ⟨le_rfl, (wholeRestartDuration_pos current.contact).le⟩⟩) ≤
      wholeRestartDuration current.contact *
        ‖fullReplayEulerObservedTangent current modes‖ := by
  rw [fullReplayEulerObservedState_eq_zero_add_smul]
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg time.2.1]
  exact mul_le_mul_of_nonneg_right time.2.2 (norm_nonneg _)

private theorem fullReplayFiniteEulerErrorEnergy_le_terminal
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    fullReplayFiniteEulerErrorEnergy current modes time.1 ≤
      fullReplayFiniteEulerErrorEnergy current modes
        (wholeRestartDuration current.contact) := by
  unfold fullReplayFiniteEulerErrorEnergy
  apply Finset.sum_le_sum
  intro wave _waveMem
  have slopeNonneg := fullReplayEulerRemainderSlope_nonneg current wave
  have timeNonneg : 0 ≤ time.1 := time.2.1
  have durationNonneg : 0 ≤ wholeRestartDuration current.contact :=
    (wholeRestartDuration_pos current.contact).le
  have scaledLe : time.1 * fullReplayEulerRemainderSlope current wave ≤
      wholeRestartDuration current.contact *
        fullReplayEulerRemainderSlope current wave :=
    mul_le_mul_of_nonneg_right time.2.2 slopeNonneg
  have scaledNonneg :
      0 ≤ time.1 * fullReplayEulerRemainderSlope current wave :=
    mul_nonneg timeNonneg slopeNonneg
  have terminalScaledNonneg :
      0 ≤ wholeRestartDuration current.contact *
        fullReplayEulerRemainderSlope current wave :=
    mul_nonneg durationNonneg slopeNonneg
  exact mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ scaledNonneg terminalScaledNonneg).2 scaledLe) (by norm_num)

/-- Time-independent coefficient of the assembled finite Euler error. -/
def fullReplayFiniteEulerSlopeEnergy
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  ∑ wave ∈ modes,
    3 * fullReplayEulerRemainderSlope current wave ^ 2

theorem fullReplayFiniteEulerErrorEnergy_eq_time_sq_mul_slopeEnergy
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (time : Real) :
    fullReplayFiniteEulerErrorEnergy current modes time =
      time ^ 2 * fullReplayFiniteEulerSlopeEnergy current modes := by
  unfold fullReplayFiniteEulerErrorEnergy fullReplayFiniteEulerSlopeEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  ring

/-- One canonical scalar escrow for the whole Euler line.  The first term
pays the complete finite-to-Euler tube and the second pays drift of the
Euler line from its time-zero source value. -/
def fullReplayNormalizedWorkTerminalEscrow
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  (fullReplayObservedNormalizedWorkLipschitzConstant current modes : Real) *
    (Real.sqrt (fullReplayFiniteEulerErrorEnergy current modes
        (wholeRestartDuration current.contact)) +
      wholeRestartDuration current.contact *
        ‖fullReplayEulerObservedTangent current modes‖)

/-- Source-current rate whose multiplication by the exact native horizon is
the complete normalized-work escrow. -/
def fullReplayNormalizedWorkTerminalEscrowRate
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Real :=
  (fullReplayObservedNormalizedWorkLipschitzConstant current modes : Real) *
    (Real.sqrt (fullReplayFiniteEulerSlopeEnergy current modes) +
      ‖fullReplayEulerObservedTangent current modes‖)

theorem fullReplayNormalizedWorkTerminalEscrowRate_nonneg
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    0 ≤ fullReplayNormalizedWorkTerminalEscrowRate current modes := by
  unfold fullReplayNormalizedWorkTerminalEscrowRate
  positivity

theorem fullReplayNormalizedWorkTerminalEscrow_eq_duration_mul_rate
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    fullReplayNormalizedWorkTerminalEscrow current modes =
      wholeRestartDuration current.contact *
        fullReplayNormalizedWorkTerminalEscrowRate current modes := by
  rw [fullReplayNormalizedWorkTerminalEscrow,
    fullReplayNormalizedWorkTerminalEscrowRate,
    fullReplayFiniteEulerErrorEnergy_eq_time_sq_mul_slopeEnergy,
    Real.sqrt_mul (sq_nonneg (wholeRestartDuration current.contact)),
    Real.sqrt_sq (wholeRestartDuration_pos current.contact).le]
  ring

private theorem fullReplayFiniteEulerState_zero
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) :
    fullReplayFiniteEulerState current modes 0 =
      complexSharpSupportProjection modes current.contact.physicalState := by
  ext wave
  simp [fullReplayFiniteEulerState, fullReplayEulerRow,
    complexSharpSupportProjection]

/-- A single source-current scalar inequality generates the complete
full-horizon Euler margin.  No future path, selected contact, branch or
pointwise margin is accepted from the caller. -/
theorem fullReplayNormalizedWorkEulerMargin_of_terminalEscrow
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (floor : Real)
    (scalar : floor + fullReplayNormalizedWorkTerminalEscrow current modes ≤
      finiteNormalizedGeneratorWork modes nu.coeff
        (complexSharpSupportProjection modes
          current.contact.physicalState)) :
    fullReplayNormalizedWorkEulerMarginAt current modes floor := by
  intro time
  let zeroTime : Icc (0 : Real) (wholeRestartDuration current.contact) :=
    ⟨0, ⟨le_rfl, (wholeRestartDuration_pos current.contact).le⟩⟩
  have lipschitz :=
    fullReplayObservedNormalizedWorkLipschitzConstant_spec current modes
  have variation := lipschitz.dist_le_mul
    (fullReplayEulerObservedState current modes time)
    (fullReplayEulerObservedState_mem_ball current modes zeroNotMem time)
    (fullReplayEulerObservedState current modes zeroTime)
    (fullReplayEulerObservedState_mem_ball current modes zeroNotMem zeroTime)
  have distanceLe :=
    fullReplayEulerObservedState_dist_zero_le current modes time
  have variationLe :
      |finiteNormalizedGeneratorWork modes nu.coeff
            (fullReplayFiniteEulerState current modes time.1) -
          finiteNormalizedGeneratorWork modes nu.coeff
            (complexSharpSupportProjection modes
              current.contact.physicalState)| ≤
        (fullReplayObservedNormalizedWorkLipschitzConstant current modes : Real) *
          (wholeRestartDuration current.contact *
            ‖fullReplayEulerObservedTangent current modes‖) := by
    rw [Real.dist_eq] at variation
    unfold fullReplayObservedNormalizedWork at variation
    rw [finiteObservedEmbedding_fullReplayEulerObservedState,
      finiteObservedEmbedding_fullReplayEulerObservedState] at variation
    rw [show zeroTime.1 = 0 by rfl,
      fullReplayFiniteEulerState_zero] at variation
    exact variation.trans
      (mul_le_mul_of_nonneg_left distanceLe (by positivity))
  have errorLe := Real.sqrt_le_sqrt
    (fullReplayFiniteEulerErrorEnergy_le_terminal current modes time)
  have errorScaledLe :
      (fullReplayObservedNormalizedWorkLipschitzConstant current modes : Real) *
          Real.sqrt (fullReplayFiniteEulerErrorEnergy current modes time.1) ≤
        (fullReplayObservedNormalizedWorkLipschitzConstant current modes : Real) *
          Real.sqrt (fullReplayFiniteEulerErrorEnergy current modes
            (wholeRestartDuration current.contact)) :=
    mul_le_mul_of_nonneg_left errorLe (by positivity)
  have eulerLower := (neg_le_neg variationLe).trans (neg_abs_le _)
  unfold fullReplayNormalizedWorkTerminalEscrow at scalar
  linarith

/-- Barrier-normalized source mouth.  The exact native duration divides the
current Euler-escrow rate by twice the generated barrier slope, so a single
rate/headroom inequality produces the full-horizon margin. -/
theorem fullReplayNormalizedWorkEulerMargin_of_rate_le_barrierHeadroom
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (floor : Real)
    (rateLe :
      fullReplayNormalizedWorkTerminalEscrowRate current modes ≤
        2 * sourceOwnedWholeStateBarrierSlope nu
              (wholeRestartCoefficientCeiling current.contact) *
          (finiteNormalizedGeneratorWork modes nu.coeff
              (complexSharpSupportProjection modes
                current.contact.physicalState) - floor)) :
    fullReplayNormalizedWorkEulerMarginAt current modes floor := by
  let slope := sourceOwnedWholeStateBarrierSlope nu
    (wholeRestartCoefficientCeiling current.contact)
  let work := finiteNormalizedGeneratorWork modes nu.coeff
    (complexSharpSupportProjection modes current.contact.physicalState)
  let rate := fullReplayNormalizedWorkTerminalEscrowRate current modes
  have slopePos : 0 < slope := by
    simpa only [slope] using sourceOwnedWholeStateBarrierSlope_pos nu
      (wholeRestartCoefficientCeiling current.contact)
  have denominatorPos : 0 < 2 * slope := mul_pos (by norm_num) slopePos
  have normalizedRateLe : rate ≤ (work - floor) * (2 * slope) := by
    dsimp only [rate, work, slope] at rateLe ⊢
    nlinarith
  have escrowLe :
      fullReplayNormalizedWorkTerminalEscrow current modes ≤ work - floor := by
    rw [fullReplayNormalizedWorkTerminalEscrow_eq_duration_mul_rate]
    change wholeRestartDuration current.contact * rate ≤ work - floor
    unfold wholeRestartDuration sourceOwnedWholeStateDuration
    change (1 / (2 * slope)) * rate ≤ work - floor
    rw [one_div_mul_eq_div]
    exact (div_le_iff₀ denominatorPos).2 normalizedRateLe
  apply fullReplayNormalizedWorkEulerMargin_of_terminalEscrow
    current modes zeroNotMem floor
  dsimp only [work] at escrowLe
  linarith

/-- The finite source margin forces the actual normalized-work readout to
stay above the same floor at every point of the unchanged receipt. -/
theorem fullReplay_actualNormalizedWork_ge_floor_of_eulerMargin
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (floor : Real)
    (margin : fullReplayNormalizedWorkEulerMarginAt
      current modes floor)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    floor ≤
      finiteNormalizedGeneratorWork modes nu.coeff
        (complexSharpSupportProjection modes
          (current.nextReceipt.wholePath time)) := by
  have escrow := fullReplay_normalizedWork_sub_euler_abs_le
    current modes zeroNotMem time
  have lower := (neg_le_neg escrow).trans (neg_abs_le
    (finiteNormalizedGeneratorWork modes nu.coeff
        (complexSharpSupportProjection modes
          (current.nextReceipt.wholePath time)) -
      finiteNormalizedGeneratorWork modes nu.coeff
        (fullReplayFiniteEulerState current modes time.1)))
  linarith [margin time]

/-- Source-side finite-mass retention inequality.  Its `12` is the exact
weight-one specialization of the existing full-replay Hölder ledger. -/
def fullReplayFiniteMassRetentionMarginAt
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector) : Prop :=
  12 * wholeRestartDuration current.contact *
      fullReplayFiniteObservedHolderBudget current modes ≤
    currentFiniteEulerMassBase current modes

/-- A generated retention margin keeps the finite augmented mass above one
quarter of its current value throughout the unchanged base horizon. -/
theorem fullReplay_finiteAugmentedMass_ge_quarter_of_retentionMargin
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (retention : fullReplayFiniteMassRetentionMarginAt current modes)
    (time : Set.Icc (0 : Real) (wholeRestartDuration current.contact)) :
    currentFiniteEulerMassBase current modes / 4 ≤
      finiteAugmentedCoefficientMass modes
        (complexSharpSupportProjection modes
          (current.nextReceipt.wholePath time)) := by
  have ledger := fullReplayFiniteMass_retention_ledger
    current modes zeroNotMem time 1 (by norm_num)
  have holderNonneg :=
    fullReplayFiniteObservedHolderBudget_nonneg current modes
  have timeErrorLe :
      6 * time.1 * fullReplayFiniteObservedHolderBudget current modes ≤
        6 * wholeRestartDuration current.contact *
          fullReplayFiniteObservedHolderBudget current modes := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left time.2.2 (by norm_num)) holderNonneg
  have errorLeHalf :
      6 * wholeRestartDuration current.contact *
          fullReplayFiniteObservedHolderBudget current modes ≤
        currentFiniteEulerMassBase current modes / 2 := by
    unfold fullReplayFiniteMassRetentionMarginAt at retention
    linarith
  have actualErrorLe := timeErrorLe.trans errorLeHalf
  have projectionMass :
      finiteStateVorticityCoefficientEnstrophy modes
          (complexSharpSupportProjection modes
            (current.nextReceipt.wholePath time)) =
        finiteStateVorticityCoefficientEnstrophy modes
          (current.nextReceipt.wholePath time) :=
    finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection
      modes (current.nextReceipt.wholePath time)
  unfold currentFiniteEulerMassBase finiteAugmentedCoefficientMass
  rw [projectionMass]
  norm_num at ledger
  unfold currentFiniteEulerMassBase at actualErrorLe
  nlinarith [actualErrorLe]

/-- Exact finite endpoint ledger stopped at any time of the unchanged full
receipt.  The restriction is internal and does not create another contact
or scheduler. -/
theorem fullReceiptNetPowerPrefix_eq_finiteMass_sub_current
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (modes : Finset IntegerWavevector)
    (zeroNotMem : (0 : IntegerWavevector) ∉ modes)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    (∫ actual in (0 : Real)..time.1,
        actualProjectedWholeNetEnstrophyPower current.nextReceipt
          modes actual) =
      finiteStateVorticityCoefficientEnstrophy modes
          (current.nextReceipt.wholePath time) -
        finiteStateVorticityCoefficientEnstrophy modes
          current.contact.physicalState := by
  by_cases timeZero : time.1 = 0
  · have zeroTime :
        time =
          (⟨0, ⟨le_rfl,
            (wholeRestartDuration_pos current.contact).le⟩⟩ :
              Icc (0 : Real) (wholeRestartDuration current.contact)) :=
      Subtype.ext timeZero
    rw [zeroTime, intervalIntegral.integral_same,
      current.nextReceipt.wholePath_initial]
    ring
  · have timePos : 0 < time.1 :=
      lt_of_le_of_ne time.2.1 (Ne.symm timeZero)
    let restricted := restrictWholeContinuousMildSerrinReceipt
      timePos time.2.2 current.nextReceipt
    have stateEq : ∀ actual ∈ Set.Icc (0 : Real) time.1,
        (actualWholeProjectedTransversePath restricted actual).1 =
          (actualWholeProjectedTransversePath
            current.nextReceipt actual).1 := by
      intro actual actualMem
      change restricted.wholePath
          (Set.projIcc (0 : Real) time.1 timePos.le actual) =
        current.nextReceipt.wholePath
          (Set.projIcc (0 : Real)
            (wholeRestartDuration current.contact)
            (wholeRestartDuration_pos current.contact).le actual)
      rw [Set.projIcc_of_mem timePos.le actualMem]
      rw [Set.projIcc_of_mem
        (wholeRestartDuration_pos current.contact).le
        ⟨actualMem.1, actualMem.2.trans time.2.2⟩]
      rfl
    have powerEq : ∀ actual ∈ Set.Icc (0 : Real) time.1,
        actualProjectedWholeNetEnstrophyPower restricted modes actual =
          actualProjectedWholeNetEnstrophyPower
            current.nextReceipt modes actual := by
      intro actual actualMem
      unfold actualProjectedWholeNetEnstrophyPower
        actualProjectedWholeEnstrophyPower
        actualProjectedWholeViscousEnstrophyPower
      rw [stateEq actual actualMem]
    have integralEq :
        (∫ actual in (0 : Real)..time.1,
            actualProjectedWholeNetEnstrophyPower
              restricted modes actual) =
          ∫ actual in (0 : Real)..time.1,
            actualProjectedWholeNetEnstrophyPower
              current.nextReceipt modes actual := by
      apply intervalIntegral.integral_congr
      intro actual actualMem
      rw [Set.uIcc_of_le timePos.le] at actualMem
      exact powerEq actual actualMem
    have ledger :=
      actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
        restricted modes zeroNotMem
    rw [integralEq] at ledger
    have terminalEq :
        restricted.wholePath
            ⟨time.1, ⟨timePos.le, le_rfl⟩⟩ =
          current.nextReceipt.wholePath time := by
      rfl
    rw [terminalEq] at ledger
    exact ledger

/-- Positive normalized resolved work and the full-receipt native `L¹`
escrow retain at least half of the initial finite mass base on every prefix.
This removes the independent Hölder-retention premise: the same physical
power decomposition that pays the terminal debit also prevents retreat. -/
theorem fullReplay_finiteAugmentedMass_ge_half_of_normalizedWorkEulerMargin
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current tolerance ≤ radius)
    (floor : Real)
    (floorPos : 0 < floor)
    (margin :
      fullReplayNormalizedWorkEulerMarginAt current
        (wholeRestartModes radius) floor)
    (toleranceLe :
      tolerance.1 ≤
        (wholeVorticityEuclideanMass current.contact.physicalState + 1) / 8)
    (time : Icc (0 : Real) (wholeRestartDuration current.contact)) :
    currentFiniteEulerMassBase current (wholeRestartModes radius) / 2 ≤
      finiteAugmentedCoefficientMass (wholeRestartModes radius)
        (complexSharpSupportProjection (wholeRestartModes radius)
          (current.nextReceipt.wholePath time)) := by
  let modes := wholeRestartModes radius
  let receipt := current.nextReceipt
  let projectedState : Real → ComplexVorticityHilbertState := fun actual =>
    complexSharpSupportProjection modes
      (actualWholeProjectedTransversePath receipt actual).1
  let resolvedPower : Real → Real := fun actual =>
    2 * finiteGeneratorRealWork modes nu.coeff (projectedState actual)
  let nativePower : Real → Real :=
    actualNativeTurbulenceEnstrophyFluxPower receipt modes
  have resolvedContinuous : Continuous resolvedPower := by
    have stateContinuous : Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 :=
      continuous_subtype_val.comp
        (actualWholeProjectedTransversePath_continuous receipt)
    have projectedContinuous : Continuous projectedState := by
      have composed := (sharpSupportProjectionCLM modes).continuous.comp
        stateContinuous
      apply composed.congr
      intro actual
      exact sharpSupportProjectionCLM_apply modes
        (actualWholeProjectedTransversePath receipt actual).1
    exact ((finiteGeneratorRealWork_contDiff modes nu.coeff).continuous.comp
      projectedContinuous).const_mul 2
  have actualPowerContinuous :=
    actualProjectedWholeNetEnstrophyPower_continuous receipt modes
  have nativeEq : nativePower =
      actualProjectedWholeNetEnstrophyPower receipt modes - resolvedPower := by
    funext actual
    have split :=
      actualProjectedWholeNetEnstrophyPower_eq_resolvedGenerator_add_nativeFlux
        receipt modes actual
    dsimp only at split
    change
      actualProjectedWholeNetEnstrophyPower receipt modes actual =
        2 * (finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes
              (actualWholeProjectedTransversePath receipt actual).1) +
          nativeTurbulenceEnstrophyFlux modes
            (actualWholeProjectedTransversePath receipt actual).1) at split
    change
      actualNativeTurbulenceEnstrophyFluxPower receipt modes actual =
        actualProjectedWholeNetEnstrophyPower receipt modes actual -
          2 * finiteGeneratorRealWork modes nu.coeff
            (projectedState actual)
    unfold actualNativeTurbulenceEnstrophyFluxPower
    dsimp only
    linarith
  have nativeContinuous : Continuous nativePower := by
    rw [nativeEq]
    exact actualPowerContinuous.sub resolvedContinuous
  have resolvedNonneg : ∀ actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration current.contact), 0 ≤ resolvedPower actual := by
    intro actual actualMem
    let physicalTime : Icc (0 : Real)
        (wholeRestartDuration current.contact) := ⟨actual, actualMem⟩
    have stateEq :
        (actualWholeProjectedTransversePath receipt actual).1 =
          receipt.wholePath physicalTime := by
      change receipt.wholePath
          (Set.projIcc (0 : Real)
            (wholeRestartDuration current.contact)
            (wholeRestartDuration_pos current.contact).le actual) = _
      rw [Set.projIcc_of_mem
        (wholeRestartDuration_pos current.contact).le actualMem]
    have normalizedLower :=
      fullReplay_actualNormalizedWork_ge_floor_of_eulerMargin
        current modes
        (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
        floor margin physicalTime
    rw [← stateEq] at normalizedLower
    let base := finiteAugmentedCoefficientMass modes (projectedState actual)
    have basePos : 0 < base := by
      dsimp only [base, finiteAugmentedCoefficientMass]
      have massNonneg : 0 ≤
          finiteStateVorticityCoefficientEnstrophy modes
            (projectedState actual) := by
        unfold finiteStateVorticityCoefficientEnstrophy
        exact Finset.sum_nonneg fun wave _ =>
          complexCoordinateAmplitudeSq_nonneg _
      linarith
    have quotientPos :
        0 < finiteNormalizedGeneratorWork modes nu.coeff
          (projectedState actual) := floorPos.trans_le normalizedLower
    have workPos :
        0 < finiteGeneratorRealWork modes nu.coeff
          (projectedState actual) := by
      have quotientPos' :
          0 < finiteGeneratorRealWork modes nu.coeff
              (projectedState actual) /
            base ^ (5 / 4 : Real) := by
        simpa only [finiteNormalizedGeneratorWork, base] using quotientPos
      have multiplied :=
        (lt_div_iff₀ (Real.rpow_pos_of_pos basePos _)).mp quotientPos'
      simpa only [zero_mul] using multiplied
    dsimp only [resolvedPower]
    linarith
  have resolvedIntegralNonneg :
      0 ≤ ∫ actual in (0 : Real)..time.1, resolvedPower actual := by
    apply intervalIntegral.integral_nonneg time.2.1
    intro actual actualMem
    exact resolvedNonneg actual
      ⟨actualMem.1, actualMem.2.trans time.2.2⟩
  have integralCaptureLeJoint :
      currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance ≤
        currentFullReceiptResolvedCaptureRadius current tolerance :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have nativeSmall :=
    current_nextReceipt_nativeFluxPrefixWork_abs_lt_of_captureRadius_le
      current tolerance radius (integralCaptureLeJoint.trans captureLe) time
  change
    |∫ actual in (0 : Real)..time.1, nativePower actual| <
      2 * tolerance.1 at nativeSmall
  have nativeLower :
      -(2 * tolerance.1) <
        ∫ actual in (0 : Real)..time.1, nativePower actual :=
    (abs_lt.mp nativeSmall).1
  have splitIntegral :
      (∫ actual in (0 : Real)..time.1,
          actualProjectedWholeNetEnstrophyPower receipt modes actual) =
        (∫ actual in (0 : Real)..time.1, resolvedPower actual) +
          ∫ actual in (0 : Real)..time.1, nativePower actual := by
    rw [← intervalIntegral.integral_add
      (resolvedContinuous.intervalIntegrable _ _)
      (nativeContinuous.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro actual _actualMem
    have split :=
      actualProjectedWholeNetEnstrophyPower_eq_resolvedGenerator_add_nativeFlux
        receipt modes actual
    dsimp only at split
    change
      actualProjectedWholeNetEnstrophyPower receipt modes actual =
        2 * (finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes
              (actualWholeProjectedTransversePath receipt actual).1) +
          nativeTurbulenceEnstrophyFlux modes
            (actualWholeProjectedTransversePath receipt actual).1) at split
    dsimp only [resolvedPower, nativePower, projectedState]
    unfold actualNativeTurbulenceEnstrophyFluxPower
    dsimp only
    linarith
  have prefixLedger := fullReceiptNetPowerPrefix_eq_finiteMass_sub_current
    current modes (zero_not_mem_puncturedIntegerWaveFrequencyCube radius) time
  have finiteMassChangeLower :
      -(2 * tolerance.1) <
        finiteStateVorticityCoefficientEnstrophy modes
            (receipt.wholePath time) -
          finiteStateVorticityCoefficientEnstrophy modes
            current.contact.physicalState := by
    rw [splitIntegral] at prefixLedger
    linarith
  have wholeLtFiniteBase :=
    current_fullReceipt_wholeMass_lt_finiteMassBase_of_captureRadius_le
      current tolerance radius captureLe
  have finiteBaseOne : 1 ≤ currentFiniteEulerMassBase current modes := by
    unfold currentFiniteEulerMassBase
    have finiteNonneg : 0 ≤
        finiteStateVorticityCoefficientEnstrophy modes
          current.contact.physicalState := by
      unfold finiteStateVorticityCoefficientEnstrophy
      exact Finset.sum_nonneg fun wave _ =>
        complexCoordinateAmplitudeSq_nonneg _
    linarith
  have wholeBaseLtTwoFinite :
      wholeVorticityEuclideanMass current.contact.physicalState + 1 <
        2 * currentFiniteEulerMassBase current modes := by
    linarith
  have twiceToleranceLtHalfFinite :
      2 * tolerance.1 < currentFiniteEulerMassBase current modes / 2 := by
    have toleranceLtQuarterFinite :
        tolerance.1 < currentFiniteEulerMassBase current modes / 4 := by
      nlinarith
    linarith
  have projectionMass :
      finiteStateVorticityCoefficientEnstrophy modes
          (complexSharpSupportProjection modes
            (receipt.wholePath time)) =
        finiteStateVorticityCoefficientEnstrophy modes
          (receipt.wholePath time) :=
    finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection
      modes (receipt.wholePath time)
  unfold finiteAugmentedCoefficientMass currentFiniteEulerMassBase
  rw [projectionMass]
  dsimp only [modes, currentFiniteEulerMassBase]
    at twiceToleranceLtHalfFinite
  dsimp only [receipt, modes] at finiteMassChangeLower ⊢
  nlinarith

/-- Direct full-edge payment splice on the one joint source cube.  A
positive finite Euler margin pays resolved work throughout the base horizon;
the independently generated native settlement is then the only loss.  This
is a subordinate calculus theorem: the concrete producer must generate its
Euler margin internally. -/
private theorem current_fullReceipt_finiteMassDebit_ge_of_normalizedWorkEulerMargin_of_massRetention_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current tolerance ≤ radius)
    (floor : Real)
    (floorPos : 0 < floor)
    (margin :
      fullReplayNormalizedWorkEulerMarginAt current
        (wholeRestartModes radius) floor)
    (massRetention :
      ∀ time : Icc (0 : Real) (wholeRestartDuration current.contact),
        currentFiniteEulerMassBase current (wholeRestartModes radius) / 4 ≤
          finiteAugmentedCoefficientMass (wholeRestartModes radius)
            (complexSharpSupportProjection (wholeRestartModes radius)
              (current.nextReceipt.wholePath time))) :
    2 * (floor *
        (currentFiniteEulerMassBase current
          (wholeRestartModes radius) / 4) ^
            (5 / 4 : Real)) *
        wholeRestartDuration current.contact -
        2 * tolerance.1 ≤
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          (current.nextReceipt.wholePath
            ⟨wholeRestartDuration current.contact,
              ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩) -
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          current.contact.physicalState := by
  let modes := wholeRestartModes radius
  let receipt := current.nextReceipt
  let projectedState : Real → ComplexVorticityHilbertState := fun actual =>
    complexSharpSupportProjection modes
      (actualWholeProjectedTransversePath receipt actual).1
  let resolvedPower : Real → Real := fun actual =>
    2 * finiteGeneratorRealWork modes nu.coeff (projectedState actual)
  let nativePower : Real → Real :=
    actualNativeTurbulenceEnstrophyFluxPower receipt modes
  have resolvedContinuous : Continuous resolvedPower := by
    have stateContinuous : Continuous fun actual : Real =>
        (actualWholeProjectedTransversePath receipt actual).1 :=
      continuous_subtype_val.comp
        (actualWholeProjectedTransversePath_continuous receipt)
    have projectedContinuous : Continuous projectedState := by
      have composed := (sharpSupportProjectionCLM modes).continuous.comp
        stateContinuous
      apply composed.congr
      intro actual
      exact sharpSupportProjectionCLM_apply modes
        (actualWholeProjectedTransversePath receipt actual).1
    exact ((finiteGeneratorRealWork_contDiff modes nu.coeff).continuous.comp
      projectedContinuous).const_mul 2
  have resolvedIntegrable : IntervalIntegrable resolvedPower volume 0
      (wholeRestartDuration current.contact) :=
    resolvedContinuous.intervalIntegrable _ _
  have actualPowerContinuous :=
    actualProjectedWholeNetEnstrophyPower_continuous receipt modes
  have nativeEq : nativePower =
      actualProjectedWholeNetEnstrophyPower receipt modes - resolvedPower := by
    funext actual
    have split :=
      actualProjectedWholeNetEnstrophyPower_eq_resolvedGenerator_add_nativeFlux
        receipt modes actual
    dsimp only at split
    change
      actualProjectedWholeNetEnstrophyPower receipt modes actual =
        2 * (finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes
              (actualWholeProjectedTransversePath receipt actual).1) +
          nativeTurbulenceEnstrophyFlux modes
            (actualWholeProjectedTransversePath receipt actual).1) at split
    change
      actualNativeTurbulenceEnstrophyFluxPower receipt modes actual =
        actualProjectedWholeNetEnstrophyPower receipt modes actual -
          2 * finiteGeneratorRealWork modes nu.coeff
            (projectedState actual)
    unfold actualNativeTurbulenceEnstrophyFluxPower
    dsimp only
    linarith
  have nativeIntegrable : IntervalIntegrable nativePower volume 0
      (wholeRestartDuration current.contact) := by
    rw [nativeEq]
    exact (actualPowerContinuous.intervalIntegrable _ _).sub
      resolvedIntegrable
  have resolvedPointwise : ∀ actual ∈ Set.Icc (0 : Real)
      (wholeRestartDuration current.contact),
      2 * (floor *
        (currentFiniteEulerMassBase current modes / 4) ^
          (5 / 4 : Real)) ≤ resolvedPower actual := by
    intro actual actualMem
    let time : Set.Icc (0 : Real)
        (wholeRestartDuration current.contact) := ⟨actual, actualMem⟩
    have stateEq :
        (actualWholeProjectedTransversePath receipt actual).1 =
          receipt.wholePath time := by
      change receipt.wholePath
          (Set.projIcc (0 : Real)
            (wholeRestartDuration current.contact)
            (wholeRestartDuration_pos current.contact).le actual) = _
      rw [Set.projIcc_of_mem
        (wholeRestartDuration_pos current.contact).le actualMem]
    have normalizedLower :=
      fullReplay_actualNormalizedWork_ge_floor_of_eulerMargin
        current modes
        (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
        floor margin time
    rw [← stateEq] at normalizedLower
    let base := finiteAugmentedCoefficientMass modes (projectedState actual)
    have baseOne : 1 ≤ base := by
      dsimp only [base, finiteAugmentedCoefficientMass]
      have massNonneg : 0 ≤
          finiteStateVorticityCoefficientEnstrophy modes
            (projectedState actual) := by
        unfold finiteStateVorticityCoefficientEnstrophy
        exact Finset.sum_nonneg fun wave _ =>
          complexCoordinateAmplitudeSq_nonneg _
      linarith
    have basePos : 0 < base := lt_of_lt_of_le (by norm_num) baseOne
    have normalizedPayment :
        floor * base ^ (5 / 4 : Real) ≤
          finiteGeneratorRealWork modes nu.coeff (projectedState actual) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos basePos _)).mp
      simpa only [finiteNormalizedGeneratorWork, base,
        projectedState] using normalizedLower
    have retained := massRetention time
    have baseLower :
        currentFiniteEulerMassBase current modes / 4 ≤ base := by
      rw [← stateEq] at retained
      simpa only [base, projectedState] using retained
    have quarterNonneg :
        0 ≤ currentFiniteEulerMassBase current modes / 4 :=
      (div_nonneg (currentFiniteEulerMassBase_pos current modes).le
        (by norm_num))
    have powerLower :
        (currentFiniteEulerMassBase current modes / 4) ^
            (5 / 4 : Real) ≤
          base ^ (5 / 4 : Real) :=
      Real.rpow_le_rpow quarterNonneg baseLower (by norm_num)
    have floorBaseLeWork :
        floor *
            (currentFiniteEulerMassBase current modes / 4) ^
              (5 / 4 : Real) ≤
          finiteGeneratorRealWork modes nu.coeff
            (projectedState actual) :=
      (mul_le_mul_of_nonneg_left powerLower floorPos.le).trans
        normalizedPayment
    dsimp only [resolvedPower]
    linarith
  have resolvedIntegralLower := intervalIntegral.integral_mono_on
    (μ := volume) (wholeRestartDuration_pos current.contact).le
    (continuous_const.intervalIntegrable 0
      (wholeRestartDuration current.contact))
    resolvedIntegrable resolvedPointwise
  have resolvedPayment :
      2 * (floor *
          (currentFiniteEulerMassBase current modes / 4) ^
            (5 / 4 : Real)) *
          wholeRestartDuration current.contact ≤
        ∫ actual in (0 : Real)..wholeRestartDuration current.contact,
          resolvedPower actual := by
    simpa [intervalIntegral.integral_const, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using resolvedIntegralLower
  have integralCaptureLeJoint :
      currentNextReceiptNativeFluxIntegralCaptureRadius current tolerance ≤
        currentFullReceiptResolvedCaptureRadius current tolerance :=
    (le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have nativeSmall :=
    current_nextReceipt_nativeFluxWork_abs_lt_of_captureRadius_le
      current tolerance radius (integralCaptureLeJoint.trans captureLe)
  change
    |actualNativeTurbulenceEnstrophyFluxWork receipt modes| <
      2 * tolerance.1 at nativeSmall
  have nativeLower :
      -(2 * tolerance.1) <
        ∫ actual in (0 : Real)..wholeRestartDuration current.contact,
          nativePower actual := by
    have lower := (abs_lt.mp nativeSmall).1
    simpa only [actualNativeTurbulenceEnstrophyFluxWork, nativePower]
      using lower
  have splitIntegral :
      (∫ actual in (0 : Real)..wholeRestartDuration current.contact,
          actualProjectedWholeNetEnstrophyPower receipt modes actual) =
        (∫ actual in (0 : Real)..wholeRestartDuration current.contact,
          resolvedPower actual) +
        ∫ actual in (0 : Real)..wholeRestartDuration current.contact,
          nativePower actual := by
    rw [← intervalIntegral.integral_add resolvedIntegrable nativeIntegrable]
    apply intervalIntegral.integral_congr
    intro actual _actualMem
    have split :=
      actualProjectedWholeNetEnstrophyPower_eq_resolvedGenerator_add_nativeFlux
        receipt modes actual
    dsimp only at split
    change
      actualProjectedWholeNetEnstrophyPower receipt modes actual =
        2 * (finiteGeneratorRealWork modes nu.coeff
            (complexSharpSupportProjection modes
              (actualWholeProjectedTransversePath receipt actual).1) +
          nativeTurbulenceEnstrophyFlux modes
            (actualWholeProjectedTransversePath receipt actual).1) at split
    dsimp only [resolvedPower, nativePower, projectedState]
    unfold actualNativeTurbulenceEnstrophyFluxPower
    dsimp only
    linarith
  have endpointLedger :=
    actualProjectedWholeNetEnstrophyPower_integral_eq_terminal_sub_initial
      receipt modes
        (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
  rw [splitIntegral] at endpointLedger
  change _ ≤ _
  rw [← endpointLedger]
  nlinarith

/-- Compatibility mouth using the earlier Hölder retention condition. -/
theorem current_fullReceipt_finiteMassDebit_ge_of_normalizedWorkEulerMargin_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current tolerance ≤ radius)
    (floor : Real)
    (floorPos : 0 < floor)
    (margin :
      fullReplayNormalizedWorkEulerMarginAt current
        (wholeRestartModes radius) floor)
    (retention :
      fullReplayFiniteMassRetentionMarginAt current
        (wholeRestartModes radius)) :
    2 * (floor *
        (currentFiniteEulerMassBase current
          (wholeRestartModes radius) / 4) ^
            (5 / 4 : Real)) *
        wholeRestartDuration current.contact -
        2 * tolerance.1 ≤
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          (current.nextReceipt.wholePath
            ⟨wholeRestartDuration current.contact,
              ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩) -
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          current.contact.physicalState := by
  apply
    current_fullReceipt_finiteMassDebit_ge_of_normalizedWorkEulerMargin_of_massRetention_of_captureRadius_le
      current tolerance radius captureLe floor floorPos margin
  intro time
  exact fullReplay_finiteAugmentedMass_ge_quarter_of_retentionMargin
    current (wholeRestartModes radius)
      (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
      retention time

/-- Stronger full-edge finite payment: the same normalized-work margin and
native prefix escrow generate mass retention internally. -/
theorem current_fullReceipt_finiteMassDebit_ge_of_normalizedWorkEulerMargin_of_captureRadius_le_withoutRetention
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current tolerance ≤ radius)
    (floor : Real)
    (floorPos : 0 < floor)
    (margin :
      fullReplayNormalizedWorkEulerMarginAt current
        (wholeRestartModes radius) floor)
    (toleranceLe :
      tolerance.1 ≤
        (wholeVorticityEuclideanMass current.contact.physicalState + 1) / 8) :
    2 * (floor *
        (currentFiniteEulerMassBase current
          (wholeRestartModes radius) / 4) ^
            (5 / 4 : Real)) *
        wholeRestartDuration current.contact -
        2 * tolerance.1 ≤
      finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          (current.nextReceipt.wholePath
            ⟨wholeRestartDuration current.contact,
              ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩) -
        finiteStateVorticityCoefficientEnstrophy
          (wholeRestartModes radius)
          current.contact.physicalState := by
  apply
    current_fullReceipt_finiteMassDebit_ge_of_normalizedWorkEulerMargin_of_massRetention_of_captureRadius_le
      current tolerance radius captureLe floor floorPos margin
  intro time
  have halfRetained :=
    fullReplay_finiteAugmentedMass_ge_half_of_normalizedWorkEulerMargin
      current tolerance radius captureLe floor floorPos margin toleranceLe time
  have baseNonneg :
      0 ≤ currentFiniteEulerMassBase current (wholeRestartModes radius) :=
    (currentFiniteEulerMassBase_pos current (wholeRestartModes radius)).le
  linarith

/-- The identical source cube converts the finite terminal payment into the
complete fixed-terminal debit.  The terminal complement is nonnegative and
the current complement is below the same source tolerance, so the only new
loss is one additional tolerance; no later selected contact or moving
inventory is involved. -/
theorem current_fullReceipt_terminalNetEnstrophyDebit_ge_of_normalizedWorkEulerMargin_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current tolerance ≤ radius)
    (floor : Real)
    (floorPos : 0 < floor)
    (margin :
      fullReplayNormalizedWorkEulerMarginAt current
        (wholeRestartModes radius) floor)
    (retention :
      fullReplayFiniteMassRetentionMarginAt current
        (wholeRestartModes radius)) :
    2 * (floor *
        (currentFiniteEulerMassBase current
          (wholeRestartModes radius) / 4) ^
            (5 / 4 : Real)) *
        wholeRestartDuration current.contact -
        3 * tolerance.1 ≤
      generatedWholeRestartTerminalNetEnstrophyDebit
        (generatedWholeRestartCanonicalReplay current.contact) := by
  let modes := wholeRestartModes radius
  let terminalState := current.nextReceipt.wholePath
    ⟨wholeRestartDuration current.contact,
      ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩
  have finiteDebit :=
    current_fullReceipt_finiteMassDebit_ge_of_normalizedWorkEulerMargin_of_captureRadius_le
      current tolerance radius captureLe floor floorPos margin retention
  have initialTail :
      wholeTailVorticityMass modes current.contact.physicalState <
        tolerance.1 := by
    simpa only [modes] using
      current_fullReceipt_initialTail_lt_of_captureRadius_le
        current tolerance radius captureLe
  have terminalTailNonneg :
      0 ≤ wholeTailVorticityMass modes terminalState :=
    wholeTailVorticityMass_nonneg modes terminalState
  have initialSplit :=
    wholeVorticityEuclideanMass_eq_finite_add_tail modes
      current.contact.physicalState
  have terminalSplit :=
    wholeVorticityEuclideanMass_eq_finite_add_tail modes terminalState
  change
    2 * (floor *
        (currentFiniteEulerMassBase current modes / 4) ^
          (5 / 4 : Real)) *
        wholeRestartDuration current.contact -
        3 * tolerance.1 ≤
      wholeVorticityEuclideanMass terminalState -
        wholeVorticityEuclideanMass current.contact.physicalState
  rw [terminalSplit, initialSplit]
  nlinarith

/-- Full-terminal form with mass retention generated by the same normalized
work/native prefix ledger. -/
theorem current_fullReceipt_terminalNetEnstrophyDebit_ge_of_normalizedWorkEulerMargin_of_captureRadius_le_withoutRetention
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (tolerance : {value : Real // 0 < value})
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current tolerance ≤ radius)
    (floor : Real)
    (floorPos : 0 < floor)
    (margin :
      fullReplayNormalizedWorkEulerMarginAt current
        (wholeRestartModes radius) floor)
    (toleranceLe :
      tolerance.1 ≤
        (wholeVorticityEuclideanMass current.contact.physicalState + 1) / 8) :
    2 * (floor *
        (currentFiniteEulerMassBase current
          (wholeRestartModes radius) / 4) ^
            (5 / 4 : Real)) *
        wholeRestartDuration current.contact -
        3 * tolerance.1 ≤
      generatedWholeRestartTerminalNetEnstrophyDebit
        (generatedWholeRestartCanonicalReplay current.contact) := by
  let modes := wholeRestartModes radius
  let terminalState := current.nextReceipt.wholePath
    ⟨wholeRestartDuration current.contact,
      ⟨(wholeRestartDuration_pos current.contact).le, le_rfl⟩⟩
  have finiteDebit :=
    current_fullReceipt_finiteMassDebit_ge_of_normalizedWorkEulerMargin_of_captureRadius_le_withoutRetention
      current tolerance radius captureLe floor floorPos margin toleranceLe
  have initialTail :
      wholeTailVorticityMass modes current.contact.physicalState <
        tolerance.1 := by
    simpa only [modes] using
      current_fullReceipt_initialTail_lt_of_captureRadius_le
        current tolerance radius captureLe
  have terminalTailNonneg :
      0 ≤ wholeTailVorticityMass modes terminalState :=
    wholeTailVorticityMass_nonneg modes terminalState
  have initialSplit :=
    wholeVorticityEuclideanMass_eq_finite_add_tail modes
      current.contact.physicalState
  have terminalSplit :=
    wholeVorticityEuclideanMass_eq_finite_add_tail modes terminalState
  change
    2 * (floor *
        (currentFiniteEulerMassBase current modes / 4) ^
          (5 / 4 : Real)) *
        wholeRestartDuration current.contact -
        3 * tolerance.1 ≤
      wholeVorticityEuclideanMass terminalState -
        wholeVorticityEuclideanMass current.contact.physicalState
  rw [terminalSplit, initialSplit]
  nlinarith

/-! ## Source-selected scale-relative terminal payment -/

/-- The residence exponent read from a `5/4` normalized-work payment and
the seventh-order source clock. -/
def fullReceiptRetainedResidenceExponent : Real := 27 / 4

/-- The fixed viscosity-dependent charge retained before the three source
tolerance losses are paid. -/
def fullReceiptRetainedCharge
    (nu : Viscosity)
    (floor : Real) : Real :=
  floor * (1 / 4 : Real) ^ (5 / 4 : Real) /
    (sourceOwnedWholeStateBarrierSeventhCoefficientUpper nu * 4 ^ 7)

theorem fullReceiptRetainedCharge_pos
    (nu : Viscosity)
    {floor : Real}
    (floorPos : 0 < floor) :
    0 < fullReceiptRetainedCharge nu floor := by
  unfold fullReceiptRetainedCharge
  exact div_pos
    (mul_pos floorPos (Real.rpow_pos_of_pos (by norm_num) _))
    (mul_pos
      (sourceOwnedWholeStateBarrierSeventhCoefficientUpper_pos nu)
      (by norm_num))

/-- Exact algebraic factorization of the retained charge through the
finite mass base and the seventh-order duration lower model. -/
private theorem fullReceiptRetainedCharge_div_massBase_eq_model
    (nu : Viscosity)
    (floor base : Real)
    (basePos : 0 < base) :
    fullReceiptRetainedCharge nu floor /
        base ^ (23 / 4 : Real) =
      2 * (floor * (base / 4) ^ (5 / 4 : Real)) *
        (1 /
          (2 * sourceOwnedWholeStateBarrierSeventhCoefficientUpper nu *
            (4 * base) ^ 7)) := by
  have upperNe :
      sourceOwnedWholeStateBarrierSeventhCoefficientUpper nu ≠ 0 :=
    (sourceOwnedWholeStateBarrierSeventhCoefficientUpper_pos nu).ne'
  have baseRpowNe : base ^ (5 / 4 : Real) ≠ 0 :=
    (Real.rpow_pos_of_pos basePos _).ne'
  have fourRpowNe : (4 : Real) ^ (5 / 4 : Real) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have baseNe : base ≠ 0 := basePos.ne'
  unfold fullReceiptRetainedCharge
  rw [Real.div_rpow basePos.le (by norm_num : (0 : Real) ≤ 4)]
  rw [show base ^ (23 / 4 : Real) =
      base ^ (7 : Real) / base ^ (5 / 4 : Real) by
    rw [← Real.rpow_sub basePos]
    norm_num]
  rw [show (1 / 4 : Real) ^ (5 / 4 : Real) =
      1 / (4 : Real) ^ (5 / 4 : Real) by
    rw [Real.div_rpow (by norm_num : (0 : Real) ≤ 1)
      (by norm_num : (0 : Real) ≤ 4)]
    simp]
  rw [show (4 * base) ^ 7 = 4 ^ 7 * base ^ 7 by ring]
  field_simp [upperNe, baseNe, baseRpowNe, fourRpowNe]
  congr 1
  exact (Real.rpow_natCast base 7).symm

/-- Tolerance generated from the current whole mass and the fixed retained
charge.  It is selected before the joint radius, so no circular dependence
on the chosen finite inventory is possible. -/
def currentFullReceiptScaleTolerance
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (floor : Real)
    (floorPos : 0 < floor) : {value : Real // 0 < value} :=
  ⟨min
      (fullReceiptRetainedCharge nu floor /
        (6 *
          (wholeVorticityEuclideanMass current.contact.physicalState + 1) ^
            (fullReceiptRetainedResidenceExponent - 1)))
      (min
        ((wholeVorticityEuclideanMass current.contact.physicalState + 1) / 8)
        (floor *
          (wholeVorticityEuclideanMass current.contact.physicalState + 1) ^
            (5 / 4 : Real) / 12)), by
    have wholeMassNonneg :
        0 ≤ wholeVorticityEuclideanMass
          current.contact.physicalState := by
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
    have wholeBasePos :
        0 < wholeVorticityEuclideanMass
            current.contact.physicalState + 1 := by
      linarith
    exact lt_min
      (div_pos (fullReceiptRetainedCharge_pos nu floorPos)
        (mul_pos (by norm_num)
          (Real.rpow_pos_of_pos wholeBasePos _)))
      (lt_min
        (div_pos wholeBasePos (by norm_num))
        (div_pos
          (mul_pos floorPos (Real.rpow_pos_of_pos wholeBasePos _))
          (by norm_num)))⟩

/-- Positive normalized-work floor computed from the complete instantaneous
whole power of this exact current.  The proof parameter only certifies the
source value's sign; no finite inventory enters the definition. -/
def currentGeneratedWholeWorkFloor
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (_wholePowerPos : 0 < currentInstantaneousWholePower current) : Real :=
  currentInstantaneousWholePower current /
    (4 *
      (wholeVorticityEuclideanMass current.contact.physicalState + 1) ^
        (5 / 4 : Real))

theorem currentGeneratedWholeWorkFloor_pos
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wholePowerPos : 0 < currentInstantaneousWholePower current) :
    0 < currentGeneratedWholeWorkFloor current wholePowerPos := by
  have wholeMassNonneg :
      0 ≤ wholeVorticityEuclideanMass current.contact.physicalState := by
    unfold wholeVorticityEuclideanMass
    exact tsum_nonneg fun wave => sq_nonneg _
  unfold currentGeneratedWholeWorkFloor
  exact div_pos wholePowerPos
    (mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (by linarith) _))

/-- Complete whole-work headroom is faithfully projected to the source-
generated joint cube at `time = 0`.  This closes the first half of the
normalized-work Euler margin without choosing a finite carrier or accepting
its seed as a premise. -/
theorem current_fullReceiptNormalizedWorkEulerMargin_seed_of_wholePower_pos
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (wholePowerPos : 0 < currentInstantaneousWholePower current) :
    let floor := currentGeneratedWholeWorkFloor current wholePowerPos
    let tolerance :=
      currentFullReceiptScaleTolerance current floor
        (currentGeneratedWholeWorkFloor_pos current wholePowerPos)
    floor ≤
      finiteNormalizedGeneratorWork
        (currentFullReceiptResolvedCaptureModes current tolerance)
        nu.coeff
        (complexSharpSupportProjection
          (currentFullReceiptResolvedCaptureModes current tolerance)
          current.contact.physicalState) := by
  let wholePower := currentInstantaneousWholePower current
  let wholeBase :=
    wholeVorticityEuclideanMass current.contact.physicalState + 1
  let floor := currentGeneratedWholeWorkFloor current wholePowerPos
  have floorPos : 0 < floor := by
    simpa only [floor] using
      currentGeneratedWholeWorkFloor_pos current wholePowerPos
  let tolerance := currentFullReceiptScaleTolerance current floor floorPos
  let modes := currentFullReceiptResolvedCaptureModes current tolerance
  let finiteBase := currentFiniteEulerMassBase current modes
  have wholeBasePos : 0 < wholeBase := by
    dsimp only [wholeBase]
    have wholeMassNonneg :
        0 ≤ wholeVorticityEuclideanMass current.contact.physicalState := by
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
    linarith
  have finiteBasePos : 0 < finiteBase := by
    simpa only [finiteBase] using currentFiniteEulerMassBase_pos current modes
  have finiteBaseLeWholeBase : finiteBase ≤ wholeBase := by
    dsimp only [finiteBase, wholeBase, currentFiniteEulerMassBase]
    gcongr
    exact finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      modes current.contact.physicalState
  have finitePowerLeWholePower :
      finiteBase ^ (5 / 4 : Real) ≤ wholeBase ^ (5 / 4 : Real) :=
    Real.rpow_le_rpow finiteBasePos.le finiteBaseLeWholeBase (by norm_num)
  have wholePowerFactorization :
      wholePower = 4 * floor * wholeBase ^ (5 / 4 : Real) := by
    have wholePowNe : wholeBase ^ (5 / 4 : Real) ≠ 0 :=
      (Real.rpow_pos_of_pos wholeBasePos _).ne'
    change
      currentInstantaneousWholePower current =
        4 *
          (currentInstantaneousWholePower current /
            (4 * wholeBase ^ (5 / 4 : Real))) *
          wholeBase ^ (5 / 4 : Real)
    field_simp [wholePowNe]
  have toleranceWorkLe :
      tolerance.1 ≤ floor * wholeBase ^ (5 / 4 : Real) / 12 := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have close :=
    current_fullReceipt_wholePower_sub_two_resolved_abs_lt
      current tolerance
  change
    |wholePower -
        2 * finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes
            current.contact.physicalState)| <
      3 * tolerance.1 at close
  have resolvedLower := (abs_lt.mp close).2
  have floorWholePowerNonneg :
      0 ≤ floor * wholeBase ^ (5 / 4 : Real) :=
    (mul_pos floorPos (Real.rpow_pos_of_pos wholeBasePos _)).le
  have floorFiniteLeResolved :
      floor * finiteBase ^ (5 / 4 : Real) ≤
        finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes
            current.contact.physicalState) := by
    have floorFiniteLeWhole :
        floor * finiteBase ^ (5 / 4 : Real) ≤
          floor * wholeBase ^ (5 / 4 : Real) :=
      mul_le_mul_of_nonneg_left finitePowerLeWholePower floorPos.le
    rw [wholePowerFactorization] at resolvedLower
    nlinarith
  have normalizedSeed : floor ≤
      finiteGeneratorRealWork modes nu.coeff
          (complexSharpSupportProjection modes
            current.contact.physicalState) /
        finiteBase ^ (5 / 4 : Real) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos finiteBasePos _)).2
      floorFiniteLeResolved
  have finiteBaseEq :
      finiteAugmentedCoefficientMass modes
          (complexSharpSupportProjection modes
            current.contact.physicalState) = finiteBase := by
    unfold finiteAugmentedCoefficientMass finiteBase
      currentFiniteEulerMassBase
    rw [finiteStateVorticityCoefficientEnstrophy_sharpSupportProjection]
  dsimp only
  unfold finiteNormalizedGeneratorWork
  rw [finiteBaseEq]
  exact normalizedSeed

/-- Once the concrete source generates the finite normalized-work Euler
margin on the
joint current-owned cube, every other coordinate is eliminated internally:
the seventh-order horizon, finite payment, native work, initial tail and
whole-terminal projection yield a scale-relative terminal debit.  Modes,
tolerance, radius and payment are all conclusions of this theorem. -/
theorem current_fullReceipt_scaleRelativeTerminalDebit_of_generatedMargin_of_captureRadius_le
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (floor : Real)
    (floorPos : 0 < floor)
    (radius : Nat)
    (captureLe :
      currentFullReceiptResolvedCaptureRadius current
          (currentFullReceiptScaleTolerance current floor floorPos) ≤ radius)
    (margin : fullReplayNormalizedWorkEulerMarginAt current
      (wholeRestartModes radius) floor) :
    (fullReceiptRetainedCharge nu floor / 2) /
        (wholeVorticityEuclideanMass current.contact.physicalState + 1) ^
          (fullReceiptRetainedResidenceExponent - 1) ≤
      generatedWholeRestartTerminalNetEnstrophyDebit
        (generatedWholeRestartCanonicalReplay current.contact) := by
  let charge := fullReceiptRetainedCharge nu floor
  let exponent := fullReceiptRetainedResidenceExponent - 1
  let wholeBase :=
    wholeVorticityEuclideanMass current.contact.physicalState + 1
  let tolerance := currentFullReceiptScaleTolerance current floor floorPos
  let modes := wholeRestartModes radius
  let finiteBase := currentFiniteEulerMassBase current modes
  let ceiling := wholeRestartCoefficientCeiling current.contact
  let upper := sourceOwnedWholeStateBarrierSeventhCoefficientUpper nu
  change fullReplayNormalizedWorkEulerMarginAt current modes floor at margin
  have chargePos : 0 < charge := by
    simpa only [charge] using fullReceiptRetainedCharge_pos nu floorPos
  have exponentPos : 0 < exponent := by
    dsimp only [exponent, fullReceiptRetainedResidenceExponent]
    norm_num
  have exponentEq : exponent = (23 / 4 : Real) := by
    dsimp only [exponent, fullReceiptRetainedResidenceExponent]
    norm_num
  have wholeBasePos : 0 < wholeBase := by
    have wholeMassNonneg :
        0 ≤ wholeVorticityEuclideanMass
          current.contact.physicalState := by
      unfold wholeVorticityEuclideanMass
      exact tsum_nonneg fun wave => sq_nonneg _
    dsimp only [wholeBase]
    linarith
  have finiteBasePos : 0 < finiteBase := by
    simpa only [finiteBase, modes] using
      currentFiniteEulerMassBase_pos current (wholeRestartModes radius)
  have ceilingPos : 0 < ceiling := by
    simpa only [ceiling] using
      wholeRestartCoefficientCeiling_pos current.contact
  have upperPos : 0 < upper := by
    simpa only [upper] using
      sourceOwnedWholeStateBarrierSeventhCoefficientUpper_pos nu
  have coverage : ceiling + 1 ≤ 4 * finiteBase := by
    simpa only [ceiling, finiteBase, modes] using
      current_fullReceipt_ceiling_add_one_le_four_mul_finiteMassBase_of_captureRadius_le
        current tolerance radius captureLe
  have seventhCovered : (ceiling + 1) ^ 7 ≤ (4 * finiteBase) ^ 7 :=
    pow_le_pow_left₀ (by positivity) coverage 7
  have barrierUpper :
      sourceOwnedWholeStateBarrierSlope nu ceiling ≤
        upper * (4 * finiteBase) ^ 7 := by
    have generatedUpper := sourceOwnedWholeStateBarrierSlope_le_seventhUpper
      nu ceiling ceilingPos.le
    exact generatedUpper.trans
      (mul_le_mul_of_nonneg_left seventhCovered upperPos.le)
  have durationLower :
      1 / (2 * upper * (4 * finiteBase) ^ 7) ≤
        wholeRestartDuration current.contact := by
    have denominatorLe :
        2 * sourceOwnedWholeStateBarrierSlope nu ceiling ≤
          2 * upper * (4 * finiteBase) ^ 7 := by nlinarith
    have denominatorPos :
        0 < 2 * sourceOwnedWholeStateBarrierSlope nu ceiling :=
      mul_pos (by norm_num)
        (sourceOwnedWholeStateBarrierSlope_pos nu ceiling)
    change
      1 / (2 * upper * (4 * finiteBase) ^ 7) ≤
        1 / (2 * sourceOwnedWholeStateBarrierSlope nu ceiling)
    simpa only [one_div] using
      (one_div_le_one_div_of_le denominatorPos denominatorLe)
  have modelFactorization :
      charge / finiteBase ^ exponent =
        2 * (floor * (finiteBase / 4) ^ (5 / 4 : Real)) *
          (1 / (2 * upper * (4 * finiteBase) ^ 7)) := by
    rw [exponentEq]
    simpa only [charge, upper] using
      fullReceiptRetainedCharge_div_massBase_eq_model
        nu floor finiteBase finiteBasePos
  have workCoefficientNonneg :
      0 ≤ 2 * (floor * (finiteBase / 4) ^ (5 / 4 : Real)) := by
    exact (mul_pos (by norm_num)
      (mul_pos floorPos
        (Real.rpow_pos_of_pos (div_pos finiteBasePos (by norm_num)) _))).le
  have finiteModelLower :
      charge / finiteBase ^ exponent ≤
        2 * (floor * (finiteBase / 4) ^ (5 / 4 : Real)) *
          wholeRestartDuration current.contact := by
    rw [modelFactorization]
    exact mul_le_mul_of_nonneg_left durationLower workCoefficientNonneg
  have finiteBaseLeWholeBase : finiteBase ≤ wholeBase := by
    dsimp only [finiteBase, wholeBase, modes,
      currentFiniteEulerMassBase]
    gcongr
    exact finiteStateVorticityCoefficientEnstrophy_le_wholeMass
      (wholeRestartModes radius) current.contact.physicalState
  have denominatorLe : finiteBase ^ exponent ≤ wholeBase ^ exponent :=
    Real.rpow_le_rpow finiteBasePos.le finiteBaseLeWholeBase exponentPos.le
  have finiteDenominatorPos : 0 < finiteBase ^ exponent :=
    Real.rpow_pos_of_pos finiteBasePos _
  have wholeDenominatorPos : 0 < wholeBase ^ exponent :=
    Real.rpow_pos_of_pos wholeBasePos _
  have wholeChargeLeFiniteCharge :
      charge / wholeBase ^ exponent ≤ charge / finiteBase ^ exponent :=
    (div_le_div_iff₀ wholeDenominatorPos finiteDenominatorPos).2
      (mul_le_mul_of_nonneg_left denominatorLe chargePos.le)
  have wholeModelLower :
      charge / wholeBase ^ exponent ≤
        2 * (floor * (finiteBase / 4) ^ (5 / 4 : Real)) *
          wholeRestartDuration current.contact :=
    wholeChargeLeFiniteCharge.trans finiteModelLower
  have toleranceMassLe :
      tolerance.1 ≤
        (wholeVorticityEuclideanMass current.contact.physicalState + 1) / 8 := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have terminalLower :=
    current_fullReceipt_terminalNetEnstrophyDebit_ge_of_normalizedWorkEulerMargin_of_captureRadius_le_withoutRetention
      current tolerance radius captureLe floor floorPos
      margin toleranceMassLe
  have toleranceScaleLe :
      tolerance.1 ≤ charge / (6 * wholeBase ^ exponent) := by
    exact min_le_left _ _
  change
    (charge / 2) / wholeBase ^ exponent ≤
      generatedWholeRestartTerminalNetEnstrophyDebit
        (generatedWholeRestartCanonicalReplay current.contact)
  change
    2 * (floor * (finiteBase / 4) ^ (5 / 4 : Real)) *
          wholeRestartDuration current.contact -
        3 * tolerance.1 ≤
      generatedWholeRestartTerminalNetEnstrophyDebit
        (generatedWholeRestartCanonicalReplay current.contact)
    at terminalLower
  have targetEq :
      (charge / 2) / wholeBase ^ exponent =
        (charge / wholeBase ^ exponent) / 2 := by ring
  have scaleToleranceLossEq :
      3 * (charge / (6 * wholeBase ^ exponent)) =
        (charge / wholeBase ^ exponent) / 2 := by
    field_simp [wholeDenominatorPos.ne']
    norm_num
  have toleranceLossLe :
      3 * tolerance.1 ≤ (charge / wholeBase ^ exponent) / 2 := by
    calc
      3 * tolerance.1 ≤
          3 * (charge / (6 * wholeBase ^ exponent)) :=
        mul_le_mul_of_nonneg_left toleranceScaleLe (by norm_num)
      _ = (charge / wholeBase ^ exponent) / 2 := scaleToleranceLossEq
  rw [targetEq]
  nlinarith

/-- Canonical-radius specialization retained for the source-first public
consumer. -/
theorem current_fullReceipt_scaleRelativeTerminalDebit_of_generatedMargin
    {nu : Viscosity}
    (current : GeneratedWholeRestartCurrent nu)
    (floor : Real)
    (floorPos : 0 < floor)
    (margin :
      let tolerance :=
        currentFullReceiptScaleTolerance current floor floorPos
      fullReplayNormalizedWorkEulerMarginAt current
        (currentFullReceiptResolvedCaptureModes current tolerance) floor) :
    (fullReceiptRetainedCharge nu floor / 2) /
        (wholeVorticityEuclideanMass current.contact.physicalState + 1) ^
          (fullReceiptRetainedResidenceExponent - 1) ≤
      generatedWholeRestartTerminalNetEnstrophyDebit
        (generatedWholeRestartCanonicalReplay current.contact) := by
  let tolerance := currentFullReceiptScaleTolerance current floor floorPos
  exact
    current_fullReceipt_scaleRelativeTerminalDebit_of_generatedMargin_of_captureRadius_le
      current floor floorPos
      (currentFullReceiptResolvedCaptureRadius current tolerance) le_rfl
      (by simpa only [currentFullReceiptResolvedCaptureModes, tolerance]
        using margin)

end
end ThreeDimensionalVorticityCoefficientFullReceiptNormalizedWorkEulerEscrow
end NavierStokes
end SaturationMonoid
