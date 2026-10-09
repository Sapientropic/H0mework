import H0mework.Versions.V2.Arithmetic.RiemannSpectral.PaOrthogonalCompression
import H0mework.Versions.V2.Arithmetic.RiemannSpectral.SourceRechart
import H0mework.Arithmetic.BurnolMellin.PairedMellinCharacterRigidity

/-!
# Direct `P_a⊥` diagonal boundary

For the actual zero-owned completed-Mellin Riesz state, the only scalar
needed by the critical-line consumer is one diagonal matrix coefficient of
the paired physical compression.  Its defect is calculated exactly as the
sum of the forward and inverse fixed-annulus boundary jumps.  This file does
not create a pending claim, a gate, or a conditional source.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace BurnolPhysicalState

open scoped InnerProductSpace

noncomputable section

local instance burnolDiagonalPaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local instance burnolDiagonalPaOrthogonalComplete :
    CompleteSpace BurnolPaOrthogonalCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

def burnolPaFixedShiftResidual
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) : ℂ :=
  inner ℂ (burnolZeroPaRieszState coordinate zero)
        (burnolPaPairedDilationCompression (Real.log stageZeroSonineQ)
          (burnolZeroPaRieszState coordinate zero)) -
    pairedMellinTranslationCharacter coordinate.value
        (Real.log stageZeroSonineQ) *
      inner ℂ (burnolZeroPaRieszState coordinate zero)
        (burnolZeroPaRieszState coordinate zero)

theorem burnolPa_fixedShift_ne_zero :
    Real.log stageZeroSonineQ ≠ 0 := by
  apply (Real.log_pos ?_).ne'
  have square : stageZeroSonineQ ^ 2 = 3 := by
    unfold stageZeroSonineQ
    rw [sq, Real.mul_self_sqrt]
    norm_num
  have nonnegative : 0 ≤ stageZeroSonineQ := Real.sqrt_nonneg _
  nlinarith

theorem burnolZeroPaRieszState_ne_zero_iff_evaluator_ne_zero
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolZeroPaRieszState coordinate zero ≠ 0 ↔
      burnolCompletedMellinEvaluator coordinate ≠ 0 := by
  constructor
  · intro stateNonzero evaluatorZero
    apply stateNonzero
    apply Subtype.ext
    apply ext_inner_right ℂ
    intro value
    change inner ℂ
        (burnolZeroPaRieszState coordinate zero : BurnolL2)
        (value : BurnolL2) = inner ℂ (0 : BurnolL2) (value : BurnolL2)
    rw [burnolZeroPaRieszState_readback]
    simp [evaluatorZero]
  · intro evaluatorNonzero stateZero
    apply evaluatorNonzero
    apply ContinuousLinearMap.ext
    intro value
    have readback := burnolZeroPaRieszState_readback coordinate zero value
    rw [stateZero] at readback
    simpa using readback.symm

/-- One nonzero diagonal physical event is sufficient; no full vector
eigenlaw is required. -/
theorem burnolZeroPa_criticalLine_of_nonzero_expectation
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (shift : ℝ) (shiftNe : shift ≠ 0)
    (stateNe : burnolZeroPaRieszState coordinate zero ≠ 0)
    (expectation :
      inner ℂ (burnolZeroPaRieszState coordinate zero)
          (burnolPaPairedDilationCompression shift
            (burnolZeroPaRieszState coordinate zero)) =
        pairedMellinTranslationCharacter coordinate.value shift *
          inner ℂ (burnolZeroPaRieszState coordinate zero)
            (burnolZeroPaRieszState coordinate zero)) :
    coordinate.value.re = 1 / 2 := by
  let state := burnolZeroPaRieszState coordinate zero
  let action := burnolPaPairedDilationCompression shift
  let character := pairedMellinTranslationCharacter coordinate.value shift
  have stateNormPos : 0 < ‖state‖ := norm_pos_iff.mpr stateNe
  have selfInner : inner ℂ state state = (‖state‖ : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K state
  have expectationConj :
      star (inner ℂ state (action state)) =
        inner ℂ state (action state) := by
    calc
      star (inner ℂ state (action state)) =
          inner ℂ (action state) state := inner_conj_symm (action state) state
      _ = inner ℂ state (action state) :=
        burnolPaPairedDilationCompression_symmetric shift state state
  have characterReal : character.im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    have productConj : star (character * inner ℂ state state) =
        character * inner ℂ state state := by
      rw [← expectation]
      exact expectationConj
    rw [selfInner, star_mul] at productConj
    have squareNe : (‖state‖ : ℂ) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr stateNormPos.ne')
    have squareStar : star ((‖state‖ : ℂ) ^ 2) =
        (‖state‖ : ℂ) ^ 2 := by simp
    rw [squareStar] at productConj
    exact mul_right_cancel₀ squareNe (by simpa [mul_comm] using productConj)
  have characterContractive : ‖character‖ ≤ 1 := by
    have actionBound := burnolPaPairedDilationCompression_contractive shift state
    have bound : ‖character‖ * ‖state‖ ^ 2 ≤ ‖state‖ ^ 2 := by
      calc
        ‖character‖ * ‖state‖ ^ 2 =
            ‖character * inner ℂ state state‖ := by
          rw [norm_mul, selfInner, norm_pow, Complex.norm_real,
            Real.norm_of_nonneg (norm_nonneg state)]
        _ = ‖inner ℂ state (action state)‖ := congrArg norm expectation.symm
        _ ≤ ‖state‖ * ‖action state‖ := norm_inner_le_norm _ _
        _ ≤ ‖state‖ * ‖state‖ :=
          mul_le_mul_of_nonneg_left actionBound (norm_nonneg _)
        _ = ‖state‖ ^ 2 := by ring
    nlinarith [sq_pos_of_pos stateNormPos]
  exact pairedMellinTranslationCharacter_rigidity coordinate.value shift
    shiftNe characterReal characterContractive

/-- The diagonal defect is precisely the paired fixed-annulus boundary
jump.  All orthogonal projections have disappeared from the right-hand side.
-/
theorem burnolZeroPa_diagonalExpectationDefect_eq_pairedBoundaryJump
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (shift : ℝ) :
    inner ℂ (burnolZeroPaRieszState coordinate zero)
          (burnolPaPairedDilationCompression shift
            (burnolZeroPaRieszState coordinate zero)) -
        pairedMellinTranslationCharacter coordinate.value shift *
          inner ℂ (burnolZeroPaRieszState coordinate zero)
            (burnolZeroPaRieszState coordinate zero) =
      (1 / 2 : ℂ) *
        ((burnolCompletedMellinEvaluator coordinate
              (evenBurnolMultiplicativeCompression
                burnolUnscaledCommonGapRadius shift
                (burnolZeroPaRieszState coordinate zero :
                  BurnolPaAmbientCarrier)) -
            fullMellinTranslationCharacter coordinate.value shift *
              burnolCompletedMellinEvaluator coordinate
                (burnolZeroPaRieszState coordinate zero :
                  BurnolPaAmbientCarrier)) +
          (burnolCompletedMellinEvaluator coordinate
              (evenBurnolMultiplicativeCompression
                burnolUnscaledCommonGapRadius (-shift)
                (burnolZeroPaRieszState coordinate zero :
                  BurnolPaAmbientCarrier)) -
            reciprocalMellinTranslationCharacter coordinate.value shift *
              burnolCompletedMellinEvaluator coordinate
                (burnolZeroPaRieszState coordinate zero :
                  BurnolPaAmbientCarrier))) := by
  have compressedRead :
      inner ℂ (burnolZeroPaRieszState coordinate zero)
          (burnolPaPairedDilationCompression shift
            (burnolZeroPaRieszState coordinate zero)) =
        burnolCompletedMellinEvaluator coordinate
          (burnolPairedAmbientCompression shift
            (burnolZeroPaRieszState coordinate zero :
              BurnolPaAmbientCarrier)) := by
    rw [burnolPaPairedDilationCompression]
    simp only [ContinuousLinearMap.comp_apply]
    rw [burnolPaOrthogonalClosedFace.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact burnolZeroPaRieszState_readback coordinate zero _
  have baseRead :
      inner ℂ (burnolZeroPaRieszState coordinate zero)
          (burnolZeroPaRieszState coordinate zero) =
        burnolCompletedMellinEvaluator coordinate
          (burnolZeroPaRieszState coordinate zero :
            BurnolPaAmbientCarrier) :=
    burnolZeroPaRieszState_readback coordinate zero _
  rw [compressedRead, baseRead]
  unfold burnolPairedAmbientCompression pairedMellinTranslationCharacter
  simp only [smul_apply, add_apply, map_smul, map_add, smul_eq_mul]
  ring

/-- Fixed-root direct consumer.  Nonvanishing of the already generated
evaluator and cancellation of its actual paired boundary jump force the
critical line at the generated first scale. -/
theorem burnolZeroPa_fixedShift_criticalLine_of_boundaryCancellation
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (evaluatorNe : burnolCompletedMellinEvaluator coordinate ≠ 0)
    (boundaryCancellation :
      (1 / 2 : ℂ) *
        ((burnolCompletedMellinEvaluator coordinate
              (evenBurnolMultiplicativeCompression
                burnolUnscaledCommonGapRadius (Real.log stageZeroSonineQ)
                (burnolZeroPaRieszState coordinate zero :
                  BurnolPaAmbientCarrier)) -
            fullMellinTranslationCharacter coordinate.value
                (Real.log stageZeroSonineQ) *
              burnolCompletedMellinEvaluator coordinate
                (burnolZeroPaRieszState coordinate zero :
                  BurnolPaAmbientCarrier)) +
          (burnolCompletedMellinEvaluator coordinate
              (evenBurnolMultiplicativeCompression
                burnolUnscaledCommonGapRadius (-Real.log stageZeroSonineQ)
                (burnolZeroPaRieszState coordinate zero :
                  BurnolPaAmbientCarrier)) -
            reciprocalMellinTranslationCharacter coordinate.value
                (Real.log stageZeroSonineQ) *
              burnolCompletedMellinEvaluator coordinate
                (burnolZeroPaRieszState coordinate zero :
                  BurnolPaAmbientCarrier))) = 0) :
    coordinate.value.re = 1 / 2 := by
  apply burnolZeroPa_criticalLine_of_nonzero_expectation
    coordinate zero (Real.log stageZeroSonineQ)
    burnolPa_fixedShift_ne_zero
    ((burnolZeroPaRieszState_ne_zero_iff_evaluator_ne_zero
      coordinate zero).2 evaluatorNe)
  apply sub_eq_zero.mp
  rw [burnolZeroPa_diagonalExpectationDefect_eq_pairedBoundaryJump]
  exact boundaryCancellation

end
end BurnolPhysicalState
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
