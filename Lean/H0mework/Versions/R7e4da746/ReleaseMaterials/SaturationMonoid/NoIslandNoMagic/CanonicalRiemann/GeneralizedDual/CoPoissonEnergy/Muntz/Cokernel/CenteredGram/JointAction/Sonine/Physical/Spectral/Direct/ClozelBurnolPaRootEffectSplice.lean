import H0mework.Versions.R7e4da746.Arithmetic.RiemannSpectral.ClozelBurnolPaZeroObservation
import H0mework.Versions.R7e4da746.Arithmetic.RiemannRuntime.PairedOmegaEffectRowRoot
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.Residual.Action.Mellin.ClozelAnalyticComplementJordanMellinAction
import H0mework.Versions.R7e4da746.Arithmetic.RiemannAnnulus.AnalyticComplementFinitePartRead

/-!
# Direct Burnol residual to fixed-root effect splice

The actual diagonal boundary residual is a dependent physical read of the
same owner-indexed zero occurrence.  Once complete-state dynamics cancels
that residual, the already installed Omega effect row has zero logarithmic
residual and retains its existing whole-ledger write and canonical next.

This file creates no root, claim, gate, classifier, or cancellation producer.
It also records the hostile direction: on the strict right-half branch the
installed residual is nonzero, so actual boundary cancellation is
incompatible with that branch rather than being selected by `NoMagic`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open CenteredGram.IntegralGraphJointAction
open scoped InnerProductSpace

noncomputable section

theorem installedOriginalKReceiptAt_eq_original
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    CenteredGram.IntegralGraphJointAction.installedOriginalKReceiptAt
        (burnolPaZeroObservation coordinate zero)
        (burnolPaZeroObservation_nontrivial coordinate zero)
        coordinate.rightHalf =
      OriginalRieszFiniteSource.Receipt.generate coordinate zero := by
  cases coordinate
  rfl

theorem installedOriginalK_fixedResidual_eq_original
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    (CenteredGram.IntegralGraphJointAction.installedOriginalKReceiptAt
      (burnolPaZeroObservation coordinate zero)
      (burnolPaZeroObservation_nontrivial coordinate zero)
      coordinate.rightHalf).fixedResidual =
        burnolPaFixedShiftResidual coordinate zero := by
  rw [installedOriginalKReceiptAt_eq_original]
  rfl

/-- The installed source retains the exact finite pair equation, rather than
only the root's scalar log-norm readout. -/
theorem installedOriginalK_fixedResidual_source
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    -(CenteredGram.IntegralGraphJointAction.installedOriginalKReceiptAt
      (burnolPaZeroObservation coordinate zero)
      (burnolPaZeroObservation_nontrivial coordinate zero)
      coordinate.rightHalf).fixedResidual =
      OriginalRieszFinitePairing.evaluatorSource coordinate
        (Real.log stageZeroSonineQ) := by
  rw [installedOriginalKReceiptAt_eq_original]
  exact OriginalRieszFinitePairing.fixed_residual_source coordinate zero

abbrev BurnolPaBoundaryCancellationAt
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) : Prop :=
  (CenteredGram.IntegralGraphJointAction.installedOriginalKReceiptAt
    (burnolPaZeroObservation coordinate zero)
    (burnolPaZeroObservation_nontrivial coordinate zero)
    coordinate.rightHalf).fixedResidual = 0

/-- The original exact-order Jordan terminal read witnesses nonvanishing of
the completed-Mellin evaluator at this same zero occurrence. -/
theorem burnolCompletedMellinEvaluator_nonzero_at_zero
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolCompletedMellinEvaluator coordinate ≠ 0 := by
  let observation := burnolPaZeroObservation coordinate zero
  have nontrivial := burnolPaZeroObservation_nontrivial coordinate zero
  have read := burnolPaFourierMellinRead_jordan_exactOrder observation nontrivial
    coordinate.rightHalf 0
  have expected := burnolAnalyticComplementExpectedPhysicalFourierRead_ne_zero
    observation nontrivial
  have same : burnolAnalyticComplementCompletedMellinCoordinate observation
      coordinate.rightHalf = coordinate := by
    cases coordinate
    rfl
  rw [same] at read
  intro evaluatorZero
  have zeroRead : burnolPaFourierMellinRead coordinate = 0 := by
    unfold burnolPaFourierMellinRead
    rw [evaluatorZero]
    simp
  rw [zeroRead] at read
  exact expected (by simpa using read.symm)

theorem burnolPaBoundaryCancellation_forces_criticalLine
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (cancellation : BurnolPaBoundaryCancellationAt coordinate zero) :
    coordinate.value.re = 1 / 2 := by
  apply burnolZeroPa_criticalLine_of_nonzero_expectation coordinate zero
    (Real.log stageZeroSonineQ) burnolPa_fixedShift_ne_zero
    ((burnolZeroPaRieszState_ne_zero_iff_evaluator_ne_zero
      coordinate zero).2 (burnolCompletedMellinEvaluator_nonzero_at_zero coordinate zero))
  have originalCancellation : burnolPaFixedShiftResidual coordinate zero = 0 := by
    simpa only [BurnolPaBoundaryCancellationAt,
      installedOriginalK_fixedResidual_eq_original] using cancellation
  exact sub_eq_zero.mp (by
    simpa only [burnolPaFixedShiftResidual] using originalCancellation)

theorem burnolPaRightHalf_installedLogNorm_ne_zero
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    (CenteredGram.IntegralGraphJointAction.installedRuntimeEffectValue
      (burnolPaZeroObservation coordinate zero)
      (burnolPaZeroObservation_nontrivial coordinate zero)).logNorm ≠ 0 := by
  rw [CenteredGram.IntegralGraphJointAction.installedRuntimeEffectValue_eq_initial]
  change CenteredGram.IntegralGraphJointAction.omegaLogNormEffect
    (burnolPaZeroObservation coordinate zero)
    (burnolPaZeroObservation_nontrivial coordinate zero) 0 ≠ 0
  rw [CenteredGram.IntegralGraphJointAction.omegaLogNormEffect_eq_coordinateResidual]
  change 2 * coordinate.value.re - 1 ≠ 0
  linarith [coordinate.rightHalf]

theorem burnolPaBoundaryCancellation_installedLogNorm_zero
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (cancellation : BurnolPaBoundaryCancellationAt coordinate zero) :
    (CenteredGram.IntegralGraphJointAction.installedRuntimeEffectValue
      (burnolPaZeroObservation coordinate zero)
      (burnolPaZeroObservation_nontrivial coordinate zero)).logNorm = 0 := by
  have critical := burnolPaBoundaryCancellation_forces_criticalLine
    coordinate zero cancellation
  rw [CenteredGram.IntegralGraphJointAction.installedRuntimeEffectValue_eq_initial]
  change CenteredGram.IntegralGraphJointAction.omegaLogNormEffect
    (burnolPaZeroObservation coordinate zero)
    (burnolPaZeroObservation_nontrivial coordinate zero) 0 = 0
  rw [CenteredGram.IntegralGraphJointAction.omegaLogNormEffect_eq_coordinateResidual]
  change 2 * coordinate.value.re - 1 = 0
  linarith

/-- Cancellation updates the already installed residual and consumes the
existing fixed-root factorization; no sibling successor is constructed. -/
theorem burnolPaBoundaryCancellation_keeps_fixedRoot_write_next
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (cancellation : BurnolPaBoundaryCancellationAt coordinate zero) :
    (CenteredGram.IntegralGraphJointAction.installedRuntimeEffectValue
      (burnolPaZeroObservation coordinate zero)
      (burnolPaZeroObservation_nontrivial coordinate zero)).logNorm = 0 ∧
    (let observation := burnolPaZeroObservation coordinate zero
     let nontrivial := burnolPaZeroObservation_nontrivial coordinate zero
     let registered := CenteredGram.IntegralGraphJointAction.runtimeEffectRootedActive
       observation nontrivial
     let root := CenteredGram.IntegralGraphJointAction.runtimeEffectRoot
       observation nontrivial
     let visit := CenteredGram.IntegralGraphJointAction.runtimeEffectVisit
       observation nontrivial
     let evolution := root.canonicalCausalAnswerAndNext (ULift.up visit)
     evolution.generated =
          root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit ∧
       HEq (evolution.generated.projectionOutcome
          (CenteredGram.IntegralGraphJointAction.runtimeEffectRecognition
            observation nontrivial).rootEffectProjection)
         registered.installedFiber ∧
       evolution.nextCurrent = root.generatedNextCurrentAt visit) := by
  exact ⟨burnolPaBoundaryCancellation_installedLogNorm_zero
      coordinate zero cancellation,
    CenteredGram.IntegralGraphJointAction.installedRuntimeEffect_factorizes
      (burnolPaZeroObservation coordinate zero)
      (burnolPaZeroObservation_nontrivial coordinate zero)⟩

theorem burnolPaBoundaryCancellation_incompatible_with_rightHalf
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (cancellation : BurnolPaBoundaryCancellationAt coordinate zero) : False := by
  exact burnolPaRightHalf_installedLogNorm_ne_zero coordinate zero
    (burnolPaBoundaryCancellation_installedLogNorm_zero
      coordinate zero cancellation)

/-- The installed original K band/source pair cannot be compressed into a
free cancellation at a right-half zero. -/
theorem installedOriginalK_sourceEquation_ne_zero
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    OriginalRieszFinitePairing.evaluatorSource coordinate
      (Real.log stageZeroSonineQ) ≠ 0 := by
  intro sourceZero
  have receiptZero : BurnolPaBoundaryCancellationAt coordinate zero := by
    have generated := installedOriginalK_fixedResidual_source coordinate zero
    rw [sourceZero] at generated
    exact neg_eq_zero.mp generated
  exact burnolPaBoundaryCancellation_incompatible_with_rightHalf
    coordinate zero receiptZero

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
