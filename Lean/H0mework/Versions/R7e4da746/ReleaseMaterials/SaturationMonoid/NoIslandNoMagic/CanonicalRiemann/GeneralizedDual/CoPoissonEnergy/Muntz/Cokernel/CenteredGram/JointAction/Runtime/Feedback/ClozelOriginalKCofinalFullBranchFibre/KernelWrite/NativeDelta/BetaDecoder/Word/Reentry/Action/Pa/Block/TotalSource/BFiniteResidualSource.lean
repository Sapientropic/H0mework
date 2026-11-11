import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteInverseConsumer
import H0mework.Versions.R7e4da746.Arithmetic.RieszSourceKernel.Consumer

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteResidualSource
open BurnolPhysicalState OriginalRieszSource OriginalKFixedBoundarySourceFibre
open scoped InnerProductSpace

namespace Inverse
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteInverseConsumer
  (originalRead)
end Inverse
namespace K
export OriginalKCofinalFullBranchFibre.KernelWrite.OriginalKInheritance (originalMaterial)
end K

private theorem sourceResidualNe
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (half : OriginalKCombCalculation.Half observation) :
    (installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual ≠ 0 := by
  let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  have state : burnolZeroPaRieszState c observation.mathlibZero ≠ 0 :=
    (Kernel.zero_owned_response observation nontrivial half.down).1
  rw [installedOriginalKReceiptAt_eq_source]
  change burnolPaFixedShiftResidual c observation.mathlibZero ≠ 0
  intro vanished
  have expectation := sub_eq_zero.mp vanished
  have centered := burnolZeroPa_criticalLine_of_nonzero_expectation c observation.mathlibZero
    (Real.log stageZeroSonineQ) burnolPa_fixedShift_ne_zero state expectation
  linarith [c.rightHalf]

private theorem consume {residual : ℂ} {kernel value self acted boundary loss : BurnolL2}
    (nonzero : residual ≠ 0)
    (price : residual = -inner ℂ kernel value)
    (faithful : self = 0 ↔ residual = 0)
    (image : acted = boundary + loss) (full : value = boundary + loss)
    (orthogonal : inner ℂ kernel loss = 0) :
    residual ≠ 0 ∧ inner ℂ kernel acted ≠ 0 ∧ inner ℂ kernel boundary ≠ 0 ∧
      boundary ≠ 0 ∧ value ≠ 0 ∧ self ≠ 0 := by
  have paired : inner ℂ kernel value ≠ 0 := by
    intro vanished
    apply nonzero
    rw [price, vanished, neg_zero]
  have boundaryPair : inner ℂ kernel boundary ≠ 0 := by
    have same : inner ℂ kernel value = inner ℂ kernel boundary := by
      rw [full, inner_add_right, orthogonal, add_zero]
    exact fun zero => paired (same.trans zero)
  have actedPair : inner ℂ kernel acted ≠ 0 := by
    rw [image, ← full]
    exact paired
  refine ⟨nonzero, actedPair, boundaryPair, ?_, ?_, ?_⟩
  · intro zero
    exact boundaryPair (by rw [zero, inner_zero_right])
  · intro zero
    exact paired (by rw [zero, inner_zero_right])
  · exact fun zero => nonzero (faithful.mp zero)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

private theorem receiptResidualNe
    (maternal : type_of% (K.originalMaterial observation nontrivial half depth))
    (receipt : type_of% (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit maternal.1).effect.originalK.receiptAt half.down)) :
    receipt.1.fixedResidual ≠ 0 := by
  have source : receipt.1 = installedOriginalKReceiptAt observation nontrivial half.down :=
    receipt.2.trans (installedOriginalKReceiptAt_eq_source observation nontrivial half.down).symm
  rw [source]
  exact sourceResidualNe observation nontrivial half

private theorem receiptLossOrthogonal
    (maternal : type_of% (K.originalMaterial observation nontrivial half depth))
    (receipt : type_of% (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit maternal.1).effect.originalK.receiptAt half.down)) :
    inner ℂ receipt.1.kernel
      (sourceProjectionLoss (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
        OriginalKBFiniteCalculation.fixedShift) = 0 := by
  have source : receipt.1 = installedOriginalKReceiptAt observation nontrivial half.down :=
    receipt.2.trans (installedOriginalKReceiptAt_eq_source observation nontrivial half.down).symm
  rw [source, installedOriginalKReceiptAt_eq_source]
  let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
  change inner ℂ (burnolCompletedMellinRieszVector c : BurnolL2)
    (sourceProjectionLoss c OriginalKBFiniteCalculation.fixedShift) = 0
  exact inner_eq_zero_symm.mp
    (sourceProjectionLoss_orthogonal c OriginalKBFiniteCalculation.fixedShift
      (burnolCompletedMellinRieszVector c))

/-- The actual source residual is nonzero, with its complete inverse and whole/next. -/
def originalRead :=
  let actual := Inverse.originalRead observation nontrivial half depth ordinal
  let maternal := actual.1.1.1.1.1
  let receipt := actual.1.1.1.1.2.1
  let nonzero := receiptResidualNe observation nontrivial half depth maternal receipt
  let orthogonal := receiptLossOrthogonal observation nontrivial half depth maternal receipt
  let generated := consume nonzero actual.1.2.2.2.1.1
    actual.1.2.2.2.2.2.2.2.1 actual.2.2.2.2.1 actual.2.2.2.1 orthogonal
  PProd.mk actual generated

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteResidualSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
