import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteInverseFibre
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.BFiniteConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteInverseConsumer
open Complex BurnolPhysicalState OriginalRieszSource OriginalKSourceResolventReconstruction
open OriginalKFixedBoundarySourceFibre
namespace Current
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteConsumer (originalRead)
namespace InstalledRead
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteConsumer.InstalledRead
  (calculation calculation_source)
namespace K
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteConsumer.InstalledRead.K
  (originalMaterial)
end K
end InstalledRead
end Current
namespace Inverse
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteInverseFibre (actualRead)
end Inverse
namespace BF
export OriginalKBFiniteCalculation (result coordinate fixedShift)
end BF

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def consumeMaternal
    (maternal : type_of% (Current.InstalledRead.K.originalMaterial observation nontrivial half depth))
    (receipt : type_of% (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit maternal.1).effect.originalK.receiptAt half.down))
    (loss : (Current.InstalledRead.calculation observation nontrivial half depth maternal).2.2.1 -
      (receipt.1.boundary BF.fixedShift : BurnolL2) =
      sourceProjectionLoss (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) BF.fixedShift) :=
  let inverse := Inverse.actualRead observation nontrivial half maternal.1
  let c := BF.coordinate observation nontrivial half maternal.1
  let material := Current.InstalledRead.calculation observation nontrivial half depth maternal
  have valueSource : material.2.2.1 = (BF.result observation nontrivial half maternal.1).2.2.1 :=
    congrArg (fun material => material.2.2.1)
      (Current.InstalledRead.calculation_source observation nontrivial half depth maternal)
  have receiptSource : receipt.1 = installedOriginalKReceiptAt observation nontrivial half.down :=
    receipt.2.trans (installedOriginalKReceiptAt_eq_source observation nontrivial half.down).symm
  have originalKernel : (installedOriginalKReceiptAt observation nontrivial half.down).kernel =
      (burnolCompletedMellinRieszVector c : BurnolL2) :=
    congrArg (fun source : OriginalRieszFiniteSource.Receipt => source.kernel)
      (installedOriginalKReceiptAt_eq_source observation nontrivial half.down)
  have kernelSource : receipt.1.kernel = generatedK c :=
    (congrArg (fun source : OriginalRieszFiniteSource.Receipt => source.kernel) receiptSource).trans
      (originalKernel.trans (generatedK_eq_original c).symm)
  have fullValue : material.2.2.1 =
      (receipt.1.boundary BF.fixedShift : BurnolL2) + sourceProjectionLoss c BF.fixedShift := by
    change material.2.2.1 - (receipt.1.boundary BF.fixedShift : BurnolL2) =
      sourceProjectionLoss c BF.fixedShift at loss
    linear_combination (norm := module) loss
  have kernelRaw : finiteBoundaryAction c BF.fixedShift receipt.1.kernel =
      (BF.result observation nontrivial half maternal.1).2.2.1 :=
    (congrArg (finiteBoundaryAction c BF.fixedShift) kernelSource).trans inverse.2.2.1.symm
  have kernelImage : finiteBoundaryAction c BF.fixedShift receipt.1.kernel =
      (receipt.1.boundary BF.fixedShift : BurnolL2) + sourceProjectionLoss c BF.fixedShift :=
    kernelRaw.trans (valueSource.symm.trans fullValue)
  have recover : ∀ source : BurnolL2,
      finiteBoundaryAction c BF.fixedShift source =
        (receipt.1.boundary BF.fixedShift : BurnolL2) + sourceProjectionLoss c BF.fixedShift →
      source = receipt.1.kernel := by
    obtain ⟨witness, _image, unique⟩ := inverse.2.1
    intro source image
    exact (unique source (image.trans (fullValue.symm.trans valueSource))).trans
      (unique receipt.1.kernel kernelRaw).symm
  PProd.mk inverse (And.intro kernelSource (And.intro fullValue (And.intro kernelImage recover)))

/-- The literal current's full boundary and fee recover its own original K source. -/
def originalRead (ordinal : Nat) :=
  let actual := Current.originalRead observation nontrivial half depth ordinal
  let consumed := consumeMaternal observation nontrivial half depth actual.1.1.1.1
    actual.1.1.1.2.1 actual.2.2.2.1.2.2.1
  PProd.mk actual consumed

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteInverseConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
