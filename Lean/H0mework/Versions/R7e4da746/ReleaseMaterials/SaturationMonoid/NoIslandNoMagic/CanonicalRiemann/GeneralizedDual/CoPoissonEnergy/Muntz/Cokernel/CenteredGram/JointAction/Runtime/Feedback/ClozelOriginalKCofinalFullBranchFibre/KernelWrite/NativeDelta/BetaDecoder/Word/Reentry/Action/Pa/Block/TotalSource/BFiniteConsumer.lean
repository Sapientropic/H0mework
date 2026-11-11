import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.KConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteMaterialConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCoefficientBSelfMaterialConsumer

/-! The inherited original-material face supplies this current's exact occurrence to
its installed B/R and cotest calculation laws. The complete paid calculation payloads
are read and transported here; their source ASTs and executions remain the installed producers. -/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteConsumer
open Complex BurnolPhysicalState OriginalRieszFinitePairing.CoPoisson.Ward
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open scoped InnerProductSpace

namespace InstalledRead
namespace K
export OriginalKCofinalFullBranchFibre.KernelWrite.OriginalKInheritance (originalMaterial)
end K
namespace BF
export OriginalKBFiniteCalculation (component result)
end BF
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
variable (maternal : type_of% (K.originalMaterial observation nontrivial half depth))

def installedOutcome := (runtimeEffectRoot observation nontrivial).source.base.projectionLaw.outcomeAt
 ((runtimeBFiniteCalculationInstallation observation nontrivial).embed half) maternal.1

def componentOutcome := (BF.component observation nontrivial).outcomeAt half maternal.1

def outcomeFromRoot : type_of% (componentOutcome observation nontrivial half depth maternal) :=
 cast (type_eq_of_heq ((runtimeBFiniteCalculationInstallation observation nontrivial).outcome_heq maternal.1 half))
  (installedOutcome observation nontrivial half depth maternal)

theorem root_component : outcomeFromRoot observation nontrivial half depth maternal =
 componentOutcome observation nontrivial half depth maternal :=
 eq_of_heq ((cast_heq _ _).trans
  ((runtimeBFiniteCalculationInstallation observation nontrivial).outcome_heq maternal.1 half))

def calculation : type_of% (BF.result observation nontrivial half maternal.1) :=
 match outcomeFromRoot observation nontrivial half depth maternal with
 | .inl actual => actual.2
 | .inr impossible => nomatch impossible

theorem calculation_source : calculation observation nontrivial half depth maternal =
 BF.result observation nontrivial half maternal.1 := by
 unfold calculation
 rw [root_component]
 rfl

theorem original_source :
 calculation observation nontrivial half depth (K.originalMaterial observation nontrivial half depth) =
 runtimeBFiniteCalculationResultAt observation nontrivial depth half :=
 (calculation_source observation nontrivial half depth (K.originalMaterial observation nontrivial half depth)).trans
  (runtimeBFiniteCalculationResultAt_source observation nontrivial depth half).symm


namespace BS
export OriginalKCoefficientBSelfCalculation (component result)
end BS

def selfInstalledOutcome := (runtimeEffectRoot observation nontrivial).source.base.projectionLaw.outcomeAt
 ((runtimeCoefficientBSelfCalculationInstallation observation nontrivial).embed half) maternal.1

def selfComponentOutcome := (BS.component observation nontrivial).outcomeAt half maternal.1

def selfOutcomeFromRoot : type_of% (selfComponentOutcome observation nontrivial half depth maternal) :=
 cast (type_eq_of_heq ((runtimeCoefficientBSelfCalculationInstallation observation nontrivial).outcome_heq maternal.1 half))
  (selfInstalledOutcome observation nontrivial half depth maternal)

theorem self_root_component : selfOutcomeFromRoot observation nontrivial half depth maternal =
 selfComponentOutcome observation nontrivial half depth maternal :=
 eq_of_heq ((cast_heq _ _).trans
  ((runtimeCoefficientBSelfCalculationInstallation observation nontrivial).outcome_heq maternal.1 half))

def selfCalculation : type_of% (BS.result observation nontrivial half maternal.1) :=
 match selfOutcomeFromRoot observation nontrivial half depth maternal with
 | .inl actual => actual.2
 | .inr impossible => nomatch impossible

theorem self_calculation_source : selfCalculation observation nontrivial half depth maternal =
 BS.result observation nontrivial half maternal.1 := by
 unfold selfCalculation
 rw [self_root_component]
 rfl

theorem self_original_source :
 selfCalculation observation nontrivial half depth (K.originalMaterial observation nontrivial half depth) =
 runtimeCoefficientBSelfCalculationResultAt observation nontrivial depth half :=
 (self_calculation_source observation nontrivial half depth (K.originalMaterial observation nontrivial half depth)).trans
  (runtimeCoefficientBSelfCalculationResultAt_source observation nontrivial depth half).symm

end InstalledRead

namespace KC
export SourceInventoryExecutionFeed.SourceWordNative.Reentry.FullRAction.Pa.Block.TotalSource.KConsumer (originalRead)
end KC
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
variable (depth ordinal : Nat)

private def consumeMaternal
 (maternal : type_of% (InstalledRead.K.originalMaterial observation nontrivial half depth))
 (receipt : type_of% (((runtimeEffectRecognition observation nontrivial).effectLaw.eventVocabulary.emit maternal.1).effect.originalK.receiptAt half.down))
 (original : maternal = InstalledRead.K.originalMaterial observation nontrivial half depth) :=
 have receiptSource : receipt.1 = installedOriginalKReceiptAt observation nontrivial half.down :=
  receipt.2.trans (installedOriginalKReceiptAt_eq_source observation nontrivial half.down).symm
 let bFinite := InstalledRead.calculation observation nontrivial half depth maternal
 let bSelf := InstalledRead.selfCalculation observation nontrivial half depth maternal
 have finiteSource : HEq bFinite (runtimeBFiniteCalculationResultAt observation nontrivial depth half) :=
  (congr_arg_heq (InstalledRead.calculation observation nontrivial half depth) original).trans
   (heq_of_eq (InstalledRead.original_source observation nontrivial half depth))
 have selfSource : HEq bSelf (runtimeCoefficientBSelfCalculationResultAt observation nontrivial depth half) :=
  (congr_arg_heq (InstalledRead.selfCalculation observation nontrivial half depth) original).trans
   (heq_of_eq (InstalledRead.self_original_source observation nontrivial half depth))
 have finiteValueSource : bFinite.2.2.1 =
   (runtimeBFiniteCalculationResultAt observation nontrivial depth half).2.2.1 :=
  (congrArg (fun material => (InstalledRead.calculation observation nontrivial half depth material).2.2.1) original).trans
   (congrArg (fun material => material.2.2.1) (InstalledRead.original_source observation nontrivial half depth))
 have selfValueSource : bSelf.2.2.1 =
   (runtimeCoefficientBSelfCalculationResultAt observation nontrivial depth half).2.2.1 :=
  (congrArg (fun material => (InstalledRead.selfCalculation observation nontrivial half depth material).2.2.1) original).trans
   (congrArg (fun material => material.2.2.1) (InstalledRead.self_original_source observation nontrivial half depth))
 have selfExpressionSource : bSelf.1.expression =
   (runtimeCoefficientBSelfCalculationResultAt observation nontrivial depth half).1.expression :=
  (congrArg (fun material => (InstalledRead.selfCalculation observation nontrivial half depth material).1.expression) original).trans
   (congrArg (fun material => material.1.expression) (InstalledRead.self_original_source observation nontrivial half depth))
 have selfEndpointSource : bSelf.2.1.1 =
   (runtimeCoefficientBSelfCalculationResultAt observation nontrivial depth half).2.1.1 :=
  (congrArg (fun material => (InstalledRead.selfCalculation observation nontrivial half depth material).2.1.1) original).trans
   (congrArg (fun material => material.2.1.1) (InstalledRead.self_original_source observation nontrivial half depth))
 have physical : receipt.1.fixedResidual = -inner ℂ receipt.1.kernel bFinite.2.2.1 ∧
    ((receipt.1.boundary OriginalKBFiniteCalculation.fixedShift : BurnolL2) =
     (burnolEvenAmbientProjection bFinite.2.2.1 : BurnolL2)) ∧
    (bFinite.2.2.1 - (receipt.1.boundary OriginalKBFiniteCalculation.fixedShift : BurnolL2) =
     OriginalKFixedBoundarySourceFibre.sourceProjectionLoss
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) OriginalKBFiniteCalculation.fixedShift) ∧
    (‖bFinite.2.2.1‖^2 = ‖(receipt.1.boundary OriginalKBFiniteCalculation.fixedShift : BurnolL2)‖^2 +
     ‖OriginalKFixedBoundarySourceFibre.sourceProjectionLoss
      (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) OriginalKBFiniteCalculation.fixedShift‖^2) := by
  rw [receiptSource,finiteValueSource]
  have read := OriginalKBFiniteCalculation.MaterialConsumer.installed_original_receipt_reads
   observation nontrivial half depth (ordinal+1)
  exact read.2
 have value : bSelf.2.2.1 = -receipt.1.fixedResidual • ConstantDual.seed :=
  (selfValueSource.trans (OriginalKCoefficientBSelfCalculation.MaterialConsumer.installed_source_value
   observation nontrivial half depth)).trans
    (congrArg (fun source : OriginalRieszFiniteSource.Receipt => -source.fixedResidual • ConstantDual.seed) receiptSource.symm)
 have bound : SourceOperationScalarPresentation.relationMap (R := ℤ)
    (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment
    ((OriginalKCombReceiptFeedback.bSelfSourceTrace observation nontrivial depth half).relationWords (R := ℤ)) =
   Finsupp.single (bSelf.1.expression.subst (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)) (1 : ℤ) -
   Finsupp.single (bSelf.2.1.1.subst (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)) (1 : ℤ) :=
  (OriginalKCoefficientBSelfCalculation.MaterialConsumer.installed_bound_source_relation observation nontrivial half depth).trans
   (congrArg₂ (fun (raw terminal : OriginalKCoefficientBSelfCalculation.E) =>
    Finsupp.single (raw.subst (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)) (1 : ℤ) -
    Finsupp.single (terminal.subst (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)) (1 : ℤ))
    selfExpressionSource.symm selfEndpointSource.symm)
 have endpoint : (bSelf.2.1.1.subst (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)).eval
    (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment =
   -receipt.1.fixedResidual • ConstantDual.seed :=
  ((congrArg (fun expression : OriginalKCoefficientBSelfCalculation.E =>
    (expression.subst (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)).eval
     (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment) selfEndpointSource).trans
   (OriginalKCoefficientBSelfCalculation.MaterialConsumer.installed_bound_endpoint_price observation nontrivial half depth)).trans
    (congrArg (fun source : OriginalRieszFiniteSource.Receipt => -source.fixedResidual • ConstantDual.seed) receiptSource.symm)
 have faithful : bSelf.2.2.1 = (0 : BurnolL2) ↔ receipt.1.fixedResidual = (0 : ℂ) :=
  (Iff.intro (fun zero => selfValueSource.symm.trans zero) (fun zero => selfValueSource.trans zero)).trans
   ((OriginalKCoefficientBSelfCalculation.MaterialConsumer.installed_source_value_zero_iff observation nontrivial half depth).trans
    (Iff.intro (fun zero => (congrArg (fun source : OriginalRieszFiniteSource.Receipt => source.fixedResidual) receiptSource).trans zero)
     (fun zero => (congrArg (fun source : OriginalRieszFiniteSource.Receipt => source.fixedResidual) receiptSource).symm.trans zero)))
 have negPrice : -receipt.1.fixedResidual = inner ℂ receipt.1.kernel bFinite.2.2.1 :=
  (congrArg (fun coefficient : ℂ => -coefficient) physical.1).trans (neg_neg _)
 have finiteCotest : bSelf.2.2.1 = inner ℂ receipt.1.kernel bFinite.2.2.1 • ConstantDual.seed :=
  value.trans (congrArg (fun coefficient : ℂ => coefficient • ConstantDual.seed) negPrice)
 have finiteEndpoint : (bSelf.2.1.1.subst (OriginalKCombReceiptFeedback.bSelfSourceBinding observation nontrivial depth half)).eval
    (OriginalKCombReceiptFeedback.receipt observation nontrivial depth half).1.environment =
   inner ℂ receipt.1.kernel bFinite.2.2.1 • ConstantDual.seed :=
  endpoint.trans (congrArg (fun coefficient : ℂ => coefficient • ConstantDual.seed) negPrice)
 PProd.mk (bFinite,bSelf)
  (And.intro finiteSource (And.intro selfSource (And.intro physical (And.intro value
   (And.intro bound (And.intro endpoint (And.intro faithful (And.intro finiteCotest finiteEndpoint))))))))


/-- The actual current supplies the complete maternal occurrence and keeps its whole/next bundle. -/
def originalRead :=
 let actual := KC.originalRead observation nontrivial half depth ordinal
 let consumed := consumeMaternal observation nontrivial half depth ordinal actual.1.1 actual.1.2.1 actual.1.2.2
 PProd.mk (actual,consumed.1.1,consumed.1.2) consumed.2


end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourceBFiniteConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
