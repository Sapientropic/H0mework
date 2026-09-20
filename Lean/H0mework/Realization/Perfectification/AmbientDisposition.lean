import H0mework.Realization.Faces.DualityTransport

/-!
# Total perfect-ambient disposition

The complete-carrier foundation now exposes two independent source-owned
outputs: the history determinant disposition and the two-sided duality
disposition.  This junction does not identify them by a comparator.  It
replays both generated outcomes on the same exact step:

* bounded compact history **and** two-sided dual equivalences produce the
  determinant-eligible `eligible` face;
* a history residual is retained as its generated coordinate;
* otherwise the duality residual (already carrying its kernel/cokernel
  coordinate) is retained.

Thus a finite determinant is earned only when the source has generated both
the bounded envelope and the duality evidence.  No finite, perfect,
nondegenerate, inverse, or determinant premise enters this file.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace CofinalPerfectAmbient

open CofinalHistorySettlement
open CofinalHistorySettlement.RootGeneratedCofinalHistoryAt
open CofinalHistorySettlementFace
open CofinalHistoryCochainCommonOccurrence
open CofinalHistoryCochainDuality
open CofinalHistoryCochainDuality.RootGeneratedCofinalHistoryCochainDualityStepAt
open CofinalHistoryDeterminantDisposition
open CofinalHistoryResidualCoordinate
open PerfectComplexDeterminantProjection
open SourceGeneratedDualEvaluation

noncomputable section

universe u

/-! ## Exact total outcome -/

inductive PerfectAmbientDispositionOutcome
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    Type (u + 2) where
  | eligible
      (trace : GeneratedHistoricalCompactnessAt step.commonStep.history)
      (readout : GeneratedCompactPerfectReadoutAt step.commonStep.history trace)
      (calculation : RootGeneratedFourTermPerfectCalculationAt
        readout.determinantProjection)
      (state : RootGeneratedFourTermPerfectDeterminantStateAt
        readout.determinantProjection calculation)
      (leftEquiv :
        step.commonStep.history.CompletionCarrier ≃ₗ[ℤ]
          Module.Dual ℤ step.commonStep.history.CompletionCarrier)
      (rightEquiv :
        step.commonStep.history.CompletionCarrier ≃ₗ[ℤ]
          Module.Dual ℤ step.commonStep.history.CompletionCarrier)
  | historyResidual
      (coordinate : GeneratedPresentedResidualCoordinateAt step.commonStep.history)
  | dualityResidual
      (residual : DualityDispositionOutcome step.pairingFace)

/-! Pattern matching on the generated determinant and duality dispositions is
the only branch selection. -/
def settlePerfectAmbient
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    PerfectAmbientDispositionOutcome step := by
  cases step.commonStep.historyDeterminantDisposition with
  | residual coordinate =>
      exact .historyResidual coordinate
  | determinant trace readout calculation state =>
      cases step.dualityDisposition with
      | dualizable leftEquiv rightEquiv =>
          exact .eligible trace readout calculation state leftEquiv rightEquiv
      | leftResidual residual =>
          exact .dualityResidual (.leftResidual residual)
      | rightResidual residual =>
          exact .dualityResidual (.rightResidual residual)

theorem settlePerfectAmbient_is_total
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}
    } {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    Nonempty (PerfectAmbientDispositionOutcome step) :=
  ⟨settlePerfectAmbient step⟩

/-! ## Root/ledger/next are inherited from the same exact step -/

def wholeLedgerWriteBack
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  step.wholeLedgerWriteBack

def nextCurrent
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :=
  step.nextCurrent

theorem wholeLedgerWriteBack_eq_root
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    HEq (wholeLedgerWriteBack step)
      (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) :=
  step.wholeLedgerWriteBack_eq_root

theorem nextCurrent_eq_root
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    nextCurrent step = root.generatedNextCurrentAt visit :=
  step.nextCurrent_eq_root

theorem installedAmbient_factorizes
    {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
    {root : SourceNativeLivingRootClosure N V}
    {recognition : SourceNativeCofinalHistoryCochainDualityRecognitionAt root}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    (step : RootGeneratedCofinalHistoryCochainDualityStepAt recognition visit) :
    HEq
      (root.toAuthoritativeRoot.source.projectionLaw.outcomeAt
        (recognition.installation.embed PUnit.unit) step.sourceOccurrence)
      (recognition.materialLaw.toProjectionLaw.outcomeAt
        PUnit.unit step.sourceOccurrence) :=
  step.installedDuality_factorizes

end
end CofinalPerfectAmbient
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
