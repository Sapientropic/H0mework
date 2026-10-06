import H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Input.Consumer
import H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame
/-! The original source input and existing source disposition instantiate the
paid math executor and its actual residual frame. Root/query cofaces remain
inherited; the nonaligned branches retain their original source feed. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Input.Runtime
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open CofinalHistoryTransition RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace D
export SourceOperationNative.Tree.Fold.Dependent (FeedAt generatedFeed nativeTree)
end D
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry
  (runtime original endpointState endpointCount endpoint_source_state original_material frame
    activated_query activated_answer activated_next)
end M
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (old : RootInquiryStateAt N V) (recognition : RecognitionAt H old.root)
variable (original : SourceNativeRootInquiryInputAt old.root old.visit old.Query)
variable (next : StepLedgerSuccessorAt (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition))
variable (history : GeneratedStepJointTransitionAt (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition) next)
variable (zip : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition))
  (stepTargetPairingOccurrence (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition) next))

abbrev actualState := SourceOperationNative.Tree.Fold.Dependent.Input.inputState old recognition original next history zip
abbrev actualInput := SourceOperationNative.Tree.Fold.Dependent.Input.queryInput old recognition original next history zip

def reader (_occurrence : (actualState old recognition original next history zip).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (actualState old recognition original next history zip).visit.current) :=
  (actualInput old recognition original next history zip).query.raw

abbrev actualRuntime := M.runtime (actualState old recognition original next history zip)
  (reader old recognition original next history zip)

abbrev RunAt (phase : PassiveEffectDispositionAt (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition)) : Type (u+15) :=
  match phase with
  | .allGenerated successor _ carry => ULift.{u+15} (type_of% (actualRuntime old recognition original successor carry.historyTransition carry.pairingAlignment))
  | .jointResidual successor _ transition alignment _ _ _ => ULift.{u+15} (type_of% (actualRuntime old recognition original successor transition alignment))
  | other => ULift.{u+15} (D.FeedAt (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition) other)

def generatedRuntime : RunAt old recognition original
    (SourceOperationNative.Tree.Fold.Dependent.Installation.selected old recognition) := by
  generalize phase_eq : SourceOperationNative.Tree.Fold.Dependent.Installation.selected old recognition = phase
  cases phase with
  | allGenerated successor eq carry => exact ⟨actualRuntime old recognition original successor carry.historyTransition carry.pairingAlignment⟩
  | jointResidual successor eq transition alignment residual exact mem => exact ⟨actualRuntime old recognition original successor transition alignment⟩
  | terminal eq => exact ⟨old.root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile
      (SourceOperationNative.Tree.Fold.Dependent.Installation.actualStep old recognition).sourceOccurrence⟩
  | generatorResidual successor eq residual => exact ⟨residual⟩
  | relationResidual successor eq compatible residual => exact ⟨residual⟩
  | pairingShapeResidual successor eq transition residual => exact ⟨residual⟩
end SourceOperationNative.Tree.Fold.Dependent.Input.Runtime
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
