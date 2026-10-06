import H0mework.Versions.AC.Realization.Operations.Tree.Fold.Dependent.Source
import H0mework.Versions.AC.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source
/-! The existing compiler successor supplies the next exact visit. Every
original feed and residual survives while its target source generates the
next calculation; no future inquiry state or target is supplied. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Next
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace D
export SourceOperationNative.Tree.Fold.Dependent (FeedAt sourceFeed nativeReader nativeTree)
end D
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (runtime activated_query activated_answer activated_next)
end M
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
abbrev step := recognition.generateStepAt visit
variable (successor : StepLedgerSuccessorAt (step root visit recognition))
variable (transition : GeneratedStepJointTransitionAt (step root visit recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (step root visit recognition)) (stepTargetPairingOccurrence (step root visit recognition) successor))
abbrev reader := D.nativeReader (step root visit recognition) successor transition alignment
abbrev actualRuntime := M.runtime root visit U7 calculus (reader root visit recognition successor transition alignment)

abbrev selected := settlePassiveEffect (step root visit recognition)
def RunAt (phase : PassiveEffectDispositionAt (step root visit recognition)) : Type (u+15) :=
  match phase with
  | .allGenerated next _ carry => ULift.{u+15} (type_of% (actualRuntime root visit recognition U7 calculus next carry.historyTransition carry.pairingAlignment))
  | .jointResidual next _ transition alignment _ _ _ => ULift.{u+15} (type_of% (actualRuntime root visit recognition U7 calculus next transition alignment))
  | other => ULift.{u+15} (D.FeedAt (step root visit recognition) other)

def generated : RunAt root visit recognition U7 calculus (selected root visit recognition) := by
  generalize selected_eq : selected root visit recognition = phase
  cases phase with
  | allGenerated next eq carry => exact ⟨actualRuntime root visit recognition U7 calculus next carry.historyTransition carry.pairingAlignment⟩
  | jointResidual next eq transition alignment residual exact mem => exact ⟨actualRuntime root visit recognition U7 calculus next transition alignment⟩
  | terminal eq => exact ⟨root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile (step root visit recognition).sourceOccurrence⟩
  | generatorResidual next eq residual => exact ⟨residual⟩
  | relationResidual next eq compatible residual => exact ⟨residual⟩
  | pairingShapeResidual next eq transition residual => exact ⟨residual⟩

abbrev nextVisit := visit.next successor.next_eq
abbrev nextRun := generated root (nextVisit root visit recognition successor) recognition U7 calculus


def NextAt (phase : PassiveEffectDispositionAt (step root visit recognition)) : Type (u+15) :=
  match phase with
  | .terminal _ => ULift.{u+15} (D.FeedAt (step root visit recognition) phase)
  | .generatorResidual next _ _
  | .relationResidual next _ _ _
  | .pairingShapeResidual next _ _ _
  | .allGenerated next _ _
  | .jointResidual next _ _ _ _ _ _ =>
      ULift.{u+15} (D.FeedAt (step root visit recognition) phase) ×
        RunAt root (nextVisit root visit recognition next) recognition U7 calculus
          (selected root (nextVisit root visit recognition next) recognition)

def generatedNext : NextAt root visit recognition U7 calculus (selected root visit recognition) := by
  generalize selected_eq : selected root visit recognition = phase
  cases phase with
  | terminal eq => exact ⟨root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile (step root visit recognition).sourceOccurrence⟩
  | generatorResidual next eq residual => exact ⟨⟨residual⟩, nextRun root visit recognition U7 calculus next⟩
  | relationResidual next eq compatible residual => exact ⟨⟨residual⟩, nextRun root visit recognition U7 calculus next⟩
  | pairingShapeResidual next eq transition residual => exact ⟨⟨residual⟩, nextRun root visit recognition U7 calculus next⟩
  | allGenerated next eq carry => exact ⟨⟨SourceOperationNative.Tree.Fold.Dependent.nativePacket (step root visit recognition)
      next carry.historyTransition carry.pairingAlignment⟩, nextRun root visit recognition U7 calculus next⟩
  | jointResidual next eq transition alignment residual exact mem => exact ⟨⟨SourceOperationNative.Tree.Fold.Dependent.nativePacket
      (step root visit recognition) next transition alignment⟩, nextRun root visit recognition U7 calculus next⟩
end SourceOperationNative.Tree.Fold.Dependent.Next
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
