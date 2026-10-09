import H0mework.Versions.AD.Realization.Operations.Tree.Fold.Consumer
import H0mework.Versions.PR.Realization.JointEffect.PassiveController

/-! An exact installed source step generates the full aligned constructor tree.
Its native code is executed by the existing OwnerFree process; every original
residual and complete old/stage material is retained. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent
open SourceOperationEffects SourceOperationExecution
open CofinalHistoryTransition RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace F
export SourceOperationNative.Tree.Fold (Value Var environment program budget program_value program_budget)
end F
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {root : SourceNativeLivingRootClosure N V} {recognition : RecognitionAt H root}
variable {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}

abbrev nativeTree (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (transition : GeneratedStepJointTransitionAt step successor)
    (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
      (stepSourcePairingOccurrence step) (stepTargetPairingOccurrence step successor)) :=
  alignedJointOccurrence step successor transition.history alignment

abbrev nativeRaw (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (transition : GeneratedStepJointTransitionAt step successor)
    (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
      (stepSourcePairingOccurrence step) (stepTargetPairingOccurrence step successor)) :
    O.Raw (Value := F.Value (AlignedJointPayloadAt step successor transition.history)
      (TreeOutcomeAt step successor transition.history))
      (Var := F.Var (AlignedJointPayloadAt step successor transition.history)) (sort := .result) :=
  ⟨F.environment, F.program (effectFoldAt step successor transition.history)
    (nativeTree step successor transition alignment)⟩

abbrev nativeReader (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (transition : GeneratedStepJointTransitionAt step successor)
    (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
      (stepSourcePairingOccurrence step) (stepTargetPairingOccurrence step successor)) :=
  fun (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) =>
    nativeRaw step successor transition alignment

abbrev nativeResult (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (transition : GeneratedStepJointTransitionAt step successor)
    (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
      (stepSourcePairingOccurrence step) (stepTargetPairingOccurrence step successor)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value root.toAuthoritativeRoot visit.current
    (nativeReader step successor transition alignment)

abbrev nativeTrace (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
    (transition : GeneratedStepJointTransitionAt step successor)
    (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
      (stepSourcePairingOccurrence step) (stepTargetPairingOccurrence step successor)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.trace root.toAuthoritativeRoot visit.current
    (nativeReader step successor transition alignment)

variable (step : StepAt recognition visit) (successor : StepLedgerSuccessorAt step)
variable (transition : GeneratedStepJointTransitionAt step successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence step) (stepTargetPairingOccurrence step successor))

theorem actual_effect_value : nativeResult step successor transition alignment =
    Finsupp.single (settleTree step successor transition.history (nativeTree step successor transition alignment)) 1 :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.value_source root.toAuthoritativeRoot visit.current
    (nativeReader step successor transition alignment)).trans (F.program_value _ _)

theorem actual_effect_charge : (nativeTrace step successor transition alignment).length =
    F.budget (nativeTree step successor transition alignment) :=
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.paid_history root.toAuthoritativeRoot visit.current
    (nativeReader step successor transition alignment)).trans (F.program_budget _ _)

abbrev nativePayment (count : Fin (F.budget (nativeTree step successor transition alignment))) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Payment.activePayment root.toAuthoritativeRoot visit.current
    (nativeReader step successor transition alignment)
      ⟨count.1, by change count.1 < remaining (nativeRaw step successor transition alignment).expression
                   rw [F.program_budget]; exact count.2⟩

theorem original_material : type_of%
    (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.original_material root.toAuthoritativeRoot visit.current
      (nativeReader step successor transition alignment)) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.original_material root.toAuthoritativeRoot visit.current
    (nativeReader step successor transition alignment)

abbrev nativeStageMaterial (count : Nat) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt
    (RootGeneratedDebtActivationJointSource.OwnerFree.authoritativeRoot root.toAuthoritativeRoot visit.current
      (nativeReader step successor transition alignment))
    ((RootGeneratedDebtActivationJointSource.OwnerFree.authoritativeRoot root.toAuthoritativeRoot visit.current
      (nativeReader step successor transition alignment)).emitted
        (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.state root.toAuthoritativeRoot visit.current
          (nativeReader step successor transition alignment) count))

abbrev NativePacketAt :=
  RootedAccountedUnfolding (AlignedJointPayloadAt step successor transition.history) ×
  SourceOperationExecutionDebt.State (nativeRaw step successor transition alignment).environment
    (nativeRaw step successor transition alignment).expression ×
  F.Value (AlignedJointPayloadAt step successor transition.history) (TreeOutcomeAt step successor transition.history) .result ×
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.SourceMaterialAt root.toAuthoritativeRoot step.sourceOccurrence ×
  ((count : Fin (F.budget (nativeTree step successor transition alignment)+1)) →
    type_of% (nativeStageMaterial step successor transition alignment count.1))

def nativePacket : NativePacketAt step successor transition alignment :=
  ⟨nativeTree step successor transition alignment,
   RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.targetState root.toAuthoritativeRoot visit.current
     (nativeReader step successor transition alignment),
   nativeResult step successor transition alignment,
   RootGeneratedDebtActivationJointSource.OwnerFree.Installation.sourceMaterialAt root.toAuthoritativeRoot step.sourceOccurrence,
   fun count => nativeStageMaterial step successor transition alignment count.1⟩

theorem source_math_whole_next (count : Nat) :
    type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Payment.destination_entry root.toAuthoritativeRoot
      visit.current (nativeReader step successor transition alignment) count) ∧
    type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.tick_math root.toAuthoritativeRoot visit.current
      (nativeReader step successor transition alignment)
      (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.runtime root.toAuthoritativeRoot visit.current
        (nativeReader step successor transition alignment) count)) :=
  ⟨RootGeneratedDebtActivationJointSource.OwnerFree.Payment.destination_entry root.toAuthoritativeRoot visit.current
     (nativeReader step successor transition alignment) count,
   RootGeneratedDebtActivationJointSource.OwnerFree.tick_math root.toAuthoritativeRoot visit.current
     (nativeReader step successor transition alignment)
     (RootGeneratedDebtActivationJointSource.OwnerFree.Completion.runtime root.toAuthoritativeRoot visit.current
       (nativeReader step successor transition alignment) count)⟩

theorem original_whole_next : HEq step.wholeLedgerWriteBack
    (root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt visit.current) ∧
    step.nextCurrent = root.generatedNextCurrentAt visit :=
  ⟨step.wholeLedgerWriteBack_eq_root, step.nextCurrent_eq_root⟩

abbrev FeedAt (selected : PassiveEffectDispositionAt step) : Type u :=
  match selected with
  | .terminal _ => SourceNativeLedgerEvolutionAt root.toAuthoritativeRoot.toLedgerRoot.source.source step.sourceOccurrence
  | .generatorResidual next _ _ => GeneratorResidual (StepSourceHistory step) (StepTargetHistory step next)
  | .relationResidual next _ compatible _ => RelationResidual (StepSourceHistory step) (StepTargetHistory step next) compatible
  | .pairingShapeResidual next _ _ _ => RootedAccountedUnfoldingZip.ShapeResidualAt
      (stepSourcePairingOccurrence step) (stepTargetPairingOccurrence step next)
  | .allGenerated next _ carry =>
      NativePacketAt step next carry.historyTransition carry.pairingAlignment
  | .jointResidual next _ transitionNext align _ _ _ =>
      NativePacketAt step next transitionNext align

-- The existing source eliminator selects history, alignment and the exact residual.
def sourceFeed : FeedAt step (settlePassiveEffect step) := by
  generalize selected_eq : settlePassiveEffect step = selected
  cases selected with
  | terminal _ => exact root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile step.sourceOccurrence
  | generatorResidual next eq residual => exact residual
  | relationResidual next eq compatible residual => exact residual
  | pairingShapeResidual next eq transitionNext residual => exact residual
  | allGenerated next eq carry => exact nativePacket step next carry.historyTransition carry.pairingAlignment
  | jointResidual next eq transitionNext align residual equation mem => exact nativePacket step next transitionNext align

abbrev generatedFeed (recognition : RecognitionAt H root)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) :=
  sourceFeed (recognition.generateStepAt visit)


end SourceOperationNative.Tree.Fold.Dependent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
