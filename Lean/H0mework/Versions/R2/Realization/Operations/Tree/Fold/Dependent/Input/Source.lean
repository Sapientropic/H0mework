import H0mework.Versions.R2.Realization.Operations.Tree.Fold.Dependent.Installation
/-! The original installed query supplies incidence. The existing source
disposition supplies successor/history/alignment; the exact-visit input face
registers the new calculation query without a caller query or target. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Input
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open CofinalHistoryTransition RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
namespace D
export SourceOperationNative.Tree.Fold.Dependent (FeedAt generatedFeed sourceFeed)
end D
namespace I
export SourceOperationNative.Tree.Fold.Dependent.Installation
  (actualStep selected reader inquiry answer answerConsumer inheritedMaterial oldCompilationFace
    inquiry_value inquiry_next query_tree result_tree result_source_state old_compilation_preserved Query)
end I
namespace Q
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry (query exactOccurrence)
end Q
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (old : RootInquiryStateAt N V) (recognition : RecognitionAt H old.root)
variable (original : SourceNativeRootInquiryInputAt old.root old.visit old.Query)
variable (next : StepLedgerSuccessorAt (I.actualStep old recognition))
variable (history : GeneratedStepJointTransitionAt (I.actualStep old recognition) next)
variable (zip : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (I.actualStep old recognition)) (stepTargetPairingOccurrence (I.actualStep old recognition) next))

abbrev question := Q.query old (I.reader old recognition next history zip) original.query

def queryLaw : SourceNativeProjectionLaw (I.inquiry old recognition next history zip).root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} occurrence => ULift.{u,0} (PLift (Q.exactOccurrence old occurrence))
  InactiveAt := fun _ {_current} occurrence => ULift.{u,0} (PLift (¬ Q.exactOccurrence old occurrence))
  classify := by
    classical
    intro projection current occurrence
    exact if same : Q.exactOccurrence old occurrence then .inl ⟨⟨same⟩⟩ else .inr ⟨⟨same⟩⟩
  PayloadAt := fun _ {_current} _ _ => I.Query old recognition next history zip
  project := fun _ {_current} _ _ => question old recognition original next history zip

def inputRoot : SourceNativeLivingRootClosure N V :=
  (I.inquiry old recognition next history zip).root.withProjectionCoface
    (queryLaw old recognition original next history zip)
abbrev inputVisit : SourceNativeTemporalVisitAt (inputRoot old recognition original next history zip).toAuthoritativeRoot.toLedgerRoot := old.visit

def queryInput : SourceNativeRootInquiryInputAt (inputRoot old recognition original next history zip)
    (inputVisit old recognition original next history zip) (I.Query old recognition next history zip) where
  projection := .component PUnit.unit
  active := ⟨⟨rfl⟩⟩
  classifier_eq := by
    change (queryLaw old recognition original next history zip).classify PUnit.unit (old.root.emitted old.visit.current) = .inl ⟨⟨rfl⟩⟩
    unfold queryLaw
    exact dif_pos rfl
  queryType_eq := rfl

theorem query_read : (queryInput old recognition original next history zip).query =
    question old recognition original next history zip := rfl

def InputAt (phase : PassiveEffectDispositionAt (I.actualStep old recognition)) : Type u :=
  match phase with
  | .allGenerated successor _ carry => SourceNativeRootInquiryInputAt
      (inputRoot old recognition original successor carry.historyTransition carry.pairingAlignment)
      (inputVisit old recognition original successor carry.historyTransition carry.pairingAlignment)
      (I.Query old recognition successor carry.historyTransition carry.pairingAlignment)
  | .jointResidual successor _ transition alignment _ _ _ => SourceNativeRootInquiryInputAt
      (inputRoot old recognition original successor transition alignment)
      (inputVisit old recognition original successor transition alignment)
      (I.Query old recognition successor transition alignment)
  | other => D.FeedAt (I.actualStep old recognition) other

def generatedInput : InputAt old recognition original (I.selected old recognition) := by
  generalize phase_eq : I.selected old recognition = phase
  cases phase with
  | allGenerated successor eq carry => exact queryInput old recognition original successor carry.historyTransition carry.pairingAlignment
  | jointResidual successor eq transition alignment residual exact mem => exact queryInput old recognition original successor transition alignment
  | terminal eq => exact old.root.toAuthoritativeRoot.toLedgerRoot.source.ledgerCompiler.compile (I.actualStep old recognition).sourceOccurrence
  | generatorResidual successor eq residual => exact residual
  | relationResidual successor eq compatible residual => exact residual
  | pairingShapeResidual successor eq transition residual => exact residual

end SourceOperationNative.Tree.Fold.Dependent.Input
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
