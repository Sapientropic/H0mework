import H0mework.Versions.R2.Realization.Operations.Tree.Fold.Dependent.Input.Source

/-! The installed input is read by the original inquiry compiler. Its source
material, parser, complete mathematical state and old compilation remain
inherited. Canonical next uses the existing kernel; no controller is created. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Input
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open CofinalHistoryTransition RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (old : RootInquiryStateAt N V) (recognition : RecognitionAt H old.root)
variable (original : SourceNativeRootInquiryInputAt old.root old.visit old.Query)
variable (next : StepLedgerSuccessorAt (I.actualStep old recognition))
variable (history : GeneratedStepJointTransitionAt (I.actualStep old recognition) next)
variable (zip : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (I.actualStep old recognition)) (stepTargetPairingOccurrence (I.actualStep old recognition) next))

abbrev inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (I.inquiry old recognition next history zip).root.source.base (queryLaw old recognition original next history zip)

def resultFace : SourceNativeRootSemanticFaceAt (inputRoot old recognition original next history zip) old.visit where
  projection := (inherited old recognition original next history zip).embed (I.answer old recognition next history zip).projection
  active := (I.answer old recognition next history zip).active
  classifier_eq := (I.answer old recognition next history zip).classifier_eq

variable (candidate : I.Query old recognition next history zip)
def consumer : SourceNativeInquiryAnswerConsumerAt (root := inputRoot old recognition original next history zip)
    (visit := inputVisit old recognition original next history zip)
    candidate (ULift.up.{u+1,u} ((inputRoot old recognition original next history zip).emitted old.visit.current))
    (old.entryAt candidate.incidence) (resultFace old recognition original next history zip) where
  projection := (inherited old recognition original next history zip).embed (I.answerConsumer old recognition next history zip candidate).projection
  active := (I.answerConsumer old recognition next history zip candidate).active
  classifier_eq := (I.answerConsumer old recognition next history zip candidate).classifier_eq
  project_heq := (I.answerConsumer old recognition next history zip candidate).project_heq

def authority : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (inputRoot old recognition original next history zip) (inputVisit old recognition original next history zip)
    (old.entryAt candidate.incidence) :=
  ((I.inquiry old recognition next history zip).authorityAt candidate).withProjectionCoface
    (queryLaw old recognition original next history zip)

def compilation : SourceNativeInquiryCompilationProgramAt (inputRoot old recognition original next history zip) (inputVisit old recognition original next history zip)
    old.U7 old.calculus old.root.source.base.lawSurface candidate
    (ULift.up.{u+1,u} ((inputRoot old recognition original next history zip).emitted old.visit.current))
    (old.entryAt candidate.incidence)
    (authority old recognition original next history zip candidate) where
  compile := fun _ => .answered (resultFace old recognition original next history zip)
    (consumer old recognition original next history zip candidate)

def inputState : RootInquiryStateAt N V where
  root := inputRoot old recognition original next history zip
  visit := inputVisit old recognition original next history zip
  U7 := old.U7
  calculus := old.calculus
  Query := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.CalculationQuery
    old (I.reader old recognition next history zip)
  entryAt := fun candidate => old.entryAt candidate.incidence
  authorityAt := authority old recognition original next history zip
  compilationProgramAt := compilation old recognition original next history zip
  compilationFaceAt := fun query => {
    projection := (inherited old recognition original next history zip).embed
      ((I.inquiry old recognition next history zip).compilationFaceAt query).projection
    active := ((I.inquiry old recognition next history zip).compilationFaceAt query).active
    classifier_eq := ((I.inquiry old recognition next history zip).compilationFaceAt query).classifier_eq
    project_heq := ((I.inquiry old recognition next history zip).compilationFaceAt query).project_heq }
  u7RootDisposition_commutes := by intro query obstruction audit impossible; exact nomatch impossible

abbrev actualQuery := (queryInput old recognition original next history zip).query

theorem actual_compiled : (inputState old recognition original next history zip).compileInquiry
    (actualQuery old recognition original next history zip) = .answered
      (resultFace old recognition original next history zip)
      (consumer old recognition original next history zip (actualQuery old recognition original next history zip)) := rfl

theorem actual_next : (RootInquiryProcessNode.answered
    ⟨N,V,.create (inputState old recognition original next history zip)⟩
    (actualQuery old recognition original next history zip)).erase =
    (⟨N,(inputRoot old recognition original next history zip).generatedNextCurrentAt old.visit⟩ : AnyAuthoritativeRootCurrent) := rfl


def materialFace : SourceNativeRootSemanticFaceAt (inputRoot old recognition original next history zip)
    (inputVisit old recognition original next history zip) where
  projection := (inherited old recognition original next history zip).embed (I.inheritedMaterial old recognition next history zip).projection
  active := (I.inheritedMaterial old recognition next history zip).active
  classifier_eq := (I.inheritedMaterial old recognition next history zip).classifier_eq

theorem material_generated : HEq (materialFace old recognition original next history zip).rootRead
    (D.generatedFeed recognition old.visit) := HEq.rfl

theorem actual_tree : SourceOperationNative.Tree.Fold.Inverse.readTree
    (actualQuery old recognition original next history zip).raw.expression =
      some (SourceOperationNative.Tree.Fold.Dependent.nativeTree (I.actualStep old recognition) next history zip) :=
  I.query_tree old recognition next history zip original.query

theorem result_tree : SourceOperationNative.Tree.Fold.Inverse.readTree
    (resultFace old recognition original next history zip).rootRead.1.expression =
      some (SourceOperationNative.Tree.Fold.Dependent.nativeTree (I.actualStep old recognition) next history zip) :=
  I.result_tree old recognition next history zip

theorem actual_value : (resultFace old recognition original next history zip).rootRead.2.2.1 =
    Finsupp.single (settleTree (I.actualStep old recognition) next history.history
      (SourceOperationNative.Tree.Fold.Dependent.nativeTree (I.actualStep old recognition) next history zip)) 1 :=
  I.inquiry_value old recognition next history zip

theorem result_source_state : (resultFace old recognition original next history zip).rootRead.2.1 =
    (SourceOperationNative.Tree.Fold.Dependent.nativePacket (I.actualStep old recognition) next history zip).2.1 :=
  I.result_source_state old recognition next history zip

def originalCompilationFace (incidence : old.Query) : SourceNativeRootSemanticFaceAt
    (inputRoot old recognition original next history zip) (inputVisit old recognition original next history zip) where
  projection := (inherited old recognition original next history zip).embed (I.oldCompilationFace old recognition next history zip incidence).projection
  active := (I.oldCompilationFace old recognition next history zip incidence).active
  classifier_eq := (I.oldCompilationFace old recognition next history zip incidence).classifier_eq

theorem old_compilation_preserved (incidence : old.Query) :
    HEq (originalCompilationFace old recognition original next history zip incidence).rootRead
      (SourceNativeInquiryCompilationTokenAt.canonical (entry := old.entryAt incidence) (query := incidence)
        (event := old.emitInquiry incidence) (audit := (old.compileInquiry incidence).audit)
        (old.compileInquiry incidence).answerReadout) :=
  I.old_compilation_preserved old recognition next history zip incidence

abbrev InputState := Σ state : RootInquiryStateAt N V,
  SourceNativeRootInquiryInputAt state.root state.visit state.Query

def generatedState : Option (InputState (N:=N) (V:=V)) :=
  match I.selected old recognition with
  | .allGenerated successor _ carry => some ⟨inputState old recognition original successor carry.historyTransition carry.pairingAlignment,
      queryInput old recognition original successor carry.historyTransition carry.pairingAlignment⟩
  | .jointResidual successor _ transition alignment _ _ _ => some ⟨inputState old recognition original successor transition alignment,
      queryInput old recognition original successor transition alignment⟩
  | _ => none

end SourceOperationNative.Tree.Fold.Dependent.Input
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
