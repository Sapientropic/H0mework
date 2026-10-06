import H0mework.Versions.AB.Realization.Operations.Tree.Fold.Dependent.Source
import H0mework.Versions.AB.Realization.Operations.Tree.Fold.Recovery

/-! The component is active at one exact source visit. Its supplied occurrence
is eliminated against that source identity; a later visit regenerates the law.
A distinct calculation query consumes the code and inherits the old inventory. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Installation
open SourceOperationEffects SourceOperationExecution
open CofinalHistoryTransition RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open RootInquiryCompletion
namespace Q
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry
  (exactOccurrence state query resultFace consumer compiles answered_next result_value result_history
    originalCompilationFace original_compilation_preserved)
end Q
variable (old : RootInquiryStateAt N V) (recognition : RecognitionAt H old.root)
abbrev actualStep := recognition.generateStepAt old.visit
abbrev selected := settlePassiveEffect (actualStep old recognition)
abbrev Occurrence (current : V.Current) := old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current

def PayloadAt {current : V.Current} (occurrence : Occurrence old current)
    (active : ULift.{u,0} (PLift (Q.exactOccurrence old occurrence))) : Type u := by
  have currentEq := congrArg Sigma.fst active.down.down
  cases currentEq
  have occurrenceEq := eq_of_heq (Sigma.mk.inj active.down.down).2
  cases occurrenceEq
  exact FeedAt (actualStep old recognition) (selected old recognition)

def project {current : V.Current} (occurrence : Occurrence old current)
    (active : ULift.{u,0} (PLift (Q.exactOccurrence old occurrence))) : PayloadAt old recognition occurrence active := by
  have currentEq := congrArg Sigma.fst active.down.down
  cases currentEq
  have occurrenceEq := eq_of_heq (Sigma.mk.inj active.down.down).2
  cases occurrenceEq
  exact sourceFeed (actualStep old recognition)

def component : SourceNativeProjectionLaw old.root.toAuthoritativeRoot.source.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} occurrence => ULift.{u,0} (PLift (Q.exactOccurrence old occurrence))
  InactiveAt := fun _ {_current} occurrence => ULift.{u,0} (PLift (¬ Q.exactOccurrence old occurrence))
  classify := by
    classical
    intro projection current occurrence
    exact if same : Q.exactOccurrence old occurrence then .inl ⟨⟨same⟩⟩ else .inr ⟨⟨same⟩⟩
  PayloadAt := fun _ {_current} occurrence active => PayloadAt old recognition occurrence active
  project := fun _ {_current} occurrence active => project old recognition occurrence active

abbrev sourceRoot := old.root.withProjectionCoface (component old recognition)
abbrev componentInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface old.root.source.base (component old recognition)

def materialFace : SourceNativeRootSemanticFaceAt (sourceRoot old recognition) old.visit where
  projection := (componentInstallation old recognition).embed PUnit.unit
  active := ⟨⟨rfl⟩⟩
  classifier_eq := by
    change (component old recognition).classify PUnit.unit (old.root.emitted old.visit.current) = .inl ⟨⟨rfl⟩⟩
    unfold component
    exact dif_pos rfl

theorem material_generated : HEq (materialFace old recognition).rootRead (generatedFeed recognition old.visit) := HEq.rfl

-- This helper is instantiated only by the original source disposition below.
variable (successor : StepLedgerSuccessorAt (actualStep old recognition))
variable (transition : GeneratedStepJointTransitionAt (actualStep old recognition) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (actualStep old recognition)) (stepTargetPairingOccurrence (actualStep old recognition) successor))

/-- This archived formula belongs to this visit's exact calculation query.
The component's active source equation identifies its tree; it is regenerated
when a different visit is queried. -/
abbrev reader := fun {_current : V.Current} (_occurrence : Occurrence old _current) =>
  nativeRaw (actualStep old recognition) successor transition alignment
abbrev calculation := Q.state old (reader old recognition successor transition alignment)
abbrev calculationRoot := (calculation old recognition successor transition alignment).root.withProjectionCoface (component old recognition)
abbrev inherited := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (calculation old recognition successor transition alignment).root.source.base (component old recognition)

def answer : SourceNativeRootSemanticFaceAt (calculationRoot old recognition successor transition alignment) old.visit where
  projection := (inherited old recognition successor transition alignment).embed
    (Q.resultFace old (reader old recognition successor transition alignment)).projection
  active := (Q.resultFace old (reader old recognition successor transition alignment)).active
  classifier_eq := (Q.resultFace old (reader old recognition successor transition alignment)).classifier_eq

abbrev Query := (calculation old recognition successor transition alignment).Query
variable (question : Query old recognition successor transition alignment)

def answerConsumer : SourceNativeInquiryAnswerConsumerAt (root := calculationRoot old recognition successor transition alignment)
    (visit := old.visit) question
    (ULift.up.{u+1,u} ((calculationRoot old recognition successor transition alignment).emitted old.visit.current))
    ((calculation old recognition successor transition alignment).entryAt question) (answer old recognition successor transition alignment) where
  projection := (inherited old recognition successor transition alignment).embed
    (Q.consumer old (reader old recognition successor transition alignment) question).projection
  active := (Q.consumer old (reader old recognition successor transition alignment) question).active
  classifier_eq := (Q.consumer old (reader old recognition successor transition alignment) question).classifier_eq
  project_heq := HEq.rfl

abbrev authority := ((calculation old recognition successor transition alignment).authorityAt question).withProjectionCoface
  (component old recognition)

def compilation : SourceNativeInquiryCompilationProgramAt (calculationRoot old recognition successor transition alignment) old.visit
    old.U7 old.calculus old.root.source.base.lawSurface question
    (ULift.up.{u+1,u} ((calculationRoot old recognition successor transition alignment).emitted old.visit.current))
    ((calculation old recognition successor transition alignment).entryAt question)
    (authority old recognition successor transition alignment question) where
  compile := fun _ => .answered (answer old recognition successor transition alignment)
    (answerConsumer old recognition successor transition alignment question)

def inquiry : RootInquiryStateAt N V where
  root := calculationRoot old recognition successor transition alignment
  visit := old.visit
  U7 := old.U7
  calculus := old.calculus
  Query := Query old recognition successor transition alignment
  entryAt := (calculation old recognition successor transition alignment).entryAt
  authorityAt := authority old recognition successor transition alignment
  compilationProgramAt := compilation old recognition successor transition alignment
  compilationFaceAt := fun candidate => {
    projection := (inherited old recognition successor transition alignment).embed
      ((calculation old recognition successor transition alignment).compilationFaceAt candidate).projection
    active := ((calculation old recognition successor transition alignment).compilationFaceAt candidate).active
    classifier_eq := ((calculation old recognition successor transition alignment).compilationFaceAt candidate).classifier_eq
    project_heq := ((calculation old recognition successor transition alignment).compilationFaceAt candidate).project_heq }
  u7RootDisposition_commutes := by
    intro candidate obstruction audit impossible
    exact nomatch impossible

def inheritedMaterial : SourceNativeRootSemanticFaceAt (inquiry old recognition successor transition alignment).root old.visit where
  projection := (SourceNativeProjectionLaw.InstallationAt.componentCoface
    (calculation old recognition successor transition alignment).root.source.base (component old recognition)).embed PUnit.unit
  active := ⟨⟨rfl⟩⟩
  classifier_eq := (materialFace old recognition).classifier_eq

theorem inquiry_material : HEq (inheritedMaterial old recognition successor transition alignment).rootRead
    (generatedFeed recognition old.visit) := HEq.rfl

theorem inquiry_value : (answer old recognition successor transition alignment).rootRead.2.2.1 =
    Finsupp.single (settleTree (actualStep old recognition) successor transition.history
      (nativeTree (actualStep old recognition) successor transition alignment)) 1 :=
  (Q.result_value old (reader old recognition successor transition alignment)).trans (F.program_value _ _)

theorem inquiry_next : (RootInquiryProcessNode.answered
    ⟨N,V,.create (inquiry old recognition successor transition alignment)⟩ question).erase =
    (⟨N, (inquiry old recognition successor transition alignment).root.generatedNextCurrentAt old.visit⟩ : AnyAuthoritativeRootCurrent) := rfl


theorem query_tree (incidence : old.Query) : SourceOperationNative.Tree.Fold.Inverse.readTree
    (Q.query old (reader old recognition successor transition alignment) incidence).raw.expression =
      some (nativeTree (actualStep old recognition) successor transition alignment) :=
  SourceOperationNative.Tree.Fold.Inverse.read_program _ _

theorem result_tree : SourceOperationNative.Tree.Fold.Inverse.readTree
    (answer old recognition successor transition alignment).rootRead.1.expression =
      some (nativeTree (actualStep old recognition) successor transition alignment) :=
  SourceOperationNative.Tree.Fold.Inverse.read_program _ _

theorem result_source_state : (answer old recognition successor transition alignment).rootRead.2.1 =
    (nativePacket (actualStep old recognition) successor transition alignment).2.1 := rfl


def oldCompilationFace (incidence : old.Query) : SourceNativeRootSemanticFaceAt
    (inquiry old recognition successor transition alignment).root old.visit where
  projection := (inherited old recognition successor transition alignment).embed
    (Q.originalCompilationFace old (reader old recognition successor transition alignment) incidence).projection
  active := (Q.originalCompilationFace old (reader old recognition successor transition alignment) incidence).active
  classifier_eq := (Q.originalCompilationFace old (reader old recognition successor transition alignment) incidence).classifier_eq

theorem old_compilation_preserved (incidence : old.Query) :
    HEq (oldCompilationFace old recognition successor transition alignment incidence).rootRead
      (SourceNativeInquiryCompilationTokenAt.canonical (entry := old.entryAt incidence) (query := incidence)
        (event := old.emitInquiry incidence) (audit := (old.compileInquiry incidence).audit)
        (old.compileInquiry incidence).answerReadout) :=
  Q.original_compilation_preserved old (reader old recognition successor transition alignment) incidence

def generatedInquiry : Option (RootInquiryStateAt N V) :=
  match selected old recognition with
  | .allGenerated next _ carry => some (inquiry old recognition next carry.historyTransition carry.pairingAlignment)
  | .jointResidual next _ transitionNext align _ _ _ => some (inquiry old recognition next transitionNext align)
  | _ => none


end SourceOperationNative.Tree.Fold.Dependent.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
