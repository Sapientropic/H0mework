import H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Installation.Source
import H0mework.Versions.R2.Foundation.Runtime.Inquiry

/-! A mathematical inquiry consumes the occurrence's generated full result.
The original query incidence only grounds its source ownership; no original
claim is discharged by replacing it with a scalar answer. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : {current : V.Current} → old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
  Raw (Value := Value) (Var := Var) (sort := sort))

abbrev Base := old.root.toAuthoritativeRoot

/-- A source calculation query has an original incidence as provenance. It
is a different query type from that incidence's original mathematical goal. -/
structure CalculationQuery where
  private mk ::
  incidence : old.Query
  occurrence : old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt old.visit.current
  raw : Raw (Value := Value) (Var := Var) (sort := sort)
  private occurrence_eq : occurrence = old.root.emitted old.visit.current
  private raw_eq : raw = reader occurrence

def query (incidence : old.Query) : CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader :=
  ⟨incidence, old.root.emitted old.visit.current, reader (old.root.emitted old.visit.current), rfl, rfl⟩
abbrev Occurrence := (current : V.Current) × old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current

def exactOccurrence {current : V.Current}
    (occurrence : old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) : Prop :=
  (⟨current, occurrence⟩ : Occurrence old) = ⟨old.visit.current, old.root.emitted old.visit.current⟩

def entryAt (query : CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader) {current : V.Current}
    (occurrence : old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current)
    (active : ULift.{u, 0} (PLift (exactOccurrence old occurrence))) : OpenResponsibilityAt N
      (old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf occurrence) := by
  have currentEq : current = old.visit.current := congrArg Sigma.fst active.down.down
  cases currentEq
  have sourceEq : occurrence = old.root.emitted old.visit.current := eq_of_heq (Sigma.mk.inj active.down.down).2
  cases sourceEq
  exact old.entryAt query.incidence

def consumerLaw : SourceNativeProjectionLaw (Base old).source.restructuringSource.toLedgerSource where
  Projection := CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader
  ActiveAt := fun _ {_current} occurrence => ULift.{u, 0} (PLift (exactOccurrence old occurrence))
  InactiveAt := fun _ {_current} occurrence => ULift.{u, 0} (PLift (¬ exactOccurrence old occurrence))
  classify := by
    classical
    intro query current occurrence
    exact if same : exactOccurrence old occurrence then .inl ⟨⟨same⟩⟩ else .inr ⟨⟨same⟩⟩
  PayloadAt := fun query {_current} occurrence active => SourceNativeInquiryAnswerConsumerTokenAt
    query (ULift.up.{u + 1, u} occurrence) (entryAt old reader query occurrence active)
    (resultAt (Base old) reader occurrence)
  project := fun _ {_current} _ _ => .canonical

def resultSource := (Base old).source.withProjectionCoface (resultLaw (Base old) reader)
def consumerSource := (resultSource old reader).withProjectionCoface (consumerLaw old reader)

def compilationLaw : SourceNativeProjectionLaw (Base old).source.restructuringSource.toLedgerSource where
  Projection := CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader
  ActiveAt := fun _ {_current} occurrence => ULift.{u, 0} (PLift (exactOccurrence old occurrence))
  InactiveAt := fun _ {_current} occurrence => ULift.{u, 0} (PLift (¬ exactOccurrence old occurrence))
  classify := by
    classical
    intro query current occurrence
    exact if same : exactOccurrence old occurrence then .inl ⟨⟨same⟩⟩ else .inr ⟨⟨same⟩⟩
  PayloadAt := fun query {_current} occurrence active => SourceNativeInquiryCompilationTokenAt
    (U7 := old.U7) (calculus := old.calculus) (oldTheory := old.root.source.base.lawSurface)
    (entryAt old reader query occurrence active) query (ULift.up.{u + 1, u} occurrence) .answered
    (ResultAt (Base old) reader occurrence)
  project := fun _ {_current} occurrence _ => .canonical (resultAt (Base old) reader occurrence)

def root := ((old.root.withProjectionCoface (resultLaw (Base old) reader)).withProjectionCoface
  (consumerLaw old reader)).withProjectionCoface (compilationLaw old reader)

abbrev visit : SourceNativeTemporalVisitAt (root old reader).toAuthoritativeRoot.toLedgerRoot := old.visit

def resultInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (Base old).source (resultLaw (Base old) reader)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (resultSource old reader) (consumerLaw old reader)) |>.trans
      (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (consumerSource old reader) (compilationLaw old reader))

def consumerInstallation := (SourceNativeProjectionLaw.InstallationAt.componentCoface
  (resultSource old reader) (consumerLaw old reader)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (consumerSource old reader) (compilationLaw old reader))

def compilationInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
  (consumerSource old reader) (compilationLaw old reader)

def oldInstallation := (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (Base old).source (resultLaw (Base old) reader)).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (resultSource old reader) (consumerLaw old reader)) |>.trans
      (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (consumerSource old reader) (compilationLaw old reader))

def resultFace : SourceNativeRootSemanticFaceAt (root old reader) (visit old reader) where
  projection := (resultInstallation old reader).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def consumer (query : CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader) : SourceNativeInquiryAnswerConsumerAt (root := root old reader) (visit := visit old reader) query
    (ULift.up.{u + 1, u} ((root old reader).emitted (visit old reader).current))
    (old.entryAt query.incidence) (resultFace old reader) where
  projection := (consumerInstallation old reader).embed query
  active := ⟨⟨rfl⟩⟩
  classifier_eq := by
    change (consumerLaw old reader).classify query (old.root.emitted old.visit.current) = .inl ⟨⟨rfl⟩⟩
    unfold consumerLaw
    exact dif_pos (show exactOccurrence old (old.root.emitted old.visit.current) from rfl)
  project_heq := by
    have entryEq : entryAt old reader query (old.root.emitted old.visit.current) ⟨⟨rfl⟩⟩ = old.entryAt query.incidence := rfl
    change HEq (SourceNativeInquiryAnswerConsumerTokenAt.canonical :
      SourceNativeInquiryAnswerConsumerTokenAt query _ (entryAt old reader query _ ⟨⟨rfl⟩⟩) _) _
    rw [entryEq]
    rfl

def authority (query : CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader) : SourceNativeLivingTemporalCausalEntryAuthorityAt
    (root old reader) (visit old reader) (old.entryAt query.incidence) :=
  (((old.authorityAt query.incidence).withProjectionCoface (resultLaw (Base old) reader)).withProjectionCoface
    (consumerLaw old reader)).withProjectionCoface (compilationLaw old reader)

def compilation (query : CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader) : SourceNativeInquiryCompilationProgramAt
    (root old reader) (visit old reader) old.U7 old.calculus old.root.source.base.lawSurface
    query (ULift.up.{u + 1, u} ((root old reader).emitted (visit old reader).current))
    (old.entryAt query.incidence) (authority old reader query) where
  compile := fun _ => .answered (resultFace old reader) (consumer old reader query)

def state : RootInquiryStateAt N V where
  root := root old reader
  visit := visit old reader
  U7 := old.U7
  calculus := old.calculus
  Query := CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader
  entryAt := fun query => old.entryAt query.incidence
  authorityAt := authority old reader
  compilationProgramAt := compilation old reader
  compilationFaceAt := fun query => {
    projection := (compilationInstallation old reader).embed query
    active := ⟨⟨rfl⟩⟩
    classifier_eq := by
      change (compilationLaw old reader).classify query (old.root.emitted old.visit.current) = .inl ⟨⟨rfl⟩⟩
      unfold compilationLaw
      exact dif_pos (show exactOccurrence old (old.root.emitted old.visit.current) from rfl)
    project_heq := by
      change HEq (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := entryAt old reader query _ ⟨⟨rfl⟩⟩) (query := query) (event := _) (audit := .answered)
        (resultAt (Base old) reader _)) _
      have entryEq : entryAt old reader query (old.root.emitted old.visit.current) ⟨⟨rfl⟩⟩ = old.entryAt query.incidence := rfl
      rw [entryEq]
      rfl }
  u7RootDisposition_commutes := by
    intro query obstruction audit impossible
    exact nomatch impossible

def presentation : RootInquiryStatePresentation where
  N := N
  V := V
  state := .create (state old reader)

theorem compiles (query : CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader) : (state old reader).compileInquiry query =
    .answered (resultFace old reader) (consumer old reader query) := rfl

theorem answered_next (query : CalculationQuery (Value := Value) (Var := Var) (sort := sort) old reader) :
    (RootInquiryProcessNode.answered (presentation old reader) query).erase =
      (⟨N, (root old reader).generatedNextCurrentAt (visit old reader)⟩ : AnyAuthoritativeRootCurrent) := rfl

theorem result_value : (resultFace old reader).rootRead.2.2.1 =
    (reader (old.root.emitted old.visit.current)).expression.eval
      (reader (old.root.emitted old.visit.current)).environment :=
  source_value (Base old) reader (old.root.emitted old.visit.current)

theorem result_history : (resultFace old reader).rootRead.2.1.2.length =
    remaining (reader (old.root.emitted old.visit.current)).expression :=
  source_history (Base old) reader (old.root.emitted old.visit.current)

def originalCompilationFace (incidence : old.Query) : SourceNativeRootSemanticFaceAt (root old reader) (visit old reader) where
  projection := (oldInstallation old reader).embed (old.compilationFaceAt incidence).projection
  active := (old.compilationFaceAt incidence).active
  classifier_eq := (old.compilationFaceAt incidence).classifier_eq

theorem original_compilation_preserved (incidence : old.Query) :
    HEq (originalCompilationFace old reader incidence).rootRead
      (SourceNativeInquiryCompilationTokenAt.canonical (entry := old.entryAt incidence)
        (query := incidence) (event := old.emitInquiry incidence)
        (audit := (old.compileInquiry incidence).audit) (old.compileInquiry incidence).answerReadout) :=
  (old.compilationFaceAt incidence).project_heq

theorem query_occurrence (incidence : old.Query) : (query old reader incidence).occurrence =
    old.root.emitted old.visit.current := rfl

theorem query_raw (incidence : old.Query) : (query old reader incidence).raw =
    reader (old.root.emitted old.visit.current) := rfl

end RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
