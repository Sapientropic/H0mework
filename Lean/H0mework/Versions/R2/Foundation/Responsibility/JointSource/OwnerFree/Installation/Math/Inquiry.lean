import H0mework.Versions.R2.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source
import H0mework.Versions.R2.Foundation.Runtime.Inquiry

/-! The already admitted mathematical row answers from its actual state.
All tokens and the query input are source cofaces; the canonical root next is
unchanged and the earlier responsibility remains in the inherited inventory. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt old.visit.current →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))
variable (count : Nat)
abbrev original := old.root.toAuthoritativeRoot
abbrev baseRoot := Math.root (original old) old.visit.current reader
abbrev visit := Math.visit (original old) old.visit.current reader count
abbrev entry := Math.entry (original old) old.visit.current reader count
abbrev authority := Math.authority (original old) old.visit.current reader count
abbrev Ledger := (baseRoot old reader).source.base.restructuringSource.toLedgerSource
abbrev Occurrence (current : (vocabulary (original old) old.visit.current reader).Current) :=
  (Ledger old reader).source.toRootSource.actual.OccurrenceAt current
abbrev World := OwnerFree.World (original old) old.visit.current reader

def exactOccurrence {current : (vocabulary (original old) old.visit.current reader).Current}
    (occurrence : Occurrence old reader current) : Prop :=
  (⟨current, occurrence⟩ : Σ current, Occurrence old reader current) =
    ⟨(visit old reader count).current, (baseRoot old reader).emitted (visit old reader count).current⟩

abbrev U7 := RootGeneratedDebtActivationU7.extendU7
  (law := OwnerFree.law (original old) old.visit.current reader) old.U7
abbrev calculus := RootGeneratedDebtActivationU7.extendU7Calculus
  (law := OwnerFree.law (original old) old.visit.current reader) old.U7 old.calculus

variable {current : (vocabulary (original old) old.visit.current reader).Current}
variable (occurrence : Occurrence old reader current)
variable (active : ULift.{u,0} (PLift (exactOccurrence old reader count occurrence)))
def entryAt : OpenResponsibilityAt (World old reader)
    ((Ledger old reader).source.toRootSource.account.supportOf occurrence) := by
  have currentEq := congrArg Sigma.fst active.down.down
  cases currentEq
  have occurrenceEq := eq_of_heq (Sigma.mk.inj active.down.down).2
  cases occurrenceEq
  exact entry old reader count

abbrev Readout := Current (original old) old.visit.current reader
def readout (_occurrence : Occurrence old reader current) : Readout old reader := current

abbrev ActiveAt := fun (_ : PUnit.{u+1}) {current} (occurrence : Occurrence old reader current) =>
  ULift.{u,0} (PLift (exactOccurrence old reader count occurrence))
abbrev InactiveAt := fun (_ : PUnit.{u+1}) {current} (occurrence : Occurrence old reader current) =>
  ULift.{u,0} (PLift (¬ exactOccurrence old reader count occurrence))
def classify (projection : PUnit.{u+1}) {current} (occurrence : Occurrence old reader current) :
    ActiveAt old reader count projection occurrence ⊕ InactiveAt old reader count projection occurrence := by
  classical
  exact if same : exactOccurrence old reader count occurrence then .inl ⟨⟨same⟩⟩ else .inr ⟨⟨same⟩⟩

def consumerLaw : SourceNativeProjectionLaw (Ledger old reader) where
  Projection := PUnit.{u+1}
  ActiveAt := ActiveAt old reader count
  InactiveAt := InactiveAt old reader count
  classify := classify old reader count
  PayloadAt := fun _ {_current} occurrence active => SourceNativeInquiryAnswerConsumerTokenAt
    PUnit.unit (ULift.up.{u+1,u} occurrence) (entryAt old reader count occurrence active) (readout old reader occurrence)
  project := fun _ {_current} _ _ => .canonical

abbrev consumerRoot := (baseRoot old reader).withProjectionCoface (consumerLaw old reader count)
def compilationLaw : SourceNativeProjectionLaw (Ledger old reader) where
  Projection := PUnit.{u+1}
  ActiveAt := ActiveAt old reader count
  InactiveAt := InactiveAt old reader count
  classify := classify old reader count
  PayloadAt := fun _ {_current} occurrence active => SourceNativeInquiryCompilationTokenAt
    (U7 := U7 old reader) (calculus := calculus old reader) (oldTheory := (baseRoot old reader).source.base.lawSurface)
    (entryAt old reader count occurrence active) PUnit.unit (ULift.up.{u+1,u} occurrence) .answered (Readout old reader)
  project := fun _ {_current} occurrence _ => .canonical (readout old reader occurrence)

abbrev compilationRoot := (consumerRoot old reader count).withProjectionCoface (compilationLaw old reader count)
def queryLaw : SourceNativeProjectionLaw (Ledger old reader) where
  Projection := PUnit.{u+1}
  ActiveAt := ActiveAt old reader count
  InactiveAt := InactiveAt old reader count
  classify := classify old reader count
  PayloadAt := fun _ {_current} _ _ => PUnit.{u+1}
  project := fun _ {_current} _ _ => PUnit.unit
abbrev root := (compilationRoot old reader count).withProjectionCoface (queryLaw old reader count)

private theorem classify_actual : classify old reader count PUnit.unit
    ((baseRoot old reader).emitted (visit old reader count).current) = .inl ⟨⟨rfl⟩⟩ := by
  unfold classify
  exact dif_pos rfl

def answerFace : SourceNativeRootSemanticFaceAt (root old reader count) (visit old reader count) where
  projection := .inherited (.inherited (.inherited ((baseInstallation (original old) old.visit.current reader).embed (.inr true))))
  active := PUnit.unit
  classifier_eq := rfl

def consumer : SourceNativeInquiryAnswerConsumerAt (root := root old reader count)
    (visit := visit old reader count) PUnit.unit
    (ULift.up.{u+1,u} ((root old reader count).emitted (visit old reader count).current))
    (entry old reader count) (answerFace old reader count) where
  projection := .inherited (.inherited (.component PUnit.unit))
  active := ⟨⟨rfl⟩⟩
  classifier_eq := classify_actual old reader count
  project_heq := HEq.rfl

abbrev entryAuthority := (((authority old reader count).withProjectionCoface (consumerLaw old reader count)).withProjectionCoface
  (compilationLaw old reader count)).withProjectionCoface (queryLaw old reader count)

def compilation : SourceNativeInquiryCompilationProgramAt (root old reader count) (visit old reader count)
    (U7 old reader) (calculus old reader) (baseRoot old reader).source.base.lawSurface PUnit.unit
    (ULift.up.{u+1,u} ((root old reader count).emitted (visit old reader count).current))
    (entry old reader count) (entryAuthority old reader count) where
  compile := fun _ => .answered (answerFace old reader count) (consumer old reader count)

def state : RootInquiryStateAt (World old reader) (vocabulary (original old) old.visit.current reader) where
  root := root old reader count
  visit := visit old reader count
  U7 := U7 old reader
  calculus := calculus old reader
  Query := PUnit.{u+1}
  entryAt := fun _ => entry old reader count
  authorityAt := fun _ => entryAuthority old reader count
  compilationProgramAt := fun question => by cases question; exact compilation old reader count
  compilationFaceAt := fun question => by
    cases question
    exact { projection := .inherited (.component PUnit.unit)
            active := ⟨⟨rfl⟩⟩
            classifier_eq := classify_actual old reader count
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro _ _ _ impossible; exact nomatch impossible

def input : SourceNativeRootInquiryInputAt (state old reader count).root (state old reader count).visit
    (state old reader count).Query where
  projection := .component PUnit.unit
  active := ⟨⟨rfl⟩⟩
  classifier_eq := classify_actual old reader count
  queryType_eq := rfl

theorem actual_state : (answerFace old reader count).rootRead = (visit old reader count).current := rfl

theorem compiled : (state old reader count).compileInquiry (input old reader count).query =
    .answered (answerFace old reader count) (consumer old reader count) := rfl

theorem actual_next : (RootInquiryProcessNode.answered
    ⟨World old reader, vocabulary (original old) old.visit.current reader, .create (state old reader count)⟩
    (input old reader count).query).erase =
    (⟨World old reader, (root old reader count).generatedNextCurrentAt (visit old reader count)⟩ : AnyAuthoritativeRootCurrent) := rfl


abbrev endpointCount := (Calculation.targetRuntime (original old) old.visit.current reader).state.down
abbrev endpointState := state old reader (endpointCount old reader)
abbrev endpointInput := input old reader (endpointCount old reader)

theorem endpoint_source_state : (answerFace old reader (endpointCount old reader)).rootRead =
    runtimeCurrent (original old) old.visit.current reader (Calculation.targetRuntime (original old) old.visit.current reader) := rfl

def originalMaterialFace : SourceNativeRootSemanticFaceAt (root old reader count) (visit old reader count) where
  projection := .inherited (.inherited (.inherited ((originalInstallation (original old) old.visit.current reader).embed PUnit.unit)))
  active := PUnit.unit
  classifier_eq := rfl

theorem original_material : (originalMaterialFace old reader count).rootRead =
    ⟨(original old).emitted old.visit.current, (original old).generatedLedgerAt old.visit.current,
      (original old).generatedPatchAt old.visit.current,
      (original old).source.restructuringSource.compiler.certifyRestructuring ((original old).emitted old.visit.current)⟩ := rfl

end RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
