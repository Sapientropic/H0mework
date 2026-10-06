import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Source
import H0mework.Versions.R2.Foundation.Runtime.Inquiry

/-! Exact root, visit and installed source calculus generate an inquiry
without a prior completed query state. The original mathematical row,
full history and source cofaces supply every authority and answer. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
open SourceOperationEffects SourceOperationExecution RootInquiryCompletion
open RootGeneratedDebtActivationJointSource.OwnerFree
open RootGeneratedDebtActivationJointSource.OwnerFree.Installation
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (sourceRoot : SourceNativeLivingRootClosure N V)
variable (sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot)
variable (sourceU7 : U7ProducerCalculus N)
variable (sourceCalculus : U7ObstructionEvolutionCalculus N sourceU7)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceVisit.current →
  Raw (Value:=Value) (Var:=Var) (sort:=sort))
variable (count : Nat)
abbrev original := sourceRoot.toAuthoritativeRoot
abbrev baseRoot := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.root (original sourceRoot) sourceVisit.current reader
abbrev visit := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.visit (original sourceRoot) sourceVisit.current reader count
abbrev entry := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.entry (original sourceRoot) sourceVisit.current reader count
abbrev authority := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.authority (original sourceRoot) sourceVisit.current reader count
abbrev Ledger := (baseRoot sourceRoot sourceVisit reader).source.base.restructuringSource.toLedgerSource
abbrev Occurrence (current : (vocabulary (original sourceRoot) sourceVisit.current reader).Current) :=
  (Ledger sourceRoot sourceVisit reader).source.toRootSource.actual.OccurrenceAt current
abbrev World := RootGeneratedDebtActivationJointSource.OwnerFree.World (original sourceRoot) sourceVisit.current reader

def exactOccurrence {current : (vocabulary (original sourceRoot) sourceVisit.current reader).Current}
    (occurrence : Occurrence sourceRoot sourceVisit reader current) : Prop :=
  (⟨current, occurrence⟩ : Σ current, Occurrence sourceRoot sourceVisit reader current) =
    ⟨(visit sourceRoot sourceVisit reader count).current, (baseRoot sourceRoot sourceVisit reader).emitted (visit sourceRoot sourceVisit reader count).current⟩

abbrev U7 := RootGeneratedDebtActivationU7.extendU7
  (law := RootGeneratedDebtActivationJointSource.OwnerFree.law (original sourceRoot) sourceVisit.current reader) sourceU7
abbrev calculus := RootGeneratedDebtActivationU7.extendU7Calculus
  (law := RootGeneratedDebtActivationJointSource.OwnerFree.law (original sourceRoot) sourceVisit.current reader) sourceU7 sourceCalculus

variable {current : (vocabulary (original sourceRoot) sourceVisit.current reader).Current}
variable (occurrence : Occurrence sourceRoot sourceVisit reader current)
variable (active : ULift.{u,0} (PLift (exactOccurrence sourceRoot sourceVisit reader count occurrence)))
def entryAt : OpenResponsibilityAt (World sourceRoot sourceVisit reader)
    ((Ledger sourceRoot sourceVisit reader).source.toRootSource.account.supportOf occurrence) := by
  have currentEq := congrArg Sigma.fst active.down.down
  cases currentEq
  have occurrenceEq := eq_of_heq (Sigma.mk.inj active.down.down).2
  cases occurrenceEq
  exact entry sourceRoot sourceVisit reader count

abbrev Readout := Current (original sourceRoot) sourceVisit.current reader
def readout (_occurrence : Occurrence sourceRoot sourceVisit reader current) : Readout sourceRoot sourceVisit reader := current

abbrev ActiveAt := fun (_ : PUnit.{u+1}) {current} (occurrence : Occurrence sourceRoot sourceVisit reader current) =>
  ULift.{u,0} (PLift (exactOccurrence sourceRoot sourceVisit reader count occurrence))
abbrev InactiveAt := fun (_ : PUnit.{u+1}) {current} (occurrence : Occurrence sourceRoot sourceVisit reader current) =>
  ULift.{u,0} (PLift (¬ exactOccurrence sourceRoot sourceVisit reader count occurrence))
def classify (projection : PUnit.{u+1}) {current} (occurrence : Occurrence sourceRoot sourceVisit reader current) :
    ActiveAt sourceRoot sourceVisit reader count projection occurrence ⊕ InactiveAt sourceRoot sourceVisit reader count projection occurrence := by
  classical
  exact if same : exactOccurrence sourceRoot sourceVisit reader count occurrence then .inl ⟨⟨same⟩⟩ else .inr ⟨⟨same⟩⟩

def consumerLaw : SourceNativeProjectionLaw (Ledger sourceRoot sourceVisit reader) where
  Projection := PUnit.{u+1}
  ActiveAt := ActiveAt sourceRoot sourceVisit reader count
  InactiveAt := InactiveAt sourceRoot sourceVisit reader count
  classify := classify sourceRoot sourceVisit reader count
  PayloadAt := fun _ {_current} occurrence active => SourceNativeInquiryAnswerConsumerTokenAt
    PUnit.unit (ULift.up.{u+1,u} occurrence) (entryAt sourceRoot sourceVisit reader count occurrence active) (readout sourceRoot sourceVisit reader occurrence)
  project := fun _ {_current} _ _ => .canonical

abbrev consumerRoot := (baseRoot sourceRoot sourceVisit reader).withProjectionCoface (consumerLaw sourceRoot sourceVisit reader count)
def compilationLaw : SourceNativeProjectionLaw (Ledger sourceRoot sourceVisit reader) where
  Projection := PUnit.{u+1}
  ActiveAt := ActiveAt sourceRoot sourceVisit reader count
  InactiveAt := InactiveAt sourceRoot sourceVisit reader count
  classify := classify sourceRoot sourceVisit reader count
  PayloadAt := fun _ {_current} occurrence active => SourceNativeInquiryCompilationTokenAt
    (U7 := U7 sourceRoot sourceVisit sourceU7 reader) (calculus := calculus sourceRoot sourceVisit sourceU7 sourceCalculus reader) (oldTheory := (baseRoot sourceRoot sourceVisit reader).source.base.lawSurface)
    (entryAt sourceRoot sourceVisit reader count occurrence active) PUnit.unit (ULift.up.{u+1,u} occurrence) .answered (Readout sourceRoot sourceVisit reader)
  project := fun _ {_current} occurrence _ => .canonical (readout sourceRoot sourceVisit reader occurrence)

abbrev compilationRoot := (consumerRoot sourceRoot sourceVisit reader count).withProjectionCoface (compilationLaw sourceRoot sourceVisit sourceU7 sourceCalculus reader count)
def queryLaw : SourceNativeProjectionLaw (Ledger sourceRoot sourceVisit reader) where
  Projection := PUnit.{u+1}
  ActiveAt := ActiveAt sourceRoot sourceVisit reader count
  InactiveAt := InactiveAt sourceRoot sourceVisit reader count
  classify := classify sourceRoot sourceVisit reader count
  PayloadAt := fun _ {_current} _ _ => PUnit.{u+1}
  project := fun _ {_current} _ _ => PUnit.unit
abbrev root := (compilationRoot sourceRoot sourceVisit sourceU7 sourceCalculus reader count).withProjectionCoface (queryLaw sourceRoot sourceVisit reader count)

private theorem classify_actual : classify sourceRoot sourceVisit reader count PUnit.unit
    ((baseRoot sourceRoot sourceVisit reader).emitted (visit sourceRoot sourceVisit reader count).current) = .inl ⟨⟨rfl⟩⟩ := by
  unfold classify
  exact dif_pos rfl

def answerFace : SourceNativeRootSemanticFaceAt (root sourceRoot sourceVisit sourceU7 sourceCalculus reader count) (visit sourceRoot sourceVisit reader count) where
  projection := .inherited (.inherited (.inherited ((baseInstallation (original sourceRoot) sourceVisit.current reader).embed (.inr (.inl true)))))
  active := PUnit.unit
  classifier_eq := rfl

def consumer : SourceNativeInquiryAnswerConsumerAt (root := root sourceRoot sourceVisit sourceU7 sourceCalculus reader count)
    (visit := visit sourceRoot sourceVisit reader count) PUnit.unit
    (ULift.up.{u+1,u} ((root sourceRoot sourceVisit sourceU7 sourceCalculus reader count).emitted (visit sourceRoot sourceVisit reader count).current))
    (entry sourceRoot sourceVisit reader count) (answerFace sourceRoot sourceVisit sourceU7 sourceCalculus reader count) where
  projection := .inherited (.inherited (.component PUnit.unit))
  active := ⟨⟨rfl⟩⟩
  classifier_eq := classify_actual sourceRoot sourceVisit reader count
  project_heq := HEq.rfl

abbrev entryAuthority := (((authority sourceRoot sourceVisit reader count).withProjectionCoface (consumerLaw sourceRoot sourceVisit reader count)).withProjectionCoface
  (compilationLaw sourceRoot sourceVisit sourceU7 sourceCalculus reader count)).withProjectionCoface (queryLaw sourceRoot sourceVisit reader count)

def compilation : SourceNativeInquiryCompilationProgramAt (root sourceRoot sourceVisit sourceU7 sourceCalculus reader count) (visit sourceRoot sourceVisit reader count)
    (U7 sourceRoot sourceVisit sourceU7 reader) (calculus sourceRoot sourceVisit sourceU7 sourceCalculus reader) (baseRoot sourceRoot sourceVisit reader).source.base.lawSurface PUnit.unit
    (ULift.up.{u+1,u} ((root sourceRoot sourceVisit sourceU7 sourceCalculus reader count).emitted (visit sourceRoot sourceVisit reader count).current))
    (entry sourceRoot sourceVisit reader count) (entryAuthority sourceRoot sourceVisit sourceU7 sourceCalculus reader count) where
  compile := fun _ => .answered (answerFace sourceRoot sourceVisit sourceU7 sourceCalculus reader count) (consumer sourceRoot sourceVisit sourceU7 sourceCalculus reader count)

def state : RootInquiryStateAt (World sourceRoot sourceVisit reader) (vocabulary (original sourceRoot) sourceVisit.current reader) where
  root := root sourceRoot sourceVisit sourceU7 sourceCalculus reader count
  visit := visit sourceRoot sourceVisit reader count
  U7 := U7 sourceRoot sourceVisit sourceU7 reader
  calculus := calculus sourceRoot sourceVisit sourceU7 sourceCalculus reader
  Query := PUnit.{u+1}
  entryAt := fun _ => entry sourceRoot sourceVisit reader count
  authorityAt := fun _ => entryAuthority sourceRoot sourceVisit sourceU7 sourceCalculus reader count
  compilationProgramAt := fun question => by cases question; exact compilation sourceRoot sourceVisit sourceU7 sourceCalculus reader count
  compilationFaceAt := fun question => by
    cases question
    exact { projection := .inherited (.component PUnit.unit)
            active := ⟨⟨rfl⟩⟩
            classifier_eq := classify_actual sourceRoot sourceVisit reader count
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by intro _ _ _ impossible; exact nomatch impossible

def input : SourceNativeRootInquiryInputAt (state sourceRoot sourceVisit sourceU7 sourceCalculus reader count).root (state sourceRoot sourceVisit sourceU7 sourceCalculus reader count).visit
    (state sourceRoot sourceVisit sourceU7 sourceCalculus reader count).Query where
  projection := .component PUnit.unit
  active := ⟨⟨rfl⟩⟩
  classifier_eq := classify_actual sourceRoot sourceVisit reader count
  queryType_eq := rfl

theorem actual_state : (answerFace sourceRoot sourceVisit sourceU7 sourceCalculus reader count).rootRead = (visit sourceRoot sourceVisit reader count).current := rfl

theorem compiled : (state sourceRoot sourceVisit sourceU7 sourceCalculus reader count).compileInquiry (input sourceRoot sourceVisit sourceU7 sourceCalculus reader count).query =
    .answered (answerFace sourceRoot sourceVisit sourceU7 sourceCalculus reader count) (consumer sourceRoot sourceVisit sourceU7 sourceCalculus reader count) := rfl

theorem actual_next : (RootInquiryProcessNode.answered
    ⟨World sourceRoot sourceVisit reader, vocabulary (original sourceRoot) sourceVisit.current reader, .create (state sourceRoot sourceVisit sourceU7 sourceCalculus reader count)⟩
    (input sourceRoot sourceVisit sourceU7 sourceCalculus reader count).query).erase =
    (⟨World sourceRoot sourceVisit reader, (root sourceRoot sourceVisit sourceU7 sourceCalculus reader count).generatedNextCurrentAt (visit sourceRoot sourceVisit reader count)⟩ : AnyAuthoritativeRootCurrent) := rfl


abbrev endpointCount := (Calculation.targetRuntime (original sourceRoot) sourceVisit.current reader).state.down
abbrev endpointState := state sourceRoot sourceVisit sourceU7 sourceCalculus reader (endpointCount sourceRoot sourceVisit reader)
abbrev endpointInput := input sourceRoot sourceVisit sourceU7 sourceCalculus reader (endpointCount sourceRoot sourceVisit reader)

theorem endpoint_source_state : (answerFace sourceRoot sourceVisit sourceU7 sourceCalculus reader (endpointCount sourceRoot sourceVisit reader)).rootRead =
    runtimeCurrent (original sourceRoot) sourceVisit.current reader (Calculation.targetRuntime (original sourceRoot) sourceVisit.current reader) := rfl

def originalMaterialFace : SourceNativeRootSemanticFaceAt (root sourceRoot sourceVisit sourceU7 sourceCalculus reader count) (visit sourceRoot sourceVisit reader count) where
  projection := .inherited (.inherited (.inherited ((originalInstallation (original sourceRoot) sourceVisit.current reader).embed PUnit.unit)))
  active := PUnit.unit
  classifier_eq := rfl

theorem original_material : (originalMaterialFace sourceRoot sourceVisit sourceU7 sourceCalculus reader count).rootRead =
    ⟨(original sourceRoot).emitted sourceVisit.current, (original sourceRoot).generatedLedgerAt sourceVisit.current,
      (original sourceRoot).generatedPatchAt sourceVisit.current,
      (original sourceRoot).source.restructuringSource.compiler.certifyRestructuring ((original sourceRoot).emitted sourceVisit.current)⟩ := rfl

end RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
