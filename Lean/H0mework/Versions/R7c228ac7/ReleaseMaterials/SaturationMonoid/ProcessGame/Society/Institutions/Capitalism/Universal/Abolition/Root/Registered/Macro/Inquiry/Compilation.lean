import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry.Package
import H0mework.Versions.Rdf421ff6.Foundation.Runtime.Inquiry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (package : Package (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  (visit : SourceNativeTemporalVisitAt package.frame.root.toAuthoritativeRoot.toLedgerRoot)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt package.frame.root visit (package.frame.entry visit.current))

abbrev Query := Raw.QueryAt package.source package.sourceData package.reader visit.current

def answerFace (work : HasWork package.source visit.current) : SourceNativeRootSemanticFaceAt package.frame.root visit where
  projection := (Raw.installation package.source package.sourceData package.reader package.basis).embed .internalAnswer
  active := ⟨work⟩
  classifier_eq := by
    change Raw.classify package.source package.sourceData .internalAnswer _ = _
    exact dif_pos work

def consumer (work : HasWork package.source visit.current) (ordinary : NotIssue package.source visit.current) :
    SourceNativeInquiryAnswerConsumerAt (Raw.QueryAt.internal work : Query package visit)
      (ULift.up.{1, 0} (package.frame.root.emitted visit.current))
      (package.frame.entry visit.current) (answerFace package visit work) where
  projection := (Raw.installation package.source package.sourceData package.reader package.basis).embed .internalConsumer
  active := ⟨work, ordinary⟩
  classifier_eq := by
    change Raw.classify package.source package.sourceData .internalConsumer _ = _
    exact dif_pos ⟨work, ordinary⟩
  project_heq := HEq.rfl

def debtCore (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition package.frame visit.current) :=
  (Admission.completeProgram package.frame package.data package.reader package.basis visit registered authority).generate
    (package.frame.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit)

def rawCore (germ : Raw.GermAt package.source package.sourceData package.reader visit.current) :=
  Raw.Target.generated package.source package.sourceData package.reader package.basis visit germ authority

theorem no_registration_is_ordinary
    (absent : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition package.frame visit.current = none) :
    NotIssue package.source visit.current := by
  change NotIssue package.frame visit.current
  unfold headRegistration? at absent
  split at absent
  next noHead => simp only [NotIssue, noHead]
  next item found =>
    cases parsed : registration? input depth count item (package.frame.account visit.current) with
    | none => simp only [NotIssue, found, parsed, Option.isSome_none]
    | some registered => rw [parsed] at absent; cases absent

def compilation (query : Query package visit) :
    SourceNativeInquiryCompilationAt package.frame.root visit package.basis.U7 package.basis.calculus
      package.frame.root.toAuthoritativeRoot.source.lawSurface query
      (ULift.up.{1, 0} (package.frame.root.emitted visit.current)) (package.frame.entry visit.current) authority :=
  match query with
  | .internal work =>
    match selected : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition package.frame visit.current with
    | some registered => .debtAdmission (debtCore package visit authority registered)
    | none => .answered (answerFace package visit work)
        (consumer package visit work (no_registration_is_ordinary package visit selected))
  | .raw germ => .actualAction (rawCore package visit authority germ)

def AnswerAt (query : Query package visit) : Type := match query with
  | .internal _ => Answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  | .raw germ => Raw.ResultAt package.source package.sourceData package.reader germ

def sourceAnswer (query : Query package visit) : AnswerAt package visit query := match query with
  | .internal _ => answer (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition package.source visit.current
  | .raw germ => Raw.reportAt package.source package.sourceData package.reader germ

theorem compilation_audit (query : Query package visit) :
    (compilation package visit authority query).audit = .answered := by
  cases query with
  | internal work => unfold compilation; split <;> rfl
  | raw germ => rfl

theorem compilation_answer (query : Query package visit) :
    HEq (compilation package visit authority query).answerReadout (sourceAnswer package visit query) := by
  cases query with
  | internal work => unfold compilation; split <;> exact HEq.rfl
  | raw germ => exact HEq.rfl

private theorem token_heq {N : WorldRelationNetwork} {U7 : U7ProducerCalculus N}
    {calculus : U7ObstructionEvolutionCalculus N U7} {theory : TheoryState N} {support : N.Support}
    (entry : OpenResponsibilityAt N support) {Query : Type} (query : Query) {Event : Type 1} (event : Event)
    (audit : SourceNativeInquiryFrontAuditAt U7 calculus theory support)
    {A B : Type} (left : A) (right : B) (same : HEq left right) :
    HEq (SourceNativeInquiryCompilationTokenAt.canonical (entry := entry) (query := query) (event := event) (audit := audit) left)
      (SourceNativeInquiryCompilationTokenAt.canonical (entry := entry) (query := query) (event := event) (audit := audit) right) := by
  cases same
  rfl

private theorem raw_token_heq
    (left right : Raw.GermAt package.source package.sourceData package.reader visit.current)
    (same : left = right) :
    HEq
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := package.frame.entry visit.current) (query := Raw.QueryAt.raw left)
        (event := ULift.up.{1, 0} (package.frame.root.emitted visit.current))
        (audit := (.answered : SourceNativeInquiryFrontAuditAt package.basis.U7 package.basis.calculus
          package.frame.root.toAuthoritativeRoot.source.lawSurface (package.frame.sourceSupport visit.current)))
        (Raw.reportAt package.source package.sourceData package.reader left))
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := package.frame.entry visit.current) (query := Raw.QueryAt.raw right)
        (event := ULift.up.{1, 0} (package.frame.root.emitted visit.current))
        (audit := (.answered : SourceNativeInquiryFrontAuditAt package.basis.U7 package.basis.calculus
          package.frame.root.toAuthoritativeRoot.source.lawSurface (package.frame.sourceSupport visit.current)))
        (Raw.reportAt package.source package.sourceData package.reader right)) := by
  cases same
  rfl

def compilationFace (query : Query package visit) :
    SourceNativeRootInquiryCompilationFaceCoreAt package.frame.root visit query
      (ULift.up.{1, 0} (package.frame.root.emitted visit.current))
      (package.frame.entry visit.current) authority (compilation package visit authority query) := by
  cases query with
  | internal work =>
    exact {
      projection := (Raw.installation package.source package.sourceData package.reader package.basis).embed .internalCompilation
      active := ⟨work⟩
      classifier_eq := by
        change Raw.classify package.source package.sourceData .internalCompilation _ = _
        exact dif_pos work
      project_heq := by
        rw [compilation_audit]
        exact token_heq (package.frame.entry visit.current) (Raw.QueryAt.internal work : Query package visit)
          (ULift.up.{1, 0} (package.frame.root.emitted visit.current)) .answered _ _
          (compilation_answer package visit authority (.internal work)).symm }
  | raw germ =>
    let available : Raw.Available package.source package.sourceData visit.current :=
      ⟨germ.ready, germ.sourceFold, germ.complete⟩
    exact {
      projection := (Raw.installation package.source package.sourceData package.reader package.basis).embed .rawCompilation
      active := ⟨available⟩
      classifier_eq := by
        change Raw.classify package.source package.sourceData .rawCompilation _ = _
        exact dif_pos available
      project_heq := by
        rw [compilation_audit]
        have same := Raw.germ_unique package.source package.sourceData package.reader visit.current available germ
        exact raw_token_heq package visit _ germ same.symm }

def state : RootInquiryStateAt package.frame.N package.frame.V where
  root := package.frame.root
  visit := visit
  U7 := package.basis.U7
  calculus := package.basis.calculus
  Query := Query package visit
  entryAt := fun _ => package.frame.entry visit.current
  authorityAt := fun _ => authority
  compilationProgramAt := fun query => { compile := fun _ => compilation package visit authority query }
  compilationFaceAt := compilationFace package visit authority
  u7RootDisposition_commutes := by
    intro query obstruction audit audited
    change (compilation package visit authority query).audit = _ at audited
    rw [compilation_audit] at audited
    cases audited

def presentation : RootInquiryStatePresentation :=
  ⟨package.frame.N, package.frame.V, RootInquiryEngineStateAt.create (state package visit authority)⟩

theorem source_selected_debt_core (work : HasWork package.source visit.current)
    (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition package.frame visit.current)
    (selected : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition package.frame visit.current = some registered) :
    (state package visit authority).compileInquiry (.internal work) = .debtAdmission (debtCore package visit authority registered) := by
  change compilation package visit authority (.internal work) = _
  unfold compilation
  split
  next actual actualEq =>
    cases Option.some.inj (actualEq.symm.trans selected)
    rfl
  next absent => rw [selected] at absent; cases absent

theorem source_selected_ordinary (work : HasWork package.source visit.current)
    (absent : headRegistration? (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition package.frame visit.current = none) :
    (state package visit authority).compileInquiry (.internal work) =
      .answered (answerFace package visit work) (consumer package visit work (no_registration_is_ordinary package visit absent)) := by
  change compilation package visit authority (.internal work) = _
  unfold compilation
  split
  next actual selected => rw [absent] at selected; cases selected
  · rfl

theorem source_selected_raw
    (germ : Raw.GermAt package.source package.sourceData package.reader visit.current) :
    (state package visit authority).compileInquiry (.raw germ) = .actualAction (rawCore package visit authority germ) := rfl

#print axioms compilation
#print axioms compilationFace
#print axioms source_selected_debt_core
#print axioms source_selected_raw

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Inquiry
