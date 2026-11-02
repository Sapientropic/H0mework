import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.Protocol

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) (installed : Installed input frame)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (entry input frame visit.current))

def debtCore (registered : Registration input frame visit.current) :=
  (Admission.program input frame visit registered authority).generate
    (frame.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt visit)

theorem registration_absent_is_ordinary (absent : registration? input frame visit.current = none) :
    NotIssue input frame visit.current := by
  intro claim selected
  unfold registration? at absent
  split at absent
  · contradiction
  all_goals rename_i observed; cases selected.symm.trans observed

def compilation : SourceNativeInquiryCompilationAt frame.root visit installed.U7 installed.calculus
    frame.root.toAuthoritativeRoot.source.lawSurface PUnit.unit
    (ULift.up.{1, 0} (frame.root.emitted visit.current))
    (entry input frame visit.current) authority :=
  match found : registration? input frame visit.current with
  | some registered => .debtAdmission (debtCore input frame visit authority registered)
  | none => .answered (answerFace input frame visit)
      (installed.consumer input visit (registration_absent_is_ordinary input frame visit found))

theorem compilation_audit : (compilation input frame installed visit authority).audit = .answered := by
  unfold compilation
  split <;> rfl

theorem compilation_answer : HEq (compilation input frame installed visit authority).answerReadout
    (observe input (frame.cursor visit.current)) := by
  unfold compilation
  split
  · exact HEq.rfl
  · exact frame.observation_heq visit.current

private theorem compilationToken_heq {N : WorldRelationNetwork}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {theory : TheoryState N} {support : N.Support} (original : OpenResponsibilityAt N support)
    {Query : Type} (query : Query) {Event : Type 1} (event : Event)
    (audit : SourceNativeInquiryFrontAuditAt U7 calculus theory support)
    {A B : Type} (left : A) (right : B) (same : HEq left right) :
    HEq (SourceNativeInquiryCompilationTokenAt.canonical
      (entry := original) (query := query) (event := event) (audit := audit) left)
      (SourceNativeInquiryCompilationTokenAt.canonical
        (entry := original) (query := query) (event := event) (audit := audit) right) := by
  cases same
  rfl

def compilationFace : SourceNativeRootInquiryCompilationFaceCoreAt frame.root visit PUnit.unit
    (ULift.up.{1, 0} (frame.root.emitted visit.current))
    (entry input frame visit.current) authority (compilation input frame installed visit authority) where
  projection := installed.compilationProjection
  active := installed.compilationActive visit.current
  classifier_eq := installed.compilationClassify visit.current
  project_heq := by
    rw [compilation_audit]
    exact (installed.compilationRead visit.current).trans
      (compilationToken_heq (entry input frame visit.current) PUnit.unit
        (ULift.up.{1, 0} (frame.root.emitted visit.current)) .answered _ _
        (compilation_answer input frame installed visit authority).symm)

def state : RootInquiryStateAt frame.N frame.V where
  root := frame.root
  visit := visit
  U7 := installed.U7
  calculus := installed.calculus
  Query := PUnit
  entryAt := fun _ => entry input frame visit.current
  authorityAt := fun _ => authority
  compilationProgramAt := fun query => by
    cases query
    exact { compile := fun _ => compilation input frame installed visit authority }
  compilationFaceAt := fun query => by
    cases query
    exact compilationFace input frame installed visit authority
  u7RootDisposition_commutes := by
    intro query obstruction audit audited
    cases query
    change (compilation input frame installed visit authority).audit = _ at audited
    rw [compilation_audit] at audited
    cases audited

def presentation : RootInquiryStatePresentation :=
  ⟨frame.N, frame.V, RootInquiryEngineStateAt.create (state input frame installed visit authority)⟩

theorem source_selected_debt_core (registered : Registration input frame visit.current)
    (selected : registration? input frame visit.current = some registered) :
    (state input frame installed visit authority).compileInquiry PUnit.unit =
      .debtAdmission (debtCore input frame visit authority registered) := by
  change compilation input frame installed visit authority = _
  unfold compilation
  split
  next actual actualEq =>
    have same := Option.some.inj (actualEq.symm.trans selected)
    subst actual
    rfl
  next absent => rw [selected] at absent; cases absent

theorem source_selected_ordinary (absent : registration? input frame visit.current = none) :
    (state input frame installed visit authority).compileInquiry PUnit.unit =
      .answered (answerFace input frame visit)
        (installed.consumer input visit (registration_absent_is_ordinary input frame visit absent)) := by
  change compilation input frame installed visit authority = _
  unfold compilation
  split
  next actual selected => rw [absent] at selected; cases selected
  · rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime
