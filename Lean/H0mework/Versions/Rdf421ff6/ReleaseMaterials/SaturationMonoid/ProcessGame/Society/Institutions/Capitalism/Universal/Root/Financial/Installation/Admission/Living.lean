import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission.Foundation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : NativeFrame input) {origin : frame.V.Current}
  (registered : Registration input frame origin)

inductive OwnProjection
  | ledger | observation | compilation | consumer

abbrev Projection := frame.root.toAuthoritativeRoot.source.projectionLaw.Projection ⊕ OwnProjection

def ActiveAt (projection : Projection input frame) {current : Current input frame registered}
    (_occurrence : (source input frame registered).toRootSource.actual.OccurrenceAt current) : Type :=
  match projection with
  | .inl old => frame.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt old (frame.root.emitted current.1)
  | .inr .consumer => PLift (¬ IsIssue input frame registered current)
  | .inr _ => Unit

def InactiveAt (projection : Projection input frame) {current : Current input frame registered}
    (_occurrence : (source input frame registered).toRootSource.actual.OccurrenceAt current) : Type :=
  match projection with
  | .inl old => frame.root.toAuthoritativeRoot.source.projectionLaw.InactiveAt old (frame.root.emitted current.1)
  | .inr .consumer => PLift (IsIssue input frame registered current)
  | .inr _ => PEmpty

def classify (projection : Projection input frame) {current : Current input frame registered}
    (occurrence : (source input frame registered).toRootSource.actual.OccurrenceAt current) :
    ActiveAt input frame registered projection occurrence ⊕ InactiveAt input frame registered projection occurrence := by
  cases projection with
  | inl old => exact frame.root.toAuthoritativeRoot.source.projectionLaw.classify old (frame.root.emitted current.1)
  | inr own =>
      cases own with
      | consumer =>
          by_cases issue : IsIssue input frame registered current
          · exact .inr ⟨issue⟩
          · exact .inl ⟨issue⟩
      | ledger | observation | compilation => exact .inl ()

noncomputable def projectionLaw : SourceNativeProjectionLaw (ledgerSource input frame registered) where
  Projection := Projection input frame
  ActiveAt := ActiveAt input frame registered
  InactiveAt := InactiveAt input frame registered
  classify := classify input frame registered
  PayloadAt := fun projection {current} occurrence active => match projection with
    | .inl old => frame.root.toAuthoritativeRoot.source.projectionLaw.PayloadAt old
        (frame.root.emitted current.1) active
    | .inr .ledger => SourceNativeLedgerEvolutionAt (source input frame registered) occurrence
    | .inr .observation => Observation input
    | .inr .compilation => SourceNativeInquiryCompilationTokenAt
        (inquiryEntryAt input frame registered occurrence) PUnit.unit (ULift.up.{1, 0} occurrence)
        (inquiryAudit input frame registered occurrence) (Observation input)
    | .inr .consumer => SourceNativeInquiryAnswerConsumerTokenAt
        PUnit.unit (ULift.up.{1, 0} occurrence) (inquiryEntryAt input frame registered occurrence)
        (observe input (frame.cursor current.1))
  project := fun projection {current} occurrence active => match projection with
    | .inl old => frame.root.toAuthoritativeRoot.source.projectionLaw.project old (frame.root.emitted current.1) active
    | .inr .ledger => (ledgerCompiler input frame registered).compile occurrence
    | .inr .observation => observe input (frame.cursor current.1)
    | .inr .compilation => .canonical (observe input (frame.cursor current.1))
    | .inr .consumer => .canonical

noncomputable def authoritySource : SourceNativeAuthoritySource (N input frame registered) (V input frame registered) where
  restructuringSource := restructuringSource input frame registered
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource input frame registered)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic (N input frame registered)
  projectionLaw := projectionLaw input frame registered

noncomputable def livingRoot : SourceNativeLivingRootClosure (N input frame registered) (V input frame registered) where
  source := {
    base := authoritySource input frame registered
    terminalHandoff := (authoritySource input frame registered).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emitted input frame registered
  compiler_commutes := fun _ => rfl

theorem inherited_projection_is_the_original_source
    (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection)
    (current : Current input frame registered)
    (active : frame.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt projection (frame.root.emitted current.1)) :
    HEq ((projectionLaw input frame registered).project (.inl projection)
      (emitted input frame registered current) active)
      (frame.root.toAuthoritativeRoot.source.projectionLaw.project projection (frame.root.emitted current.1) active) := HEq.rfl

noncomputable def nativeProgram : RootGeneratedDebtActivationJointSource.Native.Program
    (livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot where
  emit := fun current =>
    (RootGeneratedDebtActivationJointSource.Native.read?
      (livingRoot input frame registered).toAuthoritativeRoot.toLedgerRoot current).get (by rfl)

noncomputable def nativeFrame : NativeFrame input where
  N := N input frame registered
  V := V input frame registered
  root := livingRoot input frame registered
  program := nativeProgram input frame registered
  cursor := fun current => frame.cursor current.1
  next_exact := fun current => frame.next_exact current.1
  projection := .inr .observation
  active := fun _ => ()
  classify_eq := fun _ => rfl
  observation_heq := fun _ => HEq.rfl
  entrySupport := entrySupport input frame registered
  disposition := disposition input frame registered
  openAt_subsingleton := openAt_subsingleton input frame registered
  origin_injective := by
    intro current
    change Function.Injective (fun entry => ((patch input frame registered current).toLedgerWriteEvolution.origin entry).1)
    rw [patch_origin]
    exact (whole_injective input frame registered current).1
  destination_injective := by
    intro current
    change Function.Injective (fun entry => ((patch input frame registered current).toLedgerWriteEvolution.destination entry).1)
    rw [patch_destination]
    exact (whole_injective input frame registered current).2

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Admission
