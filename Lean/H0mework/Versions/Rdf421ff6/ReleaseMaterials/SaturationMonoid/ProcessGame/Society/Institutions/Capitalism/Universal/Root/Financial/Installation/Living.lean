import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Inquiry.Face
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Observation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (start : Cursor.State input) (startPositive : 0 < Cursor.physicalVisitIndex input start)

inductive Projection
  | ledger | account | pending | observation | compilation | consumer

def ActiveAt (projection : Projection) {current : Current input start}
    (_occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) : Type :=
  match projection with
  | .consumer => PLift (¬ IsIssue input start current)
  | _ => Unit

def InactiveAt (projection : Projection) {current : Current input start}
    (_occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) : Type :=
  match projection with
  | .consumer => PLift (IsIssue input start current)
  | _ => PEmpty

def classify (projection : Projection) {current : Current input start}
    (occurrence : (source input start startPositive).toRootSource.actual.OccurrenceAt current) :
    ActiveAt input start startPositive projection occurrence ⊕ InactiveAt input start startPositive projection occurrence := by
  cases projection with
  | consumer =>
      by_cases issue : IsIssue input start current
      · exact .inr ⟨issue⟩
      · exact .inl ⟨issue⟩
  | ledger | account | pending | observation | compilation => exact .inl ()

noncomputable def projectionLaw : SourceNativeProjectionLaw (ledgerSource input start startPositive) where
  Projection := Projection
  ActiveAt := ActiveAt input start startPositive
  InactiveAt := InactiveAt input start startPositive
  classify := classify input start startPositive
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .ledger => SourceNativeLedgerEvolutionAt (source input start startPositive) occurrence
    | .account => AccountFaceAt input start startPositive occurrence
    | .pending => Cursor.PendingInventory input current.cursor ×
        Cursor.PendingInventory input (next input start current).cursor
    | .observation => Observation input
    | .compilation => SourceNativeInquiryCompilationTokenAt
        (inquiryEntryAt input start startPositive occurrence) PUnit.unit (ULift.up.{1, 0} occurrence)
        (inquiryAudit input start startPositive occurrence) (Observation input)
    | .consumer => SourceNativeInquiryAnswerConsumerTokenAt
        PUnit.unit (ULift.up.{1, 0} occurrence) (inquiryEntryAt input start startPositive occurrence)
        (observe input current.cursor)
  project := fun projection {current} occurrence _ => match projection with
    | .ledger => (ledgerCompiler input start startPositive).compile occurrence
    | .account => accountFace input start startPositive occurrence
    | .pending => ⟨Cursor.pendingInventory input current.cursor,
        Cursor.pendingInventory input (next input start current).cursor⟩
    | .observation => observe input current.cursor
    | .compilation => .canonical (observe input current.cursor)
    | .consumer => .canonical

noncomputable def authoritySource : SourceNativeAuthoritySource (N input start) (V input start) where
  restructuringSource := restructuringSource input start startPositive
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource input start startPositive)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic (N input start)
  projectionLaw := projectionLaw input start startPositive

noncomputable def livingRoot : SourceNativeLivingRootClosure (N input start) (V input start) where
  source := {
    base := authoritySource input start startPositive
    terminalHandoff := (authoritySource input start startPositive).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emitted input start startPositive
  compiler_commutes := fun _ => rfl

theorem an_issue_has_no_ordinary_answer_consumer (current : Current input start)
    (issue : IsIssue input start current) :
    IsEmpty ((projectionLaw input start startPositive).ActiveAt .consumer
      (emitted input start startPositive current)) :=
  ⟨fun accepted => accepted.down issue⟩

theorem actual_root_next_is_the_source_account (current : Current input start) :
    ((projectionLaw input start startPositive).project .account
      (emitted input start startPositive current) ()).after =
        (next input start current).cursor.account := rfl

theorem original_pending_rows_are_in_the_same_root (current : Current input start) :
    (projectionLaw input start startPositive).project .pending
      (emitted input start startPositive current) () =
        (Cursor.pendingInventory input current.cursor,
          Cursor.pendingInventory input (next input start current).cursor) := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.AccountSource
