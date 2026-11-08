import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening.Compiler
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.History

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth start : Nat)

variable (reported : Matrix Instrument Party)

/-- The submitted reading can be verified against the native archive at the
original cut. The authority and the complete continuation come from its Run. -/
structure CertifiedReading where
  private mk ::
  original : Accepted input depth start
  exactReading : reported = carriedAtCut input depth start

def CertifiedReading.inherited (_certified : CertifiedReading input depth start reported) :
    (Epoch.Finance.process input depth (cut input depth start)).GeneratedState :=
  Opening.inherited input depth start

theorem CertifiedReading.reads_the_original_physical_matrix
    (certified : CertifiedReading input depth start reported) :
    reported = rawAtCut input depth start :=
  certified.exactReading.trans certified.original.exactOpening.symm

variable (genesis : Support (genesisRaw input) (genesisCarried input))
  (archive : Support reported (carriedAtCut input depth start))

inductive Reopening
  | certified (reading : CertifiedReading input depth start reported)
  | unproven (refusal : Unresolved input genesis)
  | conflicting (first : Address Instrument Party) (rest : List (Address Instrument Party))
      (exactReport : discrepancies archive = first :: rest)

def reopenAt : Reopening input depth start reported genesis archive :=
  match openAt input depth start genesis with
  | .unresolved refusal => .unproven refusal
  | .accepted opening =>
    match inspect archive with
    | .accepted matching => .certified ⟨opening, matching⟩
    | .refused first rest exactReport => .conflicting first rest exactReport

theorem reopenAt_certifies_iff :
    (∃ reading, reopenAt input depth start reported genesis archive = .certified reading) ↔
      (input.initial.claims = fun _ _ _ => 0) ∧ reported = rawAtCut input depth start := by
  constructor
  · rintro ⟨reading, _⟩
    exact ⟨reading.original.originalGenesis,
      reading.reads_the_original_physical_matrix input depth start reported⟩
  · rintro ⟨original, exactReading⟩
    obtain ⟨accepted, selected⟩ := (openAt_accepts_iff input depth start genesis).2 original
    obtain ⟨matching, archiveSelected⟩ := (accepted_iff archive).2 (exactReading.trans accepted.exactOpening)
    refine ⟨⟨accepted, matching⟩, ?_⟩
    unfold reopenAt
    rw [selected, archiveSelected]

theorem conflicting_reports_the_exact_original_residuals
    {first : Address Instrument Party} {rest : List (Address Instrument Party)}
    (report : discrepancies archive = first :: rest) (key : Address Instrument Party) :
    key ∈ first :: rest ↔ reported key - carriedAtCut input depth start key ≠ 0 :=
  refused_exact archive report key

theorem CertifiedReading.first_actual_account
    (certified : CertifiedReading input depth start reported)
    (prefixLimit renewalLimit : Nat)
    (source : Registered.Physical.Cursor Party Good Port Technology Instrument)
    (first : source.past = []) :
    Epoch.Finance.initialAccount input depth (cut input depth start)
      (.actual prefixLimit renewalLimit source) =
        certified.inherited input depth start reported := by
  change Epoch.Finance.ActualPast.account input depth (cut input depth start)
    prefixLimit renewalLimit source.past (Opening.inherited input depth start) =
      certified.inherited input depth start reported
  rw [first]
  rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Opening
