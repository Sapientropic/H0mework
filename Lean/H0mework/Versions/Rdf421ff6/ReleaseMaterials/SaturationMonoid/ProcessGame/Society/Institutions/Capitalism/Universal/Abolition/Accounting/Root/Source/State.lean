import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Family.Law
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.First
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Runtime.CursorRead

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (word : RawEvent Party Good Port Technology Instrument)

/-- One submitted actual input is consumed once. A later input is a new
inquiry; this carrier contains no table of future successful repairs. -/
inductive Phase
  | pending | declared | observed

def next : Phase → Phase
  | .pending => .declared
  | .declared => .observed
  | .observed => .observed

def nonFinancial : Prop := ∀ request ∈ word, Responsibility.NonFinancialOperation request.operation

def sourceSuccessor := Financial.Installation.Admission.sourceSuccessor input frame visit

def sourceSupport := frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
  (frame.root.emitted visit.current)

def sourceEntry := frame.entrySupport (sourceSupport input frame visit)

/-- The physical cursor comes from the original native next, so registering
an older obligation cannot replay its historical physical state. -/
def initialState : Responsibility.Family.State claim :=
  Responsibility.Family.State.atCursor claim (ProgrammeSource.rawCurrent input
    (Financial.Installation.Cursor.physicalVisit input
      (Financial.Installation.Cursor.next input (frame.cursor visit.current))).current)

def declared : Responsibility.Family.State claim :=
  Responsibility.Family.State.declare claim (initialState input frame visit claim)

def actualLaw := PublicFunction.physicalLaw input.law

/-- The family source checks the entire input before material execution and
retains the actual paid prefix when a later instruction is refused. -/
def observed : Responsibility.Family.State claim :=
  Responsibility.Family.State.advance claim (declared input frame visit claim) (actualLaw input) word

def debtState : Phase → Responsibility.Family.State claim
  | .pending => initialState input frame visit claim
  | .declared => declared input frame visit claim
  | .observed => observed input frame visit claim word

abbrev N := ExtendedNetwork frame.N (Responsibility.Family.activationLaw claim)

def oldSupport : Phase → frame.N.Support
  | .pending => sourceSupport input frame visit
  | .declared | .observed => (sourceSuccessor input frame visit).targetOccurrence.1

def support (phase : Phase) : (N input frame claim).Support :=
  (oldSupport input frame visit phase, some (debtState input frame visit claim word phase))

def firstStep : DebtAdmissionFirstWrite.SourceFixedDebtAdmissionEventAt
    (Responsibility.Family.activationLaw claim) (initialState input frame visit claim) where
  target := declared input frame visit claim
  step := .declaration (initialState input frame visit claim) rfl

theorem declaration_retains_the_whole_material_obligation :
    (debtState input frame visit claim word .declared).remaining = (initialState input frame visit claim).remaining := rfl

theorem every_actual_repair_input_keeps_all_original_financial_claims :
    (observed input frame visit claim word).raw.claims = (declared input frame visit claim).raw.claims :=
  Responsibility.Family.State.actual_advance_retains_every_original_financial_claim _ _ _ _


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source
