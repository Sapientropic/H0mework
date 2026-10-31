import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.State
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Profit.Valuation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
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

abbrev originalVisit := Financial.Installation.Cursor.lastExecutedVisit input (frame.cursor visit.current)

def originalPastWords : List (RawEvent Party Good Port Technology Instrument) :=
  (List.range (Financial.Installation.Cursor.lastExecutedIndex input (frame.cursor visit.current))).map fun index =>
    ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input index).current

/-- These equations identify the claimed damage with this root's original
executed occurrence. They carry no loss amount, replacement target or coverage. -/
structure OriginAt (_claim : Responsibility.Family.Claim mechanism past nature response) : Prop where
  law : mechanism.code.law = input.law
  before : mechanism.code.initial = ProgrammeSource.rawCurrent input (originalVisit input frame visit).current
  word : Control.responseWord mechanism past nature response =
    ProgrammeSource.rawEvent input (originalVisit input frame visit).current
  history : past = originalPastWords input frame visit
  accounted : Financial.Installation.Cursor.pending input (frame.cursor visit.current) = []

variable (origin : OriginAt input frame visit claim)

include origin in
theorem the_assessed_inventory_is_the_literal_original_execution :
    (Control.responseExecution mechanism past nature response).items =
      input.law.rawItems (ProgrammeSource.rawCurrent input (originalVisit input frame visit).current)
        (ProgrammeSource.rawEvent input (originalVisit input frame visit).current) := by
  unfold Control.responseExecution RawLaw.rawItems
  rw [origin.law,origin.before,origin.word]

def originalProduction := Profit.production input.law
  (input.law.rawItems (ProgrammeSource.rawCurrent input (originalVisit input frame visit).current)
    (ProgrammeSource.rawEvent input (originalVisit input frame visit).current))

def originalOtherTransfers := Profit.otherTransfers input.law
  (ProgrammeSource.rawCurrent input (originalVisit input frame visit).current)
  (ProgrammeSource.rawEvent input (originalVisit input frame visit).current)

def originalControlIncome := Profit.controlIncome input.law
  (ProgrammeSource.rawCurrent input (originalVisit input frame visit).current)
  (ProgrammeSource.rawEvent input (originalVisit input frame visit).current)

theorem the_compulsory_obligation_consumes_the_same_original_profit_inventory :
    Profit.fullIncome input.law
        (input.law.rawItems (ProgrammeSource.rawCurrent input (originalVisit input frame visit).current)
          (ProgrammeSource.rawEvent input (originalVisit input frame visit).current)) =
      originalProduction input frame visit + originalOtherTransfers input frame visit + originalControlIncome input frame visit :=
  Profit.the_original_full_account_separates_production_transfer_and_control _ _ _


/-- The quote reads the existing fold at the original occurrence's opening.
It does not create a replacement financial account in the live root. -/
def originalOpening := Abolition.Root.Epoch.Finance.Legacy.generated input 0 0
  (Financial.accountAt input (Financial.Installation.Cursor.lastExecutedIndex input (frame.cursor visit.current)))

def OriginalFourComponents (before after : Profit.Quotation
    (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument))
    (person : Party) (good : Good) : Prop :=
  Profit.bookIncome input 0 0 input.law
      (ProgrammeSource.rawCurrent input (originalVisit input frame visit).current)
      (originalOpening input frame visit)
      (ProgrammeSource.rawEvent input (originalVisit input frame visit).current) before after person good =
    before.unitPrice person good * originalProduction input frame visit (person,good) +
    before.unitPrice person good * originalOtherTransfers input frame visit (person,good) +
    before.unitPrice person good * originalControlIncome input frame visit (person,good) +
    Profit.revaluation input 0 0 input.law
      (ProgrammeSource.rawCurrent input (originalVisit input frame visit).current)
      (originalOpening input frame visit)
      (ProgrammeSource.rawEvent input (originalVisit input frame visit).current) before after person good

theorem the_same_original_profit_read_has_all_four_components
    (before after : Profit.Quotation (Party := Party) (Good := Good)
      (Technology := Technology) (Instrument := Instrument)) (person : Party) (good : Good) :
    OriginalFourComponents input frame visit before after person good :=
  Profit.the_original_book_return_has_its_complete_four_component_decomposition _ _ _ _ _ _ _ _ _ _ _

#print axioms the_assessed_inventory_is_the_literal_original_execution
#print axioms the_compulsory_obligation_consumes_the_same_original_profit_inventory

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source
