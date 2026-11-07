import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Global.Seed

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Background

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))

def original := Financial.Installation.Runtime.frames seed.input seed.depth seed.count

def successor := Abolition.Accounting.Root.Source.sourceSuccessor seed.input
  (original seed).native ((original seed).temporal seed.input)

def visit := ((original seed).temporal seed.input).next (successor seed).next_eq

def cursor := (original seed).native.cursor (visit seed).current
def account := (cursor seed).account
def pending := Financial.Installation.Cursor.pending seed.input (cursor seed)

private theorem inputs_keep_the_old_support {oldN : WorldRelationNetwork}
    (frame : Abolition.Accounting.Root.Reentry.Frame (oldN := oldN) seed.claim)
    (inputs : List (RawEvent Party Good Port Technology Instrument)) :
    (Abolition.Accounting.Root.Reentry.Frame.support seed.claim
      (Priority.Root.afterInputs seed.claim frame inputs)).1 =
      (Abolition.Accounting.Root.Reentry.Frame.support seed.claim frame).1 := by
  induction inputs generalizing frame with
  | nil => rfl
  | cons word rest ih =>
      exact (ih (Priority.Root.Installation.successor seed.claim frame word)).trans
        (Priority.Root.Installation.the_old_network_support_is_retained seed.claim frame word)

theorem the_live_productive_row_keeps_the_actual_background_support :
    (Abolition.Accounting.Root.Reentry.Frame.support seed.claim seed.current).1 =
      (successor seed).targetOccurrence.1 := by
  exact inputs_keep_the_old_support seed
    (Abolition.Accounting.Completion.currentFamily seed.input seed.depth seed.count seed.claim []) seed.inputs

theorem the_registered_background_visit_is_the_original_generated_next :
    (visit seed).current = (successor seed).targetCurrent := rfl

theorem the_financial_account_and_queue_are_read_from_that_same_actual_visit :
    account seed = ((original seed).native.cursor (visit seed).current).account ∧
      pending seed = Financial.Installation.Cursor.pending seed.input
        ((original seed).native.cursor (visit seed).current) := ⟨rfl,rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Background
