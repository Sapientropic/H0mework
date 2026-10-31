import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary.Progress
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Report
import Mathlib.Data.List.Infix

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary

open Source.Program Innovation

noncomputable section

attribute [local irreducible] actualLaw

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed)) (current : Current seed claim)
  (proposal : RawEvent Party Good Port Technology Instrument)

def executed := Entitlement.Execution.payable (actualLaw seed) current.raw proposal
def next := Current.advance seed claim current (executed seed claim current proposal)
def suffix := proposal.drop (executed seed claim current proposal).length
def inspection := Entitlement.Execution.inspectWord (actualLaw seed) current.raw proposal

theorem the_submitted_word_keeps_the_actual_prefix_and_unexecuted_suffix :
    proposal = executed seed claim current proposal ++ suffix seed claim current proposal :=
  List.prefix_append_drop (Entitlement.Execution.the_source_prefix_is_an_original_prefix
    (actualLaw seed) current.raw proposal)

theorem all_executed_items_are_actual :
    ∀ item ∈ (actualLaw seed).rawItems current.raw (executed seed claim current proposal),
      (actualLaw seed).Valid item.before item.request :=
  Entitlement.Execution.validity_reaches_every_original_inventory_item _ _ _
    (Entitlement.Execution.the_source_prefix_is_valid _ _ _) 0

theorem the_next_is_the_same_single_material_successor :
    (next seed claim current proposal).raw = (actualLaw seed).next current.raw (executed seed claim current proposal) := rfl

variable [DecidableEq Technology]

theorem the_actual_source_selected_word_is_this_same_executed_prefix :
    executed seed claim current (Planning.chosen seed claim current) = Planning.selected seed claim current := rfl

theorem the_actual_source_selected_next_is_this_same_shared_current :
    next seed claim current (Planning.chosen seed claim current) = Planning.actualNext seed claim current := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Boundary
