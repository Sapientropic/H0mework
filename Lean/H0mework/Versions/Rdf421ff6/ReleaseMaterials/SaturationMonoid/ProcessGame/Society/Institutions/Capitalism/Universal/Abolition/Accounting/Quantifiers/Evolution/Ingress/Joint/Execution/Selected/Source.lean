import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Interpreter
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Planning.Consent

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (window seed))

def word := Material.word seed claim
def tag := Prefix.tag seed (word seed claim)
def visit : Epoch.Interface.Visit seed.input seed.depth seed.count (tag seed claim) :=
  (Epoch.Interface.root seed.input seed.depth seed.count (tag seed claim)).initialVisit
def execution := Epoch.Interface.execution seed.input seed.depth seed.count (tag seed claim) (visit seed claim).current
def items := Epoch.Finance.inventory seed.input seed.depth seed.count (tag seed claim) (visit seed claim)

theorem the_actual_financial_body_reads_the_original_live_cursor :
    Epoch.Interface.rawAt seed.input seed.depth seed.count (tag seed claim) (visit seed claim).current =
      (Material.shared seed claim).raw :=
  Prefix.the_public_financial_visit_reads_the_original_live_shared_current seed _

theorem the_actual_incoming_word_is_the_source_selected_programme :
    word seed claim = Planning.selected seed claim (Material.shared seed claim) := rfl

theorem every_selected_request_has_no_controller_consent :
    ∀ request ∈ word seed claim, request.consents = [] :=
  Planning.selected_requires_no_controller_consent seed claim (Material.shared seed claim)

theorem every_selected_original_item_is_actual :
    ∀ item ∈ (Physical.Public.interpreter seed.input).rawItems (Prefix.sharedState seed).raw (word seed claim),
      (Physical.Public.interpreter seed.input).Valid item.before item.request := by
  rw [Prefix.the_complete_actual_source_history_reads_the_single_shared_raw,
    ← Prefix.the_source_current_reads_the_original_public_interpreter]
  exact Planning.every_selected_original_inventory_item_is_actual seed claim (Material.shared seed claim)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Selected
