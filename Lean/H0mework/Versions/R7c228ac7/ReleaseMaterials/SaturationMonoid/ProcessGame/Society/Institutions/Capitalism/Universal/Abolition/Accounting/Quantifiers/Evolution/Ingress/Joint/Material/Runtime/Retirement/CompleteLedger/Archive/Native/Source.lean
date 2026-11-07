import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Archive.Word
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Execution.Prefix.Replay
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Priority.Adequacy.Capacity.Realization
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open Abolition.Root.Registered Source.Program

variable (history : List (Compile.RawInput Party Good Port Technology Instrument))
  (before : (process input depth count).GeneratedState)

def sourceState := Physical.Public.stateAt input depth count 0 0 [] history
def word := completeWord input depth count (Physical.Public.interpreter input) before
def start := Physical.receive (Physical.Prefix.cursor history) (.execute (word input depth count before))
def tag : Abolition.Root.Epoch.Interface.Tag input depth count := .publicActual 0 0 [] (start input depth count history before)
def visit := (Abolition.Root.Epoch.Interface.root input depth count (tag input depth count history before)).initialVisit
def items := inventory input depth count (tag input depth count history before) (visit input depth count history before)
def result := Physical.Public.compile input (sourceState input depth count history) (.execute (word input depth count before))
def after := consumeVisit input depth count (tag input depth count history before) (visit input depth count history before) before

def Conditions : Prop :=
  Priority.Adequacy.Capacity.RecipeFacts (Physical.Public.interpreter input)
      (Priority.Adequacy.Primitive.execute (Physical.Public.interpreter input)
        (sourceState input depth count history).raw 0 (word input depth count before)).items ∧
    Priority.Adequacy.Capacity.Startup (Physical.Public.interpreter input)
      (sourceState input depth count history).raw (word input depth count before)

theorem every_actual_request_uses_its_original_debtor_without_extra_consent :
    ∀ request ∈ word input depth count before, request.consents = [] := by
  intro request listed
  rcases List.mem_append.mp listed with positive | archive
  · obtain ⟨slot,_,inside⟩ := List.mem_flatMap.mp positive
    obtain ⟨holder,_,selected⟩ := List.mem_filterMap.mp inside
    split at selected
    · cases Option.some.inj selected
      rfl
    · cases selected
  · exact (every_archive_request_is_an_actual_zero_settlement input depth count _ before request archive).choose_spec.choose_spec.2

theorem the_source_word_is_literal_under_its_original_signer_resigning :
    (word input depth count before).map (fun request => request.resign request.signer) = word input depth count before := by
  calc
    _ = (word input depth count before).map id := by
      apply List.map_congr_left
      intro request listed
      exact Request.resign_self request (every_actual_request_uses_its_original_debtor_without_extra_consent input depth count before request listed)
    _ = _ := List.map_id _

theorem primitive_source_resources_generate_all_actual_items
    (resources : Conditions input depth count history before) :
    ∀ item ∈ (Physical.Public.interpreter input).rawItems (sourceState input depth count history).raw (word input depth count before),
      (Physical.Public.interpreter input).Valid item.before item.request :=
  Priority.Adequacy.Capacity.original_inventory_is_valid _ _ _
    (Priority.Adequacy.Capacity.primitive_resources_generate_the_complete_conditions _ _ _ resources.1 resources.2)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.ArchiveNative
