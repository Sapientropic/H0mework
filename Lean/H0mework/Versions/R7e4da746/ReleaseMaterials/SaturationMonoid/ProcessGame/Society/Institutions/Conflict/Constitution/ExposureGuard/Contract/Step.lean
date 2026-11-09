import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Grant
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Deadline
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Runtime.Visit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Quantities.Execution (endAt endAt_append inventory)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Raw" => RawCurrent Party Good M Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument
local notation "Item" => ExecutionItem Party Good Port M Instrument

namespace Selection

variable {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {roster : List Party} {answers : OwnerAnswers seed}
  {viable : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument → Prop}
  {check : Probe viable}
  {past : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  {input : Reparation.Actual.Input Party Good Port (State Party Technology) Instrument}
  (selected : Selection roster answers grantRule viable check past input)

theorem a_written_grant_reads_each_original_bearer
    {person : Party} (exposed : person ∈ roster) (item : Item)
    (listed : item ∈ inventory (endAt seed past) selected.emitted)
    (grant : Grants item.request) :
    ∃ actual ∈ selected.emitted, ∃ position : Fin (originalItems (seed := seed) past actual).length,
      (originalItems (seed := seed) past actual)[position] = item ∧ answers past actual position person = true := by
  obtain ⟨actual, chosen, position, same⟩ := selected.original_position_of_selected_item item listed
  have valid := (selected.every_emitted_input_is_lawful actual chosen).2 position
  have opens : Grants (originalItems (seed := seed) past actual)[position].request := by
    rw [same]
    exact grant
  exact ⟨actual, chosen, position, same, valid.2 opens person exposed⟩

end Selection

variable [DecidableEq Technology] [DecidableEq Community]

abbrev GuardedVisit (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (seed : C) (community : Party → Community) (anchor : Word) (control : Raw → List Party) :=
  Visit seed community anchor (fun history => MandateExit.ReadyAt seed anchor history community base scope control)

def exitProbe (base : RawLaw Party Good Port Technology Instrument)
    (scope : Scope (Party := Party) (Good := Good) (Port := Port))
    (seed : C) (community : Party → Community) (anchor : Word) (control : Raw → List Party)
    (offer : Word → Word) :
    Probe (fun history => MandateExit.ReadyAt seed anchor history community base scope control) :=
  fun history => MandateExit.finiteProbe seed anchor history community base scope control (offer history)

namespace Visit

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community} {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  {control : RawCurrent Party Good (State Party Technology) Instrument → List Party}
  (prior : GuardedVisit base scope seed community anchor control)
  (answers : OwnerAnswers seed)
  (offer : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument →
    Reparation.Actual.Script Party Good Port (State Party Technology) Instrument)
  (input : Reparation.Actual.Input Party Good Port (State Party Technology) Instrument)

abbrev decide := prior.verdict answers grantRule (exitProbe base scope seed community anchor control offer) input

abbrev write := prior.step answers grantRule (exitProbe base scope seed community anchor control offer) input

theorem a_rival_visit_has_no_new_grant_for_any_withholding_bearer
    {person : Party} (exposed : person ∈ prior.roster) (item : Item)
    (listed : item ∈ inventory (endAt seed prior.history) (prior.decide (withhold answers person) offer input).emitted) :
    ¬ Grants item.request := by
  intro granted
  obtain ⟨actual, _, position, _, signed⟩ :=
    (prior.decide (withhold answers person) offer input).a_written_grant_reads_each_original_bearer exposed item listed granted
  rw [withholding_uses_the_original_personal_lane] at signed
  cases signed

theorem a_visit_with_no_new_grant_keeps_original_release
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed prior.history).raw)
    (closed : ∀ item ∈ inventory (endAt seed prior.history) (prior.decide answers offer input).emitted,
      ¬ Grants item.request) :
    Civil.Mandate.Released (endAt seed (prior.write answers offer input).history).raw := by
  let selected := prior.decide answers offer input
  change Civil.Mandate.Released (endAt seed (prior.history ++ selected.emitted)).raw
  rw [endAt_append]
  exact an_actual_no_grant_word_keeps_the_original_mandate_released _ _ (installed.along prior.history)
    released selected.the_original_selected_word_has_source_authority closed

theorem a_visit_keeps_the_installed_original_hard_expiry
    (installed : Emergency.Installed seed base scope)
    (crossed : scope.task.deadline < (endAt seed prior.history).raw.clock) :
    let reached := endAt seed (prior.write answers offer input).history
    Emergency.Installed reached base scope ∧ scope.task.deadline < reached.raw.clock ∧
      ∀ rawWord : RawEvent Party Good Port M Instrument, ∀ event : ActualCommand base scope reached.raw rawWord,
        event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate :=
  Emergency.no_authority_after_a_crossing installed prior.history (prior.decide answers offer input).emitted crossed

end Visit

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
