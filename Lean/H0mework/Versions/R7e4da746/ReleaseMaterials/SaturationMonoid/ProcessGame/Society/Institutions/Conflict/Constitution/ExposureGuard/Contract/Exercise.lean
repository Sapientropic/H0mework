import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Contract.Step
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit.Publication

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.MandateExit

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate
open Civil.Persistence (Window)
open Quantities.Execution (endAt endAt_append inventory)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology]
  [DecidableEq Instrument] [DecidableEq Community]

local notation "M" => State Party Technology
local notation "C" => Root.Cut Party Good Port M Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port M Instrument

variable {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  {seed : Root.Cut Party Good Port (State Party Technology) Instrument}
  {community : Party → Community} {anchor : Reparation.Actual.Script Party Good Port (State Party Technology) Instrument}
  {control : RawCurrent Party Good (State Party Technology) Instrument → List Party}
  (prior : GuardedVisit base scope seed community anchor control)

structure Chosen (answers : OwnerAnswers seed) where
  word : Word
  checked : LiveCertificate seed anchor prior.history community base scope control word
  authored : Exit.SignersChose answers prior.history word

variable {answers : OwnerAnswers seed} (chosen : Chosen prior answers)

/-- Use the owners' already selected exit word directly, including the
native clock and the original allocator at each of its actual visits. -/
def exercise : Reparation.Actual.State seed community (prior.history ++ chosen.word) :=
  Receipts.writeAfter answers prior.state chosen.word

theorem an_owner_selected_exit_pays_on_the_same_original_ledger :
    let reached := endAt seed (prior.history ++ chosen.word)
    Quantities.Recorded seed (prior.history ++ chosen.word) ∧
      (endAt seed prior.history).raw.clock < reached.raw.clock ∧
      Exit.StandingAt (Exit.roster seed community anchor prior.history) reached ∧
      Reparation.Actual.SourceAuthority (endAt seed prior.history) chosen.word ∧
      PaidAt seed anchor (prior.history ++ chosen.word) ∧
      (exercise prior chosen).stack.balances.map Prod.fst =
        Reparation.Actual.originalLosses seed community (prior.history ++ chosen.word) := by
  refine ⟨Quantities.record _ _, ?_, ?_, chosen.checked.1.1.original_authority, chosen.checked.2,
    Receipts.writeAfter_origins answers prior.history chosen.word prior.state prior.origins⟩
  · have renewed := chosen.checked.1.1.renewal.renewal
    rw [Window.run_current] at renewed
    rw [endAt_append]
    exact renewed
  · rw [endAt_append]
    exact Exit.StandingAlong.at_original_cut (tail := [])
      (by simpa only [List.append_nil] using chosen.checked.1.1.standing)

theorem exercising_an_independent_exit_never_restores_the_released_authority
    (installed : Emergency.Installed seed base scope)
    (released : Civil.Mandate.Released (endAt seed prior.history).raw) :
    Civil.Mandate.Released (endAt seed (prior.history ++ chosen.word)).raw := by
  rw [endAt_append]
  exact an_actual_no_grant_word_keeps_the_original_mandate_released _ _ (installed.along prior.history)
    released chosen.checked.1.1.original_authority (fun item listed => (chosen.checked.1.2 item listed).2)

theorem a_refused_input_cannot_suspend_the_owners_chosen_exit
    (person : Party) (offer : Word → Word) (attempt : Reparation.Actual.Input Party Good Port M Instrument)
    (refused : ¬ Admitted prior.roster (withhold answers person) prior.history attempt) :
    let reached := exercise prior chosen
    attempt ∉ (prior.decide (withhold answers person) offer attempt).emitted ∧
      Quantities.Recorded seed (prior.history ++ chosen.word) ∧
      PaidAt seed anchor (prior.history ++ chosen.word) ∧
      reached.stack.balances.map Prod.fst = Reparation.Actual.originalLosses seed community (prior.history ++ chosen.word) := by
  exact ⟨fun accepted => refused ((prior.decide (withhold answers person) offer attempt)
      |>.every_emitted_input_is_lawful attempt accepted).1,
    Quantities.record _ _, chosen.checked.2,
    Receipts.writeAfter_origins answers prior.history _ prior.state prior.origins⟩

/-- A further certified exit can immediately consume this exact paid
successor, with the same exposure cut and every original liability row. -/
def continueAfterExit
    (live : LiveAvailable seed anchor (prior.history ++ chosen.word) community base scope control) :
    GuardedVisit base scope seed community anchor control :=
  ⟨prior.history ++ chosen.word, prior.original.trans (List.prefix_append _ _),
    exercise prior chosen,
    Receipts.writeAfter_origins answers prior.history chosen.word prior.state prior.origins, ⟨chosen.checked.2, live⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.MandateExit
