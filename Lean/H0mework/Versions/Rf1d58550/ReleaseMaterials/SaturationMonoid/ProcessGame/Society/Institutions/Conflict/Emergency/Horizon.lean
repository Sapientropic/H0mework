import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Root.Execution
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "Raw" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Script" => List (Option (Compile.RawInput Party Good Port (State Party Technology) Instrument))
local notation "Base" => RawLaw Party Good Port Technology Instrument
local notation "J" => Scope (Party := Party) (Good := Good) (Port := Port)

def Installed (source : C) (base : Base) (scope : J) : Prop :=
  source.native.input.law = law base scope

theorem Installed.along {source : C} {base : Base} {scope : J}
    (original : Installed source base scope) (history : Script) :
    Installed (Quantities.Execution.endAt source history) base scope :=
  by
    unfold Installed
    rw [Quantities.Execution.endAt_input]
    exact original

/-- All material commands in an atomic original word read its own clock. -/
theorem original_item_clock (base : Base) (scope : J) (current : Raw) (word : Word)
    (index : Nat) (item : ExecutionItem Party Good Port (State Party Technology) Instrument)
    (original : item ∈ ((law base scope).execute current index word).items) :
    item.before.clock = current.clock := by
  induction word generalizing current index with
  | nil => exact (List.not_mem_nil original).elim
  | cons request rest ih =>
    rcases List.mem_cons.mp original with same | later
    · rw [same]
    · have sameClock : ((law base scope).step current request).clock = current.clock := by
        unfold RawLaw.step
        split <;> rfl
      exact (ih _ _ later).trans sameClock

/-- At a late actual cut all new holder-creating commands are refused,
irrespective of the signer, purported holder, or target version. -/
theorem late_command_is_not_a_grant (base : Base) (scope : J) (current : Raw)
    (word : Word) (event : ActualCommand base scope current word)
    (late : scope.task.deadline < current.clock) :
    event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate := by
  have clock := original_item_clock base scope current word 0 event.item.val event.item.property
  have authorised := event.authorization.2.2.2.2.2
  constructor
  · intro command
    rw [command] at authorised
    exact (not_lt_of_ge (clock ▸ authorised.2)) late
  constructor
  · intro command
    rw [command] at authorised
    exact (not_lt_of_ge (clock ▸ authorised.2.2)) late
  · intro candidate command
    rw [command] at authorised
    exact (not_lt_of_ge (clock ▸ authorised.2)) late

theorem late_protected_item_is_refused (base : Base) (scope : J) (current : Raw)
    (word : Word) (item : ExecutionItem Party Good Port (State Party Technology) Instrument)
    (original : item ∈ (law base scope).rawItems current word)
    (late : scope.task.deadline < current.clock)
    (bearer : Party) (goods : Bundle Good) (purpose : Use)
    (kind : item.request.operation = .use bearer goods purpose) (protectedUse : TaskUse scope item.request) :
    ¬ (law base scope).Valid item.before item.request := by
  intro accepted
  have timely := (protected_use_requires_current_holder base scope _ _ bearer goods purpose kind protectedUse accepted).2.2
  rw [original_item_clock base scope current word 0 item original] at timely
  exact (not_lt_of_ge timely) late

/-- Requerying or changing the current through any actual original suffix
never reinstalls a passed deadline. The original source and all claim/row
writes remain in the same rooted history. -/
theorem no_reset_on_any_original_successor {source : C} {base : Base} {scope : J}
    (original : Installed source base scope) (late : scope.task.deadline < source.raw.clock)
    (history : Script) :
    let cut := Quantities.Execution.endAt source history
    Quantities.Recorded source history ∧ Installed cut base scope ∧ scope.task.deadline < cut.raw.clock ∧
      ∀ word : Word, ∀ event : ActualCommand base scope cut.raw word,
        event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate := by
  let cut := Quantities.Execution.endAt source history
  have expired := late.trans_le (Quantities.Execution.the_actual_script_never_runs_the_clock_backwards source history)
  exact ⟨Quantities.record source history, original.along history, expired,
    fun word event => late_command_is_not_a_grant base scope cut.raw word event expired⟩

theorem no_authority_after_a_crossing {source : C} {base : Base} {scope : J}
    (original : Installed source base scope) (past future : Script)
    (crossed : scope.task.deadline < (Quantities.Execution.endAt source past).raw.clock) :
    let cut := Quantities.Execution.endAt source (past ++ future)
    Installed cut base scope ∧ scope.task.deadline < cut.raw.clock ∧
      ∀ word : Word, ∀ event : ActualCommand base scope cut.raw word,
        event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate := by
  rw [Quantities.Execution.endAt_append]
  exact (no_reset_on_any_original_successor (original.along past) crossed future).2

end
end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Emergency
