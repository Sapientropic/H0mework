import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.Crossing
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Release.Actual

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate

open Source.Program PublicFunction PublicFunction.Mandate

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}

local notation "Current" => RawCurrent Party Good (State Party Technology) Instrument
local notation "Word" => RawEvent Party Good Port (State Party Technology) Instrument
local notation "Item" => ExecutionItem Party Good Port (State Party Technology) Instrument
local notation "Inputs" => List Word

omit [DecidableEq Port] [DecidableEq Technology] in
private theorem all_items_use_the_same_source_period_clock (active : RawLaw Party Good Port (State Party Technology) Instrument)
    (current : Current) (word : Word) (index : Nat) (item : Item)
    (original : item ∈ (active.execute current index word).items) :
    item.before.clock = current.clock := by
  induction word generalizing current index with
  | nil => exact (List.not_mem_nil original).elim
  | cons command tail ih =>
      rcases List.mem_cons.mp original with same | later
      · rw [same]
      · have nextClock : (active.step current command).clock = current.clock := by
          unfold RawLaw.step
          split <;> rfl
        exact (ih _ _ later).trans nextClock

theorem expired_original_task_use_cannot_take_material
    (bound : BoundSource base scope) (inputs : Inputs) (ordinal : Nat)
    (late : scope.task.deadline < clockAt bound inputs ordinal) (word : Word) (item : Item)
    (original : item ∈ (law base scope).rawItems (OutstandingSource.History.currentAt bound.source inputs ordinal) word)
    (bearer : Party) (goods : Bundle Good) (purpose : Use)
    (kind : item.request.operation = .use bearer goods purpose) (protectedUse : TaskUse scope item.request) :
    ¬ (law base scope).Valid item.before item.request := by
  intro accepted
  have timely := (protected_use_requires_current_holder base scope _ _ bearer goods purpose kind protectedUse accepted).2.2
  rw [all_items_use_the_same_source_period_clock _ _ _ 0 item original] at timely
  exact (not_lt_of_ge timely) late

theorem the_expired_original_root_cannot_propose_accept_or_renew
    (bound : BoundSource base scope) (inputs : Inputs) (ordinal : Nat)
    (late : scope.task.deadline < clockAt bound inputs ordinal) (word : Word)
    (event : ActualCommand base scope (OutstandingSource.History.currentAt bound.source inputs ordinal) word) :
    event.command ≠ .accept ∧ event.command ≠ .renew ∧ ∀ candidate, event.command ≠ .propose candidate := by
  have clock : event.item.val.before.clock = clockAt bound inputs ordinal :=
    all_items_use_the_same_source_period_clock _ _ _ 0 event.item.val event.item.property
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

theorem an_actual_paid_review_ends_expired_authority_and_keeps_claims
    {current : Current} {word : Word} (event : ActualCommand base scope current word)
    (review : event.command = .review) (late : scope.task.deadline < current.clock) :
    event.after.technology.holder = none ∧ event.after.technology.offered = none ∧
      event.after.claims = event.item.val.before.claims := by
  have clock := all_items_use_the_same_source_period_clock _ _ _ 0 event.item.val event.item.property
  have expired : scope.task.deadline < event.item.val.before.clock := clock.symm ▸ late
  have effect := event.actual_effect
  rw [review, advance, if_pos expired] at effect
  exact ⟨congrArg State.holder effect.1, congrArg State.offered effect.1, effect.2⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate
