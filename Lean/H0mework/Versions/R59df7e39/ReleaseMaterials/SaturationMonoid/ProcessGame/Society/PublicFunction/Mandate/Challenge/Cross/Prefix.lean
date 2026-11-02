import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (bound : BoundSource base scope)
  (inputs : List (RawEvent Party Good Port (State Party Technology) Instrument))
  (word : RawEvent Party Good Port (State Party Technology) Instrument)

abbrev nextInputs := inputs ++ [word]

theorem common_current (ordinal : Nat) (inside : ordinal ≤ inputs.length + 2) :
    OutstandingSource.History.currentAt bound.source (nextInputs inputs word) ordinal =
      OutstandingSource.History.currentAt bound.source inputs ordinal := by
  rw [(OutstandingSource.History.actual_frame _ _ ordinal).1,
    (OutstandingSource.History.actual_frame _ inputs ordinal).1]
  exact congrArg (fun past : OutstandingSource.ExecutionPrefix bound.source => past.frame.raw)
    (OutstandingSource.History.extending_inputs_preserves_its_executed_prefix bound.source inputs [word] ordinal inside)

theorem common_word (birth : Nat) (inside : birth < inputs.length + 1) :
    (OutstandingSource.History.actualExecution bound.source (nextInputs inputs word) birth).submitted =
      (OutstandingSource.History.actualExecution bound.source inputs birth).submitted := by
  have past := OutstandingSource.History.extending_inputs_preserves_its_executed_prefix
    bound.source inputs [word] (birth + 2) (by omega)
  change OutstandingSource.ExecutionPrefix.append _ _ = OutstandingSource.ExecutionPrefix.append _ _ at past
  exact (OutstandingSource.History.actual_word _ _ _).trans
    ((OutstandingSource.ExecutionPrefix.extend.inj past).2.trans (OutstandingSource.History.actual_word _ _ _).symm)

theorem common_items (ordinal : Nat) (inside : ordinal < inputs.length + 2) :
    Registered.traceItems (I (fromHistory bound) (nextInputs inputs word))
      (ProgrammeHistory.visitAt (I (fromHistory bound) (nextInputs inputs word)) ordinal).current =
    Registered.traceItems (I (fromHistory bound) inputs) (ProgrammeHistory.visitAt (I (fromHistory bound) inputs) ordinal).current := by
  cases ordinal with
  | zero => rfl
  | succ birth =>
    change bound.source.seed.law.rawItems
      (OutstandingSource.History.currentAt bound.source (nextInputs inputs word) (birth + 1))
      (OutstandingSource.History.actualExecution bound.source (nextInputs inputs word) birth).submitted =
      bound.source.seed.law.rawItems (OutstandingSource.History.currentAt bound.source inputs (birth + 1))
        (OutstandingSource.History.actualExecution bound.source inputs birth).submitted
    rw [common_current bound inputs word (birth + 1) (by omega), common_word bound inputs word birth (by omega)]

def position (original : Position (fromHistory bound) inputs) (inside : original.ordinal < inputs.length + 2) :
    Position (fromHistory bound) (nextInputs inputs word) :=
  ⟨original.ordinal, ⟨original.index.val, by rw [common_items bound inputs word original.ordinal inside]; exact original.index.isLt⟩⟩

theorem position_same_item (original : Position (fromHistory bound) inputs) (inside : original.ordinal < inputs.length + 2) :
    (position bound inputs word original inside).item (fromHistory bound) (nextInputs inputs word) = original.item (fromHistory bound) inputs := by
  have same := congrArg (fun items => items[original.index.val]?) (common_items bound inputs word original.ordinal inside)
  have newBound : original.index.val < (Registered.traceItems (I (fromHistory bound) (nextInputs inputs word))
      (ProgrammeHistory.visitAt (I (fromHistory bound) (nextInputs inputs word)) original.ordinal).current).length :=
    (position bound inputs word original inside).index.isLt
  rw [List.getElem?_eq_getElem newBound,
    List.getElem?_eq_getElem original.index.isLt] at same
  exact Option.some.inj same

def replacement (original : Claim (fromHistory bound) inputs) (inside : original.position.ordinal < inputs.length + 2) :
    Claim (fromHistory bound) (nextInputs inputs word) :=
  let target := position bound inputs word original.position inside
  have found : (read (fromHistory bound) (nextInputs inputs word) target).isSome = true := by
    unfold read
    have same := position_same_item bound inputs word original.position inside
    have signed : Submission (scope := scope) (target.item (fromHistory bound) _).request := by rw [same]; exact original.signed
    have accepted : (law base scope).Valid (target.item (fromHistory bound) _).before (target.item (fromHistory bound) _).request := by rw [same]; exact original.accepted
    have active : (target.item (fromHistory bound) _).before.technology.holder.isSome = true ∨
        (target.item (fromHistory bound) _).before.technology.offered.isSome = true := by rw [same]; exact original.active
    rw [dif_pos signed, dif_pos accepted, dif_pos active]
    rfl
  (read (fromHistory bound) (nextInputs inputs word) target).get found

theorem replacement_position (original : Claim (fromHistory bound) inputs) (inside : original.position.ordinal < inputs.length + 2) :
    (replacement bound inputs word original inside).position = position bound inputs word original.position inside :=
  read_position _ _ _ _ (Option.some_get _).symm

theorem replacement_same_item_and_snapshot (original : Claim (fromHistory bound) inputs) (inside : original.position.ordinal < inputs.length + 2) :
    (replacement bound inputs word original inside).position.item (fromHistory bound) (nextInputs inputs word) = original.position.item (fromHistory bound) inputs ∧
    (replacement bound inputs word original inside).snapshot (fromHistory bound) (nextInputs inputs word) = original.snapshot (fromHistory bound) inputs ∧
    (replacement bound inputs word original inside).signer (fromHistory bound) (nextInputs inputs word) = original.signer (fromHistory bound) inputs ∧
    (replacement bound inputs word original inside).position.ordinal = original.position.ordinal ∧
    (replacement bound inputs word original inside).position.index.val = original.position.index.val := by
  unfold Claim.snapshot Claim.signer
  rw [show (replacement bound inputs word original inside).position = _ from replacement_position bound inputs word original inside]
  have same := position_same_item bound inputs word original.position inside
  exact ⟨same, congrArg (fun item => item.before.technology) same, congrArg (fun item => item.request.signer) same, rfl, rfl⟩

theorem emitted_word_is_actual :
    (OutstandingSource.History.actualExecution bound.source (nextInputs inputs word) (inputs.length + 1)).submitted = word := by
  have emitted := OutstandingSource.History.scheduled_input_is_actual bound.source (nextInputs inputs word)
    inputs.length (by simp [nextInputs])
  simpa only [nextInputs, List.getElem_append_right (Nat.le_refl inputs.length), Nat.sub_self, List.getElem_cons_zero] using emitted

theorem emitted_word_uses_actual_cut :
    (OutstandingSource.History.actualExecution bound.source (nextInputs inputs word) (inputs.length + 1)).before =
      OutstandingSource.History.currentAt bound.source inputs (inputs.length + 2) :=
  common_current bound inputs word _ (Nat.le_refl _)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
