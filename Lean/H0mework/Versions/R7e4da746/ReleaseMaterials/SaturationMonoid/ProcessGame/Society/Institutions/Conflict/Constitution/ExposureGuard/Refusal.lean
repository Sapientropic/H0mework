import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Dispatch
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Backlog

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard

open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open Quantities.Execution (endAt query submitted_is_original)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Input" => Reparation.Actual.Input Party Good Port Technology Instrument

theorem the_open_original_recourse_dispatches_a_material_free_stop (cut : C) (available : ReviewAvailable cut) :
    Boundary.Actual.items cut stop = [] := by
  let asked := query cut stop
  have control : asked.control = cut.control :=
    (cut.requery_keeps_control_and_complete_account _).1
  have selected : asked.executionRaw = .stopReview := by
    unfold Evolving.Epoch.Current.executionRaw Evolving.Epoch.Current.choice
    rw [control, show asked.proposal = .stopReview from submitted_is_original cut .stopReview]
    unfold Evolving.Epoch.select
    split
    · rfl
    · rename_i cursor active
      have recourse : cursor.recourse = true := by simpa only [ReviewAvailable, active] using available
      rw [if_pos recourse]
      rfl
  change Optimality.Programme.Epoch.materialItems asked ++ [] = []
  rw [List.append_nil]
  unfold Optimality.Programme.Epoch.materialItems
  split
  · rfl
  · unfold Evolving.Epoch.Current.physicalResult
    rw [selected]
    rfl

variable {seed : Root.Cut Party Good Port Technology Instrument}
  (roster : List Party) (answers : OwnerAnswers seed)
  (past : Reparation.Actual.Script Party Good Port Technology Instrument)
  (input : Reparation.Actual.Input Party Good Port Technology Instrument)

theorem a_denied_attempt_uses_the_executable_original_stop
    (denied : ¬ Admitted roster answers past input) (available : ReviewAvailable (endAt seed past)) :
    Dispatch.selected roster answers past input (dispatch roster answers past input) = [stop] := by
  have empty := the_open_original_recourse_dispatches_a_material_free_stop (endAt seed past) available
  unfold dispatch
  cases inspectAdmission roster answers past input with
  | inr lawful => exact (denied lawful.down).elim
  | inl failure =>
    dsimp only
    have none : (originalItems (seed := seed) past stop).length = 0 := congrArg List.length empty
    rw [dif_pos none]
    rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard
