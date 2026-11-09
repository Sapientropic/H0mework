import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Native.Backlog
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace

open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Runtime (ReviewAvailable)
open PublicFunction.Mandate
open Quantities.Execution

open private control_at_query stop_is_selected_when_review_allows_recourse from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace.Renewal.Dispatch

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port (State Party Technology) Instrument
local notation "stop" => (some Compile.RawInput.stopReview)

theorem an_original_recourse_stop_spends_no_material_and_keeps_the_clock_and_control
    (cut : C) (review : ReviewAvailable cut) :
    (next cut stop).raw = cut.raw ∧ (next cut stop).control = cut.control ∧ inventory cut [stop] = [] := by
  have empty := Renewal.a_recourse_stop_has_no_material_items cut review
  by_cases busy : Quantities.Pending cut
  · exact (a_competing_input_cannot_add_native_work_to_the_pending_visit cut stop busy).2
  · let asked := query cut stop
    have ready : ¬ Macro.Public.Inquiry.HasWork asked.native.frame asked.native.actual.actual := busy
    have selected := stop_is_selected_when_review_allows_recourse cut review
    have advances : next cut stop = Evolving.Epoch.Transition.next asked ready := asked.advance_eq_epoch ready
    refine ⟨?_, ?_, empty⟩
    · rw [advances, Evolving.Epoch.Transition.next_state_reads_the_same_actual_material_target]
      unfold Evolving.Epoch.Current.physicalResult
      rw [show asked.executionRaw = .stopReview from selected]
      rfl
    · rw [advances, Evolving.Epoch.Transition.next_reads_the_written_control]
      unfold Evolving.Epoch.Current.afterControl Evolving.Epoch.Current.choice
      rw [control_at_query cut stop, submitted_is_original cut .stopReview]
      unfold Evolving.Epoch.select
      split
      · rfl
      · rename_i cursor active
        have recourse : cursor.recourse = true := by simpa only [ReviewAvailable, active] using review
        rw [if_pos recourse]
        rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ForcePeace
