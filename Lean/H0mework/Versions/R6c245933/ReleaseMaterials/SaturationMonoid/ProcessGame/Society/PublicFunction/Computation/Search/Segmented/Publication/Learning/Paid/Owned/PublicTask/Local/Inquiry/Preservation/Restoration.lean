import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Preservation
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Selection.Restoration

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Preservation.Restoration
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open PublicFunction.Protocol.SymbolicAuthentication

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (task : Owned.Task (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

abbrev Accepts (first last : Program task.model.source.code (horizon task.domain)) :=
  Selection.Restoration.acceptable (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original first last

theorem self (cache : Owned.Cache task) : Accepts task cache.programme cache.programme :=
  (Selection.Restoration.original_self_admission_is_exact (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _).mp (Preservation.self task cache)

theorem trans {first middle last : Program task.model.source.code (horizon task.domain)}
    (left : Accepts task first middle) (right : Accepts task middle last) : Accepts task first last :=
  Selection.Restoration.acceptable_trans (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original _ _ _ right left

theorem of_same_stages {first last : Program task.model.source.code (horizon task.domain)}
    (valid : Selection.acceptable task.model task.domain task.original first first)
    (same : ∀ ordinal < horizon task.domain, last.at task.original ordinal = first.at task.original ordinal) :
    Accepts task first last := by
  have prior := (Selection.Restoration.acceptable_iff_every_same_full_opponent (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original _ _).mp
    ((Selection.Restoration.original_self_admission_is_exact (tariff := task.recoveryPricing) (requested := task.futureRequests) _ _ _ _).mp valid)
  apply (Selection.Restoration.acceptable_iff_every_same_full_opponent (tariff := task.recoveryPricing) (requested := task.futureRequests) task.model task.domain task.original _ _).mpr
  intro world rival
  have tensor : Window.Whole.Restoration.actualTensor (tariff := task.recoveryPricing) task.model world.val task.original last rival =
      Window.Whole.Restoration.actualTensor (tariff := task.recoveryPricing) task.model world.val task.original first rival := by
    apply Window.Whole.Restoration.stages_generate_the_same_complete_tensor (tariff := task.recoveryPricing)
    intro ordinal inside
    exact same ordinal (inside.trans_le (Continuation.Whole.Complete.each_remaining_horizon_is_generated task.domain world.val world.property))
  rw [tensor]
  exact prior world rival

theorem frame_advance_stages (cache : Inquiry.Frame task) (ordinal : Nat) :
    (Inquiry.Frame.advance task cache).programme.at task.original ordinal = cache.programme.at task.original ordinal := by
  change (Driving.Progress.next {cache.shell with beliefs := []}).programme.at task.original ordinal = _
  unfold Driving.Progress.next
  split
  · exact Prefix.Padding.every_stage_is_the_original_stage _ _ _
  · rfl

theorem frame_advance (cache : Inquiry.Frame task) : Accepts task cache.programme (Inquiry.Frame.advance task cache).programme :=
  of_same_stages task (Preservation.self task cache.shell) (fun ordinal _ => frame_advance_stages task cache ordinal)

private theorem owned_advance_stages (cache : Owned.Cache task) (ordinal : Nat) :
    (Owned.advance task cache).programme.at task.original ordinal = cache.programme.at task.original ordinal := by
  change (Driving.Progress.next cache).programme.at task.original ordinal = _
  unfold Driving.Progress.next
  split
  · exact Prefix.Padding.every_stage_is_the_original_stage _ _ _
  · rfl

private theorem fee_stages (cache : Inquiry.Frame task) (ordinal : Nat) :
    (Planning.fee task cache).final.programme.at task.original ordinal = cache.programme.at task.original ordinal := by
  unfold Planning.fee
  split
  · split
    · split <;> rfl
    · change (if task.continueUnreserved then Owned.advance task cache.restore else cache.restore).programme.at task.original ordinal = _
      split
      · exact owned_advance_stages task cache.restore ordinal
      · rfl
  · rfl

private theorem wait_stages (fuel : Nat) (cache : Inquiry.Frame task) (ordinal : Nat) :
    (Planning.wait task fuel cache).path.finish.programme.at task.original ordinal = cache.programme.at task.original ordinal := by
  induction fuel generalizing cache with
  | zero => rfl
  | succ fuel ih =>
      unfold Planning.wait
      split
      · split
        · rfl
        · exact (ih _).trans (frame_advance_stages task cache ordinal)
      · rfl

theorem stage_stages (cache : Inquiry.Frame task) (ordinal : Nat) :
    (Planning.stage task cache).path.finish.programme.at task.original ordinal = cache.programme.at task.original ordinal := by
  unfold Planning.stage
  dsimp only
  split
  · split
    · exact (wait_stages task _ _ ordinal).trans (fee_stages task cache ordinal)
    · exact fee_stages task cache ordinal
  · exact fee_stages task cache ordinal

theorem stage (cache : Inquiry.Frame task) : Accepts task cache.programme (Planning.stage task cache).path.finish.programme :=
  of_same_stages task (Preservation.self task cache.shell) (fun ordinal _ => stage_stages task cache ordinal)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Learning.Paid.Owned.PublicTask.Local.Inquiry.Preservation.Restoration
