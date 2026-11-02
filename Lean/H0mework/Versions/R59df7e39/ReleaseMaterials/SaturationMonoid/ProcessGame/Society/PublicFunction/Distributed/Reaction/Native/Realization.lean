import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Migration.Realization

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling.Realization

open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument]
  (code : Code Party Good Port Technology Instrument)

def receivedFromImage (image : Identity.EventImage Party Good Port Technology Instrument) (holder : Party) : ℚ :=
  match image with
  | .birth _ => 0
  | .review _ _ _ _ request sender recipient _ balance remaining =>
      match request.operation with
      | .settle .. => if holder = recipient then min remaining (balance sender) else 0
      | _ => 0

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)

omit [DecidableEq Port] in
theorem image_reads_the_actual_receipt (event : Financial.Event input) (holder : Party) :
    receivedFromImage (Identity.eventImage code input event) holder = Financial.Migration.received input event holder := by
  cases event with
  | birth => rfl
  | review claim receipt balance remaining =>
    simp only [Identity.eventImage, receivedFromImage]
    rw [receipt.operation_exact]
    cases kind : receipt.kind <;>
      simp only [Financial.reviewOperation, Financial.Migration.received, Financial.Review.allocated,
        Financial.Review.fromHolder, Financial.Review.toHolder, kind]

private theorem record_slot (record : LifecycleEvent (Financial.vocabulary input)) :
    (recordImage code input record).slot = record.slot := by cases record <;> rfl

private theorem record_source (record : LifecycleEvent (Financial.vocabulary input)) :
    (recordImage code input record).source = Identity.eventImage code input (Financial.Migration.sourceEvent input record) := by
  cases record <;> rfl

def slotImages (index : Nat) (records : List (RecordImage Party Good Port Technology Instrument)) :=
  (records.filter (fun record => record.slot == index)).map RecordImage.source

private theorem selected_images (index : Nat) (records : List (LifecycleEvent (Financial.vocabulary input))) :
    slotImages index (records.map (recordImage code input)) =
      ((records.filter (fun record => record.slot == index)).map (Financial.Migration.sourceEvent input)).map
        (Identity.eventImage code input) := by
  induction records with
  | nil => rfl
  | cons record tail ih =>
    simp only [slotImages, List.map_cons, List.filter_cons, record_slot]
    split
    · simp only [List.map_cons, record_source]
      exact congrArg (List.cons _) ih
    · exact ih

variable {oldFirst oldLast : (Financial.process input).GeneratedState}
  (oldRun : (Financial.process input).Run oldFirst.current oldLast.current)
  (other : ProgrammeSource.Input Party Good Port Technology Instrument)
  {newFirst newLast : (Financial.process other).GeneratedState}
  (newRun : (Financial.process other).Run newFirst.current newLast.current)

/-- Endpoint matches determine the whole intervening native event list. -/
theorem run_images (first : Match code input other oldFirst newFirst) (last : Match code input other oldLast newLast) :
    newRun.events.map (recordImage code other) = oldRun.events.map (recordImage code input) := by
  have whole := last.events
  unfold eventHistory at whole
  have prior := first.events
  unfold eventHistory at prior
  rw [newRun.history_eq, oldRun.history_eq, List.map_append, List.map_append, prior] at whole
  exact List.append_cancel_left whole

private theorem followed_images {first last : (Financial.process input).GeneratedState}
    (run : (Financial.process input).Run first.current last.current) (index : Nat)
    (original : ObligationSlot (Financial.vocabulary input)) (follow : Financial.Migration.Follow input run index original) :
    (follow.path.events input).map (Identity.eventImage code input) = slotImages index (run.events.map (recordImage code input)) := by
  rw [← follow.path.records_sources input index, follow.recorded]
  exact (selected_images code input index run.events).symm

/-- Real accepted receipts are transported; residual differences are never used as payments. -/
theorem receivedBy (first : Match code input other oldFirst newFirst) (last : Match code input other oldLast newLast)
    (index : Nat) (original : ObligationSlot (Financial.vocabulary input))
    (replacement : ObligationSlot (Financial.vocabulary other))
    (old : Financial.Migration.Follow input oldRun index original)
    (new : Financial.Migration.Follow other newRun index replacement) (holder : Party) :
    new.path.receivedBy other holder = old.path.receivedBy input holder := by
  have images := (followed_images code other newRun index replacement new).trans
    ((congrArg (slotImages index) (run_images code input oldRun other newRun first last)).trans
      (followed_images code input oldRun index original old).symm)
  have values := congrArg (fun images => (images.map (fun image => receivedFromImage image holder)).sum) images
  simpa only [List.map_map, Function.comp_def, image_reads_the_actual_receipt, Financial.Migration.Path.receivedBy] using values

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Coupling.Realization
