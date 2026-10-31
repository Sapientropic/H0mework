import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.ImplicitReview.Completion.Native.Identity
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Resolve
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.NativeGate

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.ImplicitReview.Completion.Native

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  (task : ReviewSource.Material.OriginalTask input depth count)
  (current : Physical.Cursor Party Good Port Technology Instrument)

inductive SlotInspection : Type
  | paid (actual : ∀ index : ReviewSource.Material.Slot input depth count task,
      (ReviewSource.Material.payment? input depth count prefixLimit renewalLimit task current index).isSome = true)
  | unpaid (index : ReviewSource.Material.Slot input depth count task)
      (missing : ReviewSource.Material.payment? input depth count prefixLimit renewalLimit task current index = none)

/-- Inspect only the finite original slot positions and occurred canonical
or actual-past receipts. No successful service witness is an input. -/
def inspectSlots : SlotInspection (prefixLimit := prefixLimit) (renewalLimit := renewalLimit) task current :=
  match Abolition.Material.inspectList (fun index : ReviewSource.Material.Slot input depth count task =>
      (ReviewSource.Material.payment? input depth count prefixLimit renewalLimit task current index).isSome = true)
      (List.finRange task.val.slots.length) with
  | .clear actual => .paid (fun index => actual index (by simp))
  | .failure index _ absent => .unpaid index (by
      cases found : ReviewSource.Material.payment? input depth count prefixLimit renewalLimit task current index with
      | none => rfl
      | some payment => exact False.elim (absent (by rw [found]; rfl)))

inductive ReadoutResult : ReviewSource.Native.ReadoutAt input depth count prefixLimit renewalLimit current → Type
  | undisclosed : ReadoutResult .undisclosed
  | unpaid (readout : ReviewSource.Native.ReadoutAt input depth count prefixLimit renewalLimit current)
      (index : ReviewSource.Material.Slot input depth count task)
      (missing : ReviewSource.Material.payment? input depth count prefixLimit renewalLimit task current index = none) :
      ReadoutResult readout
  | recorded (scope : ReviewSource.Native.RecordedAt input depth count prefixLimit renewalLimit current)
      (actual : RecordedResult task current scope) : ReadoutResult (.recorded scope)

def consumeInspection
    (readout : ReviewSource.Native.ReadoutAt input depth count prefixLimit renewalLimit current)
    (inspection : SlotInspection (prefixLimit := prefixLimit) (renewalLimit := renewalLimit) task current) :
    ReadoutResult task current readout :=
  match inspection with
  | .unpaid index missing => .unpaid readout index missing
  | .paid actual => match readout with
    | .undisclosed => .undisclosed
    | .recorded scope => .recorded scope (resolveRecorded task current scope actual)

def ReadoutResult.hasPaidScope
    {readout : ReviewSource.Native.ReadoutAt input depth count prefixLimit renewalLimit current} :
    ReadoutResult task current readout → Bool
  | .recorded _ (.paid _) => true
  | _ => false

structure BothAt (readouts : ReviewSource.Native.ReadoutsAt input depth count prefixLimit renewalLimit current) where
  explicit : ReadoutResult task current readouts.explicit
  registered : ReadoutResult task current readouts.registered

/-- Both installed sources consume the same actual slot inspection. Equal
raw tasks do not merge the two original creators or discard either GS. -/
def produceBoth (readouts : ReviewSource.Native.ReadoutsAt input depth count prefixLimit renewalLimit current) :
    BothAt task current readouts :=
  let inspection := inspectSlots task current
  ⟨consumeInspection task current readouts.explicit inspection,
    consumeInspection task current readouts.registered inspection⟩

theorem every_observed_slot_generates_a_paid_inspection
    (paid : ∀ index : ReviewSource.Material.Slot input depth count task,
      (ReviewSource.Material.payment? input depth count prefixLimit renewalLimit task current index).isSome = true) :
    ∃ actual, inspectSlots (prefixLimit := prefixLimit) (renewalLimit := renewalLimit) task current = .paid actual := by
  cases inspection : inspectSlots (prefixLimit := prefixLimit) (renewalLimit := renewalLimit) task current with
  | paid actual => exact ⟨actual, rfl⟩
  | unpaid index missing =>
      have impossible := paid index
      rw [missing] at impossible
      cases impossible

/-- Every missing slot still has its original bearer and original source
row; a native identity failure does not discharge that row either. -/
theorem the_original_native_responsibility_still_has_its_actual_next_row :
    ((ProgrammeLedger.evolution input (Settlement.committedVisit input depth count).current).destination
      (ReviewSource.Material.nativeResponsibilityEntry input depth count)).1 =
      ProgrammeSource.targetEntry input (Settlement.committedVisit input depth count).current .inherited := by
  unfold ReviewSource.Material.nativeResponsibilityEntry
  cases (Settlement.committedVisit input depth count).current <;>
    exact ProgrammeLedger.destination_exact input _ _

#print axioms inspectSlots
#print axioms produceBoth
#print axioms every_observed_slot_generates_a_paid_inspection
#print axioms the_original_native_responsibility_still_has_its_actual_next_row

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Migration.ImplicitReview.Completion.Native
