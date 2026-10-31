import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.Run
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Allocation

/-! Existing source allocation is consumed as its exact dependent native
Run. The old FIFO, share arithmetic and single quota are not reimplemented. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)
  (before : (Financial.process input).GeneratedState) (available : ℚ)

structure AllocationTransport (original : Financial.Allocation input before available) where
  private mk ::
  after : (process input depth count).GeneratedState
  transition : (process input depth count).Run
    (generated input depth count before).current after.current
  faithful : after.current = state input depth count original.after.current

def transportAllocation (original : Financial.Allocation input before available) :
    AllocationTransport input depth count before available original :=
  let computed := foldRun input depth count original.transition
  let extension : (process input depth count).Run
      (generated input depth count before).current computed.target := by
    rw [generated_current]
    exact computed.run
  ⟨⟨computed.target, (generated input depth count before).generated.concatRuns
      (process input depth count) extension⟩, extension, computed.faithful⟩

theorem old_allocation_retains_the_same_quota (original : Financial.Allocation input before available) :
    original.used input + original.remaining = available ∧
    0 ≤ original.remaining ∧ original.remaining ≤ available :=
  ⟨original.whole_quota input, original.remaining_nonnegative, original.remaining_le⟩

theorem mapped_allocation_keeps_every_old_slot (original : Financial.Allocation input before available) :
    (transportAllocation input depth count before available original).after.current.slots =
      original.after.current.slots.map (slot input depth count) ∧
    (transportAllocation input depth count before available original).after.current.slots.length =
      before.current.slots.length := by
  rw [(transportAllocation input depth count before available original).faithful]
  exact ⟨rfl, (List.length_map _).trans (original.original_slots_length input)⟩

theorem mapped_allocation_extends_the_existing_history (original : Financial.Allocation input before available) :
    before.current.history.map (lifecycle input depth count) <+:
      (transportAllocation input depth count before available original).after.current.history :=
  old_history_remains_a_prefix_of_every_native_extension input depth count before
    (transportAllocation input depth count before available original).transition

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Legacy.transportAllocation
