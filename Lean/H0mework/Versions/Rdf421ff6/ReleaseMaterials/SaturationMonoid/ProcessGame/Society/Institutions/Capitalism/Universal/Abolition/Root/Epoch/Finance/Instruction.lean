import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count : Nat)

inductive InstructionResult (origin : ActualItem input depth count)
    (before : (process input depth count).GeneratedState)
  | issued (claim : NewClaim input depth count) (exactOrigin : claim.origin = origin)
  | movement (source : Movement input depth count origin)
      (allocation : Allocation input depth count before source.quantity)
  | retained
  | refused (refused : ¬ (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
      (origin.instruction input depth count).request)

namespace InstructionResult

def next {origin : ActualItem input depth count}
    {before : (process input depth count).GeneratedState} :
    InstructionResult input depth count origin before →
      (process input depth count).GeneratedState
  | .issued claim _ => before.step (process input depth count) (.admit (.inr claim))
  | .movement _ allocation => allocation.after
  | .retained | .refused _ => before

def transition {origin : ActualItem input depth count}
    {before : (process input depth count).GeneratedState}
    (result : InstructionResult input depth count origin before) :
    (process input depth count).Run before.current (result.next input depth count).current := by
  cases result with
  | issued claim _ => exact .step .nil (.admit (P := process input depth count) (.inr claim))
  | movement _ allocation => exact allocation.transition
  | retained => exact .nil
  | refused _ => exact .nil

theorem history_retained {origin : ActualItem input depth count}
    {before : (process input depth count).GeneratedState}
    (result : InstructionResult input depth count origin before) :
    before.current.history <+: (result.next input depth count).current.history := by
  rw [(result.transition input depth count).history_eq]
  exact List.prefix_append _ _

theorem original_claims_retained {origin : ActualItem input depth count}
    {before : (process input depth count).GeneratedState}
    (result : InstructionResult input depth count origin before) :
    before.current.slots.map (slotClaim input depth count) <+:
      (result.next input depth count).current.slots.map (slotClaim input depth count) := by
  cases result with
  | issued claim exactOrigin =>
      change _ <+: (before.current.slots ++ _).map _
      rw [List.map_append]
      exact List.prefix_append _ _
  | movement _ allocation => rw [next, allocation.original_claims]
  | retained => exact List.prefix_rfl
  | refused _ => exact List.prefix_rfl

/-- An unmatched source quota remains attached to its exact executed item. -/
def Unallocated {origin : ActualItem input depth count}
    {before : (process input depth count).GeneratedState} :
    InstructionResult input depth count origin before → Prop
  | .movement _ allocation => 0 < allocation.remaining
  | _ => False

end InstructionResult

def consume (origin : ActualItem input depth count)
    (before : (process input depth count).GeneratedState) :
    InstructionResult input depth count origin before :=
  if refused : ¬ (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
      (origin.instruction input depth count).request then .refused refused
  else
    match returned : readNewClaim input depth count origin with
    | some claim => .issued claim (readNewClaim_origin input depth count origin claim returned)
    | none =>
        match readMovement input depth count origin with
        | some movement => .movement movement (allocate input depth count origin movement before)
        | none => .retained

theorem issued_appends_actual_epoch_debt (origin : ActualItem input depth count)
    (before : (process input depth count).GeneratedState)
    (claim : NewClaim input depth count)
    (returned : readNewClaim input depth count origin = some claim) :
    ((consume input depth count origin before).next input depth count).current.slots[before.current.slots.length]? =
      some (.live (admission input depth count (.inr claim)).toObligation) := by
  have source := readNewClaim_origin input depth count origin claim returned
  have accepted : (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
      (origin.instruction input depth count).request := by
    rw [← source]
    exact claim.accepted
  unfold consume
  rw [dif_neg (not_not_intro accepted)]
  split
  · rename_i actual same
    cases Option.some.inj (same.symm.trans returned)
    exact (process input depth count).admit_target_slot (.inr claim)
  · rename_i absent
    cases absent.symm.trans returned

theorem rejected_item_keeps_the_existing_account (origin : ActualItem input depth count)
    (before : (process input depth count).GeneratedState)
    (refused : ¬ (origin.interpreter input depth count).Valid (origin.instruction input depth count).before
      (origin.instruction input depth count).request) :
    (consume input depth count origin before).next input depth count = before := by
  simp only [consume, dif_pos refused, InstructionResult.next]

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.issued_appends_actual_epoch_debt
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.rejected_item_keeps_the_existing_account
