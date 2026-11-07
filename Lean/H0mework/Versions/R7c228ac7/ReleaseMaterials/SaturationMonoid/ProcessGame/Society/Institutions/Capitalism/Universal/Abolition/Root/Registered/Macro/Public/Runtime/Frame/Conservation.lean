import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame.Bound

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  {origin : Abolition.Functions.Revision.Context (input := input) (review := review)
    depth count prefixLimit renewalLimit sourceDepth sourceCount}
  {admission : Abolition.Functions.Revision.InitialAdmissionAt origin}
  (frame : Frame origin admission)

/-- All three actual source branches update the original process account.
Birth performs its single admit; a new raw body carries the complete old GS. -/
def nextNative : (Epoch.Finance.process input depth count).Run frame.account.current frame.next.account.current := by
  unfold next
  split
  · unfold internalNext
    split
    · rename_i registered parsed
      exact registered.nativeAdmission
    · exact Accounting.nativeTransitionAt input depth count prefixLimit renewalLimit origin.germ.snapshot.past frame.start frame.actual.actual
  · exact .nil

theorem next_keeps_all_original_claims :
    frame.account.current.slots.map (Epoch.Finance.slotClaim input depth count) <+:
      frame.next.account.current.slots.map (Epoch.Finance.slotClaim input depth count) :=
  Epoch.Finance.run_retains_all_claims input depth count frame.nextNative

theorem next_keeps_the_complete_original_history :
    frame.account.current.history <+: frame.next.account.current.history := by
  rw [frame.nextNative.history_eq]
  exact List.prefix_append _ _

theorem next_keeps_the_same_source_reader : frame.next.reader = frame.reader := by
  unfold next
  split
  · unfold internalNext
    split <;> rfl
  · rfl

theorem visits_keep_the_same_source_reader (tick : Nat) : (frame.visits tick).reader = frame.reader := by
  induction tick with
  | zero => rfl
  | succ tick inherited =>
    change ((next^[tick + 1]) frame).reader = _
    rw [Function.iterate_succ_apply']
    exact (next_keeps_the_same_source_reader _).trans inherited

/-- The finite trace is folded from actual source steps, including every
native admission; its original anchor is never reconstructed. -/
def visitsNative : (tick : Nat) → (Epoch.Finance.process input depth count).Run
    frame.account.current (frame.visits tick).account.current
  | 0 => .nil
  | tick + 1 => by
    simpa only [visits, Function.iterate_succ_apply'] using
      (visitsNative tick).concatRuns (Epoch.Finance.process input depth count) (frame.visits tick).nextNative

theorem visits_keep_all_original_claims (tick : Nat) :
    frame.account.current.slots.map (Epoch.Finance.slotClaim input depth count) <+:
      (frame.visits tick).account.current.slots.map (Epoch.Finance.slotClaim input depth count) :=
  Epoch.Finance.run_retains_all_claims input depth count (frame.visitsNative tick)

theorem visits_keep_the_complete_original_history (tick : Nat) :
    frame.account.current.history <+: (frame.visits tick).account.current.history := by
  rw [(frame.visitsNative tick).history_eq]
  exact List.prefix_append _ _

#print axioms nextNative
#print axioms next_keeps_all_original_claims
#print axioms next_keeps_the_complete_original_history
#print axioms visits_keep_the_same_source_reader
#print axioms visitsNative
#print axioms visits_keep_the_complete_original_history

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Runtime.Frame
