import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.Declaration
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link.Thread

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

local notation "Raw" => Compile.RawInput Party Good Port Technology Instrument

theorem an_original_actual_payment_terminates_the_same_recorded_native_slot
    (past : List Raw) (position : Fin past.length) (index : Slot code)
    (paid : (actualInput depth count prefixLimit renewalLimit (past.take position.val)
      (past.get position)).Paid (code := code) index) :
    ((OriginAt.source code).state depth count
      (atPast (.source code) depth count prefixLimit renewalLimit past index)).current.TerminalAt 0 := by
  let consumed :=  past.take position.val
  let raw := past.get position
  let suffix := past.drop (position.val + 1)
  have decomposition : past = (consumed ++ [raw]) ++ suffix := by
    dsimp [consumed, raw, suffix]
    rw [← List.take_succ_eq_append_getElem position.isLt]
    exact (List.take_append_drop (position.val + 1) past).symm
  have paidPrefix :
      (atPast (.source code) depth count prefixLimit renewalLimit (consumed ++ [raw]) index).state.current.TerminalAt 0 := by
    have same := atPast_append (.source code) depth count prefixLimit renewalLimit consumed raw index
    exact (congrArg (fun thread : Thread code index => thread.state.current.TerminalAt 0) same).mpr
      (an_actual_payment_terminates_or_retains_the_original_archive code _ _ paid)
  have final := an_actual_paid_prefix_stays_terminal_after_every_actual_suffix code depth count prefixLimit renewalLimit
    (consumed ++ [raw]) suffix
    (atPast (.source code) depth count prefixLimit renewalLimit (consumed ++ [raw]) index) paidPrefix
  change (atPast (.source code) depth count prefixLimit renewalLimit past index).state.current.TerminalAt 0
  have same : atPast (.source code) depth count prefixLimit renewalLimit past index =
      fold (.source code) depth count prefixLimit renewalLimit (consumed ++ [raw]) suffix
        (atPast (.source code) depth count prefixLimit renewalLimit (consumed ++ [raw]) index) := by
    change fold (.source code) depth count prefixLimit renewalLimit [] past _ = _
    rw [decomposition]
    exact fold_append (.source code) depth count prefixLimit renewalLimit [] (consumed ++ [raw]) suffix _
  exact (congrArg (fun thread : Thread code index => thread.state.current.TerminalAt 0) same).mpr final

omit [DecidableEq Port] in
private theorem canonical_payment_terminates_the_original_slot
    (index : Slot code) (ordinal : Nat) (prior : Prefix code index)
    (paid : SlotPaid code ordinal index) :
    (advance code index ordinal prior).state.current.TerminalAt 0 := by
  rcases prior with ⟨state, shape⟩
  cases shape with
  | live slots =>
      refine ⟨archive code index ordinal paid, ?_⟩
      simp [advance, paid, NativeResponsibilityProcess.GeneratedState.step,
        NativeResponsibilityProcess.Edge.target, process, disposition, reviewSource, inputReceipt,
        Event.Paid, slots, BoundaryDisposition.targetSlot, archive]
  | terminal paidOrdinal oldPaid slots =>
      exact ⟨archive code index paidOrdinal oldPaid, by change state.current.slots[0]? = _; rw [slots]; rfl⟩

theorem the_original_declaration_payment_is_retained_in_the_same_native_fold
    (first : declarationOrdinal code depth count = 1)
    (past : List Raw) (index : Slot code) (paid : SlotPaid code 0 index) :
    ((OriginAt.source code).state depth count
      (atPast (.source code) depth count prefixLimit renewalLimit past index)).current.TerminalAt 0 := by
  have seed : ((OriginAt.source code).seed depth count index).state.current.TerminalAt 0 := by
    change (historyAt code index (declarationOrdinal code depth count)).state.current.TerminalAt 0
    rw [first]
    exact canonical_payment_terminates_the_original_slot code index 0 _ paid
  exact an_actual_paid_prefix_stays_terminal_after_every_actual_suffix code depth count prefixLimit renewalLimit
    [] past ((OriginAt.source code).seed depth count index) seed

namespace SameBirth

variable {code depth count}
  {task : Material.OriginalTask code.input depth count}
  (identity : SameBirth code depth count task)

def nativeSlot (index : Material.Slot code.input depth count task) : Slot code :=
  ⟨index.val, by rw [← identity.task_eq]; exact index.isLt⟩

theorem native_slot_is_the_same_original_incidence
    (index : Material.Slot code.input depth count task) :
    Material.slot code.input depth count task index = serviceSlot code (identity.nativeSlot index) := by
  unfold Material.slot serviceSlot nativeSlot
  simp only [identity.task_eq, List.get_eq_getElem]
  rfl

end SameBirth

#print axioms an_original_actual_payment_terminates_the_same_recorded_native_slot
#print axioms the_original_declaration_payment_is_retained_in_the_same_native_fold
#print axioms SameBirth.native_slot_is_the_same_original_incidence

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link
