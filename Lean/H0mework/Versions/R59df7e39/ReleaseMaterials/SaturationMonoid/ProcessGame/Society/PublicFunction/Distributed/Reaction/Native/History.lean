import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Service

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native

open Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (source : Machine Party Good Port Technology Instrument)

inductive Shape (index : Slot source) (depth : Nat) (state : ResponsibilityState (V source)) : Type
  | live (unpaid : ∀ earlier < depth, ¬ Paid source earlier index)
      (slots : state.slots = [.live (obligation source index)])
  | terminal (first : Nat) (earlier : first < depth) (paid : Paid source first index)
      (slots : state.slots = [.terminal (paidArchive source index first paid)])

structure Prefix (index : Slot source) (depth : Nat) where
  state : ResponsibilityState (V source)
  run : (process source).Run (ResponsibilityState.empty (V source)) state
  shape : Shape source index depth state

def initial (index : Slot source) : Prefix source index 0 :=
  let edge : (process source).Edge (ResponsibilityState.empty (V source)) := .admit index
  ⟨edge.target, .step .nil edge, .live (by intro earlier impossible; omega) rfl⟩

def advance (index : Slot source) (depth : Nat) (prior : Prefix source index depth) : Prefix source index (depth + 1) := by
  rcases prior with ⟨state, run, shape⟩
  cases shape with
  | live unpaid slots =>
      let address : Fin state.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ 0⟩
      have present : state.slots.get address = .live (obligation source index) := by simp [slots, address]
      let edge : (process source).Edge state := .cross address (obligation source index) present (review source index depth)
      by_cases paid : Paid source depth index
      · exact ⟨edge.target, .step run edge, .terminal depth (by omega) paid (by
          simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition, reviewSource,
            review, dif_pos paid, slots, address, BoundaryDisposition.targetSlot, paidArchive])⟩
      · exact ⟨edge.target, .step run edge, .live (by
          intro earlier bound
          by_cases old : earlier < depth
          · exact unpaid earlier old
          · have same : earlier = depth := by omega
            exact same ▸ paid) (by
          simp [edge, NativeResponsibilityProcess.Edge.target, process, disposition, reviewSource,
            review, dif_neg paid, slots, address, BoundaryDisposition.targetSlot, ActiveCarryDisposition.target])⟩
  | terminal first earlier paid slots =>
      exact ⟨state, run, .terminal first (by omega) paid slots⟩

def historyAt (index : Slot source) : (depth : Nat) → Prefix source index depth
  | 0 => initial source index
  | depth + 1 => advance source index depth (historyAt index depth)

theorem native_terminal_iff_actual_payment (index : Slot source) (depth : Nat) :
    (historyAt source index depth).state.TerminalAt 0 ↔ ∃ earlier < depth, Paid source earlier index := by
  cases (historyAt source index depth).shape with
  | live unpaid slots =>
      constructor
      · rintro ⟨archive, terminal⟩; simp [slots] at terminal
      · rintro ⟨earlier, bound, paid⟩; exact False.elim (unpaid earlier bound paid)
  | terminal first earlier paid slots =>
      exact ⟨fun _ => ⟨first, earlier, paid⟩, fun _ => ⟨paidArchive source index first paid, by simp [slots]⟩⟩

theorem native_live_iff_unpaid (index : Slot source) (depth : Nat) :
    (historyAt source index depth).state.LiveAt 0 ↔ ∀ earlier < depth, ¬ Paid source earlier index := by
  cases (historyAt source index depth).shape with
  | live unpaid slots => exact ⟨fun _ => unpaid, fun _ => ⟨obligation source index, by simp [slots]⟩⟩
  | terminal first earlier paid slots =>
      constructor
      · rintro ⟨obligation, live⟩; simp [slots] at live
      · intro unpaid; exact False.elim (unpaid first earlier paid)

theorem first_archive_is_retained (index : Slot source) (depth later : Nat)
    (terminal : (historyAt source index depth).state.TerminalAt 0) :
    (historyAt source index (depth + later)).state = (historyAt source index depth).state := by
  induction later with
  | zero => rfl
  | succ later ih =>
      have still : (historyAt source index (depth + later)).state.TerminalAt 0 := ih ▸ terminal
      change (advance source index (depth + later) (historyAt source index (depth + later))).state = _
      generalize historyAt source index (depth + later) = prior at *
      rcases prior with ⟨state, run, shape⟩
      cases shape with
      | live unpaid slots =>
          obtain ⟨archive, present⟩ := still
          simp [slots] at present
      | terminal first earlier paid slots => exact ih

theorem actual_service_closes_every_native_slot (depth : Nat)
    (paid : ServiceAdequate source.code.law (source.actualExecution depth).before source.code.task
      (source.actualExecution depth).submitted) (index : Slot source) :
    (historyAt source index (depth + 1)).state.TerminalAt 0 := by
  apply (native_terminal_iff_actual_payment source index (depth + 1)).mpr
  refine ⟨depth, by omega, paid.1, ?_, paid.2.2 _ (List.get_mem _ _)⟩
  rw [(source.actualExecution depth).after_exact]
  exact paid.2.1

theorem original_admission_and_full_history (index : Slot source) (depth : Nat) :
    (historyAt source index depth).state.history = (historyAt source index depth).run.events ∧
      (historyAt source index depth).state.slots.length = 1 ∧
      (∀ archive, (historyAt source index depth).state.slots[0]? = some (.terminal archive) →
        archive.obligation = obligation source index) := by
  refine ⟨by simpa [ResponsibilityState.empty] using (historyAt source index depth).run.history_eq, ?_⟩
  cases (historyAt source index depth).shape with
  | live unpaid slots =>
      refine ⟨by simp [slots], ?_⟩
      intro archive impossible
      simp [slots] at impossible
  | terminal first earlier paid slots =>
      refine ⟨by simp [slots], ?_⟩
      intro archive present
      have same : paidArchive source index first paid = archive := by simpa [slots] using present
      exact same ▸ rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native
