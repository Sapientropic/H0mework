import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Outstanding.History.NativeThread

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro

open ResponsibilityLifecycle Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (source : OutstandingSource Party Good Port Technology Instrument)
  (originInputs : List (RawEvent Party Good Port Technology Instrument))

local notation "P" => OutstandingSource.History.NativeService.threadProcess source originInputs
local notation "obligation" => OutstandingSource.History.NativeService.obligation source originInputs

/-- This is a shape of one original native state, not an additional account.
The original archived obligation remains the only identity in either branch. -/
inductive StateShape (index : source.Slot) (state : ResponsibilityState (OutstandingSource.History.NativeService.V source originInputs)) : Type
  | live (slots : state.slots = [.live (obligation index)])
  | terminal (archive : TerminalArchive (OutstandingSource.History.NativeService.V source originInputs))
      (original : archive.obligation = obligation index) (slots : state.slots = [.terminal archive])

structure Attached (index : source.Slot) where
  private mk ::
  state : (P).GeneratedState
  shape : StateShape source originInputs index state.current

variable {source originInputs}

def Attached.fromThread {index : source.Slot} {inputs : List (RawEvent Party Good Port Technology Instrument)}
    (thread : OutstandingSource.History.NativeService.Thread source originInputs index inputs) : Attached source originInputs index :=
  ⟨thread.state, by
    cases thread.shape with
    | live unpaid slots => exact .live slots
    | terminal archive paid recorded original slots => exact .terminal archive original slots⟩

theorem Attached.inherits_the_entire_original_generated_state {index : source.Slot}
    {inputs : List (RawEvent Party Good Port Technology Instrument)}
    (thread : OutstandingSource.History.NativeService.Thread source originInputs index inputs) :
    (Attached.fromThread thread).state = thread.state := rfl

private theorem singleton_of_head {A : Type} {slots : List A} {value : A}
    (one : slots.length = 1) (head : slots[0]? = some value) : slots = [value] := by
  obtain ⟨item, same⟩ := List.length_eq_one_iff.mp one
  rw [same] at head
  cases Option.some.inj head
  exact same

variable (source originInputs)

private theorem actual_length
    (state : (P).GeneratedState) (index : source.Slot) (address : Fin state.current.slots.length)
    (present : state.current.slots.get address = .live (obligation index)) (actual : SourceInput source) :
    (OutstandingSource.History.NativeService.advanceActual source originInputs state index address present actual).current.slots.length =
      state.current.slots.length := by
  simp only [OutstandingSource.History.NativeService.advanceActual,
    OutstandingSource.History.NativeService.actualEdge, NativeResponsibilityProcess.GeneratedState.step,
    NativeResponsibilityProcess.Edge.target, List.length_set]

variable {source originInputs}

def Attached.advance {index : source.Slot} (prior : Attached source originInputs index) (actual : SourceInput source) :
    Attached source originInputs index := by
  rcases prior with ⟨state, shape⟩
  cases shape with
  | terminal archive original slots => exact ⟨state, .terminal archive original slots⟩
  | live slots =>
      let address : Fin state.current.slots.length := ⟨0, by rw [slots]; exact Nat.zero_lt_succ _⟩
      have present : state.current.slots.get address = .live (obligation index) := by simp [slots, address]
      let next := OutstandingSource.History.NativeService.advanceActual source originInputs state index address present actual
      have one : next.current.slots.length = 1 :=
        (actual_length source originInputs state index address present actual).trans (by rw [slots]; rfl)
      by_cases paid : actual.Paid index
      · exact ⟨next, .terminal
          (OutstandingSource.History.NativeService.actualArchive source originInputs index actual paid) rfl
          (singleton_of_head one (OutstandingSource.History.NativeService.actual_paid_generates_original_terminal
            source originInputs state index address present actual paid))⟩
      · exact ⟨next, .live (singleton_of_head one
          (OutstandingSource.History.NativeService.actual_unpaid_keeps_original_live
            source originInputs state index address present actual paid))⟩

def Attached.actualRun {index : source.Slot} (prior : Attached source originInputs index) (actual : SourceInput source) :
    (P).Run prior.state.current (prior.advance actual).state.current := by
  rcases prior with ⟨state, shape⟩
  cases shape with
  | terminal archive original slots => exact .nil
  | live slots =>
      dsimp only [Attached.advance]
      split <;> exact OutstandingSource.History.NativeService.actualRun source originInputs state index _ _ actual

theorem Attached.actual_payment_settles_the_original_slot {index : source.Slot}
    (prior : Attached source originInputs index) (actual : SourceInput source) (paid : actual.Paid index) :
    (prior.advance actual).state.current.TerminalAt 0 := by
  rcases prior with ⟨state, shape⟩
  cases shape with
  | terminal archive original slots => exact ⟨archive, by simp [Attached.advance, slots]⟩
  | live slots =>
      dsimp only [Attached.advance]
      rw [dif_pos paid]
      exact ⟨_, OutstandingSource.History.NativeService.actual_paid_generates_original_terminal source originInputs state index _ _ actual paid⟩

theorem Attached.terminal_keeps_the_complete_state {index : source.Slot}
    (prior : Attached source originInputs index) (actual : SourceInput source)
    (terminal : prior.state.current.TerminalAt 0) : (prior.advance actual).state = prior.state := by
  rcases prior with ⟨state, shape⟩
  cases shape with
  | terminal archive original slots => rfl
  | live slots =>
      obtain ⟨archive, present⟩ := terminal
      simp only [slots, List.getElem?_cons_zero] at present
      cases present

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro

open ResponsibilityLifecycle Source.Program PublicFunction

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {source : OutstandingSource Party Good Port Technology Instrument}
  {originInputs : List (RawEvent Party Good Port Technology Instrument)} {index : source.Slot}

namespace Attached

variable (state : Attached source originInputs index)

theorem live_iff_not_terminal : state.state.current.LiveAt 0 ↔ ¬ state.state.current.TerminalAt 0 := by
  cases state.shape with
  | live slots => simp [ResponsibilityState.LiveAt, ResponsibilityState.TerminalAt, slots]
  | terminal archive original slots => simp [ResponsibilityState.LiveAt, ResponsibilityState.TerminalAt, slots]

theorem original_obligation_is_preserved :
    state.state.current.slots = [.live (OutstandingSource.History.NativeService.obligation source originInputs index)] ∨
      ∃ archive, state.state.current.slots = [.terminal archive] ∧
        archive.obligation = OutstandingSource.History.NativeService.obligation source originInputs index := by
  cases state.shape with
  | live slots => exact .inl slots
  | terminal archive original slots => exact .inr ⟨archive, slots, original⟩

theorem advance_live_iff (actual : SourceInput source) :
    (state.advance actual).state.current.LiveAt 0 ↔ state.state.current.LiveAt 0 ∧ ¬ actual.Paid index := by
  rcases state with ⟨generated, shape⟩
  cases shape with
  | terminal archive original slots =>
      simp only [Attached.advance]
      simp [ResponsibilityState.LiveAt, slots]
  | live slots =>
      have oldLive : generated.current.LiveAt 0 :=
        ⟨OutstandingSource.History.NativeService.obligation source originInputs index, by simp [slots]⟩
      by_cases paid : actual.Paid index
      · have terminal := (⟨generated, .live slots⟩ : Attached source originInputs index).actual_payment_settles_the_original_slot actual paid
        exact ⟨fun live => False.elim
          (((⟨generated, .live slots⟩ : Attached source originInputs index).advance actual).live_iff_not_terminal.mp live terminal),
          fun pair => False.elim (pair.2 paid)⟩
      · have nextLive : ((⟨generated, .live slots⟩ : Attached source originInputs index).advance actual).state.current.LiveAt 0 := by
          dsimp only [Attached.advance]
          rw [dif_neg paid]
          exact ⟨_, OutstandingSource.History.NativeService.actual_unpaid_keeps_original_live source originInputs generated index _ _ actual paid⟩
        exact ⟨fun _ => ⟨oldLive, paid⟩, fun _ => nextLive⟩

theorem advance_terminal_iff (actual : SourceInput source) :
    (state.advance actual).state.current.TerminalAt 0 ↔ state.state.current.TerminalAt 0 ∨ actual.Paid index := by
  classical
  have before := state.live_iff_not_terminal
  have after := (state.advance actual).live_iff_not_terminal
  have evolved := state.advance_live_iff actual
  tauto

theorem original_history_is_a_prefix (actual : SourceInput source) :
    state.state.current.history <+: (state.advance actual).state.current.history := by
  have same := (state.actualRun actual).history_eq
  rw [same]
  exact List.prefix_append _ _

end Attached
end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Services.Native.Micro
