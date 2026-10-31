import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

/-- Erase only the mutable residual, retaining the complete dependent admission. -/
def identity (slot : ObligationSlot (vocabulary sources)) : AdmittedObligation (vocabulary sources) :=
  { slotObligation sources slot with residual := 0 }

def sourceEvent : LifecycleEvent (vocabulary sources) → Event sources
  | .admitted _ payload => payload.sourceEvent
  | .carried _ _ source _ | .terminal _ _ source _
  | .superseded _ _ source _ | .bearerReleased _ _ source _ => source
  | .reopened _ _ payload => payload.sourceEvent

theorem boundary_identity {obligation : AdmittedObligation (vocabulary sources)}
    (boundary : Boundary sources obligation) :
    identity sources (Boundary.disposition sources boundary).targetSlot =
      identity sources (.live obligation) := by
  unfold Boundary.disposition
  split <;> rfl

theorem cross_source {state : ResponsibilityState (vocabulary sources)}
    (index : Fin state.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.slots.get index = .live obligation) (boundary : Boundary sources obligation) :
    sourceEvent sources (NativeResponsibilityProcess.Edge.cross (P := process sources) index obligation present boundary).lifecycleEvent =
      (boundary.event sources) := by
  dsimp only [NativeResponsibilityProcess.Edge.lifecycleEvent, process]
  unfold Boundary.disposition
  split <;> rfl

/-- The record is the complete dependent lifecycle event at the stable slot. -/
def record (index : Nat) {obligation : AdmittedObligation (vocabulary sources)}
    (boundary : Boundary sources obligation) : LifecycleEvent (vocabulary sources) :=
  match Boundary.disposition sources boundary with
  | .carry carry => .carried index obligation (boundary.event sources) carry
  | .terminal (.final receipt) => .terminal index obligation (boundary.event sources) receipt
  | .terminal (.superseded receipt) => .superseded index obligation (boundary.event sources) receipt
  | .bearerRelease receipt => .bearerReleased index obligation (boundary.event sources) receipt

theorem record_source (index : Nat) {obligation : AdmittedObligation (vocabulary sources)}
    (boundary : Boundary sources obligation) : sourceEvent sources (record sources index boundary) = (boundary.event sources) := by
  unfold record Boundary.disposition
  split <;> rfl

theorem record_slot (index : Nat) {obligation : AdmittedObligation (vocabulary sources)}
    (boundary : Boundary sources obligation) : (record sources index boundary).slot = index := by
  unfold record Boundary.disposition
  split <;> rfl

theorem cross_record {state : ResponsibilityState (vocabulary sources)}
    (index : Fin state.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.slots.get index = .live obligation) (boundary : Boundary sources obligation) :
    (NativeResponsibilityProcess.Edge.cross (P := process sources) index obligation present boundary).lifecycleEvent =
      record sources index.val boundary := by
  dsimp only [NativeResponsibilityProcess.Edge.lifecycleEvent, process, record]
  cases disposition : Boundary.disposition sources boundary with
  | carry carry => rfl
  | terminal receipt => cases receipt <;> rfl
  | bearerRelease receipt => rfl

/-- A dependent financial boundary computes its target. The public `Follow`
also certifies the full records against the supplied run. -/
inductive Path : ObligationSlot (vocabulary sources) → ObligationSlot (vocabulary sources) → Type
  | nil (slot) : Path slot slot
  | snoc {first} {obligation : AdmittedObligation (vocabulary sources)}
      (prior : Path first (.live obligation)) (boundary : Boundary sources obligation) :
      Path first (Boundary.disposition sources boundary).targetSlot

namespace Path

def events {first last} : Path sources first last → List (Event sources)
  | .nil _ => []
  | .snoc prior boundary => prior.events ++ [(boundary.event sources)]

def records {first last} (index : Nat) : Path sources first last → List (LifecycleEvent (vocabulary sources))
  | .nil _ => []
  | .snoc prior boundary => prior.records index ++ [record sources index boundary]

theorem records_sources {first last} (index : Nat) (path : Path sources first last) :
    (path.records sources index).map (sourceEvent sources) = path.events sources := by
  induction path with
  | nil => rfl
  | snoc prior boundary ih =>
      simp only [records, events, List.map_append, List.map_cons, List.map_nil, record_source, ih]

theorem preserves_identity {first last} (path : Path sources first last) :
    identity sources last = identity sources first := by
  induction path with
  | nil => rfl
  | snoc prior boundary ih => exact (boundary_identity sources boundary).trans ih

theorem terminal_is_unchanged {archive : TerminalArchive (vocabulary sources)} {last}
    (path : Path sources (.terminal archive) last) : last = .terminal archive := by
  have general {first last} (path : Path sources first last) :
      ∀ archive, first = .terminal archive → last = .terminal archive := by
    induction path with
    | nil => intro archive same; exact same
    | snoc prior boundary ih =>
        intro archive same
        cases ih archive same
  exact general path archive rfl

end Path

structure Follow {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (index : Nat) (original : ObligationSlot (vocabulary sources)) where
  slot : ObligationSlot (vocabulary sources)
  present : last.slots[index]? = some slot
  path : Path sources original slot
  recorded : path.records sources index = run.events.filter (fun event => event.slot == index)

theorem Follow.sourced {first last : ResponsibilityState (vocabulary sources)}
    {run : (process sources).Run first last} {index original}
    (result : Follow sources run index original) :
    List.Sublist (result.path.events sources) (run.events.map (sourceEvent sources)) := by
  rw [← result.path.records_sources sources index]
  apply List.Sublist.map
  rw [result.recorded]
  exact List.filter_sublist

def follow {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (index : Nat) (original : ObligationSlot (vocabulary sources))
    (present : first.slots[index]? = some original) : Follow sources run index original :=
  match run with
  | .nil => ⟨original, present, .nil original, rfl⟩
  | .step prior edge => by
      rcases follow prior index original present with ⟨slot, atSlot, path, recorded⟩
      have inside := (List.getElem?_eq_some_iff.mp atSlot).choose
      cases edge with
      | admit claim =>
          refine ⟨slot, ?_, path, ?_⟩
          · exact (List.getElem?_append_left inside).trans atSlot
          · have different := Nat.ne_of_gt inside
            simpa only [NativeResponsibilityProcess.Run.events, List.filter_append,
              NativeResponsibilityProcess.Edge.lifecycleEvent, LifecycleEvent.slot,
              List.filter_cons, List.filter_nil, beq_iff_eq, different, if_false, List.append_nil] using recorded
      | cross changed obligation old boundary =>
          by_cases same : changed.val = index
          · have exactOld : slot = .live obligation := by
              have oldAt := congrArg some old
              have lookup := (List.getElem?_eq_getElem changed.isLt).trans oldAt
              rw [same] at lookup
              exact Option.some.inj (atSlot.symm.trans lookup)
            subst slot
            refine ⟨(Boundary.disposition sources boundary).targetSlot, ?_, .snoc path boundary, ?_⟩
            · simpa only [same, process] using (process sources).cross_target_slot changed obligation old boundary
            · simp only [Path.records, NativeResponsibilityProcess.Run.events, List.filter_append]
              rw [cross_record sources changed obligation old boundary, same]
              simp only [List.filter_cons, List.filter_nil]
              rw [record_slot sources index boundary]
              simp only [beq_self_eq_true, if_true]
              exact congrArg (fun records => records ++ [record sources index boundary]) recorded
          · refine ⟨slot, ?_, path, ?_⟩
            · simp only [NativeResponsibilityProcess.Edge.target]
              rw [List.getElem?_set]
              simpa only [if_neg same] using atSlot
            · simp only [NativeResponsibilityProcess.Run.events, List.filter_append,
                List.filter_cons, List.filter_nil]
              rw [cross_record sources changed obligation old boundary,
                record_slot sources changed.val boundary]
              simpa only [beq_iff_eq, same, if_false, List.append_nil] using recorded
      | reopen _ _ _ impossible => exact impossible.elim

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration
