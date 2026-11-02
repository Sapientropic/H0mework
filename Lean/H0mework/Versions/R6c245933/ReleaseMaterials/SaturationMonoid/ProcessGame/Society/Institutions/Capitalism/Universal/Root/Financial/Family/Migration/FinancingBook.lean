import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.AssignedFinancing.Joint.Posting
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.DelayedFinancing

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook
open ResponsibilityLifecycle
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

/-- The initial tag is computed from the checked original birth relations,
without requiring any future return. Later acquisitions use the same split. -/
def initial (claim : Claim sources) : Share.Split (initialBalance (sources claim.1) claim.2) :=
  if (DelayedFinancing.origins sources claim).isEmpty then AssignedFinancing.Joint.initial sources claim
  else ⟨initialBalance (sources claim.1) claim.2,0,initial_nonnegative _ _,fun _ => le_rfl,add_zero _⟩

theorem initial_positive_has_its_source (claim : Claim sources) (party : Party)
    (positive : 0 < (initial sources claim).selected party) : Nonempty (DelayedFinancing.Open sources claim) := by
  cases origins : DelayedFinancing.origins sources claim with
  | nil => simp [initial,origins,AssignedFinancing.Joint.initial] at positive
  | cons origin rest => exact ⟨origin⟩

structure Cell where
  slot : ObligationSlot (vocabulary sources)
  shares : Share.Split (slotBalance sources slot)

/-- A finite refinement of the current original slots, in their original order. -/
structure Book (state : ResponsibilityState (vocabulary sources)) where
  cells : List (Cell sources)
  slots_exact : cells.map Cell.slot = state.slots

namespace Book
variable {sources} {state : ResponsibilityState (vocabulary sources)} (book : Book sources state)

theorem length : book.cells.length = state.slots.length := by
  simpa only [List.length_map] using congrArg List.length book.slots_exact

def cellAt (index : Fin state.slots.length) : Cell sources :=
  book.cells[index.val]'(by rw [book.length]; exact index.isLt)

theorem at_slot (index : Fin state.slots.length) : (book.cellAt index).slot = state.slots.get index := by
  have same := congrArg (fun slots => slots[index.val]?) book.slots_exact
  have bounded : index.val < book.cells.length := by rw [book.length]; exact index.isLt
  simpa only [List.getElem?_map,List.getElem?_eq_getElem bounded,List.getElem?_eq_getElem index.isLt,
    Option.map_some,Option.some.injEq,cellAt,List.get_eq_getElem] using same

def before (index : Fin state.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.slots.get index = .live obligation) : Share.Split obligation.residual :=
  (book.cellAt index).shares.reindex (congrArg (slotBalance sources) ((book.at_slot index).trans present))

def empty : Book sources (ResponsibilityState.empty (vocabulary sources)) := ⟨[],rfl⟩
end Book

inductive Row where
  | birth (index : Nat) (claim : Claim sources)
  | cross (index : Nat) (entry : AssignedFinancing.Joint.Entry sources)

namespace Row
variable {sources}
def event : Row sources → Family.Event sources
  | .birth _ claim => .birth claim
  | .cross _ entry => entry.event

def index : Row sources → Nat | .birth index _ => index | .cross index _ => index

def key (row : Row sources) := (row.index,row.event)

def native : Row sources → LifecycleEvent (vocabulary sources)
  | .birth index claim => .admitted index (admission sources claim)
  | .cross index entry => record sources index entry.boundary

theorem native_source (row : Row sources) : sourceEvent sources row.native = row.event := by
  cases row with
  | birth => rfl
  | cross index entry => exact record_source sources index entry.boundary
end Row

structure Update {state : ResponsibilityState (vocabulary sources)}
    (book : Book sources state) (edge : (process sources).Edge state) where
  after : Book sources edge.target
  row : Row sources
  exact_event : row.native = edge.lifecycleEvent

variable {state : ResponsibilityState (vocabulary sources)}
def update (book : Book sources state) (edge : (process sources).Edge state) : Update sources book edge := by
  cases edge with
  | admit claim =>
    exact ⟨⟨book.cells ++ [⟨.live (admission sources claim).toObligation,initial sources claim⟩],by
      simp only [List.map_append,List.map_cons,List.map_nil,book.slots_exact]
      rfl⟩,.birth state.slots.length claim,rfl⟩
  | cross index obligation present boundary =>
    let entry := AssignedFinancing.Joint.Entry.ofBoundary sources boundary (book.before index obligation present)
    let cell : Cell sources := ⟨(Boundary.disposition sources boundary).targetSlot,
      entry.result.final⟩
    refine ⟨⟨book.cells.set index.val cell,?_⟩,.cross index.val entry,?_⟩
    · change (book.cells.set index.val cell).map Cell.slot = state.slots.set index.val cell.slot
      rw [List.map_set,book.slots_exact]
    · exact (cross_record sources index obligation present boundary).symm
  | reopen _ _ _ impossible => exact impossible.elim

structure Flow {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (before : Book sources first) where
  after : Book sources last
  rows : List (Row sources)
  events_exact : rows.map Row.native = run.events

def fold {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (before : Book sources first) : Flow sources run before :=
  match run with
  | .nil => ⟨before,[],rfl⟩
  | .step prior edge =>
      let previous := fold prior before
      let next := update sources previous.after edge
      ⟨next.after,previous.rows ++ [next.row],by
        simp only [List.map_append,List.map_cons,List.map_nil,NativeResponsibilityProcess.Run.events,
          previous.events_exact,next.exact_event]⟩

theorem fold_concat {first middle last : ResponsibilityState (vocabulary sources)}
    (left : (process sources).Run first middle) (right : (process sources).Run middle last)
    (before : Book sources first) :
    (fold sources (left.concatRuns _ right) before).after =
        (fold sources right (fold sources left before).after).after ∧
    (fold sources (left.concatRuns _ right) before).rows =
        (fold sources left before).rows ++ (fold sources right (fold sources left before).after).rows := by
  induction right with
  | nil => simp only [NativeResponsibilityProcess.Run.concatRuns,fold,List.append_nil,and_self]
  | step prior edge ih =>
      dsimp only [NativeResponsibilityProcess.Run.concatRuns,fold]
      rw [ih.1,ih.2,List.append_assoc]
      exact ⟨rfl,rfl⟩

/-- Every initial tag and later tag is generated along the actual finite native
history from the empty financial state. No completed future table is supplied. -/
def generated (state : (process sources).GeneratedState) : Book sources state.current :=
  (fold sources state.generated Book.empty).after

theorem every_original_event_occurs_once {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (before : Book sources first) :
    (fold sources run before).rows.map Row.native = run.events :=
  (fold sources run before).events_exact

theorem every_original_slot_survives {first last : ResponsibilityState (vocabulary sources)}
    (run : (process sources).Run first last) (before : Book sources first) :
    (fold sources run before).after.cells.map Cell.slot = last.slots :=
  (fold sources run before).after.slots_exact

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.FinancingBook
