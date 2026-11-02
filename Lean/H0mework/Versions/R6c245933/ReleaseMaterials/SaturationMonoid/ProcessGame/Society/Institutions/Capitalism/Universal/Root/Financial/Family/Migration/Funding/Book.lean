import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding
open ResponsibilityLifecycle FinancingBook
variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

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

/-- Replay only the already-generated original history. The selected shares
mean funded lineage, not a promise of future controlled ownership. -/
def generated (state : (process sources).GeneratedState) : Book sources state.current :=
  (fold sources state.generated Book.empty).after

structure Link where
  private mk ::
  index : Nat
  entry : AssignedFinancing.Joint.Entry sources
  acquisition : Acquisition sources entry.boundary

namespace Link
variable {sources} (link : Link sources)
def native := record sources link.index link.entry.boundary
end Link

def atRow : Row sources → List (Link sources)
  | .birth _ _ => []
  | .cross index entry => (acquisitions sources entry.boundary).map fun acquisition => ⟨index,entry,acquisition⟩

def links (rows : List (Row sources)) := rows.flatMap (atRow sources)

theorem every_link_is_its_original_actual_event (rows : List (Row sources)) (link : Link sources)
    (member : link ∈ links sources rows) : link.native ∈ rows.map Row.native := by
  obtain ⟨row,inside,generated⟩ := List.mem_flatMap.mp member
  cases row with
  | birth index claim => cases generated
  | cross index entry =>
    obtain ⟨acquisition,_,same⟩ := List.mem_map.mp generated
    subst link
    exact List.mem_map.mpr ⟨.cross index entry,inside,rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.Migration.Funding
