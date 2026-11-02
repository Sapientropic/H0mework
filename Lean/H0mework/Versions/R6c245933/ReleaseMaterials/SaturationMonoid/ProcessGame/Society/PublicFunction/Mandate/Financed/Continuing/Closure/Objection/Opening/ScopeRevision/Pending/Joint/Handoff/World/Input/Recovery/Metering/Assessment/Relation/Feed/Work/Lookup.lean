import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Comparison

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Lookup
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle Followup
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {code : Code Bool Good Mandate.Source.Port (Mandate.State Bool Unit) Unit}

private def sameRule (first second : Rule code) : Prop :=
  (∀ key, key ∈ code.keys → first.work.val key (code.key_mem key) = second.work.val key (code.key_mem key)) ∧
  (∀ key, key ∈ code.keys → (first.events key (code.key_mem key)).val = (second.events key (code.key_mem key)).val)

private instance (first second : Rule code) : Decidable (sameRule first second) := by
  unfold sameRule
  have work : Decidable (∀ key ∈ code.keys,
    first.work.val key (code.key_mem key) = second.work.val key (code.key_mem key)) := inferInstance
  have events : Decidable (∀ key ∈ code.keys,
    (first.events key (code.key_mem key)).val = (second.events key (code.key_mem key)).val) := inferInstance
  exact instDecidableAnd

private theorem sameRule_iff (first second : Rule code) : sameRule first second ↔ first = second := by
  constructor
  · rintro ⟨work,events⟩
    have hw : first.work = second.work := Subtype.ext (funext fun key => funext fun member => work key member)
    have he : first.events = second.events := funext fun key => funext fun member => Subtype.ext (events key member)
    cases first
    cases second
    cases hw
    cases he
    rfl
  · intro same
    subst second
    exact ⟨fun _ _ => rfl,fun _ _ => rfl⟩

private instance : DecidableEq (Rule code) :=
  fun first second => decidable_of_iff (sameRule first second) (sameRule_iff first second)

private instance {fuel : Nat} : DecidableEq (Whole.Program code fuel) :=
  fun first second => decidable_of_iff (first.controls = second.controls) (by
    constructor
    · intro same
      cases first
      cases second
      cases same
      rfl
    · exact congrArg Whole.Program.controls)

private def rectIndex {A B C : Type} (rows : List A) (pool : List B) (make : A → B → C)
    (row : Fin rows.length) (program : Fin pool.length) :
    Fin (rows.flatMap fun item => pool.map (make item)).length :=
  match rows with
  | [] => Fin.elim0 row
  | head::tail => Fin.cases
      ⟨program.val,by simp only [List.flatMap_cons,List.length_append,List.length_map];omega⟩
      (fun next =>
        let rest := rectIndex tail pool make next program
        ⟨pool.length+rest.val,by simp only [List.flatMap_cons,List.length_append,List.length_map];omega⟩) row

private theorem rectIndex_value {A B C : Type} (rows : List A) (pool : List B) (make : A → B → C)
    (row : Fin rows.length) (program : Fin pool.length) :
    (rows.flatMap fun item => pool.map (make item))[rectIndex rows pool make row program] =
      make rows[row] pool[program] := by
  induction rows with
  | nil => exact Fin.elim0 row
  | cons head tail ih =>
      cases row using Fin.cases with
      | zero => simp [rectIndex,program.isLt]
      | succ next =>
          have outside : ¬ pool.length + (rectIndex tail pool make next program).val < pool.length := by omega
          simpa [rectIndex,List.getElem_append,outside] using ih next

variable {epoch : Epoch}
  {model : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit)}
  {domain : List (Continuation.Cursor model.source.code)} {original : Rule model.source.code}
  {requested : List (List Action)} {inventory : Inventory epoch}
  {tariff : Restoration.Tariff (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
    (Technology := Unit) (Instrument := Unit)}

def programPosition (program : Whole.Program model.source.code (horizon domain)) :
    Fin (programs model domain).length :=
  ⟨(programs model domain).idxOf program,
    List.idxOf_lt_length_iff.mpr (every_bounded_program_is_source_generated _ _ _)⟩

theorem programPosition_value (program : Whole.Program model.source.code (horizon domain)) :
    (programs model domain)[programPosition program] = program :=
  List.getElem_idxOf (programPosition (model := model) (domain := domain) program).isLt

private def storedEntry (cells : List (Sigma fun job : Job model domain => Cell original requested inventory tariff job))
    (directory : cells.map Sigma.fst = jobs model domain)
    (index : Fin (jobs model domain).length) : Cell original requested inventory tariff (jobs model domain)[index] :=
  let position : Fin cells.length := ⟨index.val,by
    have lengths := congrArg List.length directory
    simp only [List.length_map] at lengths
    omega⟩
  let entry := cells[position.val]
  have same : entry.1 = (jobs model domain)[index] := by
    have selected := congrArg (fun entries => entries[index.val]?) directory
    rw [List.getElem?_map,List.getElem?_eq_getElem position.isLt,
      List.getElem?_eq_getElem index.isLt] at selected
    exact Option.some.inj (by simpa only [Option.map_some,entry,Fin.getElem_fin] using selected)
  same ▸ entry.2

/-- Read the same original position from eager or source-indexed storage. -/
def entryAt (batch : Batch model domain original requested inventory tariff)
    (index : Fin (jobs model domain).length) : Cell original requested inventory tariff (jobs model domain)[index] :=
  match batch.storage with
  | .eager cells directory => storedEntry cells directory index
  | .quiet _ make => make (jobs model domain)[index]

def cell (batch : Batch model domain original requested inventory tariff)
    (row : Fin (Selection.rows model domain).length)
    (program : Whole.Program model.source.code (horizon domain)) :
    Cell original requested inventory tariff ⟨(Selection.rows model domain)[row],program⟩ :=
  match batch.storage with
  | .quiet _ make => make ⟨(Selection.rows model domain)[row],program⟩
  | .eager _ _ =>
    let column := programPosition (model := model) (domain := domain) program
    let position := rectIndex (Selection.rows model domain) (programs model domain)
      (fun row program => (⟨row,program⟩ : Job model domain)) row column
    have same : (jobs model domain)[position] = (⟨(Selection.rows model domain)[row],program⟩ : Job model domain) := by
      change ((Selection.rows model domain).flatMap fun item =>
        (programs model domain).map fun program => (⟨item,program⟩ : Job model domain))[position] = _
      rw [rectIndex_value,programPosition_value]
    same ▸ entryAt batch position

def rowComparison (batch : Batch model domain original requested inventory tariff)
    (previous program : Whole.Program model.source.code (horizon domain))
    (index : Fin (Feed.Selection.rows model domain).length) : Bool :=
  Cell.compare inventory model domain original requested tariff (Feed.Selection.rows model domain)[index]
    program previous (cell batch index program) (cell batch index previous)

theorem rowComparison_iff (batch : Batch model domain original requested inventory tariff)
    (previous program : Whole.Program model.source.code (horizon domain))
    (index : Fin (Feed.Selection.rows model domain).length) :
    rowComparison batch previous program index = true ↔
      Feed.Selection.holds inventory model domain original tariff requested previous program
        (Feed.Selection.rows model domain)[index] :=
  Cell.compare_is_the_complete_original_history_relation inventory model domain original requested tariff
    (Feed.Selection.rows model domain)[index] program previous (cell batch index program) (cell batch index previous)

inductive Verdict (previous program : Whole.Program model.source.code (horizon domain)) where
  | accepted (kept : Feed.Selection.acceptable inventory model domain original tariff requested previous program)
  | rejected (fault : Feed.Selection.Rejection inventory model domain original tariff requested previous program)

/-- The original relation is decided exclusively from the supplied cached cells. -/
def inspectEager (batch : Batch model domain original requested inventory tariff)
    (previous program : Whole.Program model.source.code (horizon domain)) :
    Verdict (inventory := inventory) (original := original) (requested := requested) (tariff := tariff) previous program :=
  match Distributed.inspect (fun index : Fin (Feed.Selection.rows model domain).length =>
      rowComparison batch previous program index = true) (List.finRange (Feed.Selection.rows model domain).length) with
  | .accepted kept => .accepted (by
      intro row generated
      obtain ⟨index,bounded,same⟩ := List.mem_iff_getElem.mp generated
      subst row
      exact (rowComparison_iff batch previous program ⟨index,bounded⟩).mp
        (kept ⟨index,bounded⟩ (List.mem_finRange _)))
  | .rejected index _ broken => .rejected
      ⟨(Feed.Selection.rows model domain)[index],by
        simpa only [Fin.getElem_fin] using List.getElem_mem index.isLt,
        fun accepted => broken ((rowComparison_iff batch previous program index).mpr accepted)⟩

private inductive QuietResult
    (previous program : Whole.Program model.source.code (horizon domain))
    (worlds : List (Replanning.Point model domain)) where
  | accepted (kept : ∀ world ∈ worlds,
      Feed.Selection.holds inventory model domain original tariff requested previous program
        (Feed.Selection.silentRow model domain world))
  | rejected (fault : Feed.Selection.Rejection inventory model domain original tariff requested previous program)

private def quietScan
    (make : (job : Job model domain) → Cell original requested inventory tariff job)
    (previous program : Whole.Program model.source.code (horizon domain)) :
    (worlds : List (Replanning.Point model domain)) →
      QuietResult (inventory := inventory) (original := original) (requested := requested) (tariff := tariff)
        previous program worlds
  | [] => .accepted (by simp)
  | world::later =>
    let row := Feed.Selection.silentRow model domain world
    let current := make ⟨row,program⟩
    let old := make ⟨row,previous⟩
    if checked : Cell.compare inventory model domain original requested tariff row program previous current old = true then
      match quietScan make previous program later with
      | .rejected fault => .rejected fault
      | .accepted all => .accepted (by
          intro point member
          rcases List.mem_cons.mp member with same | after
          · subst point
            exact (Cell.compare_is_the_complete_original_history_relation inventory model domain original requested
              tariff row program previous current old).mp checked
          · exact all point after)
    else .rejected ⟨row,Selection.Restoration.every_row_is_generated _ _ _,fun valid =>
      checked ((Cell.compare_is_the_complete_original_history_relation inventory model domain original requested
        tariff row program previous current old).mpr valid)⟩

/-- The quiet proof identifies complete candidate occurrences, including their
World windows and reports. Failure still names a generated original row. -/
def inspect (batch : Batch model domain original requested inventory tariff)
    (previous program : Whole.Program model.source.code (horizon domain)) :
    Verdict (inventory := inventory) (original := original) (requested := requested) (tariff := tariff) previous program :=
  match batch.storage with
  | .eager _ _ => inspectEager batch previous program
  | .quiet checked make =>
    match quietScan make previous program (Replanning.points model domain) with
    | .rejected fault => .rejected fault
    | .accepted kept => .accepted (by
        intro row _
        exact (Feed.Selection.quiet_holds model original program checked domain inventory tariff requested previous row).mpr
          (kept row.world (Replanning.every_point_is_source_generated _ _ _)))

def Verdict.passed {previous program : Whole.Program model.source.code (horizon domain)} :
    Verdict (inventory := inventory) (original := original) (requested := requested) (tariff := tariff) previous program → Bool
  | .accepted _ => true
  | .rejected _ => false

def check (batch : Batch model domain original requested inventory tariff)
    (previous program : Whole.Program model.source.code (horizon domain)) : Bool :=
  (inspect batch previous program).passed

theorem check_iff (batch : Batch model domain original requested inventory tariff)
    (previous program : Whole.Program model.source.code (horizon domain)) :
    check batch previous program = true ↔
      Feed.Selection.acceptable inventory model domain original tariff requested previous program := by
  unfold check
  generalize actual : inspect batch previous program = decision
  cases decision with
  | accepted kept => exact ⟨fun _ => kept,fun _ => rfl⟩
  | rejected fault =>
      constructor
      · intro impossible;cases impossible
      · intro accepted
        exact False.elim (fault.broken (accepted fault.row fault.generated))

def rejectionFrom (batch : Batch model domain original requested inventory tariff)
    (previous program : Whole.Program model.source.code (horizon domain))
    (failed : check batch previous program ≠ true) :
    Feed.Selection.Rejection inventory model domain original tariff requested previous program :=
  match actual : inspect batch previous program with
  | .accepted _ => False.elim (failed (by simp only [check,actual,Verdict.passed]))
  | .rejected fault => fault

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Lookup
