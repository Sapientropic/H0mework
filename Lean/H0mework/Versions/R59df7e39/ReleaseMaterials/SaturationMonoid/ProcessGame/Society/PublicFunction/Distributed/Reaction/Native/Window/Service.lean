import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Service
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat)

private def archiveIndex {source : Machine P G O T I} {index : Native.Slot source} {depth : Nat}
    {state : ResponsibilityLifecycle.ResponsibilityState (Native.V source)} : Native.Shape source index depth state → Option Nat
  | .live .. => none | .terminal first .. => some first
private def prefixIndex {source : Machine P G O T I} {index : Native.Slot source} {depth : Nat}
    (prior : Native.Prefix source index depth) := archiveIndex prior.shape
private theorem first_prefix (source : Machine P G O T I) (index : Native.Slot source) (depth : Nat) :
    Identity.firstService source depth index = prefixIndex (Native.historyAt source index depth) := by
  cases shape : (Native.historyAt source index depth).shape <;> simp only [Identity.firstService,prefixIndex,shape,archiveIndex]
theorem first_succ (source : Machine P G O T I) (index : Native.Slot source) (depth : Nat) :
    Identity.firstService source (depth+1) index =
      match Identity.firstService source depth index with
      | some earlier => some earlier
      | none => if Native.Paid source depth index then some depth else none := by
  have rule (prior : Native.Prefix source index depth) : prefixIndex (Native.advance source index depth prior) =
      match prefixIndex prior with
      | some earlier => some earlier
      | none => if Native.Paid source depth index then some depth else none := by
    rcases prior with ⟨state,run,shape⟩
    cases shape with
    | live unpaid slots => simp only [Native.advance];split_ifs <;> rfl
    | terminal first earlier paid slots => rfl
  rw [first_prefix,first_prefix,Native.historyAt]
  exact rule (Native.historyAt source index depth)

def update (index : Native.Slot bound.source) (depth : Nat) : Option Nat → Option Nat
  | some earlier => some earlier
  | none => if Native.Paid bound.source depth index then some depth else none
structure Row (index : Native.Slot bound.source) where
  private mk ::
  atStart : Option Nat
  atEnd : Option Nat
  start_exact : atStart = Identity.firstService bound.source start index
  end_exact : atEnd = Identity.firstService bound.source (start+span) index
structure Cell (index : Native.Slot bound.source) where
  private mk ::
  ordinal : Nat
  first : Option Nat
  saved : Option (Option Nat)
  bounded : ordinal ≤ start+span
  known : first = Identity.firstService bound.source ordinal index
  checkpoint : if ordinal < start then saved = none else saved = some (Identity.firstService bound.source start index)
def Cell.initial (index : Native.Slot bound.source) : Cell bound start span index :=
  ⟨0,none,if start = 0 then some none else none,Nat.zero_le _,rfl,by
    by_cases zero : start = 0
    · subst start;rfl
    · have positive : 0 < start := Nat.pos_of_ne_zero zero
      simp [positive,zero]⟩
variable {bound start span}
def Cell.rank {index : Native.Slot bound.source} (cell : Cell bound start span index) := start+span-cell.ordinal

def Cell.move {index : Native.Slot bound.source} (cell : Cell bound start span index) : Option (Nat × Cell bound start span index) :=
  if active : cell.ordinal < start+span then
    let next := update bound index cell.ordinal cell.first
    have next_exact : next = Identity.firstService bound.source (cell.ordinal+1) index := by
      rw [first_succ,←cell.known];rfl
    some (cell.ordinal,⟨cell.ordinal+1,next,if cell.ordinal+1 = start then some next else cell.saved,by omega,next_exact,by
      by_cases hit : cell.ordinal+1 = start
      · rw [if_pos hit]
        have late : ¬cell.ordinal+1 < start := by omega
        rw [if_neg late]
        exact congrArg some (by rw [next_exact,hit])
      · rw [if_neg hit]
        by_cases early : cell.ordinal+1 < start
        · have before : cell.ordinal < start := by omega
          simpa only [if_pos early,if_pos before] using cell.checkpoint
        · have before : ¬cell.ordinal < start := by omega
          simpa only [if_neg early,if_neg before] using cell.checkpoint⟩)
  else none

def Cell.finish {index : Native.Slot bound.source} (cell : Cell bound start span index) (ending : cell.ordinal = start+span) : Row bound start span index :=
  have late : ¬cell.ordinal < start := by omega
  have saved := cell.checkpoint
  have exact_saved : cell.saved = some (Identity.firstService bound.source start index) := by simpa only [if_neg late] using saved
  match actual : cell.saved with
  | none => False.elim (by rw [actual] at exact_saved;cases exact_saved)
  | some previous => ⟨previous,cell.first,by rw [actual] at exact_saved;exact Option.some.inj exact_saved,by rw [cell.known,ending]⟩
def Cell.completed {index : Native.Slot bound.source} (cell : Cell bound start span index) : Option (Row bound start span index) :=
  if ending : cell.ordinal = start+span then some (cell.finish ending) else none

theorem Cell.move_decreases {index : Native.Slot bound.source} {before after : Cell bound start span index} {event : Nat}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  dsimp only [Cell.move] at actual
  split at actual
  · rename_i active;cases actual;dsimp only [Cell.rank];omega
  · cases actual

theorem Cell.completed_iff_stopped {index : Native.Slot bound.source} (cell : Cell bound start span index) :
    cell.completed.isSome = true ↔ cell.move = none := by
  have bounded := cell.bounded
  by_cases ending : cell.ordinal = start+span
  · simp [Cell.completed,Cell.move,ending]
  · have active : cell.ordinal < start+span := by omega
    simp [Cell.completed,Cell.move,ending,active]
theorem Cell.stopped_iff_zero {index : Native.Slot bound.source} (cell : Cell bound start span index) :
    cell.move = none ↔ cell.rank = 0 := by
  have bounded := cell.bounded
  have finished : cell.completed.isSome = true ↔ cell.ordinal = start+span := by
    by_cases ending : cell.ordinal = start+span <;> simp [Cell.completed,ending]
  rw [←Cell.completed_iff_stopped cell,finished]
  dsimp only [Cell.rank];omega

variable (bound start span)
structure Job where
  index : Native.Slot bound.source
  state : Cell bound start span index
abbrev Entry := (index : Native.Slot bound.source) × Row bound start span index
def Job.initial (index : Native.Slot bound.source) : Job bound start span := ⟨index,Cell.initial bound start span index⟩
def Job.rank (job : Job bound start span) := job.state.rank+1
structure Completed where
  private mk ::
  items : List (Entry bound start span)
  exact_keys : items.map Sigma.fst = List.finRange bound.source.code.task.slots.length
  complete : Bool
  complete_actual : complete = items.all fun entry => entry.2.atEnd.isSome
structure Cursor where
  private mk ::
  remaining : List (Job bound start span)
  cached : List (Entry bound start span)
  coherent : cached.map Sigma.fst++remaining.map Job.index = List.finRange bound.source.code.task.slots.length
  complete : Bool
  complete_actual : complete = cached.all fun entry => entry.2.atEnd.isSome

def initial : Cursor bound start span := ⟨(List.finRange bound.source.code.task.slots.length).map (Job.initial bound start span),[],
  by simp [Function.comp_def,Job.initial],true,rfl⟩
def capacity (code : Code P G O T I) (start span : Nat) := ((List.finRange code.task.slots.length).map fun _ => start+span+1).sum
variable {bound start span}
def Cursor.rank (cursor : Cursor bound start span) := (cursor.remaining.map (Job.rank bound start span)).sum
inductive Event (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) where
  | read (index : Native.Slot bound.source) (depth : Nat)
  | emit (index : Native.Slot bound.source)
def Cursor.move (cursor : Cursor bound start span) : Option (Event bound × Cursor bound start span) :=
  match remaining_actual : cursor.remaining with
  | [] => none
  | job::rest => match done : job.state.completed with
    | some row => some (.emit job.index,⟨rest,cursor.cached++[⟨job.index,row⟩],by
        have coherent := cursor.coherent;rw [remaining_actual] at coherent
        simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append] using coherent,
        cursor.complete && row.atEnd.isSome,by
          rw [cursor.complete_actual];simp only [List.all_append,List.all_cons,List.all_nil,Bool.and_true]⟩)
    | none => match moved : job.state.move with
      | none => False.elim (by have complete := (Cell.completed_iff_stopped job.state).mpr moved;rw [done] at complete;cases complete)
      | some (depth,next) => some (.read job.index depth,⟨⟨job.index,next⟩::rest,cursor.cached,by
          have coherent := cursor.coherent;rw [remaining_actual] at coherent;simpa only [List.map_cons] using coherent,cursor.complete,cursor.complete_actual⟩)
def Cursor.completed (cursor : Cursor bound start span) : Option (Completed bound start span) :=
  match actual : cursor.remaining with
  | [] => some ⟨cursor.cached,by simpa only [actual,List.map_nil,List.append_nil] using cursor.coherent,cursor.complete,cursor.complete_actual⟩
  | _::_ => none

theorem initial_rank : (initial bound start span).rank = capacity bound.source.code start span := by
  simp [initial,Cursor.rank,Job.rank,Job.initial,Cell.initial,Cell.rank,capacity,Function.comp_def]
theorem Cursor.move_decreases {before after : Cursor bound start span} {event : Event bound}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  rcases before with ⟨remaining,cached,coherent,complete,complete_actual⟩
  cases remaining with
  | nil => cases actual
  | cons job rest =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i row done
      cases actual
      have zero := (Cell.stopped_iff_zero job.state).mp ((Cell.completed_iff_stopped _).mp (by rw [done];rfl))
      simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank,zero];omega
    · rename_i done
      split at actual
      · rename_i stopped
        have complete := (Cell.completed_iff_stopped job.state).mpr stopped;rw [done] at complete;cases complete
      · rename_i offset next moved
        cases actual
        have decrease := Cell.move_decreases moved
        simp only [Cursor.rank,List.map_cons,List.sum_cons,Job.rank];omega

theorem Cursor.completed_iff_stopped (cursor : Cursor bound start span) : cursor.completed.isSome = true ↔ cursor.move = none := by
  rcases cursor with ⟨remaining,cached,coherent,complete,complete_actual⟩
  cases remaining with
  | nil => simp [Cursor.completed,Cursor.move]
  | cons job rest =>
    simp only [Cursor.completed,Option.isSome_none,Bool.false_eq_true,false_iff]
    dsimp only [Cursor.move]
    split
    · simp
    · rename_i pending
      split
      · rename_i stopped
        have complete := (Cell.completed_iff_stopped job.state).mpr stopped;rw [pending] at complete;cases complete
      · simp

theorem Cursor.stopped_iff_zero (cursor : Cursor bound start span) : cursor.move = none ↔ cursor.rank = 0 := by
  have finished := cursor.completed_iff_stopped
  rcases cursor with ⟨remaining,cached,coherent,complete,complete_actual⟩
  cases remaining with
  | nil => simp [Cursor.move,Cursor.rank]
  | cons job rest =>
    have active : (⟨job::rest,cached,coherent,complete,complete_actual⟩ : Cursor bound start span).move ≠ none := by
      intro stopped;have impossible := finished.mpr stopped;simp [Cursor.completed] at impossible
    simp only [active,false_iff,Cursor.rank,List.map_cons,List.sum_cons,Job.rank];omega

inductive History : Cursor bound start span → Cursor bound start span → List (Event bound) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor bound start span) (capacity : Nat) where
  private mk ::
  endpoint : Cursor bound start span
  work : List (Event bound)
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank

def run : (capacity : Nat) → (before : Cursor bound start span) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩
theorem run_sufficient (before : Cursor bound start span) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega

theorem run_work_exact (before : Cursor bound start span) (available : Nat) :
    (run available before).work.length = min available before.rank := by
  have covered := (run available before).covered
  have conserved := (run available before).conservation
  rcases (run available before).exhausted with stopped | full
  · have zero := (Cursor.stopped_iff_zero _).mp stopped
    rw [zero] at conserved
    have same : (run available before).work.length = before.rank := by omega
    rw [same,Nat.min_eq_right (by omega)]
  · rw [full,Nat.min_eq_left (by omega)]

def lookup (index : Native.Slot bound.source) : (items : List (Entry bound start span)) → index ∈ items.map Sigma.fst → Row bound start span index
  | [],inside => False.elim (List.not_mem_nil inside)
  | head::tail,inside => if same : head.1 = index then same ▸ head.2 else
      lookup index tail (by simpa only [List.map_cons,List.mem_cons,eq_comm (a := index) (b := head.1),same,false_or] using inside)
def Completed.at (cache : Completed bound start span) (index : Native.Slot bound.source) : Row bound start span index :=
  lookup index cache.items (by rw [cache.exact_keys];exact List.mem_finRange _)
def Completed.startValues (cache : Completed bound start span) := cache.items.map fun entry => entry.2.atStart

theorem Completed.startValues_exact (cache : Completed bound start span) : cache.startValues =
    (List.finRange bound.source.code.task.slots.length).map (Identity.firstService bound.source start) := by
  rw [←cache.exact_keys,List.map_map]
  apply List.map_congr_left
  intro entry inside
  exact entry.2.start_exact
private theorem all_exact (items : List (Entry bound start span)) :
    (items.all fun entry => entry.2.atEnd.isSome) = (items.map Sigma.fst).all (fun index => (Identity.firstService bound.source (start+span) index).isSome) := by
  induction items with
  | nil => rfl
  | cons head rest later => simp only [List.all_cons,List.map_cons,head.2.end_exact,later]
theorem Completed.complete_exact (cache : Completed bound start span) : cache.complete =
    (List.finRange bound.source.code.task.slots.length).all (fun index => (Identity.firstService bound.source (start+span) index).isSome) := by
  rw [cache.complete_actual,all_exact,cache.exact_keys]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Service
