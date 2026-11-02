import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Selection
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.CatalogueSource
variable {A : Type}
def wordRows (alphabet : List A) : Nat → List (List A)
  | 0 => [[]]
  | depth+1 => [] :: alphabet.flatMap (fun head => (wordRows alphabet depth).map (List.cons head))
structure Input (A : Type) where
  menu : List A
  work : A
  depth : Nat
  counts : List Nat
  pendingLength : Nat
inductive Job (A : Type) where
  | counts (remaining : List Nat)
  | word (production stem : List A) (depth : Nat)
  | branches (production stem : List A) (depth : Nat) (remaining : List A)
def Job.rows (input : Input A) : Job A → List (List A)
  | .counts remaining => remaining.flatMap fun count => (wordRows input.menu input.depth).map (List.replicate count input.work++·)
  | .word production stem depth => (wordRows input.menu depth).map (fun tail => production++stem++tail)
  | .branches production stem depth remaining => remaining.flatMap fun head =>
      (wordRows input.menu depth).map (fun tail => production++stem++(head::tail))
def wordCost (menuLength : Nat) : Nat → Nat
  | 0 => 1
  | depth+1 => 2+menuLength*(1+wordCost menuLength depth)
def Job.cost (input : Input A) : Job A → Nat
  | .counts remaining => 1+remaining.length*(1+wordCost input.menu.length input.depth)
  | .word _ _ depth => wordCost input.menu.length depth
  | .branches _ _ depth remaining => 1+remaining.length*(1+wordCost input.menu.length depth)
def required (pendingLength : Nat) (rows : List (List A)) :=
  1+rows.length+pendingLength+(rows.map fun row => 3*row.length+pendingLength).sum
def charge (pendingLength : Nat) (row : List A) := 1+pendingLength+3*row.length
theorem required_append (pendingLength : Nat) (rows : List (List A)) (row : List A) :
    required pendingLength (rows++[row]) = required pendingLength rows+charge pendingLength row := by
  simp [required,charge,List.map_append,List.sum_append]
  omega
structure Cursor (A : Type) where
  jobs : List (Job A)
  rows : List (List A)
  units : Nat
inductive Event (A : Type) where
  | counted (count : Nat)
  | emitted (row : List A)
  | prefixed (head : A)
  | closed
def Event.rows : Event A → List (List A)
  | .emitted row => [row]
  | _ => []
def initial (input : Input A) : Cursor A := ⟨[.counts input.counts],[],1+input.pendingLength⟩
def Cursor.meaning (input : Input A) (cursor : Cursor A) := cursor.rows++cursor.jobs.flatMap (Job.rows input)
def Cursor.rank (input : Input A) (cursor : Cursor A) := (cursor.jobs.map (Job.cost input)).sum
def Cursor.move (input : Input A) (cursor : Cursor A) : Option (Event A × Cursor A) :=
  match cursor.jobs with
  | [] => none
  | .counts []::rest => some (.closed,⟨rest,cursor.rows,cursor.units⟩)
  | .counts (count::remaining)::rest => some (.counted count,
      ⟨.word (List.replicate count input.work) [] input.depth::.counts remaining::rest,cursor.rows,cursor.units⟩)
  | .word production stem 0::rest =>
      let row := production++stem
      some (.emitted row,⟨rest,cursor.rows++[row],cursor.units+charge input.pendingLength row⟩)
  | .word production stem (depth+1)::rest =>
      let row := production++stem
      some (.emitted row,⟨.branches production stem depth input.menu::rest,cursor.rows++[row],cursor.units+charge input.pendingLength row⟩)
  | .branches _ _ _ []::rest => some (.closed,⟨rest,cursor.rows,cursor.units⟩)
  | .branches production stem depth (head::remaining)::rest => some (.prefixed head,
      ⟨.word production (stem++[head]) depth::.branches production stem depth remaining::rest,cursor.rows,cursor.units⟩)
variable {input : Input A}
theorem Cursor.move_meaning {before after : Cursor A} {event : Event A}
    (actual : before.move input = some (event,after)) : after.meaning input = before.meaning input := by
  rcases before with ⟨jobs,rows,units⟩
  cases jobs with
  | nil => cases actual
  | cons job rest =>
    cases job with
    | counts remaining => cases remaining <;> cases actual <;> simp [Cursor.meaning,Job.rows,List.append_assoc]
    | word production stem depth =>
      cases depth <;> cases actual <;>
        simp [Cursor.meaning,Job.rows,wordRows,List.map_flatMap,List.map_map,Function.comp_def,List.append_assoc]
    | branches production stem depth remaining =>
      cases remaining <;> cases actual <;>
        simp [Cursor.meaning,Job.rows,List.append_assoc]
theorem Cursor.move_rows {before after : Cursor A} {event : Event A}
    (actual : before.move input = some (event,after)) : after.rows = before.rows++event.rows := by
  rcases before with ⟨jobs,rows,units⟩
  cases jobs with
  | nil => cases actual
  | cons job rest =>
    cases job with
    | counts remaining => cases remaining <;> cases actual <;> simp [Event.rows]
    | word production stem depth => cases depth <;> cases actual <;> rfl
    | branches production stem depth remaining => cases remaining <;> cases actual <;> simp [Event.rows]
theorem Cursor.move_accounting {before after : Cursor A} {event : Event A}
    (actual : before.move input = some (event,after))
    (paid : before.units = required input.pendingLength before.rows) :
    after.units = required input.pendingLength after.rows := by
  rcases before with ⟨jobs,rows,units⟩
  cases jobs with
  | nil => cases actual
  | cons job rest =>
    cases job with
    | counts remaining => cases remaining <;> cases actual <;> exact paid
    | word production stem depth => cases depth <;> cases actual <;> simpa only [required_append] using congrArg (·+charge input.pendingLength (production++stem)) paid
    | branches production stem depth remaining => cases remaining <;> cases actual <;> exact paid
theorem Cursor.move_decreases {before after : Cursor A} {event : Event A}
    (actual : before.move input = some (event,after)) : after.rank input+1 = before.rank input := by
  rcases before with ⟨jobs,rows,units⟩
  cases jobs with
  | nil => cases actual
  | cons job rest =>
    cases job with
    | counts remaining =>
      cases remaining <;> cases actual <;> simp [Cursor.rank,Job.cost,Nat.add_mul,Nat.mul_add] <;> omega
    | word production stem depth =>
      cases depth <;> cases actual <;> simp [Cursor.rank,Job.cost,wordCost] <;> omega
    | branches production stem depth remaining =>
      cases remaining <;> cases actual <;> simp [Cursor.rank,Job.cost,Nat.add_mul,Nat.mul_add] <;> omega
theorem Cursor.stopped (current : Cursor A) : current.move input = none ↔ current.jobs = [] := by
  rcases current with ⟨jobs,rows,units⟩
  cases jobs with
  | nil => simp [Cursor.move]
  | cons job rest => cases job with
    | counts remaining => cases remaining <;> simp [Cursor.move]
    | word production stem depth => cases depth <;> simp [Cursor.move]
    | branches production stem depth remaining => cases remaining <;> simp [Cursor.move]
inductive History (input : Input A) : Cursor A → Cursor A → List (Event A) → Prop
  | nil (before) : History input before before []
  | step {before middle after event work} (actual : before.move input = some (event,middle))
      (later : History input middle after work) : History input before after (event::work)
theorem History.append : {before middle after : Cursor A} → {left right : List (Event A)} →
    History input before middle left → History input middle after right → History input before after (left++right)
  | _,_,_,_,_,.nil _,later => later
  | _,_,_,_,_,.step actual past,later => .step actual (History.append past later)
theorem History.meaning {before after : Cursor A} {work : List (Event A)} (history : History input before after work) :
    after.meaning input = before.meaning input := by
  induction history with
  | nil => rfl
  | step actual _ ih => exact ih.trans (Cursor.move_meaning actual)
theorem History.rows {before after : Cursor A} {work : List (Event A)} (history : History input before after work) :
    after.rows = before.rows++work.flatMap Event.rows := by
  induction history with
  | nil => simp
  | step actual _ ih => rw [ih,Cursor.move_rows actual,List.flatMap_cons,List.append_assoc]
theorem History.accounting {before after : Cursor A} {work : List (Event A)} (history : History input before after work)
    (paid : before.units = required input.pendingLength before.rows) : after.units = required input.pendingLength after.rows := by
  induction history with
  | nil => exact paid
  | step actual _ ih => exact ih (Cursor.move_accounting actual paid)
theorem History.conservation {before after : Cursor A} {work : List (Event A)} (history : History input before after work) :
    after.rank input+work.length = before.rank input := by
  induction history with
  | nil => simp
  | step actual _ ih => have smaller := Cursor.move_decreases actual;simp only [List.length_cons];omega
structure Run (input : Input A) (before : Cursor A) where
  endpoint : Cursor A
  work : List (Event A)
  history : History input before endpoint work
  stopped : endpoint.move input = none
def run (input : Input A) (before : Cursor A) : Run input before :=
  match actual : before.move input with
  | none => ⟨before,[],.nil _,actual⟩
  | some (event,next) =>
      let later := run input next
      ⟨later.endpoint,event::later.work,.step actual later.history,later.stopped⟩
termination_by before.rank input
decreasing_by have smaller := Cursor.move_decreases actual;omega
structure Execution (input : Input A) where
  private mk ::
  endpoint : Cursor A
  work : List (Event A)
  history : History input (initial input) endpoint work
  stopped : endpoint.move input = none
def execute (input : Input A) : Execution input :=
  let made := run input (initial input)
  ⟨made.endpoint,made.work,made.history,made.stopped⟩
def Execution.rows (made : Execution input) := made.endpoint.rows
def Execution.units (made : Execution input) := made.endpoint.units
theorem Execution.rows_exact (made : Execution input) : made.rows = (input.counts.flatMap fun count =>
    (wordRows input.menu input.depth).map (List.replicate count input.work++·)) := by
  have same := made.history.meaning
  have empty := (Cursor.stopped made.endpoint).mp made.stopped
  simpa only [Execution.rows,Cursor.meaning,initial,empty,List.flatMap_nil,List.append_nil,List.flatMap_cons,Job.rows,List.nil_append] using same
theorem Execution.units_exact (made : Execution input) : made.units = required input.pendingLength made.rows := made.history.accounting rfl
theorem Execution.emitted_rows (made : Execution input) : made.work.flatMap Event.rows = made.rows := by
  have same := made.history.rows
  simpa only [initial,List.nil_append,Execution.rows] using same.symm
theorem Execution.units_positive (made : Execution input) : 0 < made.units := by
  rw [made.units_exact]
  unfold required;omega
theorem Execution.work_length (made : Execution input) : made.work.length = (initial input).rank input := by
  have paid := made.history.conservation
  have empty := (Cursor.stopped made.endpoint).mp made.stopped
  simpa only [Cursor.rank,empty,List.map_nil,List.sum_nil,Nat.zero_add] using paid
private theorem History.unique_complete {before first second : Cursor A} {left right : List (Event A)}
    (a : History input before first left) (b : History input before second right) (doneA : first.move input = none) (doneB : second.move input = none) :
    first = second ∧ left = right := by
  induction a generalizing second right with
  | nil => cases b with
    | nil => exact ⟨rfl,rfl⟩
    | step actual later => rw [doneA] at actual;cases actual
  | step actual later ih => cases b with
    | nil => rw [doneB] at actual;cases actual
    | step other rest =>
      have same := Option.some.inj (actual.symm.trans other);cases same
      obtain ⟨endpoint,work⟩ := ih rest doneA doneB
      exact ⟨endpoint,by rw [work]⟩
theorem Execution.unique (first second : Execution input) : first = second := by
  obtain ⟨endpoint,work⟩ := History.unique_complete first.history second.history first.stopped second.stopped
  cases first;cases second;cases endpoint;cases work;rfl
structure Session (input : Input A) where
  private mk ::
  current : Cursor A
  work : List (Event A)
  history : History input (initial input) current work
def Session.initial (input : Input A) : Session input := ⟨CatalogueSource.initial input,[],.nil _⟩
def Session.rank (session : Session input) := session.current.rank input
def Session.move (session : Session input) : Option (Event A × Session input) :=
  match actual : session.current.move input with
  | none => none
  | some (event,next) => some (event,⟨next,session.work++[event],session.history.append (.step actual (.nil _))⟩)
def Session.completed (session : Session input) : Option (Execution input) :=
  match stopped : session.current.jobs with
  | [] => some ⟨session.current,session.work,session.history,(Cursor.stopped session.current).mpr stopped⟩
  | _::_ => none
theorem Session.move_appends {before after : Session input} {event : Event A} (actual : before.move = some (event,after)) :
    after.work = before.work++[event] := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · cases actual;rfl
theorem Session.move_decreases {before after : Session input} {event : Event A} (actual : before.move = some (event,after)) :
    after.rank+1 = before.rank := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · rename_i emitted next moved
    cases actual;exact Cursor.move_decreases moved
theorem Session.completed_work {session : Session input} {made : Execution input} (actual : session.completed = some made) :
    made.work = session.work := by
  dsimp only [Session.completed] at actual
  split at actual
  · cases actual;rfl
  · cases actual
theorem Session.completed_iff_stopped (session : Session input) : session.completed.isSome = true ↔ session.move = none := by
  have stopped := Cursor.stopped (input := input) session.current
  unfold Session.completed Session.move
  split <;> split <;> simp_all
theorem Session.conservation (session : Session input) : session.rank+session.work.length = (CatalogueSource.initial input).rank input := session.history.conservation

theorem Session.initial_rank : (Session.initial input).rank = (execute input).work.length := by
  rw [Execution.work_length];rfl

open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
theorem wordRows_is_original (alphabet : List (Action old)) (depth : Nat) : wordRows alphabet depth = words alphabet depth := by
  induction depth with
  | zero => rfl
  | succ depth ih => simp only [wordRows,words,ih]
def source (stage : Recovery.Cursor old oldDepth word) (actor : P) (original : List (Action old)) : Input (Action old) :=
  ⟨Search.menu stage.model actor,Search.work stage.model actor original,stage.model.source.code.actionLimit,
    List.range (Search.limit stage.model stage.before actor original+1),original.length⟩
theorem source_rows (stage : Recovery.Cursor old oldDepth word) (actor : P) (original : List (Action old))
    (made : Execution (source stage actor original)) : made.rows = Search.repairs stage.model stage.before actor original := by
  rw [made.rows_exact]
  simp only [source,wordRows_is_original,Search.repairs]
theorem source_units (stage : Recovery.Cursor old oldDepth word) (actor : P) (original : List (Action old))
    (made : Execution (source stage actor original)) : made.units = Metering.comparisonUnits original made.rows := made.units_exact
structure Archive (old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (oldDepth : Nat) (word : List (Action old)) where
  stage : Recovery.Cursor old oldDepth word
  actor : P
  original : List (Action old)
  execution : Execution (source stage actor original)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.CatalogueSource
