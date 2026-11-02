import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Fold
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) (start span : Nat)

deriving instance DecidableEq for Settlement.Material

def indices : Settlement.Material P G → List Nat
  | .debit .. | .credit .. | .admissibility => List.range span
  | _ => []
def delta (metric : Settlement.Material P G) (offset : Nat) : ℚ :=
  let actual := bound.source.actualExecution (start+offset)
  match metric with
  | .debit party good => bound.source.code.law.totalDebit actual.interpreted.items party good
  | .credit party good => -bound.source.code.law.totalCredit actual.interpreted.items party good
  | _ => 0
def legalAt (metric : Settlement.Material P G) (offset : Nat) : Bool := match metric with
  | .admissibility => let actual := bound.source.actualExecution (start+offset)
      decide (Open.Legal bound.source.code.law actual.before actual.submitted)
  | _ => true

private theorem sum_neg {α : Type} (xs : List α) (f : α → ℚ) : (xs.map fun x => -f x).sum = -(xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs later => simp [later,neg_add_rev,add_comm]

structure Row (metric : Settlement.Material P G) where
  private mk ::
  value : ℚ
  lawful : Bool
  exact_value : value = Window.material bound start span metric
  exact_lawful : metric = .admissibility → lawful = Window.legal bound start span
structure Cell (metric : Settlement.Material P G) where
  private mk ::
  remaining : List Nat
  amount : ℚ
  lawful : Bool
  balance : amount+(remaining.map (delta bound start metric)).sum = ((indices span metric).map (delta bound start metric)).sum
  legality : (lawful && remaining.all (legalAt bound start metric)) = (indices span metric).all (legalAt bound start metric)

def Cell.initial (metric : Settlement.Material P G) : Cell bound start span metric :=
  ⟨indices span metric,0,true,by simp,by simp⟩
variable {bound start span}
def Cell.rank {metric : Settlement.Material P G} (cell : Cell bound start span metric) := cell.remaining.length

def Cell.move {metric : Settlement.Material P G} (cell : Cell bound start span metric) : Option (Nat × Cell bound start span metric) :=
  match actual : cell.remaining with
  | [] => none
  | offset::rest => some (offset,⟨rest,cell.amount+delta bound start metric offset,cell.lawful && legalAt bound start metric offset,by
      have same := cell.balance;rw [actual] at same
      simpa only [List.map_cons,List.sum_cons,add_assoc] using same,by
      have same := cell.legality;rw [actual] at same
      simpa only [List.all_cons,Bool.and_assoc] using same⟩)

def Cell.completed {metric : Settlement.Material P G} (cell : Cell bound start span metric) : Option (Row bound start span metric) :=
  match actual : cell.remaining with
  | _::_ => none
  | [] =>
      let amount := match metric with
        | .debit .. | .credit .. => cell.amount
        | .inventory party good => -(Window.terminal bound start span).stock party good
        | .clock => (Window.terminal bound start span).clock
        | .admissibility => if cell.lawful then 0 else 1
      some ⟨amount,cell.lawful,by
        have sum := cell.balance;rw [actual] at sum
        simp only [List.map_nil,List.sum_nil,add_zero] at sum
        have legal := cell.legality;rw [actual] at legal
        simp only [List.all_nil,Bool.and_true] at legal
        cases metric with
        | debit party good => exact sum
        | credit party good =>
            change cell.amount = -((List.range span).map fun offset => bound.source.code.law.totalCredit (bound.source.actualExecution (start+offset)).interpreted.items party good).sum
            rw [←sum_neg]
            exact sum
        | inventory party good => rfl
        | clock => rfl
        | admissibility =>
            have same : cell.lawful = Window.legal bound start span := legal
            exact congrArg (fun flag => if flag then (0:ℚ) else 1) same,by
        intro same;subst metric
        have legal := cell.legality;rw [actual] at legal
        simp only [List.all_nil,Bool.and_true] at legal
        exact legal⟩

theorem Cell.move_decreases {metric : Settlement.Material P G} {before after : Cell bound start span metric} {event : Nat}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  rcases before with ⟨remaining,amount,lawful,balance,legality⟩
  cases remaining with
  | nil => cases actual
  | cons offset rest => cases actual;rfl

theorem Cell.completed_iff_stopped {metric : Settlement.Material P G} (cell : Cell bound start span metric) :
    cell.completed.isSome = true ↔ cell.move = none := by
  rcases cell with ⟨remaining,amount,lawful,balance,legality⟩
  cases remaining <;> simp [Cell.completed,Cell.move]
theorem Cell.stopped_iff_zero {metric : Settlement.Material P G} (cell : Cell bound start span metric) :
    cell.move = none ↔ cell.rank = 0 := by
  rcases cell with ⟨remaining,amount,lawful,balance,legality⟩
  cases remaining <;> simp [Cell.move,Cell.rank]

variable (bound start span)
structure Job where
  metric : Settlement.Material P G
  state : Cell bound start span metric
abbrev Entry := (metric : Settlement.Material P G) × Row bound start span metric
def Job.initial (metric : Settlement.Material P G) : Job bound start span := ⟨metric,Cell.initial bound start span metric⟩
def Job.rank (job : Job bound start span) := job.state.rank+1
structure Completed where
  private mk ::
  items : List (Entry bound start span)
  exact_keys : items.map Sigma.fst = Settlement.materials bound.source.code
structure Cursor where
  private mk ::
  remaining : List (Job bound start span)
  cached : List (Entry bound start span)
  coherent : cached.map Sigma.fst++remaining.map Job.metric = Settlement.materials bound.source.code

def initial : Cursor bound start span := ⟨(Settlement.materials bound.source.code).map (Job.initial bound start span),[],by simp [Function.comp_def,Job.initial]⟩
def capacity (code : Code P G O T I) (span : Nat) := ((Settlement.materials code).map fun metric => (indices span metric).length+1).sum
variable {bound start span}
def Cursor.rank (cursor : Cursor bound start span) := (cursor.remaining.map (Job.rank bound start span)).sum
inductive Event (bound : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)) where
  | read (metric : Settlement.Material P G) (offset : Nat)
  | emit (metric : Settlement.Material P G)
def Cursor.move (cursor : Cursor bound start span) : Option (Event bound × Cursor bound start span) :=
  match remaining_actual : cursor.remaining with
  | [] => none
  | job::rest => match done : job.state.completed with
    | some row => some (.emit job.metric,⟨rest,cursor.cached++[⟨job.metric,row⟩],by
        have coherent := cursor.coherent;rw [remaining_actual] at coherent
        simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append] using coherent⟩)
    | none => match moved : job.state.move with
      | none => False.elim (by have complete := (Cell.completed_iff_stopped job.state).mpr moved;rw [done] at complete;cases complete)
      | some (offset,next) => some (.read job.metric offset,⟨⟨job.metric,next⟩::rest,cursor.cached,by
          have coherent := cursor.coherent;rw [remaining_actual] at coherent;simpa only [List.map_cons] using coherent⟩)
def Cursor.completed (cursor : Cursor bound start span) : Option (Completed bound start span) :=
  match actual : cursor.remaining with
  | [] => some ⟨cursor.cached,by simpa only [actual,List.map_nil,List.append_nil] using cursor.coherent⟩
  | _::_ => none

theorem initial_rank : (initial bound start span).rank = capacity bound.source.code span := by
  simp [initial,Cursor.rank,Job.rank,Job.initial,Cell.initial,Cell.rank,capacity,Function.comp_def]

theorem Cursor.move_decreases {before after : Cursor bound start span} {event : Event bound}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  rcases before with ⟨remaining,cached,coherent⟩
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
  rcases cursor with ⟨remaining,cached,coherent⟩
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
  rcases cursor with ⟨remaining,cached,coherent⟩
  cases remaining with
  | nil => simp [Cursor.move,Cursor.rank]
  | cons job rest =>
    have active : (⟨job::rest,cached,coherent⟩ : Cursor bound start span).move ≠ none := by
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

theorem every_material (metric : Settlement.Material P G) : metric ∈ Settlement.materials bound.source.code := by
  cases metric with
  | debit party good | credit party good | inventory party good =>
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨party,bound.source.code.parties_cover party,List.mem_flatMap.mpr
        ⟨good,bound.source.code.goods_cover good,by simp⟩⟩)
  | clock | admissibility => simp [Settlement.materials]

def lookup (metric : Settlement.Material P G) : (items : List (Entry bound start span)) → metric ∈ items.map Sigma.fst → Row bound start span metric
  | [],inside => False.elim (List.not_mem_nil inside)
  | head::tail,inside => if same : head.1 = metric then same ▸ head.2 else
      lookup metric tail (by simpa only [List.map_cons,List.mem_cons,eq_comm (a := metric) (b := head.1),same,false_or] using inside)
def Completed.at (cache : Completed bound start span) (metric : Settlement.Material P G) : Row bound start span metric :=
  lookup metric cache.items (by rw [cache.exact_keys];exact every_material metric)
def Completed.material (cache : Completed bound start span) (metric : Settlement.Material P G) := (cache.at metric).value
def Completed.legal (cache : Completed bound start span) := (cache.at .admissibility).lawful

def Completed.evaluation (cache : Completed bound start span) : Evaluation bound.source.code where
  legal := cache.legal
  complete := (List.finRange bound.source.code.task.slots.length).all fun index =>
    (Identity.firstService bound.source (Window.finish start span-1) index).isSome
  profile := Window.profile bound start span
  native := Window.manifest bound start span
  value := fun axis => match axis with
    | .material metric => cache.material metric
    | .unpaid index holder => Window.value bound start span (.unpaid index holder)
    | .service index => Window.value bound start span (.service index)

theorem Completed.evaluation_exact (cache : Completed bound start span) : cache.evaluation = Window.evaluate bound start span := by
  have legal : cache.legal = Window.legal bound start span := (cache.at .admissibility).exact_lawful rfl
  have values : (cache.evaluation).value = (Window.evaluate bound start span).value := by
    funext axis;cases axis with
    | material metric => exact (cache.at metric).exact_value
    | unpaid index holder => rfl
    | service index => rfl
  exact congrArg₂ (fun (l : Bool) (v : EconomicAxis bound.source.code → ℚ) =>
    (⟨l,(Window.evaluate bound start span).complete,(Window.evaluate bound start span).profile,
      (Window.evaluate bound start span).native,v⟩ : Evaluation bound.source.code)) legal values
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Window.Fold
