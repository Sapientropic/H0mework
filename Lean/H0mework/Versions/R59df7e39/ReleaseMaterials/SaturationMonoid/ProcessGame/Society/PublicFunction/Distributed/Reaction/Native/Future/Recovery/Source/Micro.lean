import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source.Session
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Micro
open Institutions.Capitalism.Universal.Source.Program
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
abbrev Point := Stepper.Point (old := old) (oldDepth := oldDepth) (word := word)
abbrev ProgramEvent := Metering.StageProgram.Event (old := old)
abbrev WorkSession (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (position : Nat) :=
  Metering.StageProgram.Session (Metering.stageProgram point position)
abbrev QuoteSession (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fees : Metering.Quoted.Fees (Action old)) :=
  Metering.StageProgram.Session (Metering.Quoted.stageProgram point fees)
def weight : Stepper.Event (old := old) (oldDepth := oldDepth) (word := word) → Nat
  | .workloadStopped _ _ made _ | .workloadAdvanced _ _ made _ => made.execution.work.length+2
  | .quotedStopped _ _ made _ | .quotedAdvanced _ _ made _ => made.execution.work.length+2
  | _ => 1
noncomputable def fullWork : {point : Point (old := old) (oldDepth := oldDepth) (word := word)} → Walk point → Nat
  | _,.finished .. | _,.blocked .. | _,.unsupported .. | _,.unpaid .. => 1
  | _,.billed _ _ _ _ later | _,.advanced _ _ _ _ _ later => fullWork later+1
  | _,.workloadStopped _ _ made _ | _,.quotedStopped _ _ made _ => made.execution.work.length+2
  | _,.workloadAdvanced _ _ made _ later | _,.quotedAdvanced _ _ made _ later => fullWork later+made.execution.work.length+2
theorem fullWork_positive {point : Point (old := old) (oldDepth := oldDepth) (word := word)} (walk : Walk point) : 0 < fullWork walk := by
  cases walk <;> simp only [fullWork] <;> omega
noncomputable def coreRank {pricing : Pricing (Action old)} {point : Point (old := old) (oldDepth := oldDepth) (word := word)} :
    Stepper.Cursor pricing point → Nat
  | .done _ => 0
  | .active state => fullWork (state.task.expected pricing)
theorem terminal_weight {point : Point (old := old) (oldDepth := oldDepth) (word := word)} (walk : Walk point)
    (one : Stepper.steps walk = 1) : weight (Stepper.headEvent walk) = fullWork walk := by
  cases walk <;> try rfl
  all_goals
    rename_i later
    have positive := Stepper.steps_positive later
    simp only [Stepper.steps] at one
    omega
theorem segment_work {first last : Point (old := old) (oldDepth := oldDepth) (word := word)}
    (segment : Stepper.Segment first last) (later : Walk last) :
    fullWork (segment.wrap later) = fullWork later+weight segment.event := by cases segment <;> simp only [Stepper.Segment.wrap,Stepper.Segment.event,fullWork,weight] <;> omega
theorem core_move_work {pricing : Pricing (Action old)} {point : Point (old := old) (oldDepth := oldDepth) (word := word)}
    {before after : Stepper.Cursor pricing point} {event : Stepper.Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : coreRank after+weight event = coreRank before := by
  cases before with
  | done made => cases actual
  | active state =>
    dsimp only [Stepper.Cursor.move] at actual
    cases selected : state.task.advance pricing with
    | halt walk canonical one =>
      simp only [selected] at actual;cases actual
      change 0+weight (Stepper.headEvent walk) = fullWork (state.task.expected pricing)
      rw [←canonical,Nat.zero_add]
      exact terminal_weight walk one
    | more next segment canonical =>
      simp only [selected] at actual;cases actual
      change fullWork (next.expected pricing)+weight segment.event = fullWork (state.task.expected pricing)
      rw [←canonical,segment_work]

def nextEvent {pricing : Pricing (Action old)} {task : Stepper.Task (old := old) (oldDepth := oldDepth) (word := word)} :
    Stepper.Next pricing task → Stepper.Event (old := old) (oldDepth := oldDepth) (word := word)
  | .halt walk .. => Stepper.headEvent walk
  | .more _ segment _ => segment.event
inductive Dispatch (pricing : Pricing (Action old)) (task : Stepper.Task (old := old) (oldDepth := oldDepth) (word := word)) where
  | simple (selected : Stepper.Next pricing task) (actual : selected = task.advance pricing) (unit : weight (nextEvent selected) = 1)
  | workload (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (position : Nat)
      (task_eq : task = .ready point) (mode : pricing = .workload position) (nonempty : point.residual ≠ [])
  | quoted (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fees : Metering.Quoted.Fees (Action old))
      (task_eq : task = .ready point) (mode : pricing = .workloadQuote fees.construction fees.selection) (nonempty : point.residual ≠ [])
def dispatch (pricing : Pricing (Action old)) (task : Stepper.Task (old := old) (oldDepth := oldDepth) (word := word)) : Dispatch pricing task := by
  cases task with
  | searching point head tail pending =>
    exact .simple _ rfl (by dsimp only [Stepper.Task.advance];split <;> rfl)
  | ready point =>
    cases pricing with
    | unpriced =>
      exact .simple _ rfl (by
        dsimp only [Stepper.Task.advance]
        split
        · rfl
        · split <;> rfl)
    | batch fee =>
      exact .simple _ rfl (by
        dsimp only [Stepper.Task.advance]
        split
        · rfl
        · split
          · split <;> rfl
          · rfl)
    | workload position =>
      by_cases empty : point.residual = []
      · exact .simple _ rfl (by dsimp only [Stepper.Task.advance];rw [dif_pos empty];rfl)
      · exact .workload point position rfl rfl empty
    | workloadQuote construction selection =>
      by_cases empty : point.residual = []
      · exact .simple _ rfl (by dsimp only [Stepper.Task.advance];rw [dif_pos empty];rfl)
      · exact .quoted point ⟨construction,selection⟩ rfl rfl empty
variable {pricing : Pricing (Action old)} {point : Point (old := old) (oldDepth := oldDepth) (word := word)}
def transportNext {first second : Stepper.Task (old := old) (oldDepth := oldDepth) (word := word)}
    (same : first = second) (selected : Stepper.Next pricing second) : Stepper.Next pricing first := same.symm ▸ selected
theorem transportNext_actual {first second : Stepper.Task (old := old) (oldDepth := oldDepth) (word := word)}
    (same : first = second) (selected : Stepper.Next pricing second) (actual : selected = second.advance pricing) :
    transportNext same selected = first.advance pricing := by cases same;exact actual

def workloadChoice (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (position : Nat)
    (mode : pricing = .workload position) (nonempty : point.residual ≠ []) (made : Metering.Stage point position) :
    Stepper.Next pricing (.ready point) := by
  cases mode
  if progress : made.endpoint.residual.length < point.residual.length then
    exact .more (.ready made.endpoint) (.workload point position made progress) (by
      change Walk.workloadAdvanced point position made progress (executeWorkload position made.endpoint) = executeWorkload position point
      conv_rhs => rw [executeWorkload]
      simp only [dif_neg nonempty]
      rw [←made.eq_default,dif_pos progress])
  else
    exact .halt (.workloadStopped point position made progress) (by
      change Walk.workloadStopped point position made progress = executeWorkload position point
      conv_rhs => rw [executeWorkload]
      simp only [dif_neg nonempty]
      rw [←made.eq_default,dif_neg progress]) rfl

def quotedChoice (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fees : Metering.Quoted.Fees (Action old))
    (mode : pricing = .workloadQuote fees.construction fees.selection) (nonempty : point.residual ≠ [])
    (made : Metering.Quoted.Stage point fees) : Stepper.Next pricing (.ready point) := by
  cases mode
  if progress : made.endpoint.residual.length < point.residual.length then
    exact .more (.ready made.endpoint) (.quoted point fees made progress) (by
      change Walk.quotedAdvanced point fees made progress (executeQuoted fees made.endpoint) = executeQuoted fees point
      conv_rhs => rw [executeQuoted]
      simp only [dif_neg nonempty]
      rw [←made.eq_default,dif_pos progress])
  else
    exact .halt (.quotedStopped point fees made progress) (by
      change Walk.quotedStopped point fees made progress = executeQuoted fees point
      conv_rhs => rw [executeQuoted]
      simp only [dif_neg nonempty]
      rw [←made.eq_default,dif_neg progress]) rfl

theorem workloadChoice_actual (position : Nat) (mode : pricing = .workload position) (nonempty : point.residual ≠ [])
    (made : Metering.Stage point position) : workloadChoice point position mode nonempty made = (Stepper.Task.ready point).advance pricing := by
  cases mode
  rw [made.eq_default]
  dsimp only [workloadChoice,Stepper.Task.advance]
  rw [dif_neg nonempty]

theorem quotedChoice_actual (fees : Metering.Quoted.Fees (Action old))
    (mode : pricing = .workloadQuote fees.construction fees.selection) (nonempty : point.residual ≠ [])
    (made : Metering.Quoted.Stage point fees) : quotedChoice point fees mode nonempty made = (Stepper.Task.ready point).advance pricing := by
  cases mode
  rw [made.eq_default]
  dsimp only [quotedChoice,Stepper.Task.advance]
  rw [dif_neg nonempty]

theorem realize_event (state : Stepper.Running pricing point) (selected : Stepper.Next pricing state.task) :
    (Stepper.Cursor.realize state selected).1 = nextEvent selected := by cases selected <;> rfl
theorem nextEvent_transport {first second : Stepper.Task (old := old) (oldDepth := oldDepth) (word := word)}
    (same : first = second) (selected : Stepper.Next pricing second) : nextEvent (transportNext same selected) = nextEvent selected := by cases same;rfl
theorem workloadChoice_weight (position : Nat) (mode : pricing = .workload position) (nonempty : point.residual ≠ [])
    (made : Metering.Stage point position) : weight (nextEvent (workloadChoice point position mode nonempty made)) = made.execution.work.length+2 := by
  cases mode
  dsimp only [workloadChoice]
  split <;> rfl
theorem quotedChoice_weight (fees : Metering.Quoted.Fees (Action old))
    (mode : pricing = .workloadQuote fees.construction fees.selection) (nonempty : point.residual ≠ [])
    (made : Metering.Quoted.Stage point fees) : weight (nextEvent (quotedChoice point fees mode nonempty made)) = made.execution.work.length+2 := by
  cases mode
  dsimp only [quotedChoice]
  split <;> rfl
structure WorkloadState (pricing : Pricing (Action old)) (initial : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  private mk ::
  root : Stepper.Running pricing initial
  origin : Point (old := old) (oldDepth := oldDepth) (word := word)
  position : Nat
  task_eq : root.task = .ready origin
  mode : pricing = .workload position
  nonempty : origin.residual ≠ []
  session : WorkSession origin position
structure QuotedState (pricing : Pricing (Action old)) (initial : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  private mk ::
  root : Stepper.Running pricing initial
  origin : Point (old := old) (oldDepth := oldDepth) (word := word)
  fees : Metering.Quoted.Fees (Action old)
  task_eq : root.task = .ready origin
  mode : pricing = .workloadQuote fees.construction fees.selection
  nonempty : origin.residual ≠ []
  session : QuoteSession origin fees
def WorkloadState.choice (state : WorkloadState pricing point) (made : Metering.Stage state.origin state.position) :=
  transportNext state.task_eq (workloadChoice state.origin state.position state.mode state.nonempty made)
def QuotedState.choice (state : QuotedState pricing point) (made : Metering.Quoted.Stage state.origin state.fees) :=
  transportNext state.task_eq (quotedChoice state.origin state.fees state.mode state.nonempty made)
theorem WorkloadState.actual (state : WorkloadState pricing point) (made : Metering.Stage state.origin state.position) :
    state.choice made = state.root.task.advance pricing :=
  transportNext_actual _ _ (workloadChoice_actual _ state.mode state.nonempty made)
theorem QuotedState.actual (state : QuotedState pricing point) (made : Metering.Quoted.Stage state.origin state.fees) :
    state.choice made = state.root.task.advance pricing :=
  transportNext_actual _ _ (quotedChoice_actual _ state.mode state.nonempty made)
theorem WorkloadState.lower (state : WorkloadState pricing point) :
    (Metering.stage state.origin state.position).execution.work.length+2 ≤ coreRank (.active state.root) := by
  change _ ≤ fullWork (state.root.task.expected pricing)
  rw [state.task_eq]
  change _ ≤ fullWork (pricing.execute state.origin)
  have same := congrArg (fun mode => Pricing.execute mode state.origin) state.mode
  change pricing.execute state.origin = executeWorkload state.position state.origin at same
  rw [same]
  conv_rhs => rw [executeWorkload]
  simp only [dif_neg state.nonempty]
  split <;> simp only [fullWork] <;> omega
theorem QuotedState.lower (state : QuotedState pricing point) :
    (Metering.Quoted.stage state.origin state.fees).execution.work.length+2 ≤ coreRank (.active state.root) := by
  change _ ≤ fullWork (state.root.task.expected pricing)
  rw [state.task_eq]
  change _ ≤ fullWork (pricing.execute state.origin)
  have same := congrArg (fun mode => Pricing.execute mode state.origin) state.mode
  change pricing.execute state.origin = executeQuoted state.fees state.origin at same
  rw [same]
  conv_rhs => rw [executeQuoted]
  simp only [dif_neg state.nonempty]
  split <;> simp only [fullWork] <;> omega
inductive Cursor (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  | active (current : Stepper.Cursor pricing point)
  | workload (state : WorkloadState pricing point)
  | quoted (state : QuotedState pricing point)
inductive Event where
  | world (event : Stepper.Event (old := old) (oldDepth := oldDepth) (word := word))
  | beginWorkload (origin : Point (old := old) (oldDepth := oldDepth) (word := word)) (position : Nat)
  | beginQuoted (origin : Point (old := old) (oldDepth := oldDepth) (word := word)) (fees : Metering.Quoted.Fees (Action old))
  | workload (origin : Point (old := old) (oldDepth := oldDepth) (word := word)) (position : Nat)
      (before after : WorkSession origin position) (event : ProgramEvent (old := old)) (actual : before.move = some (event,after))
  | quoted (origin : Point (old := old) (oldDepth := oldDepth) (word := word)) (fees : Metering.Quoted.Fees (Action old))
      (before after : QuoteSession origin fees) (event : ProgramEvent (old := old)) (actual : before.move = some (event,after))
def Event.coarse : Event (old := old) (oldDepth := oldDepth) (word := word) → List (Stepper.Event (old := old) (oldDepth := oldDepth) (word := word))
  | .world event => [event]
  | _ => []
def initial (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) : Cursor pricing point :=
  .active (Stepper.initial pricing point)
def Cursor.core : Cursor pricing point → Stepper.Cursor pricing point
  | .active current => current
  | .workload state => .active state.root
  | .quoted state => .active state.root
noncomputable def Cursor.rank : Cursor pricing point → Nat
  | .active current => coreRank current
  | .workload state => coreRank (.active state.root)-state.session.work.length-1
  | .quoted state => coreRank (.active state.root)-state.session.work.length-1
def Cursor.completed (current : Cursor pricing point) := current.core.completed

def Cursor.move : Cursor pricing point → Option (Event (old := old) (oldDepth := oldDepth) (word := word) × Cursor pricing point)
  | .active (.done _) => none
  | .active (.active root) => match dispatch pricing root.task with
    | .simple selected actual unit =>
      let next := Stepper.Cursor.realize root selected
      some (.world next.1,.active next.2)
    | .workload origin position task_eq mode nonempty => some (.beginWorkload origin position,
        .workload ⟨root,origin,position,task_eq,mode,nonempty,Metering.StageProgram.Session.initial _⟩)
    | .quoted origin fees task_eq mode nonempty => some (.beginQuoted origin fees,
        .quoted ⟨root,origin,fees,task_eq,mode,nonempty,Metering.StageProgram.Session.initial _⟩)
  | .workload state => match done : state.session.completed with
    | some execution =>
      let made := Metering.Stage.fromExecution execution
      let next := Stepper.Cursor.realize state.root (state.choice made)
      some (.world next.1,.active next.2)
    | none => match actual : state.session.move with
      | some (event,after) => some (.workload state.origin state.position state.session after event actual,
          .workload {state with session := after})
      | none => False.elim (by
          have complete := state.session.completed_iff_stopped.mpr actual
          rw [done] at complete;cases complete)
  | .quoted state => match done : state.session.completed with
    | some execution =>
      let made := Metering.Quoted.Stage.fromExecution execution
      let next := Stepper.Cursor.realize state.root (state.choice made)
      some (.world next.1,.active next.2)
    | none => match actual : state.session.move with
      | some (event,after) => some (.quoted state.origin state.fees state.session after event actual,
          .quoted {state with session := after})
      | none => False.elim (by
          have complete := state.session.completed_iff_stopped.mpr actual
          rw [done] at complete;cases complete)

theorem WorkloadState.finished (state : WorkloadState pricing point)
    {execution : Metering.StageProgram.Execution (Metering.stageProgram state.origin state.position)}
    (complete : state.session.completed = some execution) :
    coreRank (Stepper.Cursor.realize state.root (state.choice (Metering.Stage.fromExecution execution))).2+
      state.session.work.length+2 = coreRank (.active state.root) := by
  have balance := core_move_work (Stepper.Cursor.realize_actual state.root _ (state.actual (Metering.Stage.fromExecution execution)))
  change coreRank (Stepper.Cursor.realize state.root (state.choice (Metering.Stage.fromExecution execution))).2+
    weight (Stepper.Cursor.realize state.root (state.choice (Metering.Stage.fromExecution execution))).1 = coreRank (.active state.root) at balance
  rw [realize_event,WorkloadState.choice,nextEvent_transport,workloadChoice_weight] at balance
  have work := Metering.StageProgram.Session.completed_work complete
  change execution.work = state.session.work at work
  change coreRank (Stepper.Cursor.realize state.root (state.choice (Metering.Stage.fromExecution execution))).2+
    (execution.work.length+2) = coreRank (.active state.root) at balance
  rw [work] at balance;omega
theorem QuotedState.finished (state : QuotedState pricing point)
    {execution : Metering.StageProgram.Execution (Metering.Quoted.stageProgram state.origin state.fees)}
    (complete : state.session.completed = some execution) :
    coreRank (Stepper.Cursor.realize state.root (state.choice (Metering.Quoted.Stage.fromExecution execution))).2+
      state.session.work.length+2 = coreRank (.active state.root) := by
  have balance := core_move_work (Stepper.Cursor.realize_actual state.root _ (state.actual (Metering.Quoted.Stage.fromExecution execution)))
  change coreRank (Stepper.Cursor.realize state.root (state.choice (Metering.Quoted.Stage.fromExecution execution))).2+
    weight (Stepper.Cursor.realize state.root (state.choice (Metering.Quoted.Stage.fromExecution execution))).1 = coreRank (.active state.root) at balance
  rw [realize_event,QuotedState.choice,nextEvent_transport,quotedChoice_weight] at balance
  have work := Metering.StageProgram.Session.completed_work complete
  change execution.work = state.session.work at work
  change coreRank (Stepper.Cursor.realize state.root (state.choice (Metering.Quoted.Stage.fromExecution execution))).2+
    (execution.work.length+2) = coreRank (.active state.root) at balance
  rw [work] at balance;omega
theorem Cursor.move_core {before after : Cursor pricing point} {event : Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : Stepper.History before.core after.core event.coarse := by
  cases before with
  | active current =>
    cases current with
    | done made => cases actual
    | active root =>
      dsimp only [Cursor.move] at actual
      cases selected : dispatch pricing root.task with
      | simple next correct unit =>
        simp only [selected] at actual;cases actual
        exact .step (Stepper.Cursor.realize_actual root next correct) (.nil _)
      | workload origin position task_eq mode nonempty =>
        simp only [selected] at actual;cases actual;exact .nil _
      | quoted origin fees task_eq mode nonempty =>
        simp only [selected] at actual;cases actual;exact .nil _
  | workload state =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i execution complete
      cases actual
      exact .step (Stepper.Cursor.realize_actual state.root _ (state.actual _)) (.nil _)
    · rename_i incomplete
      split at actual
      · rename_i event next moved
        cases actual;exact .nil _
      · rename_i stopped
        have complete := state.session.completed_iff_stopped.mpr stopped
        rw [incomplete] at complete;cases complete
  | quoted state =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i execution complete
      cases actual
      exact .step (Stepper.Cursor.realize_actual state.root _ (state.actual _)) (.nil _)
    · rename_i incomplete
      split at actual
      · rename_i event next moved
        cases actual;exact .nil _
      · rename_i stopped
        have complete := state.session.completed_iff_stopped.mpr stopped
        rw [incomplete] at complete;cases complete

theorem Cursor.move_decreases {before after : Cursor pricing point} {event : Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | active current =>
    cases current with
    | done made => cases actual
    | active root =>
      dsimp only [Cursor.move] at actual
      cases selected : dispatch pricing root.task with
      | simple next correct unit =>
        simp only [selected] at actual;cases actual
        have balance := core_move_work (Stepper.Cursor.realize_actual root next correct)
        change coreRank (Stepper.Cursor.realize root next).2+weight (Stepper.Cursor.realize root next).1 = coreRank (.active root) at balance
        rw [realize_event,unit] at balance
        exact balance
      | workload origin position task_eq mode nonempty =>
        simp only [selected] at actual;cases actual
        have positive := fullWork_positive (root.task.expected pricing)
        change (coreRank (.active root)-0-1)+1 = coreRank (.active root)
        change 0 < coreRank (.active root) at positive
        omega
      | quoted origin fees task_eq mode nonempty =>
        simp only [selected] at actual;cases actual
        have positive := fullWork_positive (root.task.expected pricing)
        change (coreRank (.active root)-0-1)+1 = coreRank (.active root)
        change 0 < coreRank (.active root) at positive
        omega
  | workload state =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i execution complete
      cases actual
      have balance := state.finished complete
      dsimp only [Cursor.rank];omega
    · rename_i incomplete
      split at actual
      · rename_i emitted next moved
        cases actual
        have sizes := congrArg List.length (Metering.StageProgram.Session.move_appends moved)
        have covered := next.covered
        have lower := state.lower
        change next.work.length ≤ (Metering.stage state.origin state.position).execution.work.length at covered
        simp only [List.length_append,List.length_singleton] at sizes
        dsimp only [Cursor.rank];omega
      · rename_i stopped
        have complete := state.session.completed_iff_stopped.mpr stopped
        rw [incomplete] at complete;cases complete
  | quoted state =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i execution complete
      cases actual
      have balance := state.finished complete
      dsimp only [Cursor.rank];omega
    · rename_i incomplete
      split at actual
      · rename_i emitted next moved
        cases actual
        have sizes := congrArg List.length (Metering.StageProgram.Session.move_appends moved)
        have covered := next.covered
        have lower := state.lower
        change next.work.length ≤ (Metering.Quoted.stage state.origin state.fees).execution.work.length at covered
        simp only [List.length_append,List.length_singleton] at sizes
        dsimp only [Cursor.rank];omega
      · rename_i stopped
        have complete := state.session.completed_iff_stopped.mpr stopped
        rw [incomplete] at complete;cases complete

theorem Cursor.completed_iff_stopped (current : Cursor pricing point) : current.completed.isSome = true ↔ current.move = none := by
  cases current with
  | active native =>
    cases native with
    | done made => simp [Cursor.completed,Cursor.core,Stepper.Cursor.completed,Cursor.move]
    | active root =>
      cases selected : dispatch pricing root.task <;>
        simp [Cursor.completed,Cursor.core,Stepper.Cursor.completed,Cursor.move,selected]
  | workload state =>
    dsimp only [Cursor.completed,Cursor.core,Stepper.Cursor.completed,Cursor.move]
    split
    · simp
    · rename_i incomplete
      split
      · simp
      · rename_i stopped
        have complete := state.session.completed_iff_stopped.mpr stopped
        rw [incomplete] at complete;cases complete
  | quoted state =>
    dsimp only [Cursor.completed,Cursor.core,Stepper.Cursor.completed,Cursor.move]
    split
    · simp
    · rename_i incomplete
      split
      · simp
      · rename_i stopped
        have complete := state.session.completed_iff_stopped.mpr stopped
        rw [incomplete] at complete;cases complete

theorem Cursor.stopped_iff_zero (current : Cursor pricing point) : current.move = none ↔ current.rank = 0 := by
  cases current with
  | active native =>
    cases native with
    | done made => simp [Cursor.move,Cursor.rank,coreRank]
    | active root =>
      have positive := fullWork_positive (root.task.expected pricing)
      have moving : Cursor.move (.active (.active root)) ≠ none := by
        intro stopped
        have complete := (Cursor.completed_iff_stopped (.active (.active root))).mpr stopped
        cases complete
      exact iff_of_false moving (Nat.ne_of_gt positive)
  | workload state =>
    have lower := state.lower
    have covered := state.session.covered
    change state.session.work.length ≤ (Metering.stage state.origin state.position).execution.work.length at covered
    have moving : Cursor.move (.workload state) ≠ none := by
      intro stopped
      have complete := (Cursor.completed_iff_stopped (.workload state)).mpr stopped
      cases complete
    apply iff_of_false moving
    dsimp only [Cursor.rank];omega
  | quoted state =>
    have lower := state.lower
    have covered := state.session.covered
    change state.session.work.length ≤ (Metering.Quoted.stage state.origin state.fees).execution.work.length at covered
    have moving : Cursor.move (.quoted state) ≠ none := by
      intro stopped
      have complete := (Cursor.completed_iff_stopped (.quoted state)).mpr stopped
      cases complete
    apply iff_of_false moving
    dsimp only [Cursor.rank];omega

inductive History : Cursor pricing point → Cursor pricing point → List (Event (old := old) (oldDepth := oldDepth) (word := word)) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
theorem History.conservation {before after : Cursor pricing point}
    {events : List (Event (old := old) (oldDepth := oldDepth) (word := word))}
    (actual : History before after events) : after.rank+events.length = before.rank := by
  induction actual with
  | nil before => simp
  | step actual later known =>
    have decrease := Cursor.move_decreases actual
    simp only [List.length_cons];omega
theorem History.append : {before middle after : Cursor pricing point} →
    {first second : List (Event (old := old) (oldDepth := oldDepth) (word := word))} →
    History before middle first → History middle after second → History before after (first++second)
  | _,_,_,_,_,.nil _,later => later
  | _,_,_,_,_,.step actual past,later => .step actual (History.append past later)
theorem initial_rank : (initial pricing point).rank = fullWork (pricing.execute point) := rfl
structure Run (before : Cursor pricing point) (capacity : Nat) where
  private mk ::
  endpoint : Cursor pricing point
  work : List (Event (old := old) (oldDepth := oldDepth) (word := word))
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank
def run : (capacity : Nat) → (before : Cursor pricing point) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩
theorem run_sufficient (before : Cursor pricing point) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega
theorem run_work_exact (before : Cursor pricing point) (available : Nat) :
    (run available before).work.length = min available before.rank := by
  have covered := (run available before).covered
  have conserved := (run available before).conservation
  rcases (run available before).exhausted with stopped | full
  · have zero := (Cursor.stopped_iff_zero _).mp stopped
    rw [zero] at conserved
    have same : (run available before).work.length = before.rank := by omega
    rw [same,Nat.min_eq_right (by omega)]
  · rw [full,Nat.min_eq_left (by omega)]
structure Session (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  private mk ::
  current : Cursor pricing point
  work : List (Event (old := old) (oldDepth := oldDepth) (word := word))
  history : History (Micro.initial pricing point) current work
  coarseWork : List (Stepper.Event (old := old) (oldDepth := oldDepth) (word := word))
  coarseHistory : Stepper.History (Stepper.initial pricing point) current.core coarseWork
def Session.initial (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) : Session pricing point :=
  ⟨Micro.initial pricing point,[],.nil _,[],.nil _⟩
noncomputable def Session.rank (session : Session pricing point) := session.current.rank
def Session.move (session : Session pricing point) : Option (Event (old := old) (oldDepth := oldDepth) (word := word) × Session pricing point) :=
  match actual : session.current.move with
  | none => none
  | some (event,next) => some (event,⟨next,session.work++[event],session.history.append (.step actual (.nil next)),
      session.coarseWork++event.coarse,session.coarseHistory.append (Cursor.move_core actual)⟩)
def Session.completed (session : Session pricing point) : Option (Stepper.Execution pricing point) :=
  match actual : session.current.completed with
  | none => none
  | some made => some (Stepper.Execution.fromHistory session.current.core session.coarseWork session.coarseHistory made actual)
theorem Session.completed_work {session : Session pricing point} {made : Stepper.Execution pricing point}
    (actual : session.completed = some made) : made.run.work = session.coarseWork := by
  dsimp only [Session.completed] at actual
  split at actual
  · cases actual
  · cases actual;rfl
theorem Session.initial_rank : (Session.initial pricing point).rank = fullWork (pricing.execute point) := rfl
theorem Session.move_decreases {before after : Session pricing point}
    {event : Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · rename_i emitted next moved
    cases actual
    exact Cursor.move_decreases moved
theorem Session.move_appends {before after : Session pricing point}
    {event : Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : after.work = before.work++[event] := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · cases actual;rfl
theorem Session.move_coarse {before after : Session pricing point}
    {event : Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : after.coarseWork = before.coarseWork++event.coarse := by
  dsimp only [Session.move] at actual
  split at actual
  · cases actual
  · cases actual;rfl
theorem Session.completed_iff_stopped (session : Session pricing point) : session.completed.isSome = true ↔ session.move = none := by
  have native := Cursor.completed_iff_stopped session.current
  unfold Session.completed Session.move
  split <;> split <;> simp_all
theorem Session.stopped_iff_zero (session : Session pricing point) : session.move = none ↔ session.rank = 0 := by
  unfold Session.move Session.rank
  have native := Cursor.stopped_iff_zero session.current
  split <;> simp_all
theorem Session.conservation (session : Session pricing point) : session.rank+session.work.length = fullWork (pricing.execute point) := by
  have native := session.history.conservation
  rw [Micro.initial_rank] at native
  exact native

theorem Session.completed_full_work {session : Session pricing point} {made : Stepper.Execution pricing point}
    (actual : session.completed = some made) : session.work.length = fullWork (pricing.execute point) := by
  have stopped := session.completed_iff_stopped.mp (by rw [actual];rfl)
  have zero := session.stopped_iff_zero.mp stopped
  have balance := session.conservation
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Micro
