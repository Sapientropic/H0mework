import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Runtime
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Stepper
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {old : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {oldDepth : Nat} {word : List (Action old)}
abbrev Point := Recovery.Cursor old oldDepth word
def steps : {point : Point (old := old) (oldDepth := oldDepth) (word := word)} → Walk point → Nat
  | _,.finished _ _ | _,.blocked _ _ _ _ _ | _,.unsupported _ _ _ | _,.unpaid _ _ _ _ => 1
  | _,.billed _ _ _ _ later | _,.advanced _ _ _ _ _ later => steps later+1
  | _,.workloadStopped _ _ _ _ | _,.quotedStopped _ _ _ _ => 1
  | _,.workloadAdvanced _ _ _ _ later | _,.quotedAdvanced _ _ _ _ later => steps later+1
theorem steps_positive {point : Point (old := old) (oldDepth := oldDepth) (word := word)} (walk : Walk point) : 0 < steps walk := by cases walk <;> simp only [steps] <;> omega
inductive Task where
  | ready (point : Point (old := old) (oldDepth := oldDepth) (word := word))
  | searching (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (head : Action old) (tail : List (Action old)) (pending : point.residual = head::tail)
def Task.point : Task (old := old) (oldDepth := oldDepth) (word := word) → Point (old := old) (oldDepth := oldDepth) (word := word)
  | .ready point | .searching point _ _ _ => point
noncomputable def Task.expected (pricing : Pricing (Action old)) : (task : Task (old := old) (oldDepth := oldDepth) (word := word)) → Walk task.point
  | .ready point => pricing.execute point
  | .searching point head tail pending =>
    if progress : 0 < point.quality head.signer then
      .advanced point head tail pending progress (pricing.execute (point.after head.signer))
    else .blocked point head tail pending (Nat.eq_zero_of_not_pos progress)
noncomputable def Task.rank (pricing : Pricing (Action old)) (task : Task (old := old) (oldDepth := oldDepth) (word := word)) := steps (task.expected pricing)
inductive Event where
  | finished (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (empty : point.residual = [])
  | blocked (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (head : Action old) (tail : List (Action old)) (pending : point.residual = head::tail) (noProgress : point.quality head.signer = 0)
  | billed (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fee : List (Action old))
      (supported : fee ∈ words point.source.val.code.actions point.source.val.code.actionLimit) (paid : (point.feePath fee).succeeded = true)
  | unsupported (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fee : List (Action old)) (outside : fee ∉ words point.source.val.code.actions point.source.val.code.actionLimit)
  | unpaid (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fee : List (Action old)) (supported : fee ∈ words point.source.val.code.actions point.source.val.code.actionLimit) (refused : (point.feePath fee).succeeded = false)
  | advanced (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (head : Action old) (tail : List (Action old)) (pending : point.residual = head::tail) (progress : 0 < point.quality head.signer)
  | workloadStopped (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (position : Nat) (made : Metering.Stage point position) (stopped : ¬ made.endpoint.residual.length < point.residual.length)
  | workloadAdvanced (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (position : Nat) (made : Metering.Stage point position) (progress : made.endpoint.residual.length < point.residual.length)
  | quotedStopped (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fees : Metering.Quoted.Fees (Action old)) (made : Metering.Quoted.Stage point fees) (stopped : ¬ made.endpoint.residual.length < point.residual.length)
  | quotedAdvanced (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fees : Metering.Quoted.Fees (Action old)) (made : Metering.Quoted.Stage point fees) (progress : made.endpoint.residual.length < point.residual.length)
def headEvent : {point : Point (old := old) (oldDepth := oldDepth) (word := word)} → Walk point → Event (old := old) (oldDepth := oldDepth) (word := word)
  | _,.finished point empty => .finished point empty
  | _,.blocked point head tail pending noProgress => .blocked point head tail pending noProgress
  | _,.billed point fee supported paid _ => .billed point fee supported paid
  | _,.unsupported point fee outside => .unsupported point fee outside
  | _,.unpaid point fee supported refused => .unpaid point fee supported refused
  | _,.advanced point head tail pending progress _ => .advanced point head tail pending progress
  | _,.workloadStopped point position made stopped => .workloadStopped point position made stopped
  | _,.workloadAdvanced point position made progress _ => .workloadAdvanced point position made progress
  | _,.quotedStopped point fees made stopped => .quotedStopped point fees made stopped
  | _,.quotedAdvanced point fees made progress _ => .quotedAdvanced point fees made progress
inductive Segment : Point (old := old) (oldDepth := oldDepth) (word := word) → Point (old := old) (oldDepth := oldDepth) (word := word) → Type where
  | billed (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fee : List (Action old))
      (supported : fee ∈ words point.source.val.code.actions point.source.val.code.actionLimit) (paid : (point.feePath fee).succeeded = true) : Segment point (point.charged fee)
  | advanced (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (head : Action old) (tail : List (Action old)) (pending : point.residual = head::tail) (progress : 0 < point.quality head.signer) : Segment point (point.after head.signer)
  | workload (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (position : Nat) (made : Metering.Stage point position) (progress : made.endpoint.residual.length < point.residual.length) : Segment point made.endpoint
  | quoted (point : Point (old := old) (oldDepth := oldDepth) (word := word)) (fees : Metering.Quoted.Fees (Action old)) (made : Metering.Quoted.Stage point fees) (progress : made.endpoint.residual.length < point.residual.length) : Segment point made.endpoint
section Segments
variable {before after : Point (old := old) (oldDepth := oldDepth) (word := word)}
def Segment.wrap : {before after : Point (old := old) (oldDepth := oldDepth) (word := word)} → Segment before after → Walk after → Walk before
  | _,_,.billed point fee supported paid,later => .billed point fee supported paid later
  | _,_,.advanced point head tail pending progress,later => .advanced point head tail pending progress later
  | _,_,.workload point position made progress,later => .workloadAdvanced point position made progress later
  | _,_,.quoted point fees made progress,later => .quotedAdvanced point fees made progress later
def Segment.event : {before after : Point (old := old) (oldDepth := oldDepth) (word := word)} → Segment before after → Event (old := old) (oldDepth := oldDepth) (word := word)
  | _,_,.billed point fee supported paid => .billed point fee supported paid
  | _,_,.advanced point head tail pending progress => .advanced point head tail pending progress
  | _,_,.workload point position made progress => .workloadAdvanced point position made progress
  | _,_,.quoted point fees made progress => .quotedAdvanced point fees made progress
theorem Segment.one (segment : Segment before after) (later : Walk after) : steps (segment.wrap later) = steps later+1 := by cases segment <;> rfl
theorem Segment.event_exact (segment : Segment before after) (later : Walk after) : segment.event = headEvent (segment.wrap later) := by cases segment <;> rfl
end Segments
inductive Next (pricing : Pricing (Action old)) (task : Task (old := old) (oldDepth := oldDepth) (word := word)) where
  | halt (walk : Walk task.point) (canonical : walk = task.expected pricing) (one : steps walk = 1)
  | more (after : Task (old := old) (oldDepth := oldDepth) (word := word)) (segment : Segment task.point after.point) (canonical : segment.wrap (after.expected pricing) = task.expected pricing)
def Task.advance (pricing : Pricing (Action old)) : (task : Task (old := old) (oldDepth := oldDepth) (word := word)) → Next pricing task
  | .ready point => match pricing with
    | .unpriced => match pending : point.residual with
      | [] => .halt (.finished point pending) (by
          change Walk.finished point pending = Recovery.execute point
          conv_rhs => rw [Recovery.execute]
          split
          · rfl
          · rename_i a rest same
            have impossible := pending.symm.trans same
            cases impossible) rfl
      | head::tail => if progress : 0 < point.quality head.signer then
          .more (.ready (point.after head.signer)) (.advanced point head tail pending progress) (by
            change Walk.advanced point head tail pending progress (Recovery.execute (point.after head.signer)) = Recovery.execute point
            conv_rhs => rw [Recovery.execute]
            split
            · rename_i same
              have impossible := pending.symm.trans same
              cases impossible
            · rename_i a rest same
              rcases List.cons.inj (pending.symm.trans same) with ⟨rfl,rfl⟩
              rw [dif_pos progress])
        else .halt (.blocked point head tail pending (Nat.eq_zero_of_not_pos progress)) (by
          change Walk.blocked point head tail pending (Nat.eq_zero_of_not_pos progress) = Recovery.execute point
          conv_rhs => rw [Recovery.execute]
          split
          · rename_i same
            have impossible := pending.symm.trans same
            cases impossible
          · rename_i a rest same
            rcases List.cons.inj (pending.symm.trans same) with ⟨rfl,rfl⟩
            rw [dif_neg progress]) rfl
    | .batch fee => match pending : point.residual with
      | [] => .halt (.finished point pending) (by
          change Walk.finished point pending = executePaid fee point
          conv_rhs => rw [executePaid]
          split
          · rfl
          · rename_i a rest same
            have impossible := pending.symm.trans same
            cases impossible) rfl
      | head::tail =>
          if supported : fee ∈ words point.source.val.code.actions point.source.val.code.actionLimit then
            if paid : (point.feePath fee).succeeded = true then
              .more (.searching (point.charged fee) head tail pending)
                (.billed point fee supported paid) (by
                  change Walk.billed point fee supported paid ((Task.searching (point.charged fee) head tail pending).expected (.batch fee)) = executePaid fee point
                  conv_rhs => rw [executePaid]
                  split
                  · rename_i same
                    have impossible := pending.symm.trans same
                    cases impossible
                  · rename_i a rest same
                    rcases List.cons.inj (pending.symm.trans same) with ⟨rfl,rfl⟩
                    rw [dif_pos supported,dif_pos paid]
                    dsimp only [Task.expected,Task.point,Pricing.execute]
                    split <;> rfl)
            else .halt (.unpaid point fee supported (Bool.eq_false_iff.mpr paid)) (by
              change Walk.unpaid point fee supported (Bool.eq_false_iff.mpr paid) = executePaid fee point
              conv_rhs => rw [executePaid]
              split
              · rename_i same
                have impossible := pending.symm.trans same
                cases impossible
              · rename_i a rest same
                rcases List.cons.inj (pending.symm.trans same) with ⟨rfl,rfl⟩
                rw [dif_pos supported,dif_neg paid]) rfl
          else .halt (.unsupported point fee supported) (by
            change Walk.unsupported point fee supported = executePaid fee point
            conv_rhs => rw [executePaid]
            split
            · rename_i same
              have impossible := pending.symm.trans same
              cases impossible
            · rename_i a rest same
              rcases List.cons.inj (pending.symm.trans same) with ⟨rfl,rfl⟩
              rw [dif_neg supported]) rfl
    | .workload position =>
        if empty : point.residual = [] then .halt (.finished point empty) (by
          change Walk.finished point empty = executeWorkload position point
          conv_rhs => rw [executeWorkload]
          simp only [dif_pos empty]) rfl
        else
          let made := Metering.stage point position
          if progress : made.endpoint.residual.length < point.residual.length then
            .more (.ready made.endpoint) (.workload point position made progress) (by
              change Walk.workloadAdvanced point position made progress (executeWorkload position made.endpoint) = executeWorkload position point
              conv_rhs => rw [executeWorkload]
              simp only [dif_neg empty]
              rw [dif_pos progress])
          else .halt (.workloadStopped point position made progress) (by
            change Walk.workloadStopped point position made progress = executeWorkload position point
            conv_rhs => rw [executeWorkload]
            simp only [dif_neg empty]
            rw [dif_neg progress]) rfl
    | .workloadQuote construction selection =>
        let fees : Metering.Quoted.Fees (Action old) := ⟨construction,selection⟩
        if empty : point.residual = [] then .halt (.finished point empty) (by
          change Walk.finished point empty = executeQuoted fees point
          conv_rhs => rw [executeQuoted]
          simp only [dif_pos empty]) rfl
        else
          let made := Metering.Quoted.stage point fees
          if progress : made.endpoint.residual.length < point.residual.length then
            .more (.ready made.endpoint) (.quoted point fees made progress) (by
              change Walk.quotedAdvanced point fees made progress (executeQuoted fees made.endpoint) = executeQuoted fees point
              conv_rhs => rw [executeQuoted]
              simp only [dif_neg empty]
              rw [dif_pos progress])
          else .halt (.quotedStopped point fees made progress) (by
            change Walk.quotedStopped point fees made progress = executeQuoted fees point
            conv_rhs => rw [executeQuoted]
            simp only [dif_neg empty]
            rw [dif_neg progress]) rfl
  | .searching point head tail pending =>
      if progress : 0 < point.quality head.signer then
        .more (.ready (point.after head.signer)) (.advanced point head tail pending progress) (by
          simp only [Task.expected,dif_pos progress]
          rfl)
      else .halt (.blocked point head tail pending (Nat.eq_zero_of_not_pos progress)) (by
        simp only [Task.expected,dif_neg progress]) rfl
structure Running (pricing : Pricing (Action old)) (initial : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  private mk ::
  task : Task (old := old) (oldDepth := oldDepth) (word := word)
  rebuild : Walk task.point → Walk initial
  coherent : rebuild (task.expected pricing) = pricing.execute initial
structure Completed (pricing : Pricing (Action old)) (initial : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  private mk ::
  walk : Walk initial
  generated : walk = pricing.execute initial
inductive Cursor (pricing : Pricing (Action old)) (initial : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  | active (state : Running pricing initial)
  | done (made : Completed pricing initial)
variable (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word))
def initial : Cursor pricing point := .active ⟨.ready point,id,rfl⟩
variable {pricing point}
noncomputable def Cursor.rank : Cursor pricing point → Nat
  | .active state => state.task.rank pricing
  | .done _ => 0
def Cursor.completed : Cursor pricing point → Option (Completed pricing point)
  | .active _ => none
  | .done made => some made
def Cursor.move : Cursor pricing point → Option (Event (old := old) (oldDepth := oldDepth) (word := word) × Cursor pricing point)
  | .done _ => none
  | .active state => match state.task.advance pricing with
    | .halt walk canonical _ => some (headEvent walk,.done ⟨state.rebuild walk,by rw [canonical];exact state.coherent⟩)
    | .more after segment canonical => some (segment.event,.active ⟨after,fun later => state.rebuild (segment.wrap later),by rw [canonical];exact state.coherent⟩)
theorem Cursor.move_decreases {before after : Cursor pricing point} {event : Event (old := old) (oldDepth := oldDepth) (word := word)}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | done made => cases actual
  | active state =>
    dsimp only [Cursor.move] at actual
    cases selected : state.task.advance pricing with
    | halt walk canonical one =>
      simp only [selected] at actual
      cases actual
      change 0+1 = steps (state.task.expected pricing)
      rw [← canonical,one]
    | more next segment canonical =>
      simp only [selected] at actual
      cases actual
      change steps (next.expected pricing)+1 = steps (state.task.expected pricing)
      rw [← canonical,segment.one]
theorem Cursor.completed_iff_stopped (state : Cursor pricing point) : state.completed.isSome = true ↔ state.move = none := by
  cases state with
  | done made => simp [Cursor.completed,Cursor.move]
  | active state =>
    cases selected : state.task.advance pricing <;> simp [Cursor.completed,Cursor.move,selected]
theorem Cursor.stopped_iff_zero (state : Cursor pricing point) : state.move = none ↔ state.rank = 0 := by
  cases state with
  | done made => simp [Cursor.move,Cursor.rank]
  | active state =>
    have positive : 0 < Cursor.rank (Cursor.active state) := steps_positive _
    have notStopped : Cursor.move (Cursor.active state) ≠ none := by
      intro stopped
      have finished := (Cursor.completed_iff_stopped (Cursor.active state)).mpr stopped
      cases finished
    exact iff_of_false notStopped (Nat.ne_of_gt positive)
inductive History : Cursor pricing point → Cursor pricing point → List (Event (old := old) (oldDepth := oldDepth) (word := word)) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
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
theorem initial_rank : (initial pricing point).rank = steps (pricing.execute point) := rfl
theorem execute_bound (point : Point (old := old) (oldDepth := oldDepth) (word := word)) :
    steps (Recovery.execute point) ≤ 2*point.residual.length+1 := by
  conv_lhs => rw [Recovery.execute]
  split
  · simp only [steps];omega
  · rename_i head tail pending
    split
    · rename_i progress
      have later := execute_bound (point.after head.signer)
      have decrease := point.positive_recovery_strictly_consumes_the_original_tail head.signer progress
      simp only [steps];omega
    · simp only [steps];omega
termination_by point.residual.length
decreasing_by apply point.positive_recovery_strictly_consumes_the_original_tail;assumption

theorem paid_bound (fee : List (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) :
    steps (executePaid fee point) ≤ 2*point.residual.length+1 := by
  conv_lhs => rw [executePaid]
  split
  · simp only [steps];omega
  · rename_i head tail pending
    split
    · split
      · dsimp only []
        split
        · rename_i progress
          have later := paid_bound fee ((point.charged fee).after head.signer)
          have decrease := (point.charged fee).positive_recovery_strictly_consumes_the_original_tail head.signer progress
          change ((point.charged fee).after head.signer).residual.length < point.residual.length at decrease
          simp only [steps];omega
        · have nonempty : 0 < point.residual.length := by rw [pending];simp
          simp only [steps];omega
      · simp only [steps];omega
    · simp only [steps];omega
termination_by point.residual.length
decreasing_by apply (point.charged fee).positive_recovery_strictly_consumes_the_original_tail;assumption

theorem workload_bound (position : Nat) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) :
    steps (executeWorkload position point) ≤ 2*point.residual.length+1 := by
  conv_lhs => rw [executeWorkload]
  split
  · simp only [steps];omega
  · dsimp only []
    split
    · rename_i progress
      have later := workload_bound position (Metering.stage point position).endpoint
      simp only [steps];omega
    · simp only [steps];omega
termination_by point.residual.length
decreasing_by assumption

theorem quoted_bound (fees : Metering.Quoted.Fees (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) :
    steps (executeQuoted fees point) ≤ 2*point.residual.length+1 := by
  conv_lhs => rw [executeQuoted]
  split
  · simp only [steps];omega
  · dsimp only []
    split
    · rename_i progress
      have later := quoted_bound fees (Metering.Quoted.stage point fees).endpoint
      simp only [steps];omega
    · simp only [steps];omega
termination_by point.residual.length
decreasing_by assumption

def allowance (point : Point (old := old) (oldDepth := oldDepth) (word := word)) := 2*point.residual.length+1
theorem pricing_bound (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) :
    steps (pricing.execute point) ≤ allowance point := by
  cases pricing with
  | unpriced => exact execute_bound point
  | batch fee => exact paid_bound fee point
  | workload position => exact workload_bound position point
  | workloadQuote construction selection => exact quoted_bound ⟨construction,selection⟩ point

def complete (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) : Completed pricing point :=
  ((run (allowance point) (initial pricing point)).endpoint.completed).get
    (run_sufficient _ _ (pricing_bound pricing point))
variable {target : Authority.Sources old.base old.scope} {count : Nat}
def output (pricing : Pricing (Action old)) (original : Receipt old oldDepth target count word) : Output original :=
  let made := complete pricing (Recovery.begin original)
  Output.fromWalk pricing original made.walk made.generated
theorem output_exact (pricing : Pricing (Action old)) (original : Receipt old oldDepth target count word) :
    output pricing original = produceWith pricing original := Output.fromWalk_exact _ _ _ _
structure Execution (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) where
  private mk ::
  run : Run (initial pricing point) (allowance point)
  completed : Completed pricing point
  at_end : run.endpoint.completed = some completed
def execute (pricing : Pricing (Action old)) (point : Point (old := old) (oldDepth := oldDepth) (word := word)) : Execution pricing point :=
  let actual := run (allowance point) (initial pricing point)
  let enough := run_sufficient (initial pricing point) (allowance point) (pricing_bound pricing point)
  ⟨actual,actual.endpoint.completed.get enough,Option.eq_some_of_isSome enough⟩
def Execution.output (original : Receipt old oldDepth target count word)
    (execution : Execution pricing (Recovery.begin original)) : Output original :=
  Output.fromWalk pricing original execution.completed.walk execution.completed.generated
theorem Execution.output_exact (original : Receipt old oldDepth target count word)
    (execution : Execution pricing (Recovery.begin original)) : execution.output original = produceWith pricing original :=
  Output.fromWalk_exact _ _ _ _
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
def Execution.fromHistory (endpoint : Cursor pricing point)
    (events : List (Event (old := old) (oldDepth := oldDepth) (word := word)))
    (history : History (initial pricing point) endpoint events)
    (made : Completed pricing point) (done : endpoint.completed = some made) : Execution pricing point :=
  let actual : Run (initial pricing point) (allowance point) :=
    ⟨endpoint,events,history,by
      have balance := history.conservation
      have enough := pricing_bound pricing point
      rw [initial_rank] at balance
      omega,
      Or.inl ((Cursor.completed_iff_stopped endpoint).mp (by rw [done];rfl)),history.conservation⟩
  ⟨actual,made,done⟩
def Cursor.realize (state : Running pricing point) (selected : Next pricing state.task) :
    Event (old := old) (oldDepth := oldDepth) (word := word) × Cursor pricing point :=
  match selected with
  | .halt walk canonical _ => (headEvent walk,.done ⟨state.rebuild walk,by rw [canonical];exact state.coherent⟩)
  | .more after segment canonical => (segment.event,.active ⟨after,fun later => state.rebuild (segment.wrap later),by
      rw [canonical];exact state.coherent⟩)
theorem Cursor.realize_actual (state : Running pricing point) (selected : Next pricing state.task)
    (actual : selected = state.task.advance pricing) :
    Cursor.move (.active state) = some (Cursor.realize state selected) := by
  rw [actual]
  cases generated : state.task.advance pricing <;> simp only [Cursor.move,generated,Cursor.realize]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Stepper
