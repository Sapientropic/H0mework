import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source.Micro
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source.Session
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment.Fields
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding.Source
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Restoration
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {driver : Feedback.Input seed.source.code} (cursor : Online.Cursor seed driver)
  (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
  (source : Future.Recovery.SameCodeTarget cursor.model) (count : Nat)
abbrev Word := List (Future.Recovery.Action cursor.model)
abbrev Value (word : Word cursor) := Option (Future.Recovery.Assessment.Report cursor.model ×
  Option (Future.Recovery.Funding.Failure cursor.model cursor.depth word))
inductive Outcome (word : Word cursor) where
  | rejected (reason : PLift (¬ Mandate.Replay.Legal (base := cursor.model.base) cursor.model.scope (Authority.currentAt cursor.model cursor.depth) word))
  | recovered (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word) (made : Future.Recovery.Output receipt)
def generate (word : Word cursor) : Outcome cursor source count word :=
  match Future.produce cursor.model cursor.depth source.indexed count word with
  | .inl reason => .rejected reason
  | .inr receipt =>
      let execution := Future.Recovery.Stepper.execute pricing (Future.Recovery.begin receipt)
      .recovered receipt (execution.output receipt)
def Outcome.value {word : Word cursor} : Outcome cursor source count word → Value cursor word
  | .rejected _ => none
  | .recovered _ made => some (Future.Recovery.Assessment.reportFrom made cursor.depth source.property,
      Future.Recovery.Funding.ofWalk made.walk)
theorem generated_value (word : Word cursor) : (generate cursor pricing source count word).value =
    Whole.restoration (pricing := pricing) source count word := by
  unfold generate Whole.restoration
  simp only [Future.Recovery.Stepper.Execution.output_exact]
  cases Future.produce cursor.model cursor.depth source.indexed count word <;> rfl
inductive Trace : (word : Word cursor) → Outcome cursor source count word → Type where
  | rejected {word : Word cursor} (reason : PLift (¬ Mandate.Replay.Legal (base := cursor.model.base) cursor.model.scope (Authority.currentAt cursor.model cursor.depth) word)) :
      Trace word (.rejected reason)
  | recovered {word : Word cursor} (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
      (execution : Future.Recovery.Stepper.Execution pricing (Future.Recovery.begin receipt)) :
      Trace word (.recovered receipt (execution.output receipt))
  | reported {word : Word cursor} (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
      (execution : Future.Recovery.Stepper.Execution pricing (Future.Recovery.begin receipt))
      (made : Future.Recovery.Output receipt) (generated : made = execution.output receipt)
      (fields : Future.Recovery.Assessment.Fields.Completed made cursor.depth) :
      Trace word (.recovered receipt made)
  | funded {word : Word cursor} (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
      (execution : Future.Recovery.Stepper.Execution pricing (Future.Recovery.begin receipt))
      (made : Future.Recovery.Output receipt) (generated : made = execution.output receipt)
      (fields : Future.Recovery.Assessment.Fields.Completed made cursor.depth)
      (funding : Future.Recovery.Funding.Source.Completed made.walk) :
      Trace word (.recovered receipt made)
structure Row (word : Word cursor) where
  private mk ::
  outcome : Outcome cursor source count word
  generated : outcome = generate cursor pricing source count word
  value : Value cursor word
  value_generated : value = outcome.value
  trace : Trace cursor pricing source count word outcome
def row (word : Word cursor) : Row cursor pricing source count word :=
  match produced : Future.produce cursor.model cursor.depth source.indexed count word with
  | .inl reason =>
      let outcome : Outcome cursor source count word := .rejected reason
      ⟨outcome,by unfold generate;rw [produced],outcome.value,rfl,.rejected reason⟩
  | .inr receipt =>
      let execution := Future.Recovery.Stepper.execute pricing (Future.Recovery.begin receipt)
      let outcome : Outcome cursor source count word := .recovered receipt (execution.output receipt)
      ⟨outcome,by unfold generate;rw [produced],outcome.value,rfl,.recovered receipt execution⟩
variable {cursor pricing source count}
theorem Row.value_exact {word : Word cursor} (row : Row cursor pricing source count word) : row.value =
    Whole.restoration (pricing := pricing) source count word := by
  rw [row.value_generated,row.generated];exact generated_value cursor pricing source count word
abbrev Entry (cursor : Online.Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (source : Future.Recovery.SameCodeTarget cursor.model) (count : Nat) :=
  (word : Word cursor) × Row cursor pricing source count word
variable (cursor pricing source count)
variable {source count}
noncomputable def reportCost {word : Word cursor}
    (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word) : Nat :=
  Future.Recovery.Assessment.Fields.capacity (Future.Recovery.produceWith pricing receipt) cursor.depth
noncomputable def fundingCost {word : Word cursor}
    (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word) : Nat :=
  Future.Recovery.Stepper.steps (Future.Recovery.produceWith pricing receipt).walk
variable (source count)
noncomputable def wordCost (word : Word cursor) : Nat :=
  match Future.produce cursor.model cursor.depth source.indexed count word with
  | .inl _ => 1
  | .inr receipt => Future.Recovery.Micro.fullWork (pricing.execute (Future.Recovery.begin receipt))+reportCost cursor pricing receipt+fundingCost cursor pricing receipt+4
noncomputable def listCost (words : List (Word cursor)) := (words.map (wordCost cursor pricing source count)).sum
noncomputable def capacity := listCost cursor pricing source count (Future.Recovery.capabilities cursor.model cursor.depth)
theorem wordCost_positive (word : Word cursor) : 0 < wordCost cursor pricing source count word := by
  unfold wordCost;split <;> omega
structure Ready (cursor : Online.Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (source : Future.Recovery.SameCodeTarget cursor.model) (count : Nat) where
  private mk ::
  remaining : List (Word cursor)
  cached : List (Entry cursor pricing source count)
  coherent : cached.map Sigma.fst++remaining = Future.Recovery.capabilities cursor.model cursor.depth
structure Recovering (cursor : Online.Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (source : Future.Recovery.SameCodeTarget cursor.model) (count : Nat) where
  private mk ::
  word : Word cursor
  tail : List (Word cursor)
  cached : List (Entry cursor pricing source count)
  coherent : cached.map Sigma.fst++word::tail = Future.Recovery.capabilities cursor.model cursor.depth
  receipt : Future.Receipt cursor.model cursor.depth source.indexed count word
  produced : Future.produce cursor.model cursor.depth source.indexed count word = .inr receipt
  session : Future.Recovery.Micro.Session pricing (Future.Recovery.begin receipt)
structure Reporting (cursor : Online.Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (source : Future.Recovery.SameCodeTarget cursor.model) (count : Nat) where
  private mk ::
  word : Word cursor
  tail : List (Word cursor)
  cached : List (Entry cursor pricing source count)
  coherent : cached.map Sigma.fst++word::tail = Future.Recovery.capabilities cursor.model cursor.depth
  receipt : Future.Receipt cursor.model cursor.depth source.indexed count word
  produced : Future.produce cursor.model cursor.depth source.indexed count word = .inr receipt
  execution : Future.Recovery.Stepper.Execution pricing (Future.Recovery.begin receipt)
  made : Future.Recovery.Output receipt
  generated : made = execution.output receipt
  fields : Future.Recovery.Assessment.Fields.Cursor made cursor.depth
structure Financing (cursor : Online.Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (source : Future.Recovery.SameCodeTarget cursor.model) (count : Nat) where
  private mk ::
  word : Word cursor
  tail : List (Word cursor)
  cached : List (Entry cursor pricing source count)
  coherent : cached.map Sigma.fst++word::tail = Future.Recovery.capabilities cursor.model cursor.depth
  receipt : Future.Receipt cursor.model cursor.depth source.indexed count word
  produced : Future.produce cursor.model cursor.depth source.indexed count word = .inr receipt
  execution : Future.Recovery.Stepper.Execution pricing (Future.Recovery.begin receipt)
  made : Future.Recovery.Output receipt
  generated : made = execution.output receipt
  fields : Future.Recovery.Assessment.Fields.Completed made cursor.depth
  funding : Future.Recovery.Funding.Source.Cursor made.walk
inductive Cursor (cursor : Online.Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (source : Future.Recovery.SameCodeTarget cursor.model) (count : Nat) where
  | ready (state : Ready cursor pricing source count)
  | recovering (state : Recovering cursor pricing source count)
  | reporting (state : Reporting cursor pricing source count)
  | financing (state : Financing cursor pricing source count)
def initial : Cursor cursor pricing source count := .ready ⟨Future.Recovery.capabilities cursor.model cursor.depth,[],rfl⟩
variable {cursor pricing source count}
def Cursor.remaining : Cursor cursor pricing source count → List (Word cursor)
  | .ready state => state.remaining
  | .recovering state => state.word::state.tail
  | .reporting state => state.word::state.tail
  | .financing state => state.word::state.tail
def Cursor.cached : Cursor cursor pricing source count → List (Entry cursor pricing source count)
  | .ready state => state.cached
  | .recovering state => state.cached
  | .reporting state => state.cached
  | .financing state => state.cached
noncomputable def Cursor.rank : Cursor cursor pricing source count → Nat
  | .ready state => listCost cursor pricing source count state.remaining
  | .recovering state => state.session.rank+reportCost cursor pricing state.receipt+fundingCost cursor pricing state.receipt+3+listCost cursor pricing source count state.tail
  | .reporting state => state.fields.rank+fundingCost cursor pricing state.receipt+2+listCost cursor pricing source count state.tail
  | .financing state => state.funding.rank+1+listCost cursor pricing source count state.tail
inductive Event (cursor : Online.Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (source : Future.Recovery.SameCodeTarget cursor.model) (count : Nat) where
  | begin (word : Word cursor) (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
      (produced : Future.produce cursor.model cursor.depth source.indexed count word = .inr receipt)
  | advance (word : Word cursor) (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
      (before after : Future.Recovery.Micro.Session pricing (Future.Recovery.begin receipt))
      (event : Future.Recovery.Micro.Event (old := cursor.model) (oldDepth := cursor.depth) (word := word))
      (actual : before.move = some (event,after))
  | beginReport (word : Word cursor) (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
      (execution : Future.Recovery.Stepper.Execution pricing (Future.Recovery.begin receipt))
      (made : Future.Recovery.Output receipt) (generated : made = execution.output receipt)
  | field (word : Word cursor) (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
      (made : Future.Recovery.Output receipt)
      (before after : Future.Recovery.Assessment.Fields.Cursor made cursor.depth)
      (event : Future.Recovery.Assessment.Fields.Event made cursor.depth)
      (actual : before.move = some (event,after))
  | beginFunding (word : Word cursor) (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
      (made : Future.Recovery.Output receipt) (fields : Future.Recovery.Assessment.Fields.Completed made cursor.depth)
  | funding (word : Word cursor) (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
      (made : Future.Recovery.Output receipt)
      (before after : Future.Recovery.Funding.Source.Cursor made.walk)
      (event : Future.Recovery.Funding.Source.Event (old := cursor.model) (oldDepth := cursor.depth) (word := word))
      (actual : before.move = some (event,after))
  | emit (entry : Entry cursor pricing source count)
def Row.rejected (word : Word cursor)
    (reason : PLift (¬ Mandate.Replay.Legal (base := cursor.model.base) cursor.model.scope (Authority.currentAt cursor.model cursor.depth) word))
    (produced : Future.produce cursor.model cursor.depth source.indexed count word = .inl reason) : Row cursor pricing source count word :=
  let outcome : Outcome cursor source count word := .rejected reason
  ⟨outcome,by unfold generate;rw [produced],outcome.value,rfl,.rejected reason⟩
def Row.recovered (word : Word cursor) (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
    (produced : Future.produce cursor.model cursor.depth source.indexed count word = .inr receipt)
    (execution : Future.Recovery.Stepper.Execution pricing (Future.Recovery.begin receipt)) : Row cursor pricing source count word :=
  let outcome : Outcome cursor source count word := .recovered receipt (execution.output receipt)
  ⟨outcome,by
    unfold generate;rw [produced]
    dsimp only [outcome]
    simp only [Future.Recovery.Stepper.Execution.output_exact],outcome.value,rfl,.recovered receipt execution⟩
def Row.reported (word : Word cursor) (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
    (produced : Future.produce cursor.model cursor.depth source.indexed count word = .inr receipt)
    (execution : Future.Recovery.Stepper.Execution pricing (Future.Recovery.begin receipt))
    (made : Future.Recovery.Output receipt) (generated : made = execution.output receipt)
    (fields : Future.Recovery.Assessment.Fields.Completed made cursor.depth) : Row cursor pricing source count word :=
  let outcome : Outcome cursor source count word := .recovered receipt made
  ⟨outcome,by
    unfold generate;rw [produced];dsimp only [outcome]
    rw [generated];simp only [Future.Recovery.Stepper.Execution.output_exact],
    some (Future.Recovery.Assessment.Fields.report made cursor.depth source.property fields,
      Future.Recovery.Funding.ofWalk made.walk),by
        dsimp only [outcome,Outcome.value]
        rw [Future.Recovery.Assessment.Fields.report_exact],
    .reported receipt execution made generated fields⟩
def Row.funded (word : Word cursor) (receipt : Future.Receipt cursor.model cursor.depth source.indexed count word)
    (produced : Future.produce cursor.model cursor.depth source.indexed count word = .inr receipt)
    (execution : Future.Recovery.Stepper.Execution pricing (Future.Recovery.begin receipt))
    (made : Future.Recovery.Output receipt) (generated : made = execution.output receipt)
    (fields : Future.Recovery.Assessment.Fields.Completed made cursor.depth)
    (funding : Future.Recovery.Funding.Source.Completed made.walk) : Row cursor pricing source count word :=
  let outcome : Outcome cursor source count word := .recovered receipt made
  ⟨outcome,by
    unfold generate;rw [produced];dsimp only [outcome]
    rw [generated];simp only [Future.Recovery.Stepper.Execution.output_exact],
    some (Future.Recovery.Assessment.Fields.report made cursor.depth source.property fields,funding.value),by
      dsimp only [outcome,Outcome.value]
      rw [Future.Recovery.Assessment.Fields.report_exact,funding.exact_value],
    .funded receipt execution made generated fields funding⟩
def Cursor.move : Cursor cursor pricing source count → Option (Event cursor pricing source count × Cursor cursor pricing source count)
  | .ready state => match actual : state.remaining with
    | [] => none
    | head::tail => match produced : Future.produce cursor.model cursor.depth source.indexed count head with
      | .inl reason =>
          let made : Entry cursor pricing source count := ⟨head,Row.rejected head reason produced⟩
          some (.emit made,.ready ⟨tail,state.cached++[made],by
            have known := state.coherent;rw [actual] at known
            simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using known⟩)
      | .inr receipt => some (.begin head receipt produced,.recovering ⟨head,tail,state.cached,by
          have known := state.coherent;rw [actual] at known;exact known,
          receipt,produced,Future.Recovery.Micro.Session.initial pricing (Future.Recovery.begin receipt)⟩)
  | .recovering state => match done : state.session.completed with
    | some execution =>
        let made := execution.output state.receipt
        some (.beginReport state.word state.receipt execution made rfl,
          .reporting ⟨state.word,state.tail,state.cached,state.coherent,state.receipt,state.produced,
            execution,made,rfl,Future.Recovery.Assessment.Fields.initial made cursor.depth⟩)
    | none => match moved : state.session.move with
      | none => False.elim (by
          have complete := (Future.Recovery.Micro.Session.completed_iff_stopped state.session).mpr moved
          rw [done] at complete;cases complete)
      | some (event,next) => some (.advance state.word state.receipt state.session next event moved,
          .recovering ⟨state.word,state.tail,state.cached,state.coherent,state.receipt,state.produced,next⟩)
  | .reporting state => match done : state.fields.completed with
    | some collected => some (.beginFunding state.word state.receipt state.made collected,
        .financing ⟨state.word,state.tail,state.cached,state.coherent,state.receipt,state.produced,
          state.execution,state.made,state.generated,collected,Future.Recovery.Funding.Source.initial state.made.walk⟩)
    | none => match moved : state.fields.move with
      | none => False.elim (by
          have complete := (Window.Report.Manifest.Cursor.completed_iff_stopped state.fields).mpr moved
          rw [done] at complete;cases complete)
      | some (event,next) => some (.field state.word state.receipt state.made state.fields next event moved,
          .reporting ⟨state.word,state.tail,state.cached,state.coherent,state.receipt,state.produced,
            state.execution,state.made,state.generated,next⟩)
  | .financing state => match done : state.funding.completed with
    | some collected =>
        let made : Entry cursor pricing source count := ⟨state.word,Row.funded state.word state.receipt state.produced
          state.execution state.made state.generated state.fields collected⟩
        some (.emit made,.ready ⟨state.tail,state.cached++[made],by
          simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.singleton_append] using state.coherent⟩)
    | none => match moved : state.funding.move with
      | none => False.elim (by
          have complete := (Future.Recovery.Funding.Source.Cursor.completed_iff_stopped state.funding).mpr moved
          rw [done] at complete;cases complete)
      | some (event,next) => some (.funding state.word state.receipt state.made state.funding next event moved,
          .financing ⟨state.word,state.tail,state.cached,state.coherent,state.receipt,state.produced,
            state.execution,state.made,state.generated,state.fields,next⟩)
structure Completed (cursor : Online.Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
    (source : Future.Recovery.SameCodeTarget cursor.model) (count : Nat) where
  private mk ::
  items : List (Entry cursor pricing source count)
  exact_keys : items.map Sigma.fst = Future.Recovery.capabilities cursor.model cursor.depth
def Cursor.completed : Cursor cursor pricing source count → Option (Completed cursor pricing source count)
  | .recovering _ => none
  | .reporting _ => none
  | .financing _ => none
  | .ready state => match actual : state.remaining with
    | [] => some ⟨state.cached,by simpa only [actual,List.append_nil] using state.coherent⟩
    | _::_ => none
theorem initial_rank : (initial cursor pricing source count).rank = capacity cursor pricing source count := rfl
theorem Cursor.move_decreases {before after : Cursor cursor pricing source count} {event : Event cursor pricing source count}
    (actual : before.move = some (event,after)) : after.rank+1 = before.rank := by
  cases before with
  | ready state =>
    rcases state with ⟨remaining,cached,coherent⟩
    cases remaining with
    | nil => cases actual
    | cons head tail =>
      dsimp only [Cursor.move] at actual
      split at actual
      · rename_i reason produced
        cases actual
        simp only [Cursor.rank,listCost,List.map_cons,List.sum_cons,wordCost,produced];omega
      · rename_i receipt produced
        cases actual
        simp only [Cursor.rank,Future.Recovery.Micro.Session.initial_rank,listCost,List.map_cons,List.sum_cons,wordCost,produced]
        omega
  | recovering state =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i execution done
      cases actual
      have zero := (Future.Recovery.Micro.Session.stopped_iff_zero state.session).mp
        ((Future.Recovery.Micro.Session.completed_iff_stopped _).mp (by rw [done];rfl))
      have fieldsRank : (Future.Recovery.Assessment.Fields.initial (execution.output state.receipt) cursor.depth).rank =
          reportCost cursor pricing state.receipt := by
        rw [Future.Recovery.Assessment.Fields.initial_rank,Future.Recovery.Stepper.Execution.output_exact];rfl
      simp only [Cursor.rank,zero,fieldsRank];omega
    · rename_i done
      split at actual
      · rename_i stopped
        have complete := (Future.Recovery.Micro.Session.completed_iff_stopped state.session).mpr stopped
        rw [done] at complete;cases complete
      · rename_i event next moved
        cases actual
        have decrease := Future.Recovery.Micro.Session.move_decreases moved
        dsimp only [Cursor.rank];omega
  | reporting state =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i collected done
      cases actual
      have zero := (Window.Report.Manifest.Cursor.stopped_iff_zero state.fields).mp
        ((Window.Report.Manifest.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
      have fundingRank : (Future.Recovery.Funding.Source.initial state.made.walk).rank =
          fundingCost cursor pricing state.receipt := by
        rw [Future.Recovery.Funding.Source.initial_rank,state.generated,Future.Recovery.Stepper.Execution.output_exact];rfl
      simp only [Cursor.rank,zero,fundingRank];omega
    · rename_i done
      split at actual
      · rename_i stopped
        have complete := (Window.Report.Manifest.Cursor.completed_iff_stopped state.fields).mpr stopped
        rw [done] at complete;cases complete
      · rename_i event next moved
        cases actual
        have decrease := Window.Report.Manifest.Cursor.move_decreases moved
        dsimp only [Cursor.rank];omega
  | financing state =>
    dsimp only [Cursor.move] at actual
    split at actual
    · rename_i collected done
      cases actual
      have zero := (Future.Recovery.Funding.Source.Cursor.stopped_iff_zero state.funding).mp
        ((Future.Recovery.Funding.Source.Cursor.completed_iff_stopped _).mp (by rw [done];rfl))
      simp only [Cursor.rank,zero];omega
    · rename_i done
      split at actual
      · rename_i stopped
        have complete := (Future.Recovery.Funding.Source.Cursor.completed_iff_stopped state.funding).mpr stopped
        rw [done] at complete;cases complete
      · rename_i event next moved
        cases actual
        have decrease := Future.Recovery.Funding.Source.Cursor.move_decreases moved
        dsimp only [Cursor.rank];omega
theorem Cursor.completed_iff_stopped (state : Cursor cursor pricing source count) : state.completed.isSome = true ↔ state.move = none := by
  cases state with
  | ready state =>
    rcases state with ⟨remaining,cached,coherent⟩;cases remaining with
    | nil => simp [Cursor.completed,Cursor.move]
    | cons head tail =>
      dsimp only [Cursor.completed,Cursor.move]
      split <;> simp
  | recovering state =>
    dsimp only [Cursor.completed,Cursor.move]
    split
    · simp
    · rename_i done
      split
      · rename_i stopped
        have complete := (Future.Recovery.Micro.Session.completed_iff_stopped state.session).mpr stopped
        rw [done] at complete;cases complete
      · simp
  | reporting state =>
    dsimp only [Cursor.completed,Cursor.move]
    split
    · simp
    · rename_i done
      split
      · rename_i stopped
        have complete := (Window.Report.Manifest.Cursor.completed_iff_stopped state.fields).mpr stopped
        rw [done] at complete;cases complete
      · simp
  | financing state =>
    dsimp only [Cursor.completed,Cursor.move]
    split
    · simp
    · rename_i done
      split
      · rename_i stopped
        have complete := (Future.Recovery.Funding.Source.Cursor.completed_iff_stopped state.funding).mpr stopped
        rw [done] at complete;cases complete
      · simp
theorem Cursor.stopped_iff_zero (state : Cursor cursor pricing source count) : state.move = none ↔ state.rank = 0 := by
  cases state with
  | ready state =>
    rcases state with ⟨remaining,cached,coherent⟩;cases remaining with
    | nil => simp [Cursor.move,Cursor.rank,listCost]
    | cons head tail =>
      have notStopped : Cursor.move (Cursor.ready ⟨head::tail,cached,coherent⟩) ≠ none := by
        intro stopped
        have complete := (Cursor.completed_iff_stopped _).mpr stopped
        cases complete
      have positive := wordCost_positive cursor pricing source count head
      have notZero : Cursor.rank (Cursor.ready ⟨head::tail,cached,coherent⟩) ≠ 0 := by
        change wordCost cursor pricing source count head+listCost cursor pricing source count tail ≠ 0
        omega
      exact iff_of_false notStopped notZero
  | recovering state =>
    have notStopped : Cursor.move (Cursor.recovering state) ≠ none := by
      intro stopped
      have complete := (Cursor.completed_iff_stopped _).mpr stopped;cases complete
    have notZero : Cursor.rank (Cursor.recovering state) ≠ 0 := by dsimp only [Cursor.rank];omega
    exact iff_of_false notStopped notZero
  | reporting state =>
    have notStopped : Cursor.move (Cursor.reporting state) ≠ none := by
      intro stopped
      have complete := (Cursor.completed_iff_stopped _).mpr stopped;cases complete
    have notZero : Cursor.rank (Cursor.reporting state) ≠ 0 := by dsimp only [Cursor.rank];omega
    exact iff_of_false notStopped notZero
  | financing state =>
    have notStopped : Cursor.move (Cursor.financing state) ≠ none := by
      intro stopped
      have complete := (Cursor.completed_iff_stopped _).mpr stopped;cases complete
    have notZero : Cursor.rank (Cursor.financing state) ≠ 0 := by dsimp only [Cursor.rank];omega
    exact iff_of_false notStopped notZero

def lookup (word : Word cursor) : (items : List (Entry cursor pricing source count)) → word ∈ items.map Sigma.fst → Row cursor pricing source count word
  | [],inside => False.elim (List.not_mem_nil inside)
  | head::tail,inside => if same : head.1 = word then same ▸ head.2 else
      lookup word tail (by simpa only [List.map_cons,List.mem_cons,eq_comm (a := word) (b := head.1),same,false_or] using inside)
def Completed.at (cache : Completed cursor pricing source count) (word : Word cursor)
    (inside : word ∈ Future.Recovery.capabilities cursor.model cursor.depth) : Row cursor pricing source count word :=
  lookup word cache.items (by rw [cache.exact_keys];exact inside)
-- A cache miss keeps the original source operation open; all comparison words hit.
def Completed.read (cache : Completed cursor pricing source count) (word : Word cursor) : Value cursor word :=
  if inside : word ∈ cache.items.map Sigma.fst then (lookup word cache.items inside).value
  else Whole.restoration (pricing := pricing) source count word
theorem Completed.read_exact (cache : Completed cursor pricing source count) (word : Word cursor) : cache.read word =
    Whole.restoration (pricing := pricing) source count word := by
  unfold Completed.read;split
  · exact Row.value_exact _
  · rfl
theorem Completed.read_from_cache (cache : Completed cursor pricing source count) (word : Word cursor)
    (inside : word ∈ Future.Recovery.capabilities cursor.model cursor.depth) : cache.read word = (cache.at word inside).value := by
  have found : word ∈ cache.items.map Sigma.fst := by rw [cache.exact_keys];exact inside
  simp only [Completed.read,dif_pos found,Completed.at]
theorem Completed.read_outside (cache : Completed cursor pricing source count) (word : Word cursor)
    (outside : word ∉ Future.Recovery.capabilities cursor.model cursor.depth) : cache.read word =
      Whole.restoration (pricing := pricing) source count word := by
  have absent : word ∉ cache.items.map Sigma.fst := by rw [cache.exact_keys];exact outside
  exact dif_neg absent
theorem Completed.cached_future (cache : Completed cursor pricing source count) (word : Word cursor)
    (inside : word ∈ Future.Recovery.capabilities cursor.model cursor.depth) :
    (cache.read word).map Prod.fst = (cache.at word inside).value.map Prod.fst := by rw [cache.read_from_cache word inside]
theorem Completed.cached_funding (cache : Completed cursor pricing source count) (word : Word cursor)
    (inside : word ∈ Future.Recovery.capabilities cursor.model cursor.depth) :
    (cache.read word).bind Prod.snd = (cache.at word inside).value.bind Prod.snd := by rw [cache.read_from_cache word inside]

inductive History : Cursor cursor pricing source count → Cursor cursor pricing source count → List (Event cursor pricing source count) → Prop
  | nil (before) : History before before []
  | step {before middle after event work} (actual : before.move = some (event,middle))
      (later : History middle after work) : History before after (event::work)
structure Run (before : Cursor cursor pricing source count) (capacity : Nat) where
  private mk ::
  endpoint : Cursor cursor pricing source count
  work : List (Event cursor pricing source count)
  history : History before endpoint work
  covered : work.length ≤ capacity
  exhausted : endpoint.move = none ∨ work.length = capacity
  conservation : endpoint.rank+work.length = before.rank

def run : (capacity : Nat) → (before : Cursor cursor pricing source count) → Run before capacity
  | 0,before => ⟨before,[],.nil before,Nat.le_refl _,Or.inr rfl,by simp⟩
  | capacity+1,before => match actual : before.move with
    | none => ⟨before,[],.nil before,by simp,Or.inl actual,by simp⟩
    | some (event,next) =>
        let later := run capacity next
        ⟨later.endpoint,event::later.work,.step actual later.history,by have := later.covered;simp only [List.length_cons];omega,
          later.exhausted.imp_right (fun same => by simp only [List.length_cons,same]),by
            have := later.conservation;have := Cursor.move_decreases actual;simp only [List.length_cons];omega⟩

theorem run_sufficient (before : Cursor cursor pricing source count) (capacity : Nat) (enough : before.rank ≤ capacity) :
    (run capacity before).endpoint.completed.isSome = true := by
  apply (Cursor.completed_iff_stopped _).mpr
  rcases (run capacity before).exhausted with stopped | full
  · exact stopped
  apply (Cursor.stopped_iff_zero _).mpr
  have := (run capacity before).conservation;omega

theorem run_work_exact (before : Cursor cursor pricing source count) (available : Nat) :
    (run available before).work.length = min available before.rank := by
  have covered := (run available before).covered
  have conserved := (run available before).conservation
  rcases (run available before).exhausted with stopped | full
  · have zero := (Cursor.stopped_iff_zero _).mp stopped
    rw [zero] at conserved
    have same : (run available before).work.length = before.rank := by omega
    rw [same,Nat.min_eq_right (by omega)]
  · rw [full,Nat.min_eq_left (by omega)]
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Restoration
