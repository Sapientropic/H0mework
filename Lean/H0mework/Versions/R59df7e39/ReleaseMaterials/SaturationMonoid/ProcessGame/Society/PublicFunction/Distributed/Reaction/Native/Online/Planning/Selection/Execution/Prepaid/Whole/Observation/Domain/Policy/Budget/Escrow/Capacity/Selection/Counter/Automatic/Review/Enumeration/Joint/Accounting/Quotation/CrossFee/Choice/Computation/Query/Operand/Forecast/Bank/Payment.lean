import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank.Payment
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position ordinal : Nat}

structure Opened (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (outerOverride : Option Nat) (position : Nat) where
  private mk ::
  funding : EscrowBudget.Funding prepared budget.units
  generated : funding = EscrowBudget.reserve prepared budget.units
  paid : ∀ index : Index prepared,(funding.resultAt index).funded
  positive : budget.units ≠ 0
  outer : CandidateRuntime.BudgetChoice funding.installed
  outer_generated : outer = CandidateRuntime.budgetFor funding.installed outerOverride
  audit : CrossFee.Result funding.installed position
  audit_generated : audit = CrossFee.generateFor funding.installed outer position

structure Reading (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (outerOverride : Option Nat) (position : Nat) where
  private mk ::
  opened : Opened prepared budget outerOverride position
  run : Computation.Collection.Run (Computation.Collection.initial opened.audit) budget.units
  generated : run = Computation.Collection.run budget.units (Computation.Collection.initial opened.audit)
def Reading.remaining {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) := budget.units-reading.run.work.length


structure Gathering {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (cache : Computation.Collection.Completed reading.opened.audit) where
  private mk ::
  run : Tables.Run (Tables.initial cache.items) reading.remaining
  generated : run = Tables.run reading.remaining (Tables.initial cache.items)
def Gathering.remaining {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    (gathering : Gathering reading cache) := reading.remaining-gathering.run.work.length

structure Harvesting {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (cache : Computation.Collection.Completed reading.opened.audit) where
  private mk ::
  gathering : Gathering reading cache
  tables : Tables.Completed cache.items
  tables_actual : gathering.run.endpoint.completed = some tables
  run : Bank.Run (Bank.initial tables) gathering.remaining
  generated : run = Bank.run gathering.remaining (Bank.initial tables)
def Harvesting.remaining {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    (harvesting : Harvesting reading cache) := harvesting.gathering.remaining-harvesting.run.work.length

structure Quoting {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (cache : Computation.Collection.Completed reading.opened.audit) where
  private mk ::
  gathering : Harvesting reading cache
  source : Bank.Completed gathering.tables
  source_actual : gathering.run.endpoint.completed = some source
  run : Query.Run (Query.initial (Cached.quote source)) gathering.remaining
  generated : run = Query.run gathering.remaining (Query.initial (Cached.quote source))
def Quoting.remaining {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    (quote : Quoting reading cache) := quote.gathering.remaining-quote.run.work.length

structure Sizing {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    (quote : Quoting reading cache) (quoted : {value : Nat // value = Cached.budget quote.source}) where
  private mk ::
  run : Query.Run (Query.initial (Code.atom (.natural quoted.val (quote.remaining-2)) : Code
    (Checks.Key (P := P) (G := G) (O := O) (T := T) (I := I)) (.truth (quoted.val ≤ quote.remaining-2)))) quote.remaining
  generated : run = Query.run quote.remaining (Query.initial (.atom (.natural quoted.val (quote.remaining-2))))

def allocation (available requested : Nat) (answer : Decidable (requested ≤ available-2)) : Nat :=
  match answer with | .isTrue _ => requested | .isFalse _ => available-2

theorem Sizing.completed_work {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {quote : Quoting reading cache} {quoted : {value : Nat // value = Cached.budget quote.source}}
    (sizing : Sizing quote quoted) {answer : Decidable (quoted.val ≤ quote.remaining-2)}
    (actual : sizing.run.endpoint.completed = some answer) : sizing.run.work.length = 2 := by
  have stopped := (State.completed_iff_stopped sizing.run.endpoint).mp (by rw [actual];rfl)
  have zero := (State.stopped_iff_zero sizing.run.endpoint).mp stopped
  have count := sizing.run.conservation
  rw [zero] at count
  simpa only [Query.initial,State.rank,Phase.rank,Code.cost,Kont.cost,Nat.add_zero,Nat.zero_add] using count

structure Session {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (cache : Computation.Collection.Completed reading.opened.audit) (ordinal : Nat) where
  private mk ::
  quote : Quoting reading cache
  quoted : {value : Nat // value = Cached.budget quote.source}
  quote_actual : quote.run.endpoint.completed = some quoted
  sizing : Sizing quote quoted
  answer : Decidable (quoted.val ≤ quote.remaining-2)
  sizing_actual : sizing.run.endpoint.completed = some answer
  run : Query.Run (Query.initial (Cached.program quote.source ordinal)) (allocation quote.remaining quoted.val answer)
  generated : run = Query.run (allocation quote.remaining quoted.val answer) (Query.initial (Cached.program quote.source ordinal))

inductive Outcome {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {ordinal : Nat} (session : Session reading cache ordinal) where
  | pending (actual : session.run.endpoint.completed = none)
  | absent (noReference : cache.items.length ≤ ordinal)
      (actual : session.run.endpoint.completed = some ⟨0,noReference⟩)
  | selected (slot : Nat) (yes : Query.Refiner.Claim cache.items ordinal (slot+1))
      (actual : session.run.endpoint.completed = some ⟨slot+1,yes⟩)

def finish {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {ordinal : Nat} (session : Session reading cache ordinal) : Outcome session :=
  match actual : session.run.endpoint.completed with
  | none => .pending actual
  | some ⟨0,noReference⟩ => .absent noReference actual
  | some ⟨slot+1,yes⟩ => .selected slot yes actual

theorem Session.pending_exhausts_actual_capacity {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {ordinal : Nat} (session : Session reading cache ordinal) (actual : session.run.endpoint.completed = none) :
    session.run.work.length = allocation session.quote.remaining session.quoted.val session.answer := by
  rcases session.run.exhausted with stopped | exhausted
  · have completed := (Query.State.completed_iff_stopped session.run.endpoint).mpr stopped
    rw [actual] at completed;cases completed
  · exact exhausted

theorem Session.sufficient_completes {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {ordinal : Nat} (session : Session reading cache ordinal)
    (enough : (Query.initial (Cached.program session.quote.source ordinal)).rank ≤ allocation session.quote.remaining session.quoted.val session.answer) :
    session.run.endpoint.completed.isSome = true := by
  rw [session.generated];exact Query.run_sufficient _ _ enough

theorem Session.accepted_capacity_completes {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {ordinal : Nat} (session : Session reading cache ordinal)
    (accepted : ∃ yes,session.answer = .isTrue yes) : session.run.endpoint.completed.isSome = true := by
  obtain ⟨yes,same⟩ := accepted
  apply session.sufficient_completes
  rw [same];dsimp only [allocation]
  rw [session.quoted.property]
  exact Cached.initial_rank_bound session.quote.source ordinal

inductive Decision {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (ordinal : Nat) where
  | reading (pending : reading.run.endpoint.completed = none)
  | tables (cache : Computation.Collection.Completed reading.opened.audit) (cached : reading.run.endpoint.completed = some cache)
      (gathering : Gathering reading cache) (pending : gathering.run.endpoint.completed = none)
  | bank (cache : Computation.Collection.Completed reading.opened.audit) (cached : reading.run.endpoint.completed = some cache)
      (harvesting : Harvesting reading cache) (pending : harvesting.run.endpoint.completed = none)
  | quoting (cache : Computation.Collection.Completed reading.opened.audit) (cached : reading.run.endpoint.completed = some cache)
      (quote : Quoting reading cache) (pending : quote.run.endpoint.completed = none)
  | sizing (cache : Computation.Collection.Completed reading.opened.audit) (cached : reading.run.endpoint.completed = some cache)
      (quote : Quoting reading cache) (quoted : {value : Nat // value = Cached.budget quote.source})
      (quote_actual : quote.run.endpoint.completed = some quoted) (sizing : Sizing quote quoted) (pending : sizing.run.endpoint.completed = none)
  | running (cache : Computation.Collection.Completed reading.opened.audit) (cached : reading.run.endpoint.completed = some cache)
      (session : Session reading cache ordinal) (outcome : Outcome session)

def decideReading {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (ordinal : Nat) : Decision reading ordinal :=
  match cached : reading.run.endpoint.completed with
  | none => .reading cached
  | some cache =>
      let gathering : Gathering reading cache := ⟨Tables.run reading.remaining (Tables.initial cache.items),rfl⟩
      match source_actual : gathering.run.endpoint.completed with
      | none => .tables cache cached gathering source_actual
      | some tables =>
          let harvesting : Harvesting reading cache := ⟨gathering,tables,source_actual,Bank.run gathering.remaining (Bank.initial tables),rfl⟩
          match bank_actual : harvesting.run.endpoint.completed with
          | none => .bank cache cached harvesting bank_actual
          | some source =>
              let quote : Quoting reading cache := ⟨harvesting,source,bank_actual,Query.run harvesting.remaining (Query.initial (Cached.quote source)),rfl⟩
              match quoted_actual : quote.run.endpoint.completed with
              | none => .quoting cache cached quote quoted_actual
              | some quoted =>
                  let sizing : Sizing quote quoted := ⟨Query.run quote.remaining (Query.initial (.atom (.natural quoted.val (quote.remaining-2)))),rfl⟩
                  match sized : sizing.run.endpoint.completed with
                  | none => .sizing cache cached quote quoted quoted_actual sizing sized
                  | some answer =>
                      let session : Session reading cache ordinal := ⟨quote,quoted,quoted_actual,sizing,answer,sized,
                        Query.run (allocation quote.remaining quoted.val answer) (Query.initial (Cached.program quote.source ordinal)),rfl⟩
                      .running cache cached session (finish session)

inductive Result (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (outerOverride : Option Nat) (position ordinal : Nat) where
  | empty (absent : prepared.saved = [])
  | unpaid (funding : EscrowBudget.Funding prepared budget.units) (generated : funding = EscrowBudget.reserve prepared budget.units)
      (index : Index prepared) (failed : ¬(funding.resultAt index).funded)
  | zero (funding : EscrowBudget.Funding prepared budget.units) (generated : funding = EscrowBudget.reserve prepared budget.units)
      (paid : ∀ index : Index prepared,(funding.resultAt index).funded) (zero : budget.units = 0)
  | generated (reading : Reading prepared budget outerOverride position) (decision : Decision reading ordinal)

def generateFor (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (outerOverride : Option Nat)
    (position ordinal : Nat) : Result prepared budget outerOverride position ordinal :=
  if absent : prepared.saved = [] then .empty absent else
    let funding := EscrowBudget.reserve prepared budget.units
    match Distributed.inspect (fun index : Index prepared => (funding.resultAt index).funded) (keys prepared) with
    | .rejected index _ failed => .unpaid funding rfl index failed
    | .accepted paid =>
      let every := fun index : Index prepared => paid index (List.mem_finRange index)
      if zero : budget.units = 0 then .zero funding rfl every zero else
        let outer := CandidateRuntime.budgetFor funding.installed outerOverride
        let audit := CrossFee.generateFor funding.installed outer position
        let opened : Opened prepared budget outerOverride position := ⟨funding,rfl,every,zero,outer,rfl,audit,rfl⟩
        let reading : Reading prepared budget outerOverride position := ⟨opened,Computation.Collection.run budget.units (Computation.Collection.initial audit),rfl⟩
        .generated reading (decideReading reading ordinal)

def generate (prepared : Prepared input) (position ordinal : Nat) :=
  generateFor prepared (CandidateRuntime.budgetFor prepared none) none position ordinal

namespace Decision
variable {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat} {reading : Reading prepared budget outerOverride position}
def tableWork : Decision reading ordinal → Nat
  | .tables _ _ gathering _ => gathering.run.work.length
  | .bank _ _ harvesting _ => harvesting.gathering.run.work.length
  | .quoting _ _ quote _ | .sizing _ _ quote .. => quote.gathering.gathering.run.work.length
  | .running _ _ session _ => session.quote.gathering.gathering.run.work.length
  | _ => 0
def bankWork : Decision reading ordinal → Nat
  | .bank _ _ harvesting _ => harvesting.run.work.length
  | .quoting _ _ quote _ | .sizing _ _ quote .. => quote.gathering.run.work.length
  | .running _ _ session _ => session.quote.gathering.run.work.length
  | _ => 0
def quoteWork : Decision reading ordinal → Nat
  | .quoting _ _ quote _ | .sizing _ _ quote .. => quote.run.work.length
  | .running _ _ session _ => session.quote.run.work.length
  | _ => 0
def gateWork : Decision reading ordinal → Nat
  | .sizing _ _ _ _ _ gate _ => gate.run.work.length
  | .running _ _ session _ => session.sizing.run.work.length
  | _ => 0
def selectionWork : Decision reading ordinal → Nat
  | .running _ _ session _ => session.run.work.length
  | _ => 0
def extraWork (decision : Decision reading ordinal) := decision.tableWork+decision.bankWork+decision.quoteWork+decision.gateWork+decision.selectionWork
def spent (decision : Decision reading ordinal) := reading.run.work.length+decision.extraWork
def unused (decision : Decision reading ordinal) := budget.units-decision.spent

theorem covered (decision : Decision reading ordinal) : decision.spent ≤ budget.units := by
  have base := reading.run.covered
  cases decision with
  | reading _ => simpa only [spent,extraWork,tableWork,bankWork,quoteWork,gateWork,selectionWork,Nat.add_zero] using base
  | tables cache cached gathering pending =>
      have := gathering.run.covered
      dsimp only [spent,extraWork,tableWork,bankWork,quoteWork,gateWork,selectionWork,Reading.remaining] at *;omega
  | bank cache cached harvesting pending =>
      have := harvesting.gathering.run.covered;have := harvesting.run.covered
      dsimp only [spent,extraWork,tableWork,bankWork,quoteWork,gateWork,selectionWork,Gathering.remaining,Reading.remaining] at *;omega
  | quoting cache cached quote pending =>
      have := quote.gathering.gathering.run.covered;have := quote.gathering.run.covered;have := quote.run.covered
      dsimp only [spent,extraWork,tableWork,bankWork,quoteWork,gateWork,selectionWork,Harvesting.remaining,Gathering.remaining,Reading.remaining] at *;omega
  | sizing cache cached quote quoted actual sizing pending =>
      have := quote.gathering.gathering.run.covered;have := quote.gathering.run.covered;have := quote.run.covered;have := sizing.run.covered
      dsimp only [spent,extraWork,tableWork,bankWork,quoteWork,gateWork,selectionWork,Quoting.remaining,Harvesting.remaining,Gathering.remaining,Reading.remaining] at *;omega
  | running cache cached session outcome =>
      have := session.quote.gathering.gathering.run.covered;have := session.quote.gathering.run.covered
      have := session.quote.run.covered;have := session.sizing.run.covered
      have := session.sizing.completed_work session.sizing_actual
      have := session.run.covered
      have safe : allocation session.quote.remaining session.quoted.val session.answer ≤ session.quote.remaining-2 := by
        cases session.answer with | isTrue yes => exact yes | isFalse no => exact Nat.le_refl _
      dsimp only [spent,extraWork,tableWork,bankWork,quoteWork,gateWork,selectionWork,Quoting.remaining,Harvesting.remaining,Gathering.remaining,Reading.remaining] at *;omega

theorem conservation (decision : Decision reading ordinal) : decision.spent+decision.unused = budget.units := by
  have := decision.covered;dsimp only [unused];omega

def slot (decision : Decision reading ordinal) (index : Index prepared) (event : Fin decision.spent) :
    Fin (((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).bill.units) :=
  ⟨event.val,by rw [((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).size];exact event.isLt.trans_le decision.covered⟩
theorem slots_are_distinct (decision : Decision reading ordinal) (index : Index prepared) : Function.Injective (decision.slot index) := by
  intro left right same;have values := congrArg Fin.val same;exact Fin.ext values

def workAt (decision : Decision reading ordinal) (phase : Fin 6) : Nat := match phase.val with
  | 0 => reading.run.work.length | 1 => decision.tableWork | 2 => decision.bankWork
  | 3 => decision.quoteWork | 4 => decision.gateWork | _ => decision.selectionWork
def prefixAt (decision : Decision reading ordinal) (phase : Fin 6) : Nat := match phase.val with
  | 0 => 0 | 1 => reading.run.work.length | 2 => reading.run.work.length+decision.tableWork
  | 3 => reading.run.work.length+decision.tableWork+decision.bankWork
  | 4 => reading.run.work.length+decision.tableWork+decision.bankWork+decision.quoteWork
  | _ => reading.run.work.length+decision.tableWork+decision.bankWork+decision.quoteWork+decision.gateWork

def phaseSlot (decision : Decision reading ordinal) (index : Index prepared) (phase : Fin 6) (event : Fin (decision.workAt phase)) :=
  decision.slot index ⟨decision.prefixAt phase+event.val,by
    have bounded := event.isLt
    fin_cases phase <;> simp [prefixAt,workAt,spent,extraWork] at * <;> omega⟩
theorem phases_disjoint (decision : Decision reading ordinal) (index : Index prepared) (first second : Fin 6) (different : first ≠ second)
    (a : Fin (decision.workAt first)) (b : Fin (decision.workAt second)) : decision.phaseSlot index first a ≠ decision.phaseSlot index second b := by
  intro same;have values := congrArg Fin.val same
  change decision.prefixAt first+a.val = decision.prefixAt second+b.val at values
  have aa := a.isLt;have bb := b.isLt
  fin_cases first <;> fin_cases second <;> simp [prefixAt,workAt] at * <;> omega

noncomputable def next {Payload : Type} (payload : Payload) (decision : Decision reading ordinal) (index : Index prepared) : AuthorityCurrent :=
  match decision with
  | .reading _ => Choice.retainedNext payload reading.opened.audit
      (Choice.afterIndex reading.opened.audit (Automatic.paidIndex reading.opened.funding index))
  | .tables cache .. | .bank cache .. | .quoting cache .. | .sizing cache .. => match cache.items[ordinal]? with
      | none => Choice.retainedNext payload reading.opened.audit
          (Choice.afterIndex reading.opened.audit (Automatic.paidIndex reading.opened.funding index))
      | some reference => reference.next payload (Automatic.paidIndex reading.opened.funding index)
  | .running cache _ _ outcome => match outcome with
    | .absent .. => Choice.retainedNext payload reading.opened.audit
        (Choice.afterIndex reading.opened.audit (Automatic.paidIndex reading.opened.funding index))
    | .pending .. => match cache.items[ordinal]? with
      | none => Choice.retainedNext payload reading.opened.audit
          (Choice.afterIndex reading.opened.audit (Automatic.paidIndex reading.opened.funding index))
      | some reference => reference.next payload (Automatic.paidIndex reading.opened.funding index)
    | .selected slot yes _ => (cache.items[slot]'(Query.Refiner.evidence yes).bounded).next payload (Automatic.paidIndex reading.opened.funding index)
end Decision

noncomputable def Result.next {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (result : Result prepared budget outerOverride position ordinal) (index : Index prepared) : AuthorityCurrent :=
  match result with
  | .empty _ =>
      let cursor := Policy.Protocol.retained prepared.saved[index].stage
      originalNext cursor (Computation.Payment.law result cursor)
  | .unpaid funding .. | .zero funding .. =>
      let cursor := Policy.Protocol.retained funding.installed.saved[Automatic.paidIndex funding index].stage
      originalNext cursor (Computation.Payment.law result cursor)
  | .generated _ decision => decision.next result index

-- Completion settles automatic selection; lower computation and protocol costs remain live.
def Result.pending {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (result : Result prepared budget outerOverride position ordinal) : List Choice.Debt :=
  match result with
  | .generated _ (.running _ _ _ (.absent ..)) | .generated _ (.running _ _ _ (.selected ..)) =>
      [.cacheRead,.tensorGeneration,.fullComparison,.verification,.installation,.storage,.announcement]
  | _ => Choice.computationDebts

structure Activation (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal : Nat) (point : NativePoint input) where
  private mk ::
  preparation : Prepared input
  prepared_generated : preparation = Policy.prepare input
  budget : CandidateRuntime.BudgetChoice preparation
  budget_generated : budget = CandidateRuntime.budgetFor preparation feeOverride
  result : Result preparation budget outerOverride position ordinal
  generated : result = generateFor preparation budget outerOverride position ordinal
  bound : Binding.Linked preparation point
  bound_generated : Binding.locate preparation point = .linked bound
inductive Invocation (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal : Nat) (point : NativePoint input) where
  | mismatch (broken : point.signal (position := input.position) input.site ≠ input.reading)
  | activated (made : Activation input feeOverride outerOverride position ordinal point)
def invokeWith (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal : Nat) (point : NativePoint input) :
    Invocation input feeOverride outerOverride position ordinal point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    let preparation := Policy.prepare input
    let budget := CandidateRuntime.budgetFor preparation feeOverride
    let result := generateFor preparation budget outerOverride position ordinal
    match linked : Binding.locate preparation point with
    | .linked bound => .activated ⟨preparation,rfl,budget,rfl,result,rfl,bound,linked⟩
    | .mismatch broken => False.elim (broken observed)
  else .mismatch observed

def invoke (input : Input seed) (position ordinal : Nat) (point : NativePoint input) : Invocation input none none position ordinal point :=
  invokeWith input none none position ordinal point
noncomputable def Activation.next {feeOverride outerOverride : Option Nat} {point : NativePoint input}
    (made : Activation input feeOverride outerOverride position ordinal point) : AuthorityCurrent := made.result.next made.bound.index

theorem every_matching_actual_point_is_activated (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal : Nat) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading) :
    ∃ made : Activation input feeOverride outerOverride position ordinal point,invokeWith input feeOverride outerOverride position ordinal point = .activated made := by
  unfold invokeWith;rw [dif_pos observed];dsimp only
  split
  · exact ⟨_,rfl⟩
  · rename_i broken actual;exact False.elim (broken observed)
theorem mismatched_observation_is_rejected (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal : Nat) (point : NativePoint input)
    (broken : point.signal (position := input.position) input.site ≠ input.reading) :
    invokeWith input feeOverride outerOverride position ordinal point = .mismatch broken := by simp only [invokeWith,dif_neg broken]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Operand.Forecast.Bank.Payment
