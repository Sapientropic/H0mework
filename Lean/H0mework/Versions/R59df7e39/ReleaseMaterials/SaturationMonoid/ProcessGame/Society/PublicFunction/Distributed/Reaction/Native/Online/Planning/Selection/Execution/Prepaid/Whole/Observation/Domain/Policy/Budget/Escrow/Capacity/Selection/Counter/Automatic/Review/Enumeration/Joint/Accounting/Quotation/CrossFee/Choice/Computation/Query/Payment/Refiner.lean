import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Refiner
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Payment.Refiner
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


structure Session {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (cache : Computation.Collection.Completed reading.opened.audit) (ordinal : Nat) where
  private mk ::
  run : Query.Run (Query.initial (Query.Refiner.program cache.items ordinal)) reading.remaining
  generated : run = Query.run reading.remaining (Query.initial (Query.Refiner.program cache.items ordinal))

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
    session.run.work.length = reading.remaining := by
  rcases session.run.exhausted with stopped | exhausted
  · have completed := (Query.State.completed_iff_stopped session.run.endpoint).mpr stopped
    rw [actual] at completed;cases completed
  · exact exhausted

theorem Session.sufficient_completes {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {ordinal : Nat} (session : Session reading cache ordinal)
    (enough : (Query.initial (Query.Refiner.program cache.items ordinal)).rank ≤ reading.remaining) :
    session.run.endpoint.completed.isSome = true := by
  rw [session.generated];exact Query.run_sufficient _ _ enough

inductive Decision {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (ordinal : Nat) where
  | reading (pending : reading.run.endpoint.completed = none)
  | running (cache : Computation.Collection.Completed reading.opened.audit) (generated : reading.run.endpoint.completed = some cache)
      (session : Session reading cache ordinal) (outcome : Outcome session)

def decideReading {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (ordinal : Nat) : Decision reading ordinal :=
  match cached : reading.run.endpoint.completed with
  | none => .reading cached
  | some cache =>
      let session : Session reading cache ordinal := ⟨Query.run reading.remaining (Query.initial (Query.Refiner.program cache.items ordinal)),rfl⟩
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
def extraWork : Decision reading ordinal → Nat
  | .running _ _ session _ => session.run.work.length
  | _ => 0
def spent (decision : Decision reading ordinal) := reading.run.work.length+decision.extraWork
def unused (decision : Decision reading ordinal) := budget.units-decision.spent

theorem covered (decision : Decision reading ordinal) : decision.spent ≤ budget.units := by
  have base := reading.run.covered
  cases decision with
  | reading _ => exact base
  | running cache generated session outcome =>
      have := session.run.covered
      dsimp only [spent,extraWork,Reading.remaining] at *;omega

theorem conservation (decision : Decision reading ordinal) : decision.spent+decision.unused = budget.units := by
  have := decision.covered;dsimp only [unused];omega

def slot (decision : Decision reading ordinal) (index : Index prepared) (event : Fin decision.spent) :
    Fin (((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).bill.units) :=
  ⟨event.val,by rw [((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).size];exact event.isLt.trans_le decision.covered⟩
theorem slots_are_distinct (decision : Decision reading ordinal) (index : Index prepared) : Function.Injective (decision.slot index) := by
  intro left right same;have values := congrArg Fin.val same;exact Fin.ext values

def cacheSlot (decision : Decision reading ordinal) (index : Index prepared) (event : Fin reading.run.work.length) :=
  decision.slot index ⟨event.val,event.isLt.trans_le (Nat.le_add_right _ _)⟩
def querySlot (decision : Decision reading ordinal) (index : Index prepared) (event : Fin decision.extraWork) :=
  decision.slot index ⟨reading.run.work.length+event.val,Nat.add_lt_add_left event.isLt _⟩
theorem cache_and_query_slots_disjoint (decision : Decision reading ordinal) (index : Index prepared)
    (cache : Fin reading.run.work.length) (query : Fin decision.extraWork) : decision.cacheSlot index cache ≠ decision.querySlot index query := by
  intro same;have values := congrArg Fin.val same
  change cache.val = reading.run.work.length+query.val at values
  have := cache.isLt;omega

theorem original_invoice_is_successful (_decision : Decision reading ordinal) (index : Index prepared) :
    ((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).bill.payment.succeeded = true :=
  ((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).paid

noncomputable def next {Payload : Type} (payload : Payload) (decision : Decision reading ordinal) (index : Index prepared) : AuthorityCurrent :=
  match decision with
  | .reading _ => Choice.retainedNext payload reading.opened.audit
      (Choice.afterIndex reading.opened.audit (Automatic.paidIndex reading.opened.funding index))
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

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Payment.Refiner
