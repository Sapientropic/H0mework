import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Source
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Payment
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {position ordinal proposed : Nat}

def Claim (pool : List (Offer (prepared := prepared) (position := position))) (reference candidate : Offer (prepared := prepared) (position := position)) : Prop :=
  ResponsibilityLe pool candidate reference ∧ ∀ other ∈ pool,¬(ResponsibilityLe pool other candidate ∧ ¬ResponsibilityLe pool candidate other)

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
    (reading : Reading prepared budget outerOverride position) (cache : Computation.Collection.Completed reading.opened.audit)
    (reference candidate : Offer (prepared := reading.opened.funding.installed) (position := position)) where
  private mk ::
  run : Query.Run (Query.initial (Source.verify cache.items reference candidate)) reading.remaining
  generated : run = Query.run reading.remaining (Query.initial (Source.verify cache.items reference candidate))

inductive Verdict {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {reference candidate : Offer (prepared := reading.opened.funding.installed) (position := position)} (session : Session reading cache reference candidate) where
  | pending (actual : session.run.endpoint.completed = none)
  | rejected (no : ¬Claim cache.items reference candidate) (actual : session.run.endpoint.completed = some (.isFalse no))
  | accepted (yes : Claim cache.items reference candidate) (actual : session.run.endpoint.completed = some (.isTrue yes))

def review {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {reference candidate : Offer (prepared := reading.opened.funding.installed) (position := position)} (session : Session reading cache reference candidate) : Verdict session :=
  match actual : session.run.endpoint.completed with
  | none => .pending actual
  | some (.isTrue yes) => .accepted yes actual
  | some (.isFalse no) => .rejected no actual

theorem Session.pending_exhausts_actual_capacity {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    {reading : Reading prepared budget outerOverride position} {cache : Computation.Collection.Completed reading.opened.audit}
    {reference candidate : Offer (prepared := reading.opened.funding.installed) (position := position)} (session : Session reading cache reference candidate)
    (actual : session.run.endpoint.completed = none) : session.run.work.length = reading.remaining := by
  rcases session.run.exhausted with stopped | exhausted
  · have completed := (Query.State.completed_iff_stopped session.run.endpoint).mpr stopped
    rw [actual] at completed;cases completed
  · exact exhausted

def acceptedRefinement {after : Prepared input} {audit : CrossFee.Result after position} (cache : Computation.Collection.Completed audit)
    (reference candidate : Offer (prepared := after) (position := position)) (listed : candidate ∈ cache.items)
    (yes : Claim cache.items reference candidate) : Choice.Refined cache.items reference :=
  Choice.refinementOfVerified cache.items reference candidate listed (decide_eq_true yes)

theorem accepted_is_original_full_verification {after : Prepared input} {audit : CrossFee.Result after position}
    (cache : Computation.Collection.Completed audit) (reference candidate : Offer (prepared := after) (position := position))
    (yes : Claim cache.items reference candidate) : Choice.verify (Pool.collect audit) reference candidate = true := by
  rw [←cache.exact];exact decide_eq_true yes

inductive Decision {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (ordinal proposed : Nat) where
  | reading (pending : reading.run.endpoint.completed = none)
  | noReference (cache : Computation.Collection.Completed reading.opened.audit) (generated : reading.run.endpoint.completed = some cache)
      (absent : cache.items[ordinal]? = none)
  | noCandidate (cache : Computation.Collection.Completed reading.opened.audit) (generated : reading.run.endpoint.completed = some cache)
      (reference : Offer (prepared := reading.opened.funding.installed) (position := position)) (located : cache.items[ordinal]? = some reference)
      (absent : cache.items[proposed]? = none)
  | checked (cache : Computation.Collection.Completed reading.opened.audit) (generated : reading.run.endpoint.completed = some cache)
      (reference candidate : Offer (prepared := reading.opened.funding.installed) (position := position))
      (located : cache.items[ordinal]? = some reference) (proposal : cache.items[proposed]? = some candidate)
      (session : Session reading cache reference candidate) (result : Verdict session)

def decideReading {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (reading : Reading prepared budget outerOverride position) (ordinal proposed : Nat) : Decision reading ordinal proposed :=
  match cached : reading.run.endpoint.completed with
  | none => .reading cached
  | some cache => match located : cache.items[ordinal]? with
    | none => .noReference cache cached located
    | some reference => match proposal : cache.items[proposed]? with
      | none => .noCandidate cache cached reference located proposal
      | some candidate =>
          let session : Session reading cache reference candidate := ⟨Query.run reading.remaining (Query.initial (Source.verify cache.items reference candidate)),rfl⟩
          .checked cache cached reference candidate located proposal session (review session)

inductive Result (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (outerOverride : Option Nat) (position ordinal proposed : Nat) where
  | empty (absent : prepared.saved = [])
  | unpaid (funding : EscrowBudget.Funding prepared budget.units) (generated : funding = EscrowBudget.reserve prepared budget.units)
      (index : Index prepared) (failed : ¬(funding.resultAt index).funded)
  | zero (funding : EscrowBudget.Funding prepared budget.units) (generated : funding = EscrowBudget.reserve prepared budget.units)
      (paid : ∀ index : Index prepared,(funding.resultAt index).funded) (zero : budget.units = 0)
  | generated (reading : Reading prepared budget outerOverride position) (decision : Decision reading ordinal proposed)

def generateFor (prepared : Prepared input) (budget : CandidateRuntime.BudgetChoice prepared) (outerOverride : Option Nat)
    (position ordinal proposed : Nat) : Result prepared budget outerOverride position ordinal proposed :=
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
        .generated reading (decideReading reading ordinal proposed)

def generate (prepared : Prepared input) (position ordinal proposed : Nat) :=
  generateFor prepared (CandidateRuntime.budgetFor prepared none) none position ordinal proposed

namespace Decision
variable {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat} {reading : Reading prepared budget outerOverride position}
def extraWork : Decision reading ordinal proposed → Nat
  | .checked _ _ _ _ _ _ session _ => session.run.work.length
  | _ => 0
def spent (decision : Decision reading ordinal proposed) := reading.run.work.length+decision.extraWork
def unused (decision : Decision reading ordinal proposed) := budget.units-decision.spent
theorem covered (decision : Decision reading ordinal proposed) : decision.spent ≤ budget.units := by
  have base := reading.run.covered
  cases decision with
  | reading _ => exact base
  | noReference _ _ _ => exact base
  | noCandidate _ _ _ _ _ => exact base
  | checked cache generated reference candidate located proposal session result =>
      have := session.run.covered
      dsimp only [spent,extraWork,Reading.remaining] at *;omega

theorem conservation (decision : Decision reading ordinal proposed) : decision.spent+decision.unused = budget.units := by
  have := decision.covered;dsimp only [unused];omega

def slot (decision : Decision reading ordinal proposed) (index : Index prepared) (event : Fin decision.spent) :
    Fin (((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).bill.units) :=
  ⟨event.val,by rw [((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).size];exact event.isLt.trans_le decision.covered⟩
theorem slots_are_distinct (decision : Decision reading ordinal proposed) (index : Index prepared) : Function.Injective (decision.slot index) := by
  intro left right same;have values := congrArg Fin.val same;exact Fin.ext values

def cacheSlot (decision : Decision reading ordinal proposed) (index : Index prepared) (event : Fin reading.run.work.length) :=
  decision.slot index ⟨event.val,event.isLt.trans_le (Nat.le_add_right _ _)⟩
def querySlot (decision : Decision reading ordinal proposed) (index : Index prepared) (event : Fin decision.extraWork) :=
  decision.slot index ⟨reading.run.work.length+event.val,Nat.add_lt_add_left event.isLt _⟩
theorem cache_and_query_slots_disjoint (decision : Decision reading ordinal proposed) (index : Index prepared)
    (cache : Fin reading.run.work.length) (query : Fin decision.extraWork) : decision.cacheSlot index cache ≠ decision.querySlot index query := by
  intro same;have values := congrArg Fin.val same
  change cache.val = reading.run.work.length+query.val at values
  have := cache.isLt;omega

theorem original_invoice_is_successful (_decision : Decision reading ordinal proposed) (index : Index prepared) :
    ((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).bill.payment.succeeded = true :=
  ((reading.opened.funding.resultAt index).invoice (reading.opened.paid index)).paid

noncomputable def next {Payload : Type} (payload : Payload) (decision : Decision reading ordinal proposed) (index : Index prepared) : AuthorityCurrent :=
  match decision with
  | .reading _ | .noReference .. => Choice.retainedNext payload reading.opened.audit
      (Choice.afterIndex reading.opened.audit (Automatic.paidIndex reading.opened.funding index))
  | .noCandidate _ _ reference .. => reference.next payload (Automatic.paidIndex reading.opened.funding index)
  | .checked _ _ reference candidate _ _ _ result => match result with
    | .accepted .. => candidate.next payload (Automatic.paidIndex reading.opened.funding index)
    | .pending .. | .rejected .. => reference.next payload (Automatic.paidIndex reading.opened.funding index)
end Decision

noncomputable def Result.next {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (result : Result prepared budget outerOverride position ordinal proposed) (index : Index prepared) : AuthorityCurrent :=
  match result with
  | .empty _ =>
      let cursor := Policy.Protocol.retained prepared.saved[index].stage
      originalNext cursor (Computation.Payment.law result cursor)
  | .unpaid funding .. | .zero funding .. =>
      let cursor := Policy.Protocol.retained funding.installed.saved[Automatic.paidIndex funding index].stage
      originalNext cursor (Computation.Payment.law result cursor)
  | .generated _ decision => decision.next result index

-- Independent proposal verification does not discharge automatic selection or primitive internals.
def Result.pending {budget : CandidateRuntime.BudgetChoice prepared} {outerOverride : Option Nat}
    (_result : Result prepared budget outerOverride position ordinal proposed) : List Choice.Debt := Choice.computationDebts

structure Activation (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal proposed : Nat) (point : NativePoint input) where
  private mk ::
  preparation : Prepared input
  prepared_generated : preparation = Policy.prepare input
  budget : CandidateRuntime.BudgetChoice preparation
  budget_generated : budget = CandidateRuntime.budgetFor preparation feeOverride
  result : Result preparation budget outerOverride position ordinal proposed
  generated : result = generateFor preparation budget outerOverride position ordinal proposed
  bound : Binding.Linked preparation point
  bound_generated : Binding.locate preparation point = .linked bound
inductive Invocation (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal proposed : Nat) (point : NativePoint input) where
  | mismatch (broken : point.signal (position := input.position) input.site ≠ input.reading)
  | activated (made : Activation input feeOverride outerOverride position ordinal proposed point)
def invokeWith (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal proposed : Nat) (point : NativePoint input) :
    Invocation input feeOverride outerOverride position ordinal proposed point :=
  if observed : point.signal (position := input.position) input.site = input.reading then
    let preparation := Policy.prepare input
    let budget := CandidateRuntime.budgetFor preparation feeOverride
    let result := generateFor preparation budget outerOverride position ordinal proposed
    match linked : Binding.locate preparation point with
    | .linked bound => .activated ⟨preparation,rfl,budget,rfl,result,rfl,bound,linked⟩
    | .mismatch broken => False.elim (broken observed)
  else .mismatch observed

def invoke (input : Input seed) (position ordinal proposed : Nat) (point : NativePoint input) : Invocation input none none position ordinal proposed point :=
  invokeWith input none none position ordinal proposed point
noncomputable def Activation.next {feeOverride outerOverride : Option Nat} {point : NativePoint input}
    (made : Activation input feeOverride outerOverride position ordinal proposed point) : AuthorityCurrent := made.result.next made.bound.index

theorem every_matching_actual_point_is_activated (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal proposed : Nat) (point : NativePoint input)
    (observed : point.signal (position := input.position) input.site = input.reading) :
    ∃ made : Activation input feeOverride outerOverride position ordinal proposed point,invokeWith input feeOverride outerOverride position ordinal proposed point = .activated made := by
  unfold invokeWith;rw [dif_pos observed];dsimp only
  split
  · exact ⟨_,rfl⟩
  · rename_i broken actual;exact False.elim (broken observed)
theorem mismatched_observation_is_rejected (input : Input seed) (feeOverride outerOverride : Option Nat) (position ordinal proposed : Nat) (point : NativePoint input)
    (broken : point.signal (position := input.position) input.site ≠ input.reading) :
    invokeWith input feeOverride outerOverride position ordinal proposed point = .mismatch broken := by simp only [invokeWith,dif_neg broken]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Choice.Computation.Query.Payment
