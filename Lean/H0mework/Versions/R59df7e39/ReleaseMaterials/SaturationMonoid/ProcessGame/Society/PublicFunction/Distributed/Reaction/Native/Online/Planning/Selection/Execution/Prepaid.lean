import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Settlement
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {seed : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {driver : Feedback.Input seed.source.code}
  (cursor : Cursor seed driver) (pricing : Future.Recovery.Pricing (Future.Recovery.Action cursor.model))
  (n : Nat) (reference : Term cursor)

def reindex (word : List (Future.Recovery.Action cursor.model)) : Term (cursor.submit word) :=
  ⟨reference.val,by change reference.val ∈ controls cursor;exact reference.property⟩

/-- One native material reservation, scaled from the registered unit bundle.
    It is generated raw work, rather than a request for market approval. -/
def scaled (fee : Future.Recovery.Action cursor.model) (units : Nat) : Future.Recovery.Action cursor.model :=
  match fee.operation with
  | .use bearer bundle .external =>
      {fee with operation := .use bearer (bundle.map fun entry => (entry.1,(units:ℚ)*entry.2)) .external}
  | _ => fee

abbrev baseUnits := workBudget cursor pricing n
abbrev probeInvoice (fee : Future.Recovery.Action cursor.model) := [scaled cursor fee (baseUnits cursor pricing n)]
abbrev probePayment (fee : Future.Recovery.Action cursor.model) :=
  Mandate.Replay.compile cursor.model.base cursor.model.scope cursor.state.current (probeInvoice cursor pricing n fee)
abbrev probePoint (fee : Future.Recovery.Action cursor.model) := cursor.submit (probePayment cursor pricing n fee).output

def probeFees := cursor.source.val.code.actions.filter (fun fee => decide (IsWorkFee cursor fee.signer fee))
private def maximum : List Nat → Nat
  | [] => 0
  | head::tail => max head (maximum tail)
private theorem le_maximum (values : List Nat) (value : Nat) (inside : value ∈ values) : value ≤ maximum values := by
  induction values with
  | nil => simp at inside
  | cons head tail ih =>
    rcases List.mem_cons.mp inside with same | later
    · subst value;exact Nat.le_max_left _ _
    · exact (ih later).trans (Nat.le_max_right _ _)

/-- Probe each registered owner-only physical invoice before choosing its reservation.
    The actual postpayment budget is still checked on its own source below. -/
def units := max (baseUnits cursor pricing n)
  (maximum ((probeFees cursor).map (fun fee => workBudget (probePoint cursor pricing n fee) pricing n)))

theorem initial_work_budget_is_reserved : workBudget cursor pricing n ≤ units cursor pricing n := Nat.le_max_left _ _
theorem every_registered_probe_budget_is_reserved (fee : Future.Recovery.Action cursor.model) (inside : fee ∈ probeFees cursor) :
    workBudget (probePoint cursor pricing n fee) pricing n ≤ units cursor pricing n :=
  (le_maximum ((probeFees cursor).map (fun item => workBudget (probePoint cursor pricing n item) pricing n))
    (workBudget (probePoint cursor pricing n fee) pricing n) (List.mem_map.mpr ⟨fee,inside,rfl⟩)).trans (Nat.le_max_right _ _)

theorem a_registered_owner_fee_has_a_source_probe (actor : Party) (position : Nat)
    (fee : Future.Recovery.Action cursor.model) (registered : feeAt cursor actor position = some fee) : fee ∈ probeFees cursor := by
  unfold feeAt at registered
  split at registered
  · contradiction
  · rename_i listed lookup
    split at registered
    · rename_i valid
      have same := Option.some.inj registered
      subst listed
      apply List.mem_filter.mpr
      refine ⟨List.mem_of_getElem? lookup,?_⟩
      apply decide_eq_true
      simpa only [valid.1] using valid
    · contradiction
abbrev invoice (fee : Future.Recovery.Action cursor.model) := [scaled cursor fee (units cursor pricing n)]
abbrev payment (fee : Future.Recovery.Action cursor.model) :=
  Mandate.Replay.compile cursor.model.base cursor.model.scope cursor.state.current (invoice cursor pricing n fee)
abbrev point (fee : Future.Recovery.Action cursor.model) := cursor.submit (payment cursor pricing n fee).output
abbrev paidReference (fee : Future.Recovery.Action cursor.model) :=
  reindex cursor reference (payment cursor pricing n fee).output
abbrev required (fee : Future.Recovery.Action cursor.model) := workBudget (point cursor pricing n fee) pricing n

inductive Result (actor : Party) (position : Nat) where
  | unpriced (absent : feeAt cursor actor position = none)
  | refused (fee : Future.Recovery.Action cursor.model) (registered : feeAt cursor actor position = some fee)
      (unpaid : (payment cursor pricing n fee).succeeded = false)
  | shortfall (fee : Future.Recovery.Action cursor.model) (registered : feeAt cursor actor position = some fee)
      (paid : (payment cursor pricing n fee).succeeded = true)
      (lacks : units cursor pricing n < required cursor pricing n fee)
  | ready (fee : Future.Recovery.Action cursor.model) (registered : feeAt cursor actor position = some fee)
      (paid : (payment cursor pricing n fee).succeeded = true)
      (covered : required cursor pricing n fee ≤ units cursor pricing n)
      (compilation : Compilation (point cursor pricing n fee) pricing n (paidReference cursor pricing n reference fee))
      (compiled : compilation = compile (point cursor pricing n fee) pricing n (paidReference cursor pricing n reference fee))

def produce (actor : Party) (position : Nat) : Result cursor pricing n reference actor position :=
  match registered : feeAt cursor actor position with
  | none => .unpriced registered
  | some fee =>
    if paid : (payment cursor pricing n fee).succeeded = true then
      if covered : required cursor pricing n fee ≤ units cursor pricing n then
        .ready fee registered paid covered
          (compile (point cursor pricing n fee) pricing n (paidReference cursor pricing n reference fee)) rfl
      else .shortfall fee registered paid (Nat.lt_of_not_ge covered)
    else .refused fee registered (Bool.eq_false_iff.mpr paid)

structure Protocol (actor : Party) (position : Nat) where
  private mk ::
  result : Result cursor pricing n reference actor position
  generated : result = produce cursor pricing n reference actor position

def invoke (actor : Party) (position : Nat) : Protocol cursor pricing n reference actor position :=
  ⟨produce cursor pricing n reference actor position,rfl⟩

/-- These computations have not been priced by the explicit instruction bound. -/
inductive Pending (stage : Cursor seed driver) where
  | setup (actor : Party) (position : Nat)
  | quote (pricing : Future.Recovery.Pricing (Future.Recovery.Action stage.model)) (horizon : Nat)
  | invoiceProbe (pricing : Future.Recovery.Pricing (Future.Recovery.Action stage.model)) (horizon : Nat)
      (fee : Future.Recovery.Action stage.model) (reservation : Nat)
  | native (query : Query stage)

def probePending : List (Sigma fun stage : Cursor seed driver => Pending stage) :=
  (probeFees cursor).map (fun fee => ⟨cursor,.invoiceProbe pricing n fee (baseUnits cursor pricing n)⟩)

namespace Result
variable {cursor pricing n reference} {actor : Party} {position : Nat}
  (made : Result cursor pricing n reference actor position)

def status : Nat := match made with | .unpriced .. => 0 | .refused .. => 1 | .shortfall .. => 2 | .ready .. => 3

def planning : Cursor seed driver := match made with
  | .unpriced .. => cursor
  | .refused fee .. | .shortfall fee .. | .ready fee .. => point cursor pricing n fee

def endpoint : Cursor seed driver := match made with
  | .ready fee _ _ _ compilation _ => match compilation.result with
    | .selected choice => execute (point cursor pricing n fee) choice.policy.term n
    | .blocked _ => point cursor pricing n fee
  | _ => made.planning

def work : List (Sigma fun stage : Cursor seed driver => Operation stage) := match made with
  | .ready fee _ _ _ compilation _ =>
    (checkedWork (point cursor pricing n fee) pricing n compilation).map (fun operation => ⟨point cursor pricing n fee,operation⟩)
  | _ => []

def pending : List (Sigma fun stage : Cursor seed driver => Pending stage) :=
  ⟨cursor,.setup actor position⟩ :: match made with
  | .unpriced .. => []
  | .refused .. => [⟨cursor,.quote pricing n⟩] ++ probePending cursor pricing n
  | .shortfall fee .. => [⟨cursor,.quote pricing n⟩] ++ probePending cursor pricing n ++ [⟨point cursor pricing n fee,.quote pricing n⟩]
  | .ready fee _ _ _ compilation _ =>
      [⟨cursor,.quote pricing n⟩] ++ probePending cursor pricing n ++ [⟨point cursor pricing n fee,.quote pricing n⟩] ++
      (nativeObligations (point cursor pricing n fee) (checkedWork (point cursor pricing n fee) pricing n compilation)).map
        (fun query => ⟨point cursor pricing n fee,.native query⟩)
end Result

namespace Protocol
variable {cursor pricing n reference} {actor : Party} {position : Nat}
  (made : Protocol cursor pricing n reference actor position)
abbrev endpoint := made.result.endpoint
abbrev planning := made.result.planning
abbrev work := made.result.work
abbrev pending := made.result.pending
end Protocol

theorem every_ready_selection_fits_the_already_paid_instruction_budget
    {actor : Party} {position : Nat} (fee : Future.Recovery.Action cursor.model)
    (_registered : feeAt cursor actor position = some fee) (_paid : (payment cursor pricing n fee).succeeded = true)
    (covered : required cursor pricing n fee ≤ units cursor pricing n)
    (compilation : Compilation (point cursor pricing n fee) pricing n (paidReference cursor pricing n reference fee))
    (compiled : compilation = compile (point cursor pricing n fee) pricing n (paidReference cursor pricing n reference fee)) :
    controlSteps (point cursor pricing n fee) (checkedWork (point cursor pricing n fee) pricing n compilation) ≤ units cursor pricing n := by
  rw [compiled]
  exact (complete_selection_verification_and_rejection_fit_the_generated_budget _ _ _ _).trans covered

theorem payment_is_an_actual_source_event (fee : Future.Recovery.Action cursor.model) :
    ((point cursor pricing n fee).source.val.actualExecution cursor.depth).submitted = (payment cursor pricing n fee).output :=
  cursor.submit_is_the_actual_word _

theorem a_paid_reservation_consumes_its_generated_material_invoice (fee : Future.Recovery.Action cursor.model)
    (paid : (payment cursor pricing n fee).succeeded = true) :
    (payment cursor pricing n fee).consumed = invoice cursor pricing n fee := by
  have split := (payment cursor pricing n fee).original_split
  have empty := Future.Recovery.Search.no_residual_after_success cursor.model (payment cursor pricing n fee) paid
  simpa only [empty,List.append_nil] using split

theorem reindex_preserves_the_source_term (fee : Future.Recovery.Action cursor.model) :
    (paidReference cursor pricing n reference fee).val = reference.val := rfl

theorem reservation_keeps_the_original_opponent_budget (fee : Future.Recovery.Action cursor.model) :
    (point cursor pricing n fee).state.remaining = cursor.state.remaining := rfl
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid
