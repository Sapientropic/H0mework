import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Work
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Plan
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Scan

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (allocation : List Allocation) (announcements : List (Rule model.source.code))

abbrev Cache := Work model domain original reference worker receiver quote (globalQuotas allocation) announcements
abbrev GlobalCache := Sparse.Cache model domain original reference worker quote (globalQuotas allocation)

/-- The original slot ordinal survives unpaid gaps. Its actual receipt is reused
    for qualification only when its global quota is zero. -/
structure Payment (rival : Opponent model.source.code) where
  before : View (code := model.source.code)
  ordinal : Nat
  quota : Nat
  assigned : allocation[ordinal]? = some (0,quota)
  receipt : Charge.paid quote model worker before rival (Charge.endAt quote model worker before rival)

def applyPayment {rival : Opponent model.source.code}
    (cache : Option (Cache model domain original reference worker receiver quote allocation announcements))
    (payment : Payment model worker quote allocation rival) :
    Option (Cache model domain original reference worker receiver quote allocation announcements) :=
  some (advance model domain original reference worker receiver quote (globalQuotas allocation) announcements payment.quota
    (cache.getD (initial model domain original reference worker receiver quote (globalQuotas allocation) announcements)))

def replayPayments {rival : Opponent model.source.code}
    (cache : Option (Cache model domain original reference worker receiver quote allocation announcements))
    (payments : List (Payment model worker quote allocation rival)) :=
  payments.foldl (applyPayment model domain original reference worker receiver quote allocation announcements) cache

structure Observation (rival : Opponent model.source.code) (start : Nat)
    (prior : Option (Cache model domain original reference worker receiver quote allocation announcements)) where
  cached : Option (Cache model domain original reference worker receiver quote allocation announcements)
  payments : List (Payment model worker quote allocation rival)
  replayed : cached = replayPayments model domain original reference worker receiver quote allocation announcements prior payments
  ordered : payments.Pairwise (fun first second => first.ordinal < second.ordinal)
  afterStart : ∀ payment ∈ payments,start ≤ payment.ordinal

variable (rival : Opponent model.source.code)

private def Observation.weaken {first second : Nat}
    {prior : Option (Cache model domain original reference worker receiver quote allocation announcements)}
    (observed : Observation model domain original reference worker receiver quote allocation announcements rival second prior)
    (earlier : first ≤ second) : Observation model domain original reference worker receiver quote allocation announcements rival first prior :=
  ⟨observed.cached,observed.payments,observed.replayed,observed.ordered,
    fun payment inside => earlier.trans (observed.afterStart payment inside)⟩

/-- The fold follows every physical scan node, not its filtered payment list. -/
def observe {before : View (code := model.source.code)}
    {global : Option (GlobalCache model domain original reference worker quote allocation)} {jobs : List Nat}
    (execution : Sparse.Scan model domain original reference worker quote (globalQuotas allocation) rival before global jobs)
    (remaining : List Allocation) (aligned : remaining.map Prod.fst = jobs)
    (index : Nat) (source : allocation.drop index = remaining)
    (prior : Option (Cache model domain original reference worker receiver quote allocation announcements)) :
    Observation model domain original reference worker receiver quote allocation announcements rival index prior :=
  match execution with
  | .empty .. | .stopped .. => ⟨prior,[],rfl,by simp,by simp⟩
  | .next before global quota rest _ later =>
    match remaining with
    | [] => False.elim (by cases aligned)
    | assignment :: remaining =>
      have tailAligned : remaining.map Prod.fst = rest := (List.cons.inj aligned).2
      have nextSource : allocation.drop (index+1) = remaining := by
        simpa only [List.drop_drop,List.drop_succ_cons,List.drop_zero] using congrArg (List.drop 1) source
      if idle : assignment.1 = 0 then
        if positive : assignment.2 ≠ 0 then
          match seen : (Charge.read quote model worker before rival (Charge.endAt quote model worker before rival)).1 with
          | some (.accepted checked) =>
            let payment : Payment model worker quote allocation rival :=
              ⟨before,index,assignment.2,by
                have headAt := congrArg List.head? source
                have here : allocation[index]? = some assignment := by
                  simpa only [List.head?_drop,List.head?_cons] using headAt
                exact here.trans (congrArg some (Prod.ext idle rfl)),
                ⟨checked,seen⟩⟩
            let next := observe later remaining tailAligned (index+1) nextSource
              (applyPayment model domain original reference worker receiver quote allocation announcements prior payment)
            ⟨next.cached,payment::next.payments,next.replayed,
              List.pairwise_cons.mpr ⟨fun other inside => by
                have bounded := next.afterStart other inside
                change index < other.ordinal
                omega,next.ordered⟩,by
              intro other inside
              rcases List.mem_cons.mp inside with same | later
              · subst other;exact Nat.le_refl _
              · exact (Nat.le_succ index).trans (next.afterStart other later)⟩
          | _ => Observation.weaken model domain original reference worker receiver quote allocation announcements rival
            (observe later remaining tailAligned (index+1) nextSource prior) (Nat.le_succ index)
        else Observation.weaken model domain original reference worker receiver quote allocation announcements rival
            (observe later remaining tailAligned (index+1) nextSource prior) (Nat.le_succ index)
      else Observation.weaken model domain original reference worker receiver quote allocation announcements rival
            (observe later remaining tailAligned (index+1) nextSource prior) (Nat.le_succ index)

variable (point : View (code := model.source.code))
abbrev execution := Sparse.trace model domain original reference worker quote (globalQuotas allocation) point rival
def observed := observe model domain original reference worker receiver quote allocation announcements rival
  (execution model domain original reference worker quote allocation rival point) allocation rfl 0 rfl none

theorem the_qualification_cache_replays_only_distinct_original_paid_slots :
    let paid := observed model domain original reference worker receiver quote allocation announcements rival point
    paid.cached = replayPayments model domain original reference worker receiver quote allocation announcements none paid.payments ∧
      paid.payments.Pairwise (fun first second => first.ordinal < second.ordinal) ∧
      ∀ payment ∈ paid.payments,allocation[payment.ordinal]? = some (0,payment.quota) ∧
        Charge.paid quote model worker payment.before rival (Charge.endAt quote model worker payment.before rival) := by
  exact ⟨(observed model domain original reference worker receiver quote allocation announcements rival point).replayed,
    (observed model domain original reference worker receiver quote allocation announcements rival point).ordered,
    fun payment _ => ⟨payment.assigned,payment.receipt⟩⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified
