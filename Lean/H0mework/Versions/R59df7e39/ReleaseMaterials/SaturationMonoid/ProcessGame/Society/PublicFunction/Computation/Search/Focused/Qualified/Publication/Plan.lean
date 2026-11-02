import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Deployment
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Material
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Segmented.Publication.Selected

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]


variable {code : Code Party Good Port (Mandate.State Party Technology) Instrument}
private def ruleDecidableEq : DecidableEq (Prefix.Rule code) := fun first second =>
  decidable_of_iff (∀ key : code.Key,
    first.work.val key (code.key_mem key) = second.work.val key (code.key_mem key) ∧
    (first.events key (code.key_mem key)).val = (second.events key (code.key_mem key)).val) (by
    constructor
    · intro same
      have work : first.work = second.work := Subtype.ext (funext fun key => funext fun _ => (same key).1)
      have events : first.events = second.events := funext fun key => funext fun _ => Subtype.ext (same key).2
      cases first
      cases second
      cases work
      cases events
      rfl
    · intro same
      subst second
      exact fun _ => ⟨rfl,rfl⟩)
local instance : DecidableEq (Prefix.Rule code) := ruleDecidableEq

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code)) (original : Rule model.source.code)
  (reference : Program model.source.code (horizon domain)) (worker receiver : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (allocation : List Allocation) (announcements : List (Rule model.source.code)) (slots : Nat)
  (point : View (code := model.source.code)) (rival : Opponent model.source.code)
  (send : Rule model.source.code) (ordinal : Nat)

abbrev QualifiedChoice := {choice : Choice model domain original reference worker quote (globalQuotas allocation) //
  eligible model domain original reference worker receiver quote (globalQuotas allocation) announcements point send choice.policy = true}

structure Selection where
  finished : Finished model domain original reference worker receiver quote allocation announcements point rival send
  released : Deployment.available model domain original reference worker receiver quote allocation announcements point rival send ordinal = some finished
  choice : QualifiedChoice model domain original reference worker receiver quote allocation announcements point send
  selected : finished.choice = some choice
  registered : Segmented.Publication.Plan.layout model worker receiver slots = some announcements
  within : (globalQuotas allocation).length+announcements.length ≤ Segmented.Deployment.actualHorizon model point

variable (selection : Selection model domain original reference worker receiver quote allocation announcements slots point rival send ordinal)

private theorem physical :
    (Segmented.trace model domain original reference worker quote (globalQuotas allocation) point rival).final =
        (execution model domain original reference worker quote allocation rival point).final ∧
    (Segmented.trace model domain original reference worker quote (globalQuotas allocation) point rival).rules =
        (execution model domain original reference worker quote allocation rival point).rules ∧
    (Segmented.trace model domain original reference worker quote (globalQuotas allocation) point rival).remaining =
        (execution model domain original reference worker quote allocation rival point).remaining ∧
    (Segmented.trace model domain original reference worker quote (globalQuotas allocation) point rival).closingReceipt =
        (execution model domain original reference worker quote allocation rival point).closingReceipt ∧
    (Segmented.trace model domain original reference worker quote (globalQuotas allocation) point rival).payments =
        (execution model domain original reference worker quote allocation rival point).payments :=
  Sparse.Material.both_scans_have_the_same_entire_physical_prefix model domain original reference worker quote
    (globalQuotas allocation) rival _ _

private def closing : Segmented.PaidSlot model worker quote rival :=
  (execution model domain original reference worker quote allocation rival point).closingReceipt.get selection.finished.closing

private theorem closing_exact :
    (execution model domain original reference worker quote allocation rival point).closingReceipt =
      some (closing model domain original reference worker receiver quote allocation announcements slots point rival send ordinal selection) :=
  (Option.some_get selection.finished.closing).symm

private theorem publication_prefix :
    Segmented.Publication.Plan.eligible model domain original reference worker quote (globalQuotas allocation) announcements selection.choice.val.policy = true := by
  have retained := (Segmented.Publication.Reservation.eligible_iff model domain original reference worker receiver quote
    (globalQuotas allocation) announcements selection.choice.val.policy).mp (Bool.and_eq_true_iff.mp selection.choice.property).1
  apply (Segmented.Publication.Plan.eligible_iff _ _ _ _ _ _ _ _ _).mpr
  have earlier := congrArg (List.take ((globalQuotas allocation).length+announcements.length)) retained
  rw [List.take_take,Nat.min_eq_left (Nat.le_succ _)] at earlier
  have size : (Segmented.reserved model original worker quote (globalQuotas allocation) ++ announcements).length =
      (globalQuotas allocation).length+announcements.length := by simp only [Segmented.reserved,List.length_append,List.length_replicate]
  unfold Segmented.Publication.Reservation.reservedBlock at earlier
  rw [←size,List.take_append_of_le_length (Nat.le_refl _),List.take_length] at earlier
  simpa only [size] using earlier

/-- Only the shared physical occurrence is transported; the qualified/global caches stay distinct. -/
def materialPlan : Segmented.Publication.Selected.Plan model domain original reference worker receiver quote
    (globalQuotas allocation) slots point rival ordinal where
  announcements := announcements
  registered := selection.registered
  within := selection.within
  choice := selection.choice.val
  publicationPrefix := publication_prefix model domain original reference worker receiver quote allocation announcements slots point rival send ordinal selection
  complete := (physical model domain original reference worker quote allocation point rival).2.2.1.trans selection.finished.executed
  room := by simpa only [past,Segmented.reserved,List.length_replicate] using selection.finished.room
  payments := (execution model domain original reference worker quote allocation rival point).payments
  payments_exact := (physical model domain original reference worker quote allocation point rival).2.2.2.2.symm
  closing := closing model domain original reference worker receiver quote allocation announcements slots point rival send ordinal selection
  sealed := (physical model domain original reference worker quote allocation point rival).2.2.2.1.trans
    (closing_exact model domain original reference worker receiver quote allocation announcements slots point rival send ordinal selection)
  arrived := by
    rw [(physical model domain original reference worker quote allocation point rival).1]
    have released := selection.released
    unfold Deployment.available at released
    split at released
    · assumption
    · cases released

inductive Blocked where
  | unregistered (missing : Segmented.Publication.Plan.layout model worker receiver slots ≠ some announcements)
  | outsideWindow (short : ¬ (globalQuotas allocation).length+announcements.length ≤ Segmented.Deployment.actualHorizon model point)
  | notArrived (early : ¬ arrival (Deployment.paidFinal model domain original reference worker quote allocation point rival) ≤ ordinal)
  | unfinished (reason : CloseReason model domain original reference worker receiver quote allocation announcements point rival)
  | noQualifiedChoice (finished : Finished model domain original reference worker receiver quote allocation announcements point rival send)
      (released : Deployment.available model domain original reference worker receiver quote allocation announcements point rival send ordinal = some finished)
      (empty : finished.choice = none)

inductive Outcome where
  | blocked (reason : Blocked model domain original reference worker receiver quote allocation announcements slots point rival send ordinal)
  | selected (selection : Selection model domain original reference worker receiver quote allocation announcements slots point rival send ordinal)

/-- The source computes every admission, actual completion and choice; no cache is supplied. -/
def generate : Outcome model domain original reference worker receiver quote allocation announcements slots point rival send ordinal :=
  if registered : Segmented.Publication.Plan.layout model worker receiver slots = some announcements then
    if within : (globalQuotas allocation).length+announcements.length ≤ Segmented.Deployment.actualHorizon model point then
      if arrived : arrival (Deployment.paidFinal model domain original reference worker quote allocation point rival) ≤ ordinal then
        match released : Deployment.available model domain original reference worker receiver quote allocation announcements point rival send ordinal with
        | none => .blocked (.unfinished (closing_obstruction model domain original reference worker receiver quote allocation announcements point rival send (by
            simpa only [Deployment.available,if_pos arrived] using released)))
        | some finished => match selected : finished.choice with
          | none => .blocked (.noQualifiedChoice finished released selected)
          | some choice => .selected ⟨finished,released,choice,selected,registered,within⟩
      else .blocked (.notArrived arrived)
    else .blocked (.outsideWindow within)
  else .blocked (.unregistered registered)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Qualified.Publication
