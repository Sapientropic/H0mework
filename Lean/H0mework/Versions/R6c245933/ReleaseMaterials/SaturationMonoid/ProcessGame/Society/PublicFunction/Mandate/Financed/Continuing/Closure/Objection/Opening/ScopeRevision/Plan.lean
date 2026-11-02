import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Review

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Followup

variable {fuel : ℚ} {inventory : Joint.Inventory fuel} (ready : Ready inventory)

def epochLaw := Mandate.law base ready.scope
def epochInitial (_ : Ready inventory) := (advance inventory).cut.past.frame.raw

def required (actor : Bool) : ℚ :=
  ((ready.task.slots.filter (fun slot => decide (slot.bearer = actor))).map
    (fun slot => Institutions.Capitalism.Universal.Source.Program.amount Good slot.goods .service)).sum + if actor = ready.actor then 4 else 0

def productionCount (current : Current) (actor : Bool) : Nat :=
  (Rat.ceil ((required ready actor - current.stock actor .service) / 3)).toNat

def provisionActor (current : Current) (actor : Bool) : List Action :=
  let count := productionCount ready current actor
  let missing := (count : ℚ) - current.stock actor .feedstock
  (if 0 < missing then
    [⟨!actor, [], .resource, [], .transfer (!actor) actor [(.feedstock, missing)]⟩] else []) ++
    List.replicate count (Exit.production actor)

def productionWord (current : Current) : List Bool → List Action
  | [] => []
  | actor :: tail =>
      let word := provisionActor ready current actor
      word ++ productionWord ((epochLaw ready).execute current 0 word).final tail

inductive Method where
  | direct | productive
  deriving DecidableEq

def Method.front (method : Method) (current : Current) : List Action :=
  match method with
  | .direct => []
  | .productive => productionWord ready current (participants inventory)

def signedPair (current : Current) : List Action :=
  let proposal := request ready.scope current ready.actor (.propose ready.actor)
  [proposal, request ready.scope ((epochLaw ready).step current proposal) ready.actor .accept]

def services : List Action := ready.task.slots.map fun slot =>
  ⟨ready.actor, [], .service, [.service], .use slot.bearer slot.goods slot.purpose⟩

def challenge : Action := ⟨ready.actor, [], .challenge, [.challenge], .present⟩

def candidate (current : Current) (method : Method) : List Action :=
  let front := method.front ready current
  let beforePair := ((epochLaw ready).execute current 0 front).final
  let serving := front ++ signedPair ready beforePair ++ services ready ++ [challenge ready]
  let beforeRevoke := ((epochLaw ready).execute current 0 serving).final
  let revoke := request ready.scope beforeRevoke ready.actor .revoke
  serving ++ [revoke, request ready.scope ((epochLaw ready).step beforeRevoke revoke) ready.actor .review]

def Pass (current : Current) (method : Method) : Prop :=
  (∀ item ∈ (epochLaw ready).rawItems current (candidate ready current method),
    (epochLaw ready).Valid item.before item.request) ∧
  ServiceAdequate (epochLaw ready) current ready.task (candidate ready current method)

instance (current : Current) (method : Method) : Decidable (Pass ready current method) := by
  unfold Pass
  infer_instance

def methods : List Method := [.direct, .productive]

structure Paid (current : Current) where
  private mk ::
  method : Method
  legal : Pass ready current method

def select (current : Current) : Option (Paid ready current) :=
  match selected : methods.find? (fun method => decide (Pass ready current method)) with
  | some method => some ⟨method, of_decide_eq_true
      (List.find?_some (p := fun method => decide (Pass ready current method)) selected)⟩
  | none => none

def epochWord (current : Current) :=
  candidate ready current ((select ready current).map Paid.method |>.getD .productive)

theorem selected_word_really_pays_the_generated_task (current : Current) (paid : Paid ready current)
    (selected : select ready current = some paid) :
    (∀ item ∈ (epochLaw ready).rawItems current (epochWord ready current), (epochLaw ready).Valid item.before item.request) ∧
    ServiceAdequate (epochLaw ready) current ready.task (epochWord ready current) := by
  simpa only [epochWord, selected, Option.map_some, Option.getD_some, Pass] using paid.legal

theorem blocked_menu_has_concrete_failed_checks (current : Current) (blocked : select ready current = none) :
    ∀ method ∈ methods, ¬ Pass ready current method := by
  unfold select at blocked
  split at blocked
  · cases blocked
  · rename_i absent
    intro method inside paid
    have denied := List.find?_eq_none.mp absent method inside
    rw [decide_eq_true paid] at denied
    exact denied rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision
