import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.PaidOpening

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (ready : Ready bound inputs)

def law := Mandate.law base ready.scope
def initial (_ : Ready bound inputs) := after bound inputs

def required (actor : Bool) : ℚ :=
  ((ready.task.slots.filter fun slot => decide (slot.bearer = actor)).map
    (fun slot => Institutions.Capitalism.Universal.Source.Program.amount Good slot.goods .service)).sum +
      if actor = ready.actor then 4 else 0

def productionCount (before : Current) (actor : Bool) : Nat :=
  (Rat.ceil ((required ready actor - before.stock actor .service) / 3)).toNat

def provisionActor (before : Current) (actor : Bool) : List Action :=
  let count := productionCount ready before actor
  let missing := (count : ℚ) - before.stock actor .feedstock
  (if 0 < missing then [⟨!actor, [], .resource, [], .transfer (!actor) actor [(.feedstock,missing)]⟩] else []) ++
    List.replicate count (Exit.production actor)

def productionWord (before : Current) : List Bool → List Action
  | [] => []
  | actor :: tail =>
      let word := provisionActor ready before actor
      word ++ productionWord ((law ready).execute before 0 word).final tail

def affordableProduction (before : Current) (actor : Bool) : Nat → List Action
  | 0 => []
  | count + 1 => if (law ready).Valid before (Exit.production actor) then
      Exit.production actor :: affordableProduction ((law ready).step before (Exit.production actor)) actor count
    else []

def affordableWord (before : Current) : List Bool → List Action
  | [] => []
  | actor :: tail =>
      let word := affordableProduction ready before actor (productionCount ready before actor)
      word ++ affordableWord ((law ready).execute before 0 word).final tail

def financing (before : Current) : List Bool → List Action
  | [] => []
  | actor :: tail =>
      let word := Future.funding before actor (required ready actor)
      word ++ financing ((law ready).execute before 0 word).final tail

inductive Method where
  | direct | productive | financed | reserved
  deriving DecidableEq

def financedFront (before : Current) : List Action :=
  let word := affordableWord ready before ready.actors
  word ++ financing ready ((law ready).execute before 0 word).final ready.actors

def reserveStart (before : Current) := ((law ready).execute before 0 (financedFront ready before)).final

def reserveFront (before : Current) : List Action :=
  financedFront ready before ++ Future.provision (reserveStart ready before) ready.actor

def Method.front (method : Method) (before : Current) : List Action :=
  match method with
  | .direct => []
  | .productive => productionWord ready before ready.actors
  | .financed => financedFront ready before
  | .reserved => reserveFront ready before

def signedPair (before : Current) : List Action :=
  let proposal := request ready.scope before ready.actor (.propose ready.actor)
  [proposal, request ready.scope ((law ready).step before proposal) ready.actor .accept]

def services : List Action := ready.task.slots.map fun slot =>
  ⟨ready.actor, [], .service, [.service], .use slot.bearer slot.goods slot.purpose⟩

def challenger : Bool := (ready.actors.find? (fun actor => decide (actor ≠ ready.actor))).getD ready.actor

def challenge : Action := ⟨challenger ready, [], .challenge, [.challenge], .present⟩

def ExitEnvelope (current : Current) : Prop :=
  1 ≤ current.stock false .service + current.stock true .service ∨
    1 ≤ current.stock false .feedstock + current.stock true .feedstock

instance (current : Current) : Decidable (ExitEnvelope current) := by unfold ExitEnvelope; infer_instance

def MaterialHealthy (current : Current) : Prop := ∀ actor good, 0 ≤ current.stock actor good

instance (current : Current) : Decidable (MaterialHealthy current) :=
  decidable_of_iff (0 ≤ current.stock false .feedstock ∧ 0 ≤ current.stock false .service ∧
    0 ≤ current.stock true .feedstock ∧ 0 ≤ current.stock true .service) (by
      constructor
      · intro values actor good
        cases actor <;> cases good
        · exact values.1
        · exact values.2.1
        · exact values.2.2.1
        · exact values.2.2.2
      · intro values
        exact ⟨values false .feedstock,values false .service,values true .feedstock,values true .service⟩)

def serviceWord (before : Current) (method : Method) : List Action :=
  let first := method.front ready before
  let serving := first ++ signedPair ready ((law ready).execute before 0 first).final ++ services ready ++ [challenge ready]
  let last := ((law ready).execute before 0 serving).final
  let withdraw := request ready.scope last ready.actor .exit
  serving ++ [withdraw, request ready.scope ((law ready).step last withdraw) ready.actor .review]

-- This continuation acts on the actual paid prefix; a failed supply remains a raw refusal.
def restoreExit (before : Current) : List Action :=
  if ExitEnvelope before then [] else Future.provision before ready.actor

def candidate (before : Current) (method : Method) : List Action :=
  let word := serviceWord ready before method
  word ++ restoreExit ready ((law ready).execute before 0 word).final

def Pass (before : Current) (method : Method) : Prop :=
  (∀ item ∈ (law ready).rawItems before (candidate ready before method), (law ready).Valid item.before item.request) ∧
    ServiceAdequate (law ready) before ready.task (candidate ready before method) ∧
    (decodePaidOpening ready before (candidate ready before method)).isSome = true ∧
    MaterialHealthy before

instance (before : Current) (method : Method) : Decidable (Pass ready before method) := by unfold Pass; infer_instance

-- When direct payment lacks a reserve, create liquid exit supplies before spending on the task.
def methods : List Method := [.direct,.reserved,.productive,.financed]

structure Paid (before : Current) where
  private mk ::
  method : Method
  listed : method ∈ methods
  pass : Pass ready before method

def select (before : Current) : Option (Paid ready before) :=
  match selected : methods.find? (fun method => decide (Pass ready before method)) with
  | some method => some ⟨method, List.mem_of_find?_eq_some selected,
      of_decide_eq_true (List.find?_some (p := fun method => decide (Pass ready before method)) selected)⟩
  | none => none

def emitAt (before : Current) := candidate ready before ((select ready before).map Paid.method |>.getD .productive)

theorem selected_word_pays_the_generated_scope (before : Current) (paid : Paid ready before)
    (selected : select ready before = some paid) :
    (∀ item ∈ (law ready).rawItems before (emitAt ready before), (law ready).Valid item.before item.request) ∧
      ServiceAdequate (law ready) before ready.task (emitAt ready before) := by
  have checked : (∀ item ∈ (law ready).rawItems before (candidate ready before paid.method), (law ready).Valid item.before item.request) ∧
      ServiceAdequate (law ready) before ready.task (candidate ready before paid.method) := ⟨paid.pass.1,paid.pass.2.1⟩
  simpa only [emitAt, selected, Option.map_some, Option.getD_some] using checked

def Paid.opening (before : Current) (paid : Paid ready before) : PaidOpening ready before (candidate ready before paid.method) :=
  (decodePaidOpening ready before (candidate ready before paid.method)).get paid.pass.2.2.1

theorem selected_word_has_its_own_paid_opening (before : Current) (paid : Paid ready before)
    (selected : select ready before = some paid) : (decodePaidOpening ready before (emitAt ready before)).isSome = true := by
  have same : emitAt ready before = candidate ready before paid.method := by
    simp only [emitAt,selected,Option.map_some,Option.getD_some]
  rw [same]
  exact paid.pass.2.2.1

theorem blocked_menu_has_actual_failed_checks (before : Current) (blocked : select ready before = none) :
    ∀ method ∈ methods, ¬ Pass ready before method := by
  unfold select at blocked
  split at blocked
  · cases blocked
  · rename_i absent
    intro method member accepted
    have refused := List.find?_eq_none.mp absent method member
    rw [decide_eq_true accepted] at refused
    exact refused rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
