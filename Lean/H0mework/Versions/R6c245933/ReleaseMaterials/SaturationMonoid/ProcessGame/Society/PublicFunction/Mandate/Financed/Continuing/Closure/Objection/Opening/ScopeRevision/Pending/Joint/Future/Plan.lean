import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Settlement.Native

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup
variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (ready : Ready old)

inductive Intent where
  | admission | challenge | exit | revision | renewal
  deriving DecidableEq

inductive Method where
  | direct | productive | supplied | financed
  deriving DecidableEq

structure Choice where
  actor : Bool
  method : Method
  deriving DecidableEq

def sponsor := (Mandate.Response.firstMember ready.scope).val

def Eligible (intent : Intent) (before : Current) : Prop :=
  match intent with
  | .admission => before.technology.holder = none ∧ before.technology.offered = none ∧ before.clock ≤ ready.task.deadline
  | .challenge => Mandate.Response.Active before
  | .exit => before.technology.holder.isSome = true
  | .revision => True
  | .renewal => before.technology.holder.isSome = true ∧ before.clock ≤ ready.task.deadline

instance (intent : Intent) (before : Current) : Decidable (Eligible ready intent before) := by
  unfold Eligible Mandate.Response.Active
  cases intent <;> infer_instance

def actors (intent : Intent) (before : Current) : List Bool :=
  match intent with
  | .exit | .renewal => [before.technology.holder.getD (sponsor ready)]
  | .challenge => [sponsor ready]
  | _ => (Delegation.members ready.scope.task).eraseDups

def fallback (intent : Intent) (before : Current) : Choice :=
  ⟨match intent with | .exit | .renewal => before.technology.holder.getD (sponsor ready) | _ => sponsor ready,
    if before.clock ≤ ready.task.deadline then .productive else .direct⟩

def menu (intent : Intent) (before : Current) : List Choice :=
  [.direct, .productive, .supplied, .financed].flatMap (fun method =>
    (actors ready intent before).map fun actor => ⟨actor, method⟩) ++ [fallback ready intent before]

def provision (before : Current) (actor : Bool) : List Action :=
  let missing := 1 - before.stock actor .feedstock
  (if 0 < missing then [⟨!actor, [], .resource, [], .transfer (!actor) actor [(.feedstock, missing)]⟩] else []) ++
    [Exit.production actor]

def funding (before : Current) (actor : Bool) (required : ℚ) : List Action :=
  let missing := required - before.stock actor .service
  if 0 < missing then
    [⟨actor, [], .resource, [], .issue () actor (!actor) missing⟩,
     ⟨!actor, [], .resource, [], .transfer (!actor) actor [(.service, missing)]⟩]
  else []

def pairFront (before : Current) (actor : Bool) (method : Method) : List Action :=
  match method with
  | .direct => []
  | .productive => [Exit.production (sponsor ready)] ++ if actor = sponsor ready then [] else [Exit.production actor]
  | .supplied =>
      let first := provision before (sponsor ready)
      first ++ if actor = sponsor ready then [] else provision ((epochLaw ready).execute before 0 first).final actor
  | .financed =>
      let first := funding before (sponsor ready) (if actor = sponsor ready then 2 else 1)
      first ++ if actor = sponsor ready then [] else funding ((epochLaw ready).execute before 0 first).final actor 1

def front (intent : Intent) (before : Current) (choice : Choice) : List Action :=
  match intent with
  | .admission | .renewal => pairFront ready before choice.actor choice.method
  | .challenge => []
  | .exit | .revision => match choice.method with
    | .direct => []
    | .productive => [Exit.production choice.actor]
    | .supplied => provision before choice.actor
    | .financed => funding before choice.actor 1

def signature (actor : Bool) : Action := ⟨actor, [], ready.scope.challenge, [ready.scope.challenge], .present⟩

def commands (intent : Intent) (before : Current) (actor : Bool) : List Action :=
  match intent with
  | .admission | .renewal =>
      let proposal := request ready.scope before (sponsor ready) (.propose actor)
      let after := (epochLaw ready).step before proposal
      let acceptance := request ready.scope after actor (if intent = .admission then .accept else .renew)
      [proposal, acceptance, signature ready actor]
  | .challenge => [signature ready actor]
  | .exit => [signature ready actor, request ready.scope before actor .exit]
  | .revision => [request ready.scope before actor .review, signature ready actor]

def candidate (intent : Intent) (before : Current) (choice : Choice) :=
  let first := front ready intent before choice
  first ++ commands ready intent ((epochLaw ready).execute before 0 first).final choice.actor

def Legal (intent : Intent) (before : Current) (choice : Choice) : Prop :=
  Eligible ready intent before ∧
    ∀ item ∈ (epochLaw ready).rawItems before (candidate ready intent before choice),
      (epochLaw ready).Valid item.before item.request

instance (intent : Intent) (before : Current) (choice : Choice) : Decidable (Legal ready intent before choice) := by
  unfold Legal; infer_instance

structure Paid (intent : Intent) (before : Current) where
  private mk ::
  choice : Choice
  listed : choice ∈ menu ready intent before
  legal : Legal ready intent before choice

def choose (intent : Intent) (before : Current) : Option (Paid ready intent before) :=
  match selected : (menu ready intent before).find? (fun choice => decide (Legal ready intent before choice)) with
  | some choice => some ⟨choice, List.mem_of_find?_eq_some selected,
      of_decide_eq_true (List.find?_some (p := fun choice => decide (Legal ready intent before choice)) selected)⟩
  | none => none

def selected (intent : Intent) (before : Current) :=
  ((choose ready intent before).map Paid.choice).getD (fallback ready intent before)

def core (intent : Intent) (before : Current) := candidate ready intent before (selected ready intent before)

theorem selected_is_generated (intent : Intent) (before : Current) : selected ready intent before ∈ menu ready intent before := by
  unfold selected
  cases found : choose ready intent before with
  | some paid => exact paid.listed
  | none => exact List.mem_append_right _ (List.mem_singleton_self _)

theorem no_selected_choice_has_escaped_its_actual_check (intent : Intent) (before : Current)
    (blocked : choose ready intent before = none) :
    ∀ choice ∈ menu ready intent before, ¬ Legal ready intent before choice := by
  unfold choose at blocked
  split at blocked
  · cases blocked
  · rename_i absent
    intro choice inside accepted
    have denied := List.find?_eq_none.mp absent choice inside
    rw [decide_eq_true accepted] at denied
    exact denied rfl

theorem an_eligible_blocked_core_has_an_actual_refused_item (intent : Intent) (before : Current)
    (eligible : Eligible ready intent before) (blocked : choose ready intent before = none) :
    ∃ item ∈ (epochLaw ready).rawItems before (core ready intent before), ¬ (epochLaw ready).Valid item.before item.request := by
  by_contra absent
  apply no_selected_choice_has_escaped_its_actual_check ready intent before blocked _ (selected_is_generated ready intent before)
  refine ⟨eligible, ?_⟩
  intro item member
  by_contra refused
  exact absent ⟨item, member, refused⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Future
