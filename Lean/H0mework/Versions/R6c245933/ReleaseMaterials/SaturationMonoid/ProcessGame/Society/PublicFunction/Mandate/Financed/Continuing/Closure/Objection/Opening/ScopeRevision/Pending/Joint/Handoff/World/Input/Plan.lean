import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Effects

/-! Each actual epoch owns its future input menu. Every candidate is
checked under that epoch's current law and intermediate material states. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
abbrev Intent := Future.Intent
abbrev Choice := Future.Choice
abbrev Method := Future.Method
variable (epoch : Epoch)

def sponsor := (Mandate.Response.firstMember epoch.scope).val

def counterpart (actor : Bool) :=
  if (!actor) ∈ Delegation.members epoch.scope.task then !actor else sponsor epoch

theorem counterpart_without_other_standing (actor : Bool)
    (absent : (!actor) ∉ Delegation.members epoch.scope.task) : counterpart epoch actor = sponsor epoch := by
  exact if_neg absent

def challengeActor (before : Current) : Bool :=
  match before.technology.holder with
  | some actor => counterpart epoch actor
  | none => match before.technology.offered with
    | some actor => counterpart epoch actor
    | none => sponsor epoch

theorem challenge_actor_has_actual_standing (before : Current) :
    challengeActor epoch before ∈ Delegation.members epoch.scope.task := by
  have real (actor : Bool) : counterpart epoch actor ∈ Delegation.members epoch.scope.task := by
    unfold counterpart
    split
    · assumption
    · exact (Mandate.Response.firstMember epoch.scope).property
  unfold challengeActor
  split
  · exact real _
  · split
    · exact real _
    · exact (Mandate.Response.firstMember epoch.scope).property

def Eligible (intent : Intent) (before : Current) : Prop :=
  match intent with
  | .admission => before.technology.holder = none ∧ before.technology.offered = none ∧ before.clock ≤ epoch.scope.task.deadline
  | .challenge => Mandate.Response.Active before
  | .exit => before.technology.holder.isSome = true
  | .revision => True
  | .renewal => before.technology.holder.isSome = true ∧ before.clock ≤ epoch.scope.task.deadline

instance (intent : Intent) (before : Current) : Decidable (Eligible epoch intent before) := by
  unfold Eligible Mandate.Response.Active
  cases intent <;> infer_instance

def actors (intent : Intent) (before : Current) : List Bool :=
  match intent with
  | .exit | .renewal => [before.technology.holder.getD (sponsor epoch)]
  | .challenge => [challengeActor epoch before]
  | _ => Delegation.members epoch.scope.task

def fallback (intent : Intent) (before : Current) : Choice :=
  ⟨match intent with
    | .exit | .renewal => before.technology.holder.getD (sponsor epoch)
    | .challenge => challengeActor epoch before
    | _ => sponsor epoch,
    if before.clock ≤ epoch.scope.task.deadline then .productive else .direct⟩

def menu (intent : Intent) (before : Current) : List Choice :=
  [.direct, .productive, .supplied, .financed].flatMap (fun method =>
    (actors epoch intent before).map fun actor => ⟨actor, method⟩) ++ [fallback epoch intent before]

def pairFront (before : Current) (actor : Bool) (method : Method) : List Action :=
  match method with
  | .direct => []
  | .productive => [Exit.production (sponsor epoch)] ++ if actor = sponsor epoch then [] else [Exit.production actor]
  | .supplied =>
      let first := Future.provision before (sponsor epoch)
      first ++ if actor = sponsor epoch then [] else Future.provision ((Mandate.law base epoch.scope).execute before 0 first).final actor
  | .financed =>
      let first := Future.funding before (sponsor epoch) (if actor = sponsor epoch then 2 else 1)
      first ++ if actor = sponsor epoch then [] else Future.funding ((Mandate.law base epoch.scope).execute before 0 first).final actor 1

def front (intent : Intent) (before : Current) (choice : Choice) : List Action :=
  match intent with
  | .admission | .renewal => pairFront epoch before choice.actor choice.method
  | .challenge => []
  | .exit | .revision => match choice.method with
    | .direct => []
    | .productive => [Exit.production choice.actor]
    | .supplied => Future.provision before choice.actor
    | .financed => Future.funding before choice.actor 1

def signature (actor : Bool) : Action := ⟨actor, [], epoch.scope.challenge, [epoch.scope.challenge], .present⟩

def commands (intent : Intent) (before : Current) (actor : Bool) : List Action :=
  match intent with
  | .admission | .renewal =>
      let proposal := request epoch.scope before (sponsor epoch) (.propose actor)
      let after := (Mandate.law base epoch.scope).step before proposal
      let acceptance := request epoch.scope after actor (if intent = .admission then .accept else .renew)
      [proposal, acceptance, signature epoch actor]
  | .challenge => [signature epoch actor]
  | .exit => [signature epoch actor, request epoch.scope before actor .exit]
  | .revision => [request epoch.scope before actor .review, signature epoch actor]

def candidate (intent : Intent) (before : Current) (choice : Choice) :=
  let first := front epoch intent before choice
  first ++ commands epoch intent ((Mandate.law base epoch.scope).execute before 0 first).final choice.actor

def Legal (intent : Intent) (before : Current) (choice : Choice) : Prop :=
  Eligible epoch intent before ∧
    ∀ item ∈ (Mandate.law base epoch.scope).rawItems before (candidate epoch intent before choice),
      (Mandate.law base epoch.scope).Valid item.before item.request

instance (intent : Intent) (before : Current) (choice : Choice) : Decidable (Legal epoch intent before choice) := by
  unfold Legal; infer_instance

structure Paid (intent : Intent) (before : Current) where
  private mk ::
  choice : Choice
  listed : choice ∈ menu epoch intent before
  legal : Legal epoch intent before choice

def choose (intent : Intent) (before : Current) : Option (Paid epoch intent before) :=
  match selected : (menu epoch intent before).find? (fun choice => decide (Legal epoch intent before choice)) with
  | some choice => some ⟨choice, List.mem_of_find?_eq_some selected,
      of_decide_eq_true (List.find?_some (p := fun choice => decide (Legal epoch intent before choice)) selected)⟩
  | none => none

def selected (intent : Intent) (before : Current) :=
  ((choose epoch intent before).map Paid.choice).getD (fallback epoch intent before)

def core (intent : Intent) (before : Current) := candidate epoch intent before (selected epoch intent before)

theorem selected_is_generated (intent : Intent) (before : Current) : selected epoch intent before ∈ menu epoch intent before := by
  unfold selected
  cases found : choose epoch intent before with
  | some paid => exact paid.listed
  | none => exact List.mem_append_right _ (List.mem_singleton_self _)

theorem no_selected_choice_has_escaped_its_actual_check (intent : Intent) (before : Current)
    (blocked : choose epoch intent before = none) :
    ∀ choice ∈ menu epoch intent before, ¬ Legal epoch intent before choice := by
  unfold choose at blocked
  split at blocked
  · cases blocked
  · rename_i absent
    intro choice inside accepted
    have denied := List.find?_eq_none.mp absent choice inside
    rw [decide_eq_true accepted] at denied
    exact denied rfl

theorem an_eligible_blocked_core_has_an_actual_refused_item (intent : Intent) (before : Current)
    (eligible : Eligible epoch intent before) (blocked : choose epoch intent before = none) :
    ∃ item ∈ (Mandate.law base epoch.scope).rawItems before (core epoch intent before), ¬ (Mandate.law base epoch.scope).Valid item.before item.request := by
  by_contra absent
  apply no_selected_choice_has_escaped_its_actual_check epoch intent before blocked _ (selected_is_generated epoch intent before)
  refine ⟨eligible, ?_⟩
  intro item member
  by_contra refused
  exact absent ⟨item, member, refused⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input
