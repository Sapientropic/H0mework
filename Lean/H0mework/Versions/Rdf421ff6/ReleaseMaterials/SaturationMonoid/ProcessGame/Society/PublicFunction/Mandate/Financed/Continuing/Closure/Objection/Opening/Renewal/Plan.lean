import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Admission.Source

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

def sponsor := (Mandate.Response.firstMember scope).val

theorem sponsor_is_a_real_member : sponsor ∈ Delegation.members task :=
  (Mandate.Response.firstMember scope).property

inductive Method where
  | direct | productive | financed
  deriving DecidableEq

def fund (current : Current) (actor : Bool) (required : ℚ) : List Action :=
  let quantity := required - current.stock actor .service
  if 0 < quantity then
    [⟨actor, [], .resource, [], .issue () actor (!actor) quantity⟩,
     ⟨!actor, [], .resource, [], .transfer (!actor) actor [(.service, quantity)]⟩]
  else []

def funding (current : Current) : List (Bool × ℚ) → List Action
  | [] => []
  | (actor, required) :: tail =>
      let word := fund current actor required
      word ++ funding (law.execute current 0 word).final tail

def Method.prefix (method : Method) (current : Current) (actor : Bool) : List Action :=
  match method with
  | .direct => []
  | .productive => [Exit.production sponsor] ++ if actor = sponsor then [] else [Exit.production actor]
  | .financed => funding current (if actor = sponsor then [(sponsor, 2)] else [(sponsor, 1), (actor, 1)])

def beforeProposal (current : Current) (actor : Bool) (method : Method) :=
  (law.execute current 0 (method.prefix current actor)).final

def proposal (current : Current) (actor : Bool) (method : Method) :=
  request scope (beforeProposal current actor method) sponsor (.propose actor)

def beforeRenewal (current : Current) (actor : Bool) (method : Method) :=
  law.step (beforeProposal current actor method) (proposal current actor method)

def renewal (current : Current) (actor : Bool) (method : Method) :=
  request scope (beforeRenewal current actor method) actor .renew

def candidate (current : Current) (actor : Bool) (method : Method) :=
  method.prefix current actor ++ [proposal current actor method, renewal current actor method]

def Legal (current : Current) (actor : Bool) (method : Method) : Prop :=
  ∀ item ∈ law.rawItems current (candidate current actor method), law.Valid item.before item.request

instance (current : Current) (actor : Bool) (method : Method) : Decidable (Legal current actor method) := by
  unfold Legal; infer_instance

def methods : List Method := [.direct, .productive, .financed]

structure Ready (current : Current) (actor : Bool) where
  private mk ::
  method : Method
  included : method ∈ methods
  legal : Legal current actor method

def choose (current : Current) (actor : Bool) : Option (Ready current actor) :=
  match found : methods.find? (fun method => decide (Legal current actor method)) with
  | some method => some ⟨method, List.mem_of_find?_eq_some found,
      of_decide_eq_true (List.find?_some (p := fun method => decide (Legal current actor method)) found)⟩
  | none => none

theorem no_choice_refuses_every_generated_method (current : Current) (actor : Bool)
    (blocked : choose current actor = none) (method : Method) (inside : method ∈ methods) : ¬ Legal current actor method := by
  unfold choose at blocked
  split at blocked
  · cases blocked
  · rename_i absent
    intro legal
    have denied := List.find?_eq_none.mp absent method inside
    rw [decide_eq_true legal] at denied
    exact denied rfl

def selected (current : Current) (actor : Bool) : Method :=
  match choose current actor with
  | some ready => ready.method
  | none => if current.clock ≤ task.deadline then .productive else .direct

def core (current : Current) (actor : Bool) := candidate current actor (selected current actor)

theorem blocked_core_has_a_real_refusal (current : Current) (actor : Bool) (blocked : choose current actor = none) :
    ∃ item ∈ law.rawItems current (core current actor), ¬ law.Valid item.before item.request := by
  have inside : selected current actor ∈ methods := by
    unfold selected
    split
    · rename_i ready _; exact ready.included
    · split <;> decide +kernel
  by_contra absent
  apply no_choice_refuses_every_generated_method current actor blocked _ inside
  intro item actual
  by_contra refused
  exact absent ⟨item, actual, refused⟩

def renewalItem (current : Current) (actor : Bool) (method : Method) :
    ExecutionItem Bool Good Mandate.Source.Port (State Bool Unit) Unit :=
  ⟨(method.prefix current actor).length + 1, beforeRenewal current actor method, renewal current actor method⟩

theorem renewal_is_a_real_item (current : Current) (actor : Bool) (method : Method) :
    renewalItem current actor method ∈ law.rawItems current (candidate current actor method) := by
  unfold candidate RawLaw.rawItems
  rw [law.execute_append]
  simp only [RawLaw.execute, Nat.zero_add]
  apply List.mem_append_right
  simp [renewalItem, beforeRenewal, beforeProposal]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.Renewal
