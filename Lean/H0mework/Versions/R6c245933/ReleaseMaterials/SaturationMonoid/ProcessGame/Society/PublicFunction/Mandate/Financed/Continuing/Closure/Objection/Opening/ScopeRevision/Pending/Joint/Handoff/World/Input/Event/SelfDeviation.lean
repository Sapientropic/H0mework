import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.InheritedResponse

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle Followup
noncomputable section
variable {epoch : Epoch} (inventory : Inventory epoch) (intent : Input.Intent) (actor : Bool)

/-- Local control concerns the incoming word only. The unchanged source owns
all subsequent reactions; another party's signature is never supplied here. -/
def LocalWord (actor : Bool) (word : List Action) : Prop :=
  ∀ request ∈ word, request.signer = actor ∧ ∀ consent ∈ request.consents, consent = actor

instance (actor : Bool) (word : List Action) : Decidable (LocalWord actor word) := by
  unfold LocalWord
  infer_instance

abbrev before := current epoch inventory.inputs
abbrev Choice := {choice : Input.Choice // choice ∈ Input.menu epoch intent (before inventory)}

def word (choice : Choice inventory intent) := Input.candidate epoch intent (before inventory) choice.val

structure Permit where
  private mk ::
  choice : Choice inventory intent
  legal : Input.Legal epoch intent (before inventory) choice.val
  controlled : LocalWord actor (word inventory intent choice)

inductive Assessment (choice : Choice inventory intent) where
  | private ready (permit : Permit inventory intent actor) (exactChoice : permit.choice = choice)
  | private ineligible (reason : ¬ Input.Eligible epoch intent (before inventory))
  | private refused (eligible : Input.Eligible epoch intent (before inventory))
      (failure : ∃ item ∈ (Mandate.law base epoch.scope).rawItems (before inventory) (word inventory intent choice),
        ¬ (Mandate.law base epoch.scope).Valid item.before item.request)
  | private foreign (legal : Input.Legal epoch intent (before inventory) choice.val)
      (reason : ¬ LocalWord actor (word inventory intent choice))

def assess (choice : Choice inventory intent) : Assessment inventory intent actor choice := by
  by_cases legal : Input.Legal epoch intent (before inventory) choice.val
  · by_cases own : LocalWord actor (word inventory intent choice)
    · exact .ready ⟨choice,legal,own⟩ rfl
    · exact .foreign legal own
  · by_cases eligible : Input.Eligible epoch intent (before inventory)
    · apply Assessment.refused eligible
      classical
      by_contra absent
      apply legal
      refine ⟨eligible, ?_⟩
      intro item inside
      by_contra denied
      exact absent ⟨item,inside,denied⟩
    · exact .ineligible eligible

def Assessment.get? {choice : Choice inventory intent} : Assessment inventory intent actor choice → Option (Permit inventory intent actor)
  | .ready permit _ => some permit
  | .ineligible _ | .refused .. | .foreign .. => none

theorem checked_iff (choice : Choice inventory intent) :
    ((assess inventory intent actor choice).get? inventory intent actor).isSome = true ↔
      Input.Legal epoch intent (before inventory) choice.val ∧ LocalWord actor (word inventory intent choice) := by
  unfold assess
  split
  · split <;> simp_all [Assessment.get?]
  · split <;> simp_all [Assessment.get?]

def choices : List (Choice inventory intent) := (Input.menu epoch intent (before inventory)).attach

def permits : List (Permit inventory intent actor) :=
  (choices inventory intent).filterMap fun choice => (assess inventory intent actor choice).get? inventory intent actor

theorem every_legal_self_controlled_choice_is_generated (choice : Choice inventory intent)
    (legal : Input.Legal epoch intent (before inventory) choice.val)
    (own : LocalWord actor (word inventory intent choice)) :
    ∃ permit ∈ permits inventory intent actor, permit.choice = choice := by
  unfold permits
  have checked := (checked_iff inventory intent actor choice).mpr ⟨legal,own⟩
  obtain ⟨permit,found⟩ := Option.isSome_iff_exists.mp checked
  refine ⟨permit,List.mem_filterMap.mpr ⟨choice,List.mem_attach _ _,found⟩,?_⟩
  generalize actual : assess inventory intent actor choice = result at found
  cases result
  next candidate same => cases found; exact same
  all_goals cases found

theorem foreign_means_an_actual_request_uses_someone_else (choice : Choice inventory intent)
    (denied : ¬ LocalWord actor (word inventory intent choice)) :
    ∃ request ∈ word inventory intent choice,
      request.signer ≠ actor ∨ ∃ consent ∈ request.consents, consent ≠ actor := by
  classical
  by_contra absent
  apply denied
  intro request inside
  constructor
  · by_contra different
    exact absent ⟨request,inside,Or.inl different⟩
  · intro consent member
    by_contra different
    exact absent ⟨request,inside,Or.inr ⟨consent,member,different⟩⟩

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.SelfDeviation
