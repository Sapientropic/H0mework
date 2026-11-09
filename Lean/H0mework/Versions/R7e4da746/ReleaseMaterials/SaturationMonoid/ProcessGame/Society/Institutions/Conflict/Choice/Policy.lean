import Mathlib.Data.Set.Function

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice

variable {World Observation Action : Type*}

/-- Policy selection only has to specify actions for observations the source can emit. -/
abbrev Policy (observe : World → Observation) (Action : Type*) :=
  Set.range observe → Action

def Satisfies (observe : World → Observation) (acceptable : World → Action → Prop)
    (policy : Policy observe Action) : Prop :=
  ∀ world, acceptable world (policy (Set.rangeFactorization observe world))

theorem policy_factorization_iff (observe : World → Observation) (response : World → Action) :
    response.FactorsThrough observe ↔
      ∃ policy : Policy observe Action,
        ∀ world, policy (Set.rangeFactorization observe world) = response world := by
  constructor
  · intro factor
    refine ⟨fun seen => response (Set.rangeSplitting observe seen), fun world => factor ?_⟩
    exact Set.apply_rangeSplitting observe (Set.rangeFactorization observe world)
  · rintro ⟨policy, execution⟩ first second same
    rw [← execution first, ← execution second,
      (Set.rangeFactorization_eq_rangeFactorization_iff first second).mpr same]

theorem policy_exists_iff_fiberwise (observe : World → Observation)
    (acceptable : World → Action → Prop) :
    (∃ policy, Satisfies observe acceptable policy) ↔
      ∀ seen : Set.range observe, ∃ action,
        ∀ world, observe world = seen.1 → acceptable world action := by
  constructor
  · rintro ⟨policy, satisfies⟩ seen
    refine ⟨policy seen, fun world same => ?_⟩
    have result := satisfies world
    rw [(Set.rangeFactorization_eq_iff world seen).mpr same] at result
    exact result
  · intro fibers
    classical
    exact ⟨fun seen => Classical.choose (fibers seen), fun world =>
      Classical.choose_spec (fibers (Set.rangeFactorization observe world)) world rfl⟩

/-- Every action is refuted inside one realized observation fiber if no prior policy works. -/
theorem no_policy_iff_obstruction (observe : World → Observation)
    (acceptable : World → Action → Prop) :
    (¬ ∃ policy, Satisfies observe acceptable policy) ↔
      ∃ seen : Set.range observe, ∀ action,
        ∃ world, observe world = seen.1 ∧ ¬ acceptable world action := by
  classical
  rw [policy_exists_iff_fiberwise]
  constructor
  · intro unavailable
    obtain ⟨seen, fails⟩ := not_forall.mp unavailable
    refine ⟨seen, fun action => ?_⟩
    have invalid := not_exists.mp fails action
    obtain ⟨world, rejected⟩ := not_forall.mp invalid
    exact ⟨world, Classical.not_imp.mp rejected⟩
  · rintro ⟨seen, rejects⟩ available
    obtain ⟨action, eligible⟩ := available seen
    obtain ⟨world, same, rejected⟩ := rejects action
    exact rejected (eligible world same)

section Finite

variable (observe : World → Observation) (acceptable : World → Action → Prop)
  [DecidableEq Observation] [DecidableRel acceptable]
  (worlds : List World)

def rejectedWorld (seen : Observation) (action : Action) : Option World :=
  worlds.find? fun world => decide (observe world = seen ∧ ¬ acceptable world action)

theorem rejectedWorld_sound {seen : Observation} {action : Action} {world : World}
    (returned : rejectedWorld observe acceptable worlds seen action = some world) :
    world ∈ worlds ∧ observe world = seen ∧ ¬ acceptable world action := by
  have rejected := List.find?_some
    (p := fun candidate => decide (observe candidate = seen ∧ ¬ acceptable candidate action)) returned
  exact ⟨List.mem_of_find?_eq_some returned, of_decide_eq_true rejected⟩

theorem rejectedWorld_eq_none_iff (seen : Observation) (action : Action) :
    rejectedWorld observe acceptable worlds seen action = none ↔
      ∀ world ∈ worlds, observe world = seen → acceptable world action := by
  unfold rejectedWorld
  simp only [List.find?_eq_none, decide_eq_true_eq]
  constructor
  · intro none world member same
    by_cases accepted : acceptable world action
    · exact accepted
    · exact (none world member ⟨same, accepted⟩).elim
  · exact fun good world member rejected => rejected.2 (good world member rejected.1)

variable (actions : List Action)

/-- Enumerate actions against a whole observation fiber. A rejected action has its own
source branch, recoverable by `rejectedWorld`. -/
def synthesizeAt (seen : Observation) : Option Action :=
  actions.find? fun action => (rejectedWorld observe acceptable worlds seen action).isNone

theorem synthesizeAt_sound {seen : Observation} {action : Action}
    (returned : synthesizeAt observe acceptable worlds actions seen = some action) :
    action ∈ actions ∧ ∀ world ∈ worlds, observe world = seen → acceptable world action := by
  refine ⟨List.mem_of_find?_eq_some returned, ?_⟩
  apply (rejectedWorld_eq_none_iff observe acceptable worlds seen action).mp
  exact Option.isNone_iff_eq_none.mp
    (List.find?_some (p := fun candidate => (rejectedWorld observe acceptable worlds seen candidate).isNone)
      returned)

theorem synthesizeAt_eq_none_iff (seen : Observation) :
    synthesizeAt observe acceptable worlds actions seen = none ↔
      ∀ action ∈ actions, ∃ world, rejectedWorld observe acceptable worlds seen action = some world := by
  unfold synthesizeAt
  simp only [List.find?_eq_none, Option.isNone_iff_eq_none, ← Option.isSome_iff_ne_none,
    Option.isSome_iff_exists]

theorem finite_synthesis_is_complete
    (allWorlds : ∀ world, world ∈ worlds) (allActions : ∀ action, action ∈ actions) :
    (∃ policy, Satisfies observe acceptable policy) ↔
      ∀ seen : Set.range observe, (synthesizeAt observe acceptable worlds actions seen.1).isSome := by
  constructor
  · rintro ⟨policy, satisfies⟩ seen
    apply Option.isSome_iff_ne_none.mpr
    intro empty
    obtain ⟨world, failure⟩ :=
      (synthesizeAt_eq_none_iff observe acceptable worlds actions seen.1).mp empty (policy seen)
        (allActions (policy seen))
    obtain ⟨_, same, rejected⟩ := rejectedWorld_sound observe acceptable worlds failure
    have result := satisfies world
    rw [(Set.rangeFactorization_eq_iff world seen).mpr same] at result
    exact rejected result
  · intro canSynthesize
    let policy : Policy observe Action := fun seen =>
      (synthesizeAt observe acceptable worlds actions seen.1).get (canSynthesize seen)
    refine ⟨policy, fun world => ?_⟩
    have found : synthesizeAt observe acceptable worlds actions (observe world) =
        some (policy (Set.rangeFactorization observe world)) :=
      (Option.some_get (canSynthesize (Set.rangeFactorization observe world))).symm
    exact (synthesizeAt_sound observe acceptable worlds actions found).2 world (allWorlds world) rfl

end Finite

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Choice
