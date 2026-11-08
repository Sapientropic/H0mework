import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Install
import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Event.Trace
import Mathlib.Data.Nat.Find

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Install

open Source.Program PublicFunction PublicFunction.Mandate
open PublicFunction.Mandate.Financed (Action base)
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
open SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World

noncomputable section

variable {epoch : Epoch}

def submitAllEvolution (inventory : Inventory epoch) (words : Words) :
    Input.Event.Evolution ⟨epoch, inventory⟩ ⟨epoch, submitAll inventory words⟩ :=
  match words with
  | [] => .same _
  | word :: tail => .append (.submit inventory word) (submitAllEvolution (World.submit inventory word) tail)

def Accepted.evolution {inventory : Inventory epoch} {cutoff : ℚ} {words : Words}
    (accepted : Accepted inventory cutoff words) :
    Input.Event.Evolution ⟨epoch, inventory⟩ accepted.next :=
  .handoffAt inventory accepted.fresh words

def Accepted.originalEvolution (inventory : Inventory epoch) (older : Words) {cutoff : ℚ} {words : Words}
    (accepted : Accepted (submitAll inventory older) cutoff words) :
    Input.Event.Evolution ⟨epoch, inventory⟩ accepted.next :=
  .append (submitAllEvolution inventory older) accepted.evolution

theorem submit_all_uses_the_actual_elapsed_clock (inventory : Inventory epoch) (words : Words) :
    (World.current epoch (submitAll inventory words).inputs).clock =
      (World.current epoch inventory.inputs).clock + words.length := by
  have clock (history : Words) (ordinal : Nat) :
      clockAt epoch.bound history ordinal = epoch.bound.source.seed.initial.clock + ordinal := by
    simpa only [mul_one] using constant_source_duration_gives_the_literal_clock epoch.bound history 1
      (by decide) (fun _ => rfl) ordinal
  change clockAt epoch.bound (submitAll inventory words).inputs _ = clockAt epoch.bound inventory.inputs _ + _
  rw [submit_all_inputs, clock, clock, List.length_append]
  push_cast
  ring

/-- The source clock, including the native installation and first service
commit, generates the numerical candidate before the new grant. -/
def cutoffAt (inventory : Inventory epoch) (steps : Nat) : ℚ :=
  (World.current epoch inventory.inputs).clock + 3 + steps

theorem accepted_term_is_its_native_grid_point (inventory : Inventory epoch)
    (older : Words) {cutoff : ℚ} {words : Words}
    (accepted : Accepted (submitAll inventory older) cutoff words) :
    cutoff = cutoffAt inventory older.length := by
  have registered := (registered_cutoff_is_the_native_successor_clock (submitAll inventory older) cutoff).mp
    ⟨accepted.fresh, accepted.chosen, accepted.exactCutoff⟩
  rw [registered.2, submit_all_uses_the_actual_elapsed_clock, cutoffAt]
  ring

def inspectFrom (inventory : Inventory epoch) (older words : Words) :
    Decision (submitAll inventory older) (cutoffAt inventory older.length) words :=
  inspect (submitAll inventory older) (cutoffAt inventory older.length) words

def SafeCutoffs (inventory : Inventory epoch) : Set ℚ :=
  fun cutoff => ∃ older words, Acceptance (submitAll inventory older) cutoff words

def SafeStep (inventory : Inventory epoch) (steps : Nat) : Prop :=
  ∃ older words, older.length = steps ∧ Acceptance (submitAll inventory older) (cutoffAt inventory steps) words

/-- Arbitrary words are allowed before and after installation. Each safe
cutoff is an admitted clock point of that same original root. -/
theorem safe_cutoffs_are_exactly_the_admitted_clock_points (inventory : Inventory epoch) (cutoff : ℚ) :
    cutoff ∈ SafeCutoffs inventory ↔ ∃ steps, SafeStep inventory steps ∧ cutoff = cutoffAt inventory steps := by
  constructor
  · rintro ⟨older, words, ⟨accepted⟩⟩
    have point := accepted_term_is_its_native_grid_point inventory older accepted
    refine ⟨older.length, ⟨older, words, rfl, ?_⟩, point⟩
    rw [← point]
    exact ⟨accepted⟩
  · rintro ⟨steps, ⟨older, words, _, accepted⟩, rfl⟩
    exact ⟨older, words, accepted⟩

theorem registered_cutoff_equals_first_service_commit {scope : World.Scope}
    {bound : BoundSource base scope} {inputs : Words} (fresh : Handoff.Ready bound inputs) (draft : Words) :
    clockAt (Handoff.newBound fresh) draft 2 = fresh.task.earliest ∧
      clockAt (Handoff.newBound fresh) draft 3 = fresh.task.deadline := by
  have clock (ordinal : Nat) :
      clockAt (Handoff.newBound fresh) draft ordinal =
        (Handoff.newBound fresh).source.seed.initial.clock + ordinal := by
    simpa only [mul_one] using constant_source_duration_gives_the_literal_clock
      (Handoff.newBound fresh) draft 1 (by decide) (fun _ => rfl) ordinal
  rw [clock, clock]
  exact ⟨rfl, rfl⟩

inductive Frontier (inventory : Inventory epoch) : Prop
  | bounded (first last : ℚ) (earliest : IsLeast (SafeCutoffs inventory) first)
      (latest : IsGreatest (SafeCutoffs inventory) last)
  | unbounded (first : ℚ) (earliest : IsLeast (SafeCutoffs inventory) first)
      (later : ∀ before, ∃ actual ∈ SafeCutoffs inventory, before < actual)
  | blocked (issues : ∀ older words cutoff, Nonempty (Failure (submitAll inventory older) cutoff words))

/-- The complete original admission set either has actual extreme
installations, is unbounded above with a later actual installation at
every finite bound, or returns a concrete failed check for every draft. -/
theorem original_root_has_the_complete_safe_term_frontier (inventory : Inventory epoch) : Frontier inventory := by
  classical
  by_cases available : ∃ steps, SafeStep inventory steps
  · let first := Nat.find available
    have exactFirst : first ∈ {steps | SafeStep inventory steps} := Nat.find_spec available
    have earliest : IsLeast (SafeCutoffs inventory) (cutoffAt inventory first) := by
      constructor
      · exact (safe_cutoffs_are_exactly_the_admitted_clock_points inventory _).mpr ⟨first, exactFirst, rfl⟩
      · intro cutoff admitted
        obtain ⟨steps, possible, rfl⟩ := (safe_cutoffs_are_exactly_the_admitted_clock_points inventory cutoff).mp admitted
        have ordered : first ≤ steps := Nat.find_min' available possible
        have realOrder : (first : ℚ) ≤ steps := by exact_mod_cast ordered
        dsimp [cutoffAt]
        linarith
    by_cases bounded : BddAbove (SafeCutoffs inventory)
    · obtain ⟨ceiling, upper⟩ := bounded
      let ceilingSteps := ⌈ceiling - cutoffAt inventory 0⌉₊
      have boundedSteps (steps : Nat) (possible : SafeStep inventory steps) : steps ≤ ceilingSteps := by
        have below := upper ((safe_cutoffs_are_exactly_the_admitted_clock_points inventory _).mpr ⟨steps, possible, rfl⟩)
        have inSteps : (steps : ℚ) ≤ ceiling - cutoffAt inventory 0 := by
          dsimp [cutoffAt] at below ⊢
          linarith
        exact_mod_cast inSteps.trans (Nat.le_ceil _)
      let last := Nat.findGreatest (SafeStep inventory) ceilingSteps
      have exactLast := Nat.findGreatest_spec (boundedSteps first exactFirst) exactFirst
      refine .bounded _ (cutoffAt inventory last) earliest ⟨?_, ?_⟩
      · exact (safe_cutoffs_are_exactly_the_admitted_clock_points inventory _).mpr ⟨last, exactLast, rfl⟩
      · intro cutoff admitted
        obtain ⟨steps, possible, rfl⟩ := (safe_cutoffs_are_exactly_the_admitted_clock_points inventory cutoff).mp admitted
        have ordered : steps ≤ last := Nat.le_findGreatest (boundedSteps steps possible) possible
        have realOrder : (steps : ℚ) ≤ last := by exact_mod_cast ordered
        dsimp [cutoffAt]
        linarith
    · refine .unbounded _ earliest ?_
      intro before
      by_contra absent
      apply bounded
      refine ⟨before, ?_⟩
      intro actual possible
      exact le_of_not_gt fun later => absent ⟨actual, possible, later⟩
  · refine .blocked ?_
    intro older words cutoff
    cases inspect (submitAll inventory older) cutoff words with
    | accept accepted =>
      have actual := (safe_cutoffs_are_exactly_the_admitted_clock_points inventory cutoff).mp
        ⟨older, words, ⟨accepted⟩⟩
      obtain ⟨steps, possible, _⟩ := actual
      exact (available ⟨steps, possible⟩).elim
    | reject issue => exact ⟨issue⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Clock.Mandate.SafeTerm.Install
