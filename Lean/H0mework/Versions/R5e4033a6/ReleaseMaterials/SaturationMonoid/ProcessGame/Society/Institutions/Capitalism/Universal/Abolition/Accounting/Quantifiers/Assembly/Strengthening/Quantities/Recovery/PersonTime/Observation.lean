import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Intervals.Overlap
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.TimedInventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime

open Source.Program Abolition.Root Abolition.Root.Registered
open Intervals

noncomputable section

universe u

inductive Phase where
  | ordinary
  | exposure
  | recovery
  deriving DecidableEq

/-- The party whose action was enacted is read from the operation. The
signer authorizes the request and can be a different party. -/
def operationActor {Party Good Technology Instrument : Type}
    (operation : Operation Party Good Technology Instrument) : Option Party :=
  match operation with
  | .produce actor | .revise actor _ | .use actor _ _ => some actor
  | _ => none

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

abbrev Ordinal (source : C) (script : Script) := Fin (Execution.inventory source script).length

def opensAt (source : C) (script : Script) (ordinal : Ordinal source script) : ℚ :=
  (Execution.timedAt source script ordinal).1.before.clock

def commitsAt (source : C) (script : Script) (ordinal : Ordinal source script) : ℚ :=
  (Execution.timedAt source script ordinal).2

def ownAction (source : C) (script : Script) (ordinal : Ordinal source script) (person : Party) : Prop :=
  let item := (Execution.timedAt source script ordinal).1
  operationActor item.request.operation = some person ∧
    (Physical.Public.interpreter source.native.input).Valid item.before item.request

/-- A source meter's physical occupation evidence is indexed by actual
ordinals. Even a valid work request does not carry such evidence by itself. -/
structure Meter (source : C) where
  OccupiedAt : (script : Script) → Party → Phase →
    (opens performs closes : Ordinal source script) → Type u

/-- The observation carries source evidence for the whole personal
interval. Its exact bounds are read from the original execution. -/
structure Observation (source : C) (meter : Meter.{u} source) (script : Script) where
  person : Party
  phase : Phase
  opens : Ordinal source script
  performs : Ordinal source script
  closes : Ordinal source script
  operation : ownAction source script performs person
  measured : meter.OccupiedAt script person phase opens performs closes
  withinSource : source.raw.clock ≤ opensAt source script opens
  starts : opensAt source script opens ≤ opensAt source script performs
  enacted : opensAt source script performs ≤ commitsAt source script performs
  finishes : commitsAt source script performs ≤ commitsAt source script closes

variable {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {meter : Meter.{u} source}
  {script : List (Option (Compile.RawInput Party Good Port Technology Instrument))}

def Observation.span (observed : Observation source meter script) : Span :=
  ⟨opensAt source script observed.opens, commitsAt source script observed.closes,
    observed.starts.trans (observed.enacted.trans observed.finishes)⟩

theorem Observation.span_inside_original_execution (observed : Observation source meter script) :
    source.raw.clock ≤ observed.span.start ∧
      observed.span.finish ≤ (Execution.endAt source script).raw.clock :=
  ⟨observed.withinSource,
    (Execution.an_ordinal_uses_its_actual_committing_clock source script observed.closes).2⟩

theorem Observation.actor_is_fixed_by_its_own_action (observed : Observation source meter script)
    (person : Party) (also : ownAction source script observed.performs person) :
    person = observed.person :=
  Option.some.inj (also.1.symm.trans observed.operation.1)

def spansFor (observed : List (Observation source meter script))
    (person : Party) (includes : Phase → Bool) : List Span :=
  (observed.filter fun evidence => decide (evidence.person = person) && includes evidence.phase).map
    Observation.span

theorem cover_for_iff_original_person_occupation (observed : List (Observation source meter script))
    (person : Party) (includes : Phase → Bool) (time : ℝ) :
    time ∈ cover (spansFor observed person includes) ↔
      ∃ evidence ∈ observed, evidence.person = person ∧ includes evidence.phase = true ∧
        time ∈ evidence.span.cover := by
  change (∃ span ∈ spansFor observed person includes, time ∈ span.cover) ↔ _
  unfold spansFor
  constructor
  · rintro ⟨span, listed, inside⟩
    obtain ⟨evidence, selected, rfl⟩ := List.mem_map.mp listed
    obtain ⟨original, kind⟩ := List.mem_filter.mp selected
    simp only [Bool.and_eq_true, decide_eq_true_eq] at kind
    exact ⟨evidence, original, kind.1, kind.2, inside⟩
  · rintro ⟨evidence, listed, owned, kind, inside⟩
    refine ⟨evidence.span, List.mem_map.mpr ⟨evidence, List.mem_filter.mpr ⟨listed, ?_⟩, rfl⟩, inside⟩
    simp [owned, kind]

def hours (observed : List (Observation source meter script))
    (person : Party) (includes : Phase → Bool) : ℚ :=
  length (spansFor observed person includes)

theorem personal_hours_are_bounded_by_actual_elapsed_time
    (observed : List (Observation source meter script)) (person : Party) (includes : Phase → Bool) :
    hours observed person includes ≤ (Execution.endAt source script).raw.clock - source.raw.clock := by
  let whole : Span := ⟨source.raw.clock, (Execution.endAt source script).raw.clock,
    Execution.the_actual_script_never_runs_the_clock_backwards source script⟩
  have covered : cover (spansFor observed person includes) ⊆ cover [whole] := by
    intro time personal
    obtain ⟨evidence, _, _, _, inside⟩ :=
      (cover_for_iff_original_person_occupation observed person includes time).mp personal
    obtain ⟨begins, finishes⟩ := evidence.span_inside_original_execution
    exact ⟨whole, List.mem_cons_self, (Rat.cast_le.mpr begins).trans inside.1,
      inside.2.trans_le (Rat.cast_le.mpr finishes)⟩
  have bound := length_mono covered
  rw [length_one] at bound
  exact bound

theorem recorded_person_occupation_has_its_original_whole_ledger
    (observed : Observation source meter script) :
    ownAction source script observed.performs observed.person ∧
      observed.span.start = opensAt source script observed.opens ∧
      observed.span.finish = commitsAt source script observed.closes ∧ Recorded source script :=
  ⟨observed.operation, rfl, rfl, record source script⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime
