import H0mework.Versions.R5e4033a6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime.Accounting

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime

open Source.Program Abolition.Root Abolition.Root.Registered
open Intervals

noncomputable section

universe u

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument)
local notation "Script" => List (Option (Compile.RawInput Party Good Port Technology Instrument))

private def candidateFor (source : C) (meter : Meter.{u} source) (script : Script)
    (person : Party) (phase : Phase) (opens performs closes : Ordinal source script) :
    Option (Observation source meter script) := by
  classical
  exact if occupied : ownAction source script performs person ∧
      Nonempty (meter.OccupiedAt script person phase opens performs closes) ∧
      source.raw.clock ≤ opensAt source script opens ∧
      opensAt source script opens ≤ opensAt source script performs ∧
      opensAt source script performs ≤ commitsAt source script performs ∧
      commitsAt source script performs ≤ commitsAt source script closes then
    some ⟨person, phase, opens, performs, closes, occupied.1, Classical.choice occupied.2.1,
      occupied.2.2.1, occupied.2.2.2.1, occupied.2.2.2.2.1, occupied.2.2.2.2.2⟩
  else none

private def candidate (source : C) (meter : Meter.{u} source) (script : Script)
    (phase : Phase) (opens performs closes : Ordinal source script) :
    Option (Observation source meter script) :=
  match operationActor (Execution.timedAt source script performs).1.request.operation with
  | none => none
  | some person => candidateFor source meter script person phase opens performs closes

/-- Every candidate is found in a finite enumeration of original ordinal
triples and phases. The enacted operation determines the person. -/
def roster (source : C) (meter : Meter.{u} source) (script : Script) :
    List (Observation source meter script) :=
  let ordinals := List.finRange (Execution.inventory source script).length
  [.ordinary, .exposure, .recovery].flatMap fun phase =>
    ordinals.flatMap fun opens =>
      ordinals.flatMap fun performs =>
        ordinals.filterMap (candidate source meter script phase opens performs)

private theorem candidate_finds (source : C) (meter : Meter.{u} source) (script : Script)
    (observation : Observation source meter script) :
    ∃ read, candidate source meter script observation.phase
        observation.opens observation.performs observation.closes = some read ∧
      read.person = observation.person ∧ read.phase = observation.phase ∧
      read.opens = observation.opens ∧ read.performs = observation.performs ∧
      read.closes = observation.closes := by
  have actor : operationActor (Execution.timedAt source script observation.performs).1.request.operation =
      some observation.person := observation.operation.1
  unfold candidate
  rw [actor]
  change ∃ read, candidateFor source meter script observation.person observation.phase
    observation.opens observation.performs observation.closes = some read ∧ _
  unfold candidateFor
  rw [dif_pos ⟨observation.operation, ⟨observation.measured⟩, observation.withinSource,
    observation.starts, observation.enacted, observation.finishes⟩]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem roster_contains_every_original_occupation
    (source : C) (meter : Meter.{u} source) (script : Script)
    (observation : Observation source meter script) :
    ∃ read ∈ roster source meter script,
      read.person = observation.person ∧ read.phase = observation.phase ∧
      read.performs = observation.performs ∧ read.span = observation.span := by
  obtain ⟨read, found, person, phase, opens, performs, closes⟩ :=
    candidate_finds source meter script observation
  have phaseListed : observation.phase ∈ [Phase.ordinary, .exposure, .recovery] := by
    cases observation.phase <;> simp
  refine ⟨read, ?_, person, phase, performs, ?_⟩
  · exact List.mem_flatMap.mpr ⟨_, phaseListed,
      List.mem_flatMap.mpr ⟨_, by simp, List.mem_flatMap.mpr ⟨_, by simp,
        List.mem_filterMap.mpr ⟨_, by simp, found⟩⟩⟩⟩
  · unfold Observation.span
    simp only [opens, closes]

/-- The generated roster measures exactly the clock set certified by the
source, independently of a submitted subset or duplicate meter proofs. -/
theorem roster_covers_exactly_the_source_occupations
    (source : C) (meter : Meter.{u} source) (script : Script)
    (person : Party) (includes : Phase → Bool) (time : ℝ) :
    time ∈ cover (spansFor (roster source meter script) person includes) ↔
      ∃ observation : Observation source meter script, observation.person = person ∧
        includes observation.phase = true ∧ time ∈ observation.span.cover := by
  rw [cover_for_iff_original_person_occupation]
  constructor
  · rintro ⟨observation, _, owner, phase, inside⟩
    exact ⟨observation, owner, phase, inside⟩
  · rintro ⟨observation, owner, phase, inside⟩
    obtain ⟨read, listed, sameOwner, samePhase, _, sameSpan⟩ :=
      roster_contains_every_original_occupation source meter script observation
    exact ⟨read, listed, sameOwner.trans owner, samePhase ▸ phase, sameSpan ▸ inside⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Recovery.PersonTime
