import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit.Roster

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit

open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Quantities.Execution (endAt next)

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Conflict.Root.Cut Party Good Port Technology Instrument
local notation "Word" => Reparation.Actual.Script Party Good Port Technology Instrument

def StandingAt (people : List Party) (cut : C) : Prop :=
  ∀ person ∈ people, person ∈ cut.members

def StandingAlong (people : List Party) : C → Word → Prop
  | cut, [] => StandingAt people cut
  | cut, input :: rest => StandingAt people cut ∧ StandingAlong people (next cut input) rest

theorem StandingAlong.at_original_cut {people : List Party} {cut : C} {before tail : Word}
    (kept : StandingAlong people cut (before ++ tail)) : StandingAt people (endAt cut before) := by
  induction before generalizing cut with
  | nil => cases tail with
    | nil => exact kept
    | cons => exact kept.1
  | cons input rest earlier => exact earlier kept.2

structure StandingFailure (people : List Party) (cut : C) (word : Word) where
  before : Word
  remaining : Word
  original : word = before ++ remaining
  person : Party
  resident : person ∈ people
  missing : person ∉ (endAt cut before).members

theorem StandingFailure.refutes {people : List Party} {cut : C} {word : Word}
    (issue : StandingFailure people cut word) : ¬ StandingAlong people cut word := by
  intro kept
  exact issue.missing ((issue.original ▸ kept : StandingAlong people cut (issue.before ++ issue.remaining)).at_original_cut
    issue.person issue.resident)

def inspectStanding (people : List Party) : (cut : C) → (word : Word) →
    StandingFailure people cut word ⊕ PLift (StandingAlong people cut word)
  | cut, [] =>
    match Capitalism.Universal.Abolition.Material.inspectList (fun person => person ∈ cut.members) people with
    | .failure person resident missing => .inl ⟨[], [], rfl, person, resident, missing⟩
    | .clear standing => .inr ⟨standing⟩
  | cut, input :: rest =>
    match Capitalism.Universal.Abolition.Material.inspectList (fun person => person ∈ cut.members) people with
    | .failure person resident missing => .inl ⟨[], input :: rest, rfl, person, resident, missing⟩
    | .clear standing =>
      match inspectStanding people (next cut input) rest with
      | .inl issue => .inl ⟨input :: issue.before, issue.remaining, congrArg (List.cons input) issue.original,
          issue.person, issue.resident, issue.missing⟩
      | .inr kept => .inr ⟨⟨standing, kept.down⟩⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.ExposureGuard.Exit
