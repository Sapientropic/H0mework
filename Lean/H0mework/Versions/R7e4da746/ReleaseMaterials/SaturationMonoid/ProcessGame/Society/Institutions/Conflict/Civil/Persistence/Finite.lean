import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence.Strategy

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence

noncomputable section

universe u v

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {Observation : Type u}

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Word" => Script Party Good Port Technology Instrument
local notation "P" => Position Party Good Port Technology Instrument Observation
local notation "Strategy" => History Observation → Word

def submitted (rival : List Word) (round : Nat) : Word := rival[round]?.getD []

abbrev AtRound (origin : C) (read : C → Observation) (strategy : Strategy)
    (required : P → Word → Word → Prop) (rival : List Word) (round : Nat) :=
  let position := (play origin read strategy (submitted rival) round).position
  required position (strategy position.seen) (submitted rival round)

structure FiniteFailure (origin : C) (read : C → Observation) (strategy : Strategy)
    (required : P → Word → Word → Prop) (Issue : P → Word → Word → Type v) (rival : List Word) where
  round : Nat
  original : round < rival.length
  earlier : ∀ before < round, AtRound origin read strategy required rival before
  failure :
    let position := (play origin read strategy (submitted rival) round).position
    Issue position (strategy position.seen) (submitted rival round)

def inspectFinite (origin : C) (read : C → Observation) (strategy : Strategy)
    (required : P → Word → Word → Prop) (Issue : P → Word → Word → Type v)
    (inspect : ∀ position move reply, Issue position move reply ⊕ PLift (required position move reply))
    (rival : List Word) : (count : Nat) → count ≤ rival.length →
      { first : FiniteFailure origin read strategy required Issue rival // first.round < count } ⊕
        PLift (∀ round < count, AtRound origin read strategy required rival round)
  | 0, _ => .inr ⟨fun _ absent => (Nat.not_lt_zero _ absent).elim⟩
  | count + 1, fits =>
    match inspectFinite origin read strategy required Issue inspect rival count (Nat.le_of_succ_le fits) with
    | .inl earlier => .inl ⟨earlier.val, Nat.lt_succ_of_lt earlier.property⟩
    | .inr earlier =>
      let position := (play origin read strategy (submitted rival) count).position
      match inspect position (strategy position.seen) (submitted rival count) with
      | .inl failed => .inl ⟨⟨count, fits, earlier.down, failed⟩, Nat.lt_succ_self count⟩
      | .inr good => .inr ⟨fun round within => by
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ within) with before | atLast
          · exact earlier.down round before
          · subst round
            exact good.down⟩

/-- An adverse input tape is used only to select a finite initial segment.
The original checks produce the earliest typed failure in that segment. -/
theorem a_failed_contract_has_an_original_first_counterexample
    {origin : C} {read : C → Observation} {strategy : Strategy}
    (required : P → Word → Word → Prop) (Issue : P → Word → Word → Type v)
    (inspect : ∀ position move reply, Issue position move reply ⊕ PLift (required position move reply))
    (defeated : ¬ Follows origin read strategy required) :
    Nonempty (Σ rival : List Word, FiniteFailure origin read strategy required Issue rival) := by
  classical
  unfold Follows at defeated
  push Not at defeated
  obtain ⟨tape, round, failed⟩ := defeated
  let rival : List Word := (List.range (round + 1)).map tape
  have size : rival.length = round + 1 := by simp [rival]
  have before (tick : Nat) (within : tick < round + 1) : submitted rival tick = tape tick := by
    have listed : tick < rival.length := size.symm ▸ within
    unfold submitted
    rw [List.getElem?_eq_getElem listed]
    simp only [rival, List.getElem_map, List.getElem_range, Option.getD_some]
  have original := play_ignores_future_submissions origin read strategy (submitted rival) tape round
    (fun tick earlier => before tick (Nat.lt_succ_of_lt earlier))
  have broken : ¬ AtRound origin read strategy required rival round := by
    dsimp only [AtRound]
    rw [original, before round (Nat.lt_succ_self round)]
    exact failed
  cases inspectFinite origin read strategy required Issue inspect rival (round + 1) size.ge with
  | inl first => exact ⟨⟨rival, first.val⟩⟩
  | inr sound => exact (broken (sound.down round (Nat.lt_succ_self round))).elim

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Civil.Persistence
