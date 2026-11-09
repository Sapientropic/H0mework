import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability.Path
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Continuation.Retiming

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Abolition.Material.Continuation (actualUse_retime originalNeedFloor_retime)
open Capitalism.Universal.Exit.AutonomousProduction (executed_items_retime retimed)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

local notation "Raw" => RawCurrent Party Good Technology Instrument

variable {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {origin raw finish : RawCurrent Party Good Technology Instrument} {roster : List Party} {length : Nat}

/-- The current source still registers its words and pays the same
physical duration when only its clock and round change. -/
structure RetimeStableAt (input : ProgrammeSource.Input Party Good Port Technology Instrument)
    (raw : Raw) : Prop where
  duration : ∀ clock round, input.law.duration (raw.retime clock round) = input.law.duration raw
  registered : ∀ clock round word, Supply.Registered input raw word →
    Supply.Registered input (raw.retime clock round) word

def shifted (raw : Raw) (clock : ℚ) (round : Nat) : Raw :=
  raw.retime (raw.clock + clock) (raw.round + round)

private theorem period_retime {origin raw : Raw}
    {word : RawEvent Party Good Port Technology Instrument}
    (timing : input.law.TimeIndependent) (stable : RetimeStableAt input raw)
    (paid : Supply.Period input origin raw roster word) (clock : ℚ) (round : Nat) :
    Supply.Period input origin (raw.retime clock round) roster word := by
  refine ⟨?_, (originalNeedFloor_retime input timing origin raw clock round roster word).mpr paid.originalFloor,
    ?_, (stable.duration clock round).symm ▸ paid.positiveClock⟩
  · intro item listed
    unfold RawLaw.rawItems at listed
    rw [executed_items_retime input.law timing raw clock round 0 word] at listed
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp listed
    have owned := paid.own original member
    exact ⟨owned.operation, owned.member, owned.noConsent,
      (input.law.valid_retime timing _ _ _ _).mpr owned.valid⟩
  · simpa only [OriginalNeedFloor, originalRequirements, timing.necessities,
      timing.maintenance, actualUse_retime input timing] using paid.currentFloor

namespace Move

def retime (move : Move input origin roster raw) (timing : input.law.TimeIndependent)
    (stable : RetimeStableAt input raw) (clock : ℚ) (round : Nat) :
    Move input origin roster (shifted raw clock round) where
  word := move.word
  registered := stable.registered _ _ _ move.registered
  paid := period_retime timing stable move.paid _ _
  personal := by
    intro person member
    obtain ⟨word, registered, paid⟩ := move.personal person member
    exact ⟨word, stable.registered _ _ _ registered, period_retime timing stable paid _ _⟩

theorem next_retime {origin raw : Raw}
    (move : Move input origin roster raw) (timing : input.law.TimeIndependent)
    (stable : RetimeStableAt input raw) (clock : ℚ) (round : Nat) :
    (move.retime timing stable clock round).next = shifted move.next clock round := by
  change input.law.next (shifted raw clock round) move.word = shifted (input.law.next raw move.word) clock round
  unfold shifted RawLaw.next
  rw [input.law.execute_retime timing, stable.duration]
  apply RawCurrent.ext
  · rfl
  · rfl
  · rfl
  · change (raw.clock + clock) + max 0 (input.law.duration raw) =
      (raw.clock + max 0 (input.law.duration raw)) + clock
    ac_rfl
  · change (raw.round + round) + 1 = (raw.round + 1) + round
    ac_rfl

end Move

namespace Path

/-- Stability is used only at openings of the actual finite path. -/
def RetimeStable : {raw finish : Raw} → {length : Nat} → Path input origin roster raw length finish → Prop
  | _, _, _, .nil _ => True
  | current, _, _, .cons _ rest => RetimeStableAt input current ∧ RetimeStable rest

theorem retimeStable_of_source (path : Path input origin roster raw length finish)
    (stable : ∀ current, RetimeStableAt input current) : path.RetimeStable := by
  induction path with
  | nil => trivial
  | cons _ _ later => exact ⟨stable _, later⟩

def retime (timing : input.law.TimeIndependent) (clock : ℚ) (round : Nat) :
    {raw finish : Raw} → {length : Nat} → (path : Path input origin roster raw length finish) →
    path.RetimeStable → Path input origin roster (shifted raw clock round) length (shifted finish clock round)
  | _, _, _, .nil _, _ => .nil _
  | _, _, _, .cons first rest, stable =>
    .cons (first.retime timing stable.1 clock round)
      ((first.next_retime timing stable.1 clock round).symm ▸ retime timing clock round rest stable.2)

end Path

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Viability
