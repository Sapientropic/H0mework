import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Abolition.Material.Continuation
open Capitalism.Universal.Root
open Runtime.Viability (Move)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq (Request Party Good Port Technology Instrument)]

local notation "Word" => RawEvent Party Good Port Technology Instrument
local notation "Raw" => RawCurrent Party Good Technology Instrument

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin raw : RawCurrent Party Good Technology Instrument)

/-- Only the source's stability laws are certified ahead of time. The
production and personal words still have to pay at this actual cut. -/
structure RepeatCode where
  production : Word
  personal : Party → Word
  timing : input.law.TimeIndependent
  reserve : input.law.ReserveInsensitive
  registration : Move.RegistrationOnReserves input raw
  duration : ∀ (extra : Party → Good → ℚ), (∀ person good, 0 ≤ extra person good) →
    ∀ clock round, input.law.duration ((raw.addReserve extra).retime clock round) = input.law.duration raw

local notation "Alphabet" => Migration.sourceAlphabet input raw

variable (people : List Party) (word : RawEvent Party Good Port Technology Instrument)

inductive WordIssue
  | unregistered (request : Request Party Good Port Technology Instrument)
      (listed : request ∈ word) (absent : request ∉ Alphabet)
  | unpaid (issue : Supply.Issue input origin raw people word)

omit [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem WordIssue.refutes (issue : WordIssue input origin raw people word) :
    ¬ (Supply.Registered input raw word ∧ Supply.Period input origin raw people word) := by
  intro paid
  cases issue with
  | unregistered request listed absent => exact absent (paid.1 request listed)
  | unpaid issue => exact issue.refutes _ _ _ _ _ paid.2

def checkWord : WordIssue input origin raw people word ⊕
    PLift (Supply.Registered input raw word ∧ Supply.Period input origin raw people word) :=
  match inspectList (fun request : Request Party Good Port Technology Instrument => request ∈ Alphabet) word with
  | .failure request listed absent => .inl (.unregistered request listed absent)
  | .clear registered =>
    match Supply.inspect input origin raw people word with
    | .inl unpaid => .inl (.unpaid unpaid)
    | .inr paid => .inr ⟨registered, paid.down⟩

variable (code : RepeatCode input raw)

structure PersonalIssue where
  person : Party
  listed : person ∈ people
  issue : WordIssue input origin raw [person] (code.personal person)

def checkPersonal : (roster : List Party) → PersonalIssue input origin raw roster code ⊕
    PLift (∀ person ∈ roster, Supply.Registered input raw (code.personal person) ∧
      Supply.Period input origin raw [person] (code.personal person))
  | [] => .inr ⟨fun _ absent => (List.not_mem_nil absent).elim⟩
  | p :: tail =>
    match checkWord input origin raw [p] (code.personal p) with
    | .inl failed => .inl ⟨p, List.mem_cons_self, failed⟩
    | .inr first =>
      match checkPersonal tail with
      | .inl failed => .inl ⟨failed.person, List.mem_cons_of_mem _ failed.listed, failed.issue⟩
      | .inr rest => .inr ⟨fun person listed => by
          rcases List.mem_cons.mp listed with same | later
          · subst person
            exact first.down
          · exact rest.down _ later⟩

inductive RecipeIssue
  | production (issue : WordIssue input origin raw people code.production)
  | personal (issue : PersonalIssue input origin raw people code)
  | imbalance (issue : Balance.Issue .accumulating input.law raw code.production)
  | stalled (zero : ∀ person good, Balance.gain input.law raw code.production person good ≤ 0)

def RecipeConditions : Prop :=
  (Supply.Registered input raw code.production ∧ Supply.Period input origin raw people code.production) ∧
  (∀ person ∈ people, Supply.Registered input raw (code.personal person) ∧
    Supply.Period input origin raw [person] (code.personal person)) ∧
  Balance.FiniteChecks .accumulating input.law raw code.production ∧
  ∃ person good, 0 < Balance.gain input.law raw code.production person good

omit [DecidableEq (Request Party Good Port Technology Instrument)] in
theorem RecipeIssue.refutes (issue : RecipeIssue input origin raw people code) :
    ¬ RecipeConditions input origin raw people code := by
  intro funded
  cases issue with
  | production issue => exact issue.refutes input origin raw people code.production funded.1
  | personal issue =>
    exact (issue.issue.refutes input origin raw [issue.person] _) (funded.2.1 issue.person issue.listed)
  | imbalance issue => exact issue.refutes _ _ _ _ funded.2.2.1
  | stalled zero =>
    obtain ⟨person, good, growth⟩ := funded.2.2.2
    exact (zero person good).not_gt growth

private def positiveGain : PLift (∃ person good, 0 < Balance.gain input.law raw code.production person good) ⊕
    PLift (∀ person good, Balance.gain input.law raw code.production person good ≤ 0) :=
  let support := Balance.cells input.law raw code.production
  let grows := fun cell : Party × Good => decide (0 < Balance.gain input.law raw code.production cell.1 cell.2)
  match found : support.find? grows with
  | some cell =>
    let gained := List.find?_some found
    .inl ⟨⟨cell.1, cell.2, of_decide_eq_true gained⟩⟩
  | none =>
    .inr ⟨fun person good => by
      if listed : (person, good) ∈ support then
        exact le_of_not_gt fun gain => (List.find?_eq_none.mp found _ listed) (decide_eq_true gain)
      else
        obtain ⟨debit, credit⟩ := Balance.no_effect_outside_original_support input.law raw code.production person good listed
        simp [Balance.gain, debit, credit]⟩

/-- Check the actual stock effects, independent exit of every original
participant, and positive clock. The clock bound is the actual duration. -/
def checkRecipe : RecipeIssue input origin raw people code ⊕
    { recipe : Recipe input origin people raw (input.law.duration raw) // recipe.move.word = code.production } :=
  match checkWord input origin raw people code.production with
  | .inl failed => .inl (.production failed)
  | .inr round =>
    match checkPersonal input origin raw code people with
    | .inl failed => .inl (.personal failed)
    | .inr exits =>
      match Balance.check .accumulating input.law raw code.production with
      | .rejected failed => .inl (.imbalance failed)
      | .accepted balance =>
        match positiveGain input raw code with
        | .inr zero => .inl (.stalled zero.down)
        | .inl grows =>
          let move : Move input origin people raw :=
            ⟨code.production, round.down.1, round.down.2, fun person listed =>
              ⟨code.personal person, (exits.down person listed).1, (exits.down person listed).2⟩⟩
          let nonnegative := (Balance.checked_productive_period input.law raw code.production balance).2
          .inr ⟨{
            move := move
            law := {
              timing := code.timing
              reserve := code.reserve
              accumulating := balance
              positive := round.down.2.positiveClock
              duration := fun extra available clock ordinal => (code.duration extra available clock ordinal).ge
              registered := fun n clock ordinal word old =>
                code.registration _ (accumulatedReserve_nonnegative _ nonnegative n) clock ordinal word old }
            registration := code.registration
            positiveGain := grows.down }, rfl⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational
