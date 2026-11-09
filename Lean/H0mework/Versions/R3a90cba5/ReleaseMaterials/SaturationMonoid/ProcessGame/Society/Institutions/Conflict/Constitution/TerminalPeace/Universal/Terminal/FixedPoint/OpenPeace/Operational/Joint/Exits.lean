import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint.Alphabet

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq (Request Party Good Port Technology Instrument)]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin raw : RawCurrent Party Good Technology Instrument) (width : Nat)

local notation "Word" => RawEvent Party Good Port Technology Instrument

structure Exits (people : List Party) where
  word : Party → Word
  registered : ∀ person ∈ people, Supply.Registered input raw (word person)
  paid : ∀ person ∈ people, Supply.Period input origin raw [person] (word person)
  bounded : ∀ person ∈ people, (word person).length ≤ width

structure ExitIssue (people : List Party) where
  person : Party
  listed : person ∈ people
  refused : ∀ i : Fin (words input raw [person] width).length,
    Supply.Issue input origin raw [person] (words input raw [person] width)[i]

theorem ExitIssue.refutes {people : List Party} (issue : ExitIssue input origin raw width people)
    {word : Word} (bounded : word.length ≤ width)
    (registered : Supply.Registered input raw word) :
    ¬ Supply.Period input origin raw [issue.person] word := by
  intro paid
  have listed := every_paid_registered_word_is_listed input origin raw [issue.person] bounded registered paid
  obtain ⟨i, within, exactWord⟩ := List.getElem_of_mem listed
  exact (issue.refused ⟨i, within⟩).refutes _ _ _ _ _ (exactWord.symm ▸ paid)

private def prependExit {people : List Party} (head : Party) (word : Word)
    (registered : Supply.Registered input raw word) (paid : Supply.Period input origin raw [head] word)
    (bounded : word.length ≤ width) (later : Exits input origin raw width people) :
    Exits input origin raw width (head :: people) := by
  refine ⟨fun person => if person = head then word else later.word person, ?_, ?_, ?_⟩
  · intro person listed
    split
    · exact registered
    · exact later.registered _ ((List.mem_cons.mp listed).resolve_left ‹person ≠ head›)
  · intro person listed
    split
    · exact ‹person = head›.symm ▸ paid
    · exact later.paid _ ((List.mem_cons.mp listed).resolve_left ‹person ≠ head›)
  · intro person listed
    split
    · exact bounded
    · exact later.bounded _ ((List.mem_cons.mp listed).resolve_left ‹person ≠ head›)

/-- An exit is independently found with the original person's own
permissions and stock. The joint period supplies no private choices. -/
def exits : (people : List Party) → ExitIssue input origin raw width people ⊕ Exits input origin raw width people
  | [] => .inr ⟨fun _ => [], by simp, by simp, by simp⟩
  | head :: tail =>
    let options := words input raw [head] width
    match Supply.select input origin raw [head] options with
    | .blocked refused => .inl ⟨head, List.mem_cons_self, refused⟩
    | .paid position paid _ =>
      match exits tail with
      | .inl issue => .inl ⟨issue.person, List.mem_cons_of_mem _ issue.listed, issue.refused⟩
      | .inr later =>
        let listed := List.getElem_mem (l := options) position.isLt
        .inr (prependExit input origin raw width head options[position]
          (words_are_registered input raw [head] listed) paid
          (words_have_bounded_length input raw [head] listed) later)

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint
