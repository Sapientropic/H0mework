import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply.Check
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Material.Migration.Candidates

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Material.Migration (sourceWords)

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin current : RawCurrent Party Good Technology Instrument) (roster : List Party)

local notation "Word" => RawEvent Party Good Port Technology Instrument

inductive Selection (offers : List Word)
  | paid (position : Fin offers.length) (period : Period input origin current roster offers[position])
      (earlier : ∀ prior : Fin offers.length, prior.val < position.val → Issue input origin current roster offers[prior])
  | blocked (failure : ∀ position : Fin offers.length, Issue input origin current roster offers[position])

/-- A failed menu returns the original reason for every offered ordinal.
An accepted word keeps the same prior refutations and takes its own next. -/
def select : (offers : List Word) → Selection input origin current roster offers
  | [] => .blocked (fun position => Fin.elim0 position)
  | first :: later =>
    match inspect input origin current roster first with
    | .inr paid => .paid 0 paid.down (fun _ before => (Nat.not_lt_zero _ before).elim)
    | .inl issue =>
      match select later with
      | .paid position paid earlier =>
        .paid position.succ paid (by
          intro candidate
          refine Fin.cases ?_ (fun tail => ?_) candidate
          · intro _
            exact issue
          · intro before
            exact earlier tail (Nat.lt_of_succ_lt_succ before))
      | .blocked all => .blocked (fun position => Fin.cases issue all position)

theorem the_original_menu_is_blocked_iff_no_submitted_word_pays (offers : List Word) :
    (∃ failure, select input origin current roster offers = .blocked failure) ↔
      ∀ word ∈ offers, ¬ Period input origin current roster word := by
  constructor
  · rintro ⟨failure, _⟩ word listed paid
    obtain ⟨index, inside, same⟩ := List.getElem_of_mem listed
    have exactPeriod : Period input origin current roster offers[index] := by rwa [same]
    exact (failure ⟨index, inside⟩).refutes _ _ _ _ _ exactPeriod
  · intro unavailable
    cases select input origin current roster offers with
    | paid position period _ =>
      exact (unavailable _ (List.getElem_mem position.isLt) period).elim
    | blocked failure => exact ⟨failure, rfl⟩

/-- The normal registered alphabet uses the original local attempts and
the source's literal request word. -/
def selectRegistered (limit : Nat) :
    Selection input origin current roster (sourceWords input current limit) :=
  select input origin current roster (sourceWords input current limit)

/-- A joint period does not supply any private successful choice. Each
person's own menu is tested with precisely that person's authority. -/
def selectPersonal (person : Party) (offers : List Word) :
    Selection input origin current [person] offers :=
  select input origin current [person] offers

def selectPersonalRegistered (person : Party) (limit : Nat) :
    Selection input origin current [person] (sourceWords input current limit) :=
  selectRegistered input origin current [person] limit

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Supply
