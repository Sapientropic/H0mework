import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Repair

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Material
open Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  [DecidableEq (Request Party Good Port Technology Instrument)]

local notation "Action" => Request Party Good Port Technology Instrument
local notation "Word" => RawEvent Party Good Port Technology Instrument

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin raw : RawCurrent Party Good Technology Instrument) (people : List Party)

private def allowed (request : Action) : Prop :=
  Supply.OwnOperation request ∧ request.signer ∈ people ∧ request.consents = []

private instance (request : Action) : Decidable (allowed people request) := by
  unfold allowed
  infer_instance

/-- Discard instructions that cannot occur in any paid period before
enumeration. Registration still comes from the reached cut. -/
def alphabet : List Action :=
  (Migration.sourceAlphabet input raw).dedup.filter fun request => decide (allowed people request)

def words (width : Nat) : List Word :=
  PublicFunction.words (alphabet input raw people) width

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem words_are_registered {width : Nat} {word : Word}
    (listed : word ∈ words input raw people width) : Supply.Registered input raw word := by
  intro request used
  have included := (PublicFunction.mem_words_iff _ _ _).mp listed
  have permitted := List.mem_filter.mp (included.2 request used)
  exact List.mem_dedup.mp permitted.1

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem words_have_bounded_length {width : Nat} {word : Word}
    (listed : word ∈ words input raw people width) : word.length ≤ width :=
  ((PublicFunction.mem_words_iff _ _ _).mp listed).1

theorem every_paid_registered_word_is_listed {width : Nat} {word : Word}
    (bounded : word.length ≤ width) (registered : Supply.Registered input raw word)
    (paid : Supply.Period input origin raw people word) : word ∈ words input raw people width := by
  apply (PublicFunction.mem_words_iff _ _ _).mpr
  refine ⟨bounded, fun request used => ?_⟩
  have actual : request ∈ (input.law.rawItems raw word).map ExecutionItem.request := by
    simpa only [RawLaw.rawItems, RawLaw.inventory_requests_exact] using used
  obtain ⟨item, listed, same⟩ := List.mem_map.mp actual
  have own := paid.own item listed
  apply List.mem_filter.mpr
  exact ⟨List.mem_dedup.mpr (registered request used),
    decide_eq_true (same ▸ ⟨own.operation, own.member, own.noConsent⟩ :
      allowed people request)⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Operational.Joint
