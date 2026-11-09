import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision

open Capitalism.Universal.Source.Program
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open NoFreeProbe

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {origin : RawCurrent Party Good Technology Instrument} {people : List Party} {quantum : ℚ}
  {reserveBase : RawCurrent Party Good Technology Instrument}

variable {home : AnyAuthoritativeRootCurrent.{0}} {replies : Replies Party Good Port Technology Instrument}
  {before : Runtime.State (seed := seed) (cut := cut) (community := community) origin people quantum (reserveBase := reserveBase)}
  {input : OpenPeace.Input Party Good Port Technology Instrument}

local notation "Actual" => Runtime.source home replies before input
local notation "Covered" => Set.Subset (Runtime.scope home replies before input) before.base.language.covered
local notation "Answer" => Result home replies before input

/-- The unresolved branch exposes its existing material receipt and
adaptive successor. The network language still awaits its decision. -/
def Result.postedPrefix (answer : Answer) : Option (type_of% Actual) :=
  match answer with
  | .committed _ _ _ => none
  | .needsEvidence _ _ => some Actual

private theorem posted_is_original (answer : Answer) (posted : type_of% Actual)
    (found : answer.postedPrefix = some posted) : posted = Actual := by
  cases answer with
  | committed _ _ _ => cases found
  | needsEvidence _ _ => exact Option.some.inj found.symm

/-- The checked branch consumes the posted step directly. A later scope
decision cannot call the payment dispatcher on that step's successor. -/
def Result.complete (answer : Answer) (posted : type_of% Actual)
    (found : answer.postedPrefix = some posted) (checked : Decidable Covered) :
    Runtime.Step (seed := seed) (cut := cut) (community := community)
      (origin := origin) (people := people) (quantum := quantum) (reserveBase := reserveBase) :=
  Runtime.completePosted home replies before input posted (posted_is_original answer posted found) checked

theorem Result.complete_eq_canonical (answer : Answer) (posted : type_of% Actual)
    (found : answer.postedPrefix = some posted) (checked : Decidable Covered) :
    answer.complete posted found checked = Runtime.advance home replies before input :=
  Runtime.completePosted_eq_advance home replies before input posted (posted_is_original answer posted found) checked

/-- Both exact scope decisions extend the same receipt and whole
material accounts. Only a novel scope emits a further language write. -/
theorem pending_completion_uses_the_posted_receipt
    (wire : Wire Party Good Port Technology Instrument) (charged : (Actual).source.paidWire = some wire)
    (checked : Decidable Covered) :
    let answer : Answer := .needsEvidence wire charged
    let finished := answer.complete Actual rfl checked
    answer.postedPrefix = some Actual ∧
      (Actual).source.paidWire = some wire ∧
      finished.next.current.physical = (Actual).next.native.physical ∧
      HEq finished.next.current.ledger.stack (Actual).next.native.ledger.stack ∧
      match checked with
      | .isTrue _ => finished.write = none ∧ finished.next.current.ledger = (Actual).next.native.ledger
      | .isFalse novel =>
        finished.write = some (Runtime.languageWrite home replies before input novel) ∧
          finished.next.current.ledger = (Runtime.languageWrite home replies before input novel).state := by
  dsimp only
  rw [(Result.needsEvidence wire charged).complete_eq_canonical Actual rfl checked]
  refine ⟨rfl, charged, Runtime.same_physical home replies before input, Runtime.same_stack home replies before input, ?_⟩
  cases checked with
  | isTrue covered =>
    rw [← Runtime.advanceChecked_eq_advance home replies before input (.isTrue covered)]
    exact ⟨rfl, rfl⟩
  | isFalse novel =>
    rw [← Runtime.advanceChecked_eq_advance home replies before input (.isFalse novel)]
    exact ⟨rfl, rfl⟩

end

#print axioms pending_completion_uses_the_posted_receipt

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision
