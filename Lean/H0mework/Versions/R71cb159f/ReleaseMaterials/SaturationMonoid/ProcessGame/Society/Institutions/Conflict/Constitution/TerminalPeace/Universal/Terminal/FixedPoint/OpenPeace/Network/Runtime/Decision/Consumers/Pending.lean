import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Pending
import H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Consumers.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Original

open Capitalism.Universal.Source.Program
open NoFreeProbe
open OriginalScopes OriginalOrders
open private submit first second second_novel second_scope first_landing_reads second_ordinal replies receipt
  from H0mework.Versions.R71cb159f.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Consumers.Original

noncomputable section

private abbrev posted := Runtime.source registration replies first.next (submit 1)

private theorem original_wire : posted.source.paidWire = some (proposal 1).wire :=
  congrArg Prepayment.Step.paidWire (receipt first_landing_reads second_ordinal)

set_option maxHeartbeats 1000000 in
/-- A paid term gap can wait for its old-language witness while retaining
the literal signed material visit. The checked completion consumes it. -/
theorem the_second_paid_gap_resolves_at_its_original_charged_cut
    (read : Reader first.next) (unreadable : read.probe termsEffect = none) :
    let answer : Result registration replies first.next (submit 1) := .needsEvidence (proposal 1).wire original_wire
    let finished := answer.complete posted rfl (.isFalse second_novel)
    Decision.advance registration replies first.next (submit 1) read
        (Advice.raw first.next (submit 1)) [] = answer ∧
      answer.postedPrefix = some posted ∧
      finished = second ∧
      finished.next.current.physical = posted.next.native.physical ∧
      HEq finished.next.current.ledger.stack posted.next.native.ledger.stack ∧
      finished.next.current.ledger = (Runtime.languageWrite registration replies first.next (submit 1) second_novel).state := by
  dsimp only
  have absent (point : Effect Bool Bool Bool Unit Unit)
      (actual : point ∈ Runtime.scope registration replies first.next (submit 1)) :
      read.probe point = none := by
    have exactScope : Runtime.scope registration replies first.next (submit 1) = {termsEffect} := second_scope
    rw [exactScope, Set.mem_singleton_iff] at actual
    subst point
    exact unreadable
  have openGap := advance_retains_an_unreadable_paid_scope registration replies first.next (submit 1)
    read (Advice.raw first.next (submit 1)) [] (proposal 1).wire original_wire second_novel absent
  have same := (Result.needsEvidence (proposal 1).wire original_wire).complete_eq_canonical posted rfl (.isFalse second_novel)
  have finished := pending_completion_uses_the_posted_receipt (proposal 1).wire original_wire (.isFalse second_novel)
  exact ⟨openGap, finished.1, same, finished.2.2.1, finished.2.2.2.1, finished.2.2.2.2.2⟩

end

#print axioms the_second_paid_gap_resolves_at_its_original_charged_cut

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.Decision.Original
