import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Write

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Live

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Renewal (Request Replies Refusal)
open Reparation.Actual (identityWhole)
open private action publish the_canonical_write_is_the_published_whole_state
  original_rows_are_the_whole_first_write earlier_reads_are_kept_at_the_landing from
  H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Write

noncomputable section

variable {history : Original.Word} (live : Live history) (request : Request)
  {answers : Replies live.native request} (issue : Refusal live.native request answers)

private abbrev refusedEvent : Event := .refused live.effect request answers issue

def rejectAction := action live.state (refusedEvent live request issue)

/-- Write the exact refusal and its original proposal as metadata on the
current ledger. The next physical read stays at the last paid occurrence. -/
def reject : Live history :=
  publish live.state (refusedEvent live request issue)

theorem reject_is_the_canonical_whole_write :
    (⟨live.state.world, (rejectAction live request issue).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (reject live request issue).state.resident.erase :=
  the_canonical_write_is_the_published_whole_state live.state (refusedEvent live request issue)

theorem reject_reads_its_exact_refusal :
    (reject live request issue).event = .refused live.effect request answers issue :=
  rfl

theorem reject_keeps_material_effect :
    (reject live request issue).effect = live.effect :=
  rfl

theorem reject_has_no_material_items :
    (reject live request issue).items = [] :=
  rfl

theorem reject_keeps_the_exact_original_stack :
    (reject live request issue).state.stack = live.state.stack :=
  rfl

theorem reject_keeps_every_original_row :
    let written := (rejectAction live request issue).target.firstSuccessor.ledgerEvolution
    let original := (identityWhole live.state.resident.support).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  original_rows_are_the_whole_first_write live.state (refusedEvent live request issue)

theorem reject_retains_every_earlier_read
    (projection : live.state.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (reject live request issue).state.resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (live.state.resident.root.source.base.projectionLaw.outcomeAt projection
        (live.state.resident.root.emitted live.state.resident.visit.current)) :=
  earlier_reads_are_kept_at_the_landing live.state (refusedEvent live request issue) projection

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Live
