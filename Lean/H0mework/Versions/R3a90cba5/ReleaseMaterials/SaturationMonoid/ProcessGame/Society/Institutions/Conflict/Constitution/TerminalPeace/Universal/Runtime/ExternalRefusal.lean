import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime.Projection

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (StateAt)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  (prior : StateAt seed community cut)
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (origin : RawCurrent Party Good Technology Instrument) (roster : List Party)
  (menus : Menus Party Good Port Technology Instrument)

private def residentAt : Nat → StateAt seed community cut
  | 0 => prior
  | n + 1 => (run prior input origin roster menus n).state

variable (external : External.Trace Current (Write Party Good Port Technology Instrument))

/-- The independent external write is rejected at its first discrepant
position. The witness stores only that position and its original check. -/
structure ForeignProposal where
  position : Nat
  failed : ¬ external.Check (currentAt prior input origin roster menus) (writeAt prior input origin roster menus) position
  earlier : ∀ n < position,
    external.Check (currentAt prior input origin roster menus) (writeAt prior input origin roster menus) n

variable {prior input origin roster menus external}
  (fault : ForeignProposal prior input origin roster menus external)

abbrev originalVisit :=
  residentAt prior input origin roster menus (external.ordinal fault.position)

def recordForeignProposal :=
  Installation.Core.publish (originalVisit fault) fault true

theorem the_original_read_at_the_first_foreign_proposal
    (starts : external.current 0 = currentAt prior input origin roster menus 0) :
    (external.current fault.position).1 = (originalVisit fault).resident.erase := by
  have source := congrArg Prod.fst
    (external.read_at_checked_prefix (currentAt prior input origin roster menus)
      (writeAt prior input origin roster menus) starts fault.position fault.earlier)
  exact source.trans (by unfold originalVisit currentAt; cases external.ordinal fault.position <;> rfl)

theorem a_foreign_proposal_has_its_own_root_write_without_changing_any_original_row :
    let visit := originalVisit fault
    let action := Installation.Core.action visit fault true
    (⟨visit.world, action.target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
        (recordForeignProposal fault).state.resident.erase ∧
      (recordForeignProposal fault).state.stack = visit.stack ∧
      (recordForeignProposal fault).read = fault :=
  ⟨Installation.Core.the_canonical_write_is_the_published_whole_state _ _ _,
    Installation.Core.publish_preserves_the_entire_stack _ _ _,
    Installation.Core.publish_reads_the_exact_payload _ _ _⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Runtime
