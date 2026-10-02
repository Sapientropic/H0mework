import H0mework.Versions.R2.Foundation.Semantics.RootReality

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace GroundedFaithfulRealization

open TotalReality CausalCore ZeroLawRootAdmission

universe u
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {root : SourceNativeLivingRootClosure N V}

abbrev Visit (root : SourceNativeLivingRootClosure N V) :=
  SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot

def recover {process : Process root.toAnswerNextCausalWorld}
    (faithful : FaithfulRealization root.toAnswerNextCausalWorld process)
    (visit : Visit root) (event : process.EventAt (ULift.up visit)) :=
  ((faithful.occurrencePresentation (ULift.up visit)).invFun event).down

theorem recover_eq_generated {process : Process root.toAnswerNextCausalWorld}
    (faithful : FaithfulRealization root.toAnswerNextCausalWorld process)
    (visit : Visit root) (event : process.EventAt (ULift.up visit)) :
    recover faithful visit event = root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit :=
  (recover faithful visit event).eq_generated

theorem event_eq_emitted {process : Process root.toAnswerNextCausalWorld}
    (faithful : FaithfulRealization root.toAnswerNextCausalWorld process)
    (visit : Visit root) (event : process.EventAt (ULift.up visit)) :
    event = process.emitted (ULift.up visit) := by
  let presentation := faithful.occurrencePresentation (ULift.up visit)
  have original : presentation.invFun event = root.toAnswerNextCausalWorld.emitted (ULift.up visit) := by
    exact congrArg ULift.up (recover_eq_generated faithful visit event)
  calc
    event = presentation.toFun (presentation.invFun event) := (presentation.right_inv event).symm
    _ = presentation.toFun (root.toAnswerNextCausalWorld.emitted (ULift.up visit)) := congrArg presentation.toFun original
    _ = process.emitted (ULift.up visit) := faithful.emitted_commutes (ULift.up visit)

def representedVisit (process : Process root.toAnswerNextCausalWorld) (visit : Visit root) :
    Σ current : Visit root, process.EventAt (ULift.up current) :=
  ⟨visit, process.emitted (ULift.up visit)⟩

theorem representedVisit_injective (process : Process root.toAnswerNextCausalWorld) :
    Function.Injective (representedVisit process) := by
  intro left right same
  exact congrArg Sigma.fst same

theorem grounded_iff_represented_difference (process : Process root.toAnswerNextCausalWorld)
    (left right : Visit root) :
    InternallyDeterminedAt (RootTotalReality.semantics root.toAuthoritativeRoot) (left, right) ↔
      representedVisit process left ≠ representedVisit process right := by
  constructor
  · intro grounded same
    exact grounded.actualDifference.realDifference (representedVisit_injective process same)
  · intro different
    have unequal : left ≠ right := fun same => different (congrArg (representedVisit process) same)
    exact ⟨RootTotalReality.actualDifference root.toAuthoritativeRoot unequal,
      LawfulWorldStateAt.registeredOccurrence_ne_of_ne unequal⟩

theorem recovered_projection {process : Process root.toAnswerNextCausalWorld}
    (faithful : FaithfulRealization root.toAnswerNextCausalWorld process)
    (visit : Visit root) (event : process.EventAt (ULift.up visit))
    (projection : root.toAuthoritativeRoot.source.projectionLaw.Projection) :
    HEq ((recover faithful visit event).projectionOutcome projection)
      (root.toAuthoritativeRoot.projectionOutcomeAt projection visit.current) :=
  (recover faithful visit event).projectionOutcome_heq_sourceOutcome projection

theorem compiled_next (process : Process root.toAnswerNextCausalWorld)
    (visit : Visit root) (event : process.EventAt (ULift.up visit)) :
    (process.compile event).nextCurrent = root.generatedNextCurrentAt visit := rfl

def comparison
    {left right : Process root.toAnswerNextCausalWorld}
    (leftFaithful : FaithfulRealization root.toAnswerNextCausalWorld left)
    (rightFaithful : FaithfulRealization root.toAnswerNextCausalWorld right) :
    ProcessCommutingPresentation left right :=
  leftFaithful.commutingPresentation root.answerNextNoSuspendedCausalMagic rightFaithful

theorem comparison_unique
    {left right : Process root.toAnswerNextCausalWorld}
    (leftFaithful : FaithfulRealization root.toAnswerNextCausalWorld left)
    (rightFaithful : FaithfulRealization root.toAnswerNextCausalWorld right)
    (candidate : (current : SourceNativeLivingRootCausalCurrentAt root) →
      left.EventAt current → right.EventAt current)
    (current : SourceNativeLivingRootCausalCurrentAt root) (event : left.EventAt current) :
    candidate current event = ((comparison leftFaithful rightFaithful).eventPresentation current).toFun event := by
  rcases current with ⟨visit⟩
  exact (event_eq_emitted rightFaithful visit (candidate (ULift.up visit) event)).trans
    (event_eq_emitted rightFaithful visit (((comparison leftFaithful rightFaithful).eventPresentation (ULift.up visit)).toFun event)).symm

theorem source_generates_unique_comparison
    {left right : Process root.toAnswerNextCausalWorld}
    (leftFaithful : FaithfulRealization root.toAnswerNextCausalWorld left)
    (rightFaithful : FaithfulRealization root.toAnswerNextCausalWorld right) :
    ∃ generated : ProcessCommutingPresentation left right,
      ∀ candidate : ProcessCommutingPresentation left right,
      ∀ current event, (candidate.eventPresentation current).toFun event =
        (generated.eventPresentation current).toFun event :=
  ⟨comparison leftFaithful rightFaithful,
    fun candidate current event => comparison_unique leftFaithful rightFaithful
      (fun current => (candidate.eventPresentation current).toFun) current event⟩

theorem source_generates_faithful_realization (root : SourceNativeLivingRootClosure N V) :
    Nonempty (Σ process : Process root.toAnswerNextCausalWorld,
      FaithfulRealization root.toAnswerNextCausalWorld process) :=
  ⟨⟨root.canonicalAnswerNextCausalProcess, root.canonicalAnswerNextFaithfulRealization⟩⟩

end GroundedFaithfulRealization
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
