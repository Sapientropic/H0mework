import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaidContinuation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory

set_option autoImplicit false
noncomputable section

universe u

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

open RootInquiryCompletion SourceNativeInquiryRuntime

private theorem stored_history_preserves_its_occurrence_and_exact_prefix
    {process : SourceNativeInquiryEngineProcess.{u}} {runtime : SourceNativeInquiryRuntime process}
    {fuel : Nat} {state : runtime.State} (history : HistoryAt runtime fuel state)
    (i : Fin fuel) (total : Nat) (within : fuel ≤ total) :
    history.storedOccurrenceAt i = history.occurrenceAt i ∧
    (history.extendTo total within).prefix fuel within = history :=
  ⟨history.stored_occurrence_eq i, history.extendTo_prefix total within⟩

#eval IO.println "CP596_CONTROL + stored_history_preserves_its_occurrence_and_exact_prefix"

namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace PaidPrefixContinuationCertificate

open BurnolPhysicalState
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
open OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory (actual_relation_stock_next)
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)

open private sampleEnd from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "original" => scheduledNativeRun observation nontrivial half depth
local notation "withinOld" => actual_retained_length observation nontrivial half depth
local notation "continueAt" => continuedCandidate observation nontrivial half depth
local notation "token" => tapeOccurrence observation nontrivial half depth
local notation "ending" => sampleEnd observation nontrivial half depth
local notation "chosen" => paidPivot observation nontrivial half depth

private def preparedOriginal (start count : Nat) :=
  preparePaidRun observation nontrivial half depth start (count+1) (original start count) (withinOld start count)

private def preparedNewborn (start count : Nat) (row : Fin (count+1)) :=
  preparedMaterial observation nontrivial half depth start (count+1)
    (preparedOriginal observation nontrivial half depth start count) (Fin.last (count+1)) row

set_option cleanup.letToHave false in
private theorem preparation_reaches_the_newborn_at_every_retained_price
    (start count : Nat) (row : Fin (count+1)) :
    let reached := preparedNewborn observation nontrivial half depth start count row
    reached.1 = scheduledMaterial observation nontrivial half depth start (count+1) (start+(count+1)) row ∧
    type_of% reached.2.down :=
  ⟨rfl,(preparedNewborn observation nontrivial half depth start count row).2.down⟩

#eval IO.println "CP596_CONTROL + preparation_reaches_the_newborn_at_every_retained_price"

set_option cleanup.letToHave false in
private theorem the_paid_budget_preserves_both_existing_prefixes (start count : Nat) :
    type_of% (actual_paid_latest_time observation nontrivial half depth start (count+1)) ∧
    type_of% (actual_paid_continuation_length observation nontrivial half depth start (count+1)) ∧
    type_of% (actual_continued_preparation observation nontrivial half depth
      start (count+1) (original start count) (withinOld start count)) ∧
    type_of% (actual_continued_prefix observation nontrivial half depth
      start (count+1) (original start count) (withinOld start count)) :=
  ⟨actual_paid_latest_time observation nontrivial half depth start (count+1),
    actual_paid_continuation_length observation nontrivial half depth start (count+1),
    actual_continued_preparation observation nontrivial half depth
      start (count+1) (original start count) (withinOld start count),
    actual_continued_prefix observation nontrivial half depth
      start (count+1) (original start count) (withinOld start count)⟩

#eval IO.println "CP596_CONTROL + the_paid_budget_preserves_both_existing_prefixes"

set_option cleanup.letToHave false in
private def LiteralWholeNext (ordinal : Nat) : Prop :=
  type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
    type_of% (actual_division_action_same_root observation nontrivial half depth ordinal)

private theorem literal_whole_next (ordinal : Nat) :
    LiteralWholeNext observation nontrivial half depth ordinal :=
  ⟨actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

set_option cleanup.letToHave false in
private theorem resumed_candidate_feeds_the_same_token_and_original_writes
    (start count : Nat) (actor : Fin (count+2))
    (offset : CandidateOffsets observation nontrivial half depth start (count+1))
    (a : Record.Values (count+1)) (b : ℂ) :
    let nextCount := count+1
    let last := Fin.last nextCount
    type_of% (actual_continued_candidate observation nontrivial half depth
      start nextCount (original start count) (withinOld start count) actor offset) ∧
    type_of% (actual_continued_selected observation nontrivial half depth
      start nextCount (original start count) (withinOld start count) actor) ∧
    type_of% (actual_tape_whole observation nontrivial half depth start nextCount last last) ∧
    type_of% (actual_tape_next observation nontrivial half depth start nextCount last last) ∧
    type_of% (actual_selected_paid_writeback observation nontrivial half depth start count a b) ∧
    LiteralWholeNext observation nontrivial half depth
      (sampleSourceOrdinal observation nontrivial half depth start nextCount last last) :=
  ⟨actual_continued_candidate observation nontrivial half depth
      start (count+1) (original start count) (withinOld start count) actor offset,
    actual_continued_selected observation nontrivial half depth
      start (count+1) (original start count) (withinOld start count) actor,
    actual_tape_whole observation nontrivial half depth start (count+1) (Fin.last _) (Fin.last _),
    actual_tape_next observation nontrivial half depth start (count+1) (Fin.last _) (Fin.last _),
    actual_selected_paid_writeback observation nontrivial half depth start count a b,
    literal_whole_next observation nontrivial half depth _⟩

#eval IO.println "CP596_CONTROL + resumed_candidate_feeds_the_same_token_and_original_writes"

private theorem later_paid_continuation_cannot_reuse_the_old_final_token (start count : Nat) :
    token start count (Fin.last count) (Fin.last count) ≠
      continueAt start (count+1) (original start count) (withinOld start count)
        (Fin.last (count+1)) (chosen start (count+1)) := by
  intro same
  have oldNew := same.trans (actual_continued_selected observation nontrivial half depth
    start (count+1) (original start count) (withinOld start count) (Fin.last (count+1)))
  have sameEpoch := (actual_tape_occurrence_iff observation nontrivial half depth start count start (count+1)
    (Fin.last count) (Fin.last count) (Fin.last (count+1)) (Fin.last (count+1))).1 oldNew
  have sameEnd : ending start count (Fin.last count) (Fin.last count) =
      ending start (count+1) (Fin.last (count+1)) (Fin.last (count+1)) := by
    unfold sampleEnd
    rw [sameEpoch]
  exact (ne_of_lt (actual_tape_endpoint_strict observation nontrivial half depth start count)) sameEnd

#eval IO.println "CP596_CONTROL - later_paid_continuation_cannot_reuse_the_old_final_token"
#eval IO.println "CP596_GATE_PASS positive=4 negative=1"

end PaidPrefixContinuationCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
