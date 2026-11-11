import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.NativeHistoryContinuation
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PaidPivot

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe

open BurnolPhysicalState Finset RootInquiryCompletion SourceNativeInquiryRuntime

open private acquisitionStop from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.Window
open private nativeLanguage sampleEnd from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private oldFit from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DelayedResidualProbe
open private nextCutoff from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord
open private candidateStart candidate_start_le_end candidate_end_within bounded_token_at from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.CandidateRead

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "runtime" => acquisitionRuntime observation nontrivial half depth
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "cut" => sourceCutoff observation nontrivial half depth
local notation "runLength" => acquisitionStop observation nontrivial half depth
local notation "chosen" => paidPivot observation nontrivial half depth
local notation "Offsets" => CandidateOffsets observation nontrivial half depth
local notation "packet" => Native.packet observation nontrivial half depth

private def admissionHorizon (start count time : Nat) : Nat :=
  Tape.index factory initial cfg language (start+count+time-1+2)+1

private def lastOldTime (start count : Nat) : Nat := cut start count-1

private theorem old_row_le_last (start count : Nat) (row : Fin count) :
    (schedule start count).val row ≤ lastOldTime observation nontrivial half depth start count := by
  unfold lastOldTime sourceCutoff nextCutoff
  rw [Nat.add_sub_cancel]
  exact Finset.le_sup (f := (schedule start count).val) (mem_univ row)

/-- The first continuation reaches all retained rows for the old and the newborn actors. -/
def preparationLength (start count : Nat) : Nat :=
  admissionHorizon observation nontrivial half depth start count
    (lastOldTime observation nontrivial half depth start count)

/-- Only already paid columns enter the second continuation's time bound. -/
def paidLatestTime (start count : Nat) : Nat :=
  cut start count+
    probeFuel observation half (probeBase observation start (cut start count)) count
      (Fin.snoc (fun j => -paidOldFit observation nontrivial half depth start count j) 1)
      (‖xiOpening observation half‖/4)

def paidContinuationLength (start count : Nat) : Nat :=
  admissionHorizon observation nontrivial half depth start count (paidLatestTime observation nontrivial half depth start count)

theorem actual_paid_latest_time (start count : Nat) :
    paidLatestTime observation nontrivial half depth start count = latestTime observation nontrivial half depth start count := by
  simp only [paidLatestTime,latestTime,residualFuel,fittedCoefficients,actual_paid_old_fit,oldFit]

theorem actual_paid_continuation_length (start count : Nat) :
    paidContinuationLength observation nontrivial half depth start count = runLength start count+1 := by
  unfold paidContinuationLength admissionHorizon acquisitionStop
  rw [actual_paid_latest_time]

local notation "prepared" => preparationLength observation nontrivial half depth
local notation "finished" => paidContinuationLength observation nontrivial half depth

private theorem preparation_le_paid (start count : Nat) : prepared start count ≤ finished start count := by
  unfold preparationLength paidContinuationLength admissionHorizon
  apply Nat.succ_le_succ
  apply (Tape.strictMono factory initial cfg language).monotone
  have old : lastOldTime observation nontrivial half depth start count ≤ cut start count := Nat.sub_le _ _
  have future : cut start count ≤ paidLatestTime observation nontrivial half depth start count := Nat.le_add_right _ _
  omega

theorem actual_retained_length (start count : Nat) :
    sampleEnd observation nontrivial half depth start count (Fin.last count) (Fin.last count)+1 ≤
      prepared start (count+1) := by
  unfold sampleEnd preparationLength admissionHorizon
  apply Nat.succ_le_succ
  apply (Tape.strictMono factory initial cfg language).monotone
  have old := old_row_le_last observation nontrivial half depth start (count+1) (Fin.last count)
  change start+count+(schedule start (count+1)).val (Fin.last count)-1+2 ≤
    start+(count+1)+lastOldTime observation nontrivial half depth start (count+1)-1+2
  omega

abbrev NativeRun (length : Nat) := HistoryAt (runtime) length (runtime).initialState

/-- Extend an actually retained canonical history to the point at which the old fit is paid. -/
def preparePaidRun (start count : Nat) {priorLength : Nat}
    (prior : NativeRun observation nontrivial half depth priorLength) (within : priorLength ≤ prepared start count) :=
  prior.extendTo (prepared start count) within

/-- Retain the prepared prefix and execute only its missing suffix to the paid bound. -/
def continuePaidRun (start count : Nat) {priorLength : Nat}
    (prior : NativeRun observation nontrivial half depth priorLength) (within : priorLength ≤ prepared start count) :=
  (preparePaidRun observation nontrivial half depth start count prior within).extendTo
    (finished start count) (preparation_le_paid observation nontrivial half depth start count)

theorem actual_continued_preparation (start count : Nat) {priorLength : Nat}
    (prior : NativeRun observation nontrivial half depth priorLength) (within : priorLength ≤ prepared start count) :
    (continuePaidRun observation nontrivial half depth start count prior within).prefix
      (prepared start count) (preparation_le_paid observation nontrivial half depth start count) =
      preparePaidRun observation nontrivial half depth start count prior within :=
  HistoryAt.extendTo_prefix _ _ _

theorem actual_continued_prefix (start count : Nat) {priorLength : Nat}
    (prior : NativeRun observation nontrivial half depth priorLength) (within : priorLength ≤ prepared start count) :
    (continuePaidRun observation nontrivial half depth start count prior within).prefix priorLength
      (within.trans (preparation_le_paid observation nontrivial half depth start count)) = prior := by
  have canonical := (continuePaidRun observation nontrivial half depth start count prior within).eq_runFrom
  rw [canonical,prefix_runFrom]
  exact prior.eq_runFrom.symm

private def retainedOrdinal (start count : Nat) (actor : Fin (count+1)) (row : Fin count) : Nat :=
  (scheduledMaterial observation nontrivial half depth start count (start+actor.val) row).1

private def retainedAddress (start count : Nat) (actor : Fin (count+1)) (row : Fin count) : Nat :=
  Tape.index factory initial cfg language (retainedOrdinal observation nontrivial half depth start count actor row+1)

private theorem retained_address_in_prepared (start count : Nat) (actor : Fin (count+1)) (row : Fin count) :
    retainedAddress observation nontrivial half depth start count actor row < prepared start count := by
  unfold retainedAddress preparationLength admissionHorizon
  apply Nat.lt_succ_of_le
  apply (Tape.strictMono factory initial cfg language).monotone
  have actorBound : actor.val ≤ count := Nat.le_of_lt_succ actor.isLt
  have rowBound := old_row_le_last observation nontrivial half depth start count row
  change start+actor.val+(schedule start count).val row-1+1 ≤
    start+count+lastOldTime observation nontrivial half depth start count-1+2
  omega

private def preparedOccurrence (start count : Nat) (history : NativeRun observation nontrivial half depth (prepared start count))
    (actor : Fin (count+1)) (row : Fin count) : ActivatedAt runtime :=
  history.storedOccurrenceAt ⟨retainedAddress observation nontrivial half depth start count actor row,
    retained_address_in_prepared observation nontrivial half depth start count actor row⟩

/-- Every vector used by the old fit has its exact original material in the prepared execution. -/
def preparedMaterial (start count : Nat) (history : NativeRun observation nontrivial half depth (prepared start count))
    (actor : Fin (count+1)) (row : Fin count) :
    Σ material : (type_of% (scheduledMaterial observation nontrivial half depth start count (start+actor.val) row)),
      PLift ((preparedOccurrence observation nontrivial half depth start count history actor row).1.engine.node =
        .active (Tape.admissionPresentation factory (packet material.1))) := by
  refine ⟨scheduledMaterial observation nontrivial half depth start count (start+actor.val) row,⟨?_⟩⟩
  have canonical : history = (runtime).run (prepared start count) := history.eq_runFrom
  unfold preparedOccurrence
  rw [HistoryAt.stored_occurrence_eq,canonical,occurrenceAt_run]
  exact Tape.actual_index factory initial cfg language
    (retainedOrdinal observation nontrivial half depth start count actor row+1)

private theorem candidate_within (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    candidateStart observation nontrivial half depth start count actor offset < finished start count := by
  rw [actual_paid_continuation_length]
  exact Nat.lt_succ_of_le ((candidate_start_le_end observation nontrivial half depth start count actor offset).trans
    (candidate_end_within observation nontrivial half depth start count actor offset))

/-- Look up a candidate in the resumed history, retaining its exact activated token. -/
def continuedCandidate (start count : Nat) {priorLength : Nat}
    (prior : NativeRun observation nontrivial half depth priorLength) (within : priorLength ≤ prepared start count)
    (actor : Fin (count+1)) (offset : Offsets start count) : ActivatedAt runtime :=
  (continuePaidRun observation nontrivial half depth start count prior within).storedOccurrenceAt
    ⟨candidateStart observation nontrivial half depth start count actor offset,
      candidate_within observation nontrivial half depth start count actor offset⟩

theorem actual_continued_candidate (start count : Nat) {priorLength : Nat}
    (prior : NativeRun observation nontrivial half depth priorLength) (within : priorLength ≤ prepared start count)
    (actor : Fin (count+1)) (offset : Offsets start count) :
    continuedCandidate observation nontrivial half depth start count prior within actor offset =
      candidateOccurrence observation nontrivial half depth start count actor offset := by
  have canonical : continuePaidRun observation nontrivial half depth start count prior within =
      (runtime).run (finished start count) :=
    (continuePaidRun observation nontrivial half depth start count prior within).eq_runFrom
  unfold continuedCandidate
  rw [HistoryAt.stored_occurrence_eq,canonical,occurrenceAt_run,candidateOccurrence,bounded_token_at]

/-- The resumed execution feeds the full token of the original selected paid occurrence. -/
theorem actual_continued_selected (start count : Nat) {priorLength : Nat}
    (prior : NativeRun observation nontrivial half depth priorLength) (within : priorLength ≤ prepared start count)
    (actor : Fin (count+1)) :
    continuedCandidate observation nontrivial half depth start count prior within actor (chosen start count) =
      tapeOccurrence observation nontrivial half depth start count actor (Fin.last count) :=
  (actual_continued_candidate observation nontrivial half depth start count prior within actor
    (chosen start count)).trans (actual_selected_occurrence observation nontrivial half depth start count actor)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
