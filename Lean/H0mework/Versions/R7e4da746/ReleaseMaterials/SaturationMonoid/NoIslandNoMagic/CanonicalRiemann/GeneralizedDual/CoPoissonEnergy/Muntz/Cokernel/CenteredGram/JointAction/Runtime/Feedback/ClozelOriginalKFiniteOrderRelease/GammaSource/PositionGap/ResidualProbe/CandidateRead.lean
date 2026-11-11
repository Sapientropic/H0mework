import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.Window

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe

open BurnolPhysicalState RootInquiryCompletion SourceNativeInquiryRuntime SourceOperationScalarInventoryLift
open scoped InnerProductSpace

open private acquisitionStop from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.Window
open private nativeLanguage from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private paidAt materialWhole material_whole_is_target from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativePrice
open private sourcePrices from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CofinalPriceRecord
open private nextCutoff from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.CofinalRecord

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "runtime" => acquisitionRuntime observation nontrivial half depth
local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "packet" => Native.packet observation nontrivial half depth
local notation "bound" => acquisitionStop observation nontrivial half depth
local notation "cut" => sourceCutoff observation nontrivial half depth
local notation "length" => residualFuel observation nontrivial half depth

abbrev CandidateOffsets (start count : Nat) :=
  Fin (length start count (cut start count)+1)

local notation "Offsets" => CandidateOffsets observation nontrivial half depth

def candidateTime (start count : Nat) (offset : Offsets start count) : Nat :=
  cut start count+offset.val

local notation "time" => candidateTime observation nontrivial half depth

private theorem candidate_time_pos (start count : Nat) (offset : Offsets start count) :
    0 < time start count offset := by
  unfold candidateTime sourceCutoff nextCutoff
  omega

private def candidateEpoch (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :=
  start+actor.val+time start count offset-1

local notation "epoch" => candidateEpoch observation nontrivial half depth

private def candidateStart (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :=
  Tape.index factory initial cfg language (epoch start count actor offset+1)

private def candidateEnd (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :=
  Tape.index factory initial cfg language (epoch start count actor offset+2)

local notation "before" => candidateStart observation nontrivial half depth
local notation "after" => candidateEnd observation nontrivial half depth

private theorem candidate_end_within (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    after start count actor offset ≤ bound start count := by
  unfold candidateEnd acquisitionStop
  apply (Tape.strictMono factory initial cfg language).monotone
  have t : time start count offset ≤ latestTime observation nontrivial half depth start count :=
    Nat.add_le_add_left (Nat.le_of_lt_succ offset.isLt) (cut start count)
  have a : actor.val ≤ count := Nat.le_of_lt_succ actor.isLt
  change start+actor.val+time start count offset-1+2 ≤
    start+count+latestTime observation nontrivial half depth start count-1+2
  omega

private theorem candidate_start_le_end (start count : Nat) (actor : Fin (count+1))
    (offset : Offsets start count) : before start count actor offset ≤ after start count actor offset :=
  (Tape.strictMono factory initial cfg language).monotone (Nat.le_succ _)

private def boundedToken (start count tick : Nat) (within : tick ≤ bound start count) : ActivatedAt runtime :=
  (boundedNativeRun observation nontrivial half depth start count).occurrenceAt ⟨tick,Nat.lt_succ_of_le within⟩

private theorem bounded_token_at (start count tick : Nat) (within : tick ≤ bound start count) :
    boundedToken observation nontrivial half depth start count tick within =
      ⟨(runtime).stateAt tick,((runtime).stateAt tick).tick⟩ :=
  occurrenceAt_run (runtime) _ _

/-- Every candidate reads an actual token already present in the one bounded canonical run. -/
def candidateOccurrence (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    ActivatedAt runtime :=
  boundedToken observation nontrivial half depth start count (before start count actor offset)
    ((candidate_start_le_end observation nontrivial half depth start count actor offset).trans
      (candidate_end_within observation nontrivial half depth start count actor offset))

/-- Read the original native packet at the observed activation with its precise dependent identity. -/
def candidateAdmission (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    Σ p : (type_of% (packet 0)), PLift
      ((candidateOccurrence observation nontrivial half depth start count actor offset).1.engine.node =
        .active (Tape.admissionPresentation factory p)) := by
  refine ⟨packet (epoch start count actor offset),⟨?_⟩⟩
  unfold candidateOccurrence
  rw [bounded_token_at]
  exact Tape.actual_index factory initial cfg language (epoch start count actor offset+1)

private def paidCandidate (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    type_of% (paidAt observation nontrivial half depth (epoch start count actor offset)) :=
  let native := (candidateAdmission observation nontrivial half depth start count actor offset).1
  Native.actualMaterial native.2.1.1 native.2.2.1

private theorem paid_candidate_eq (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    paidCandidate observation nontrivial half depth start count actor offset =
      paidAt observation nontrivial half depth (epoch start count actor offset) := by
  unfold paidCandidate candidateAdmission paidAt
  rfl

/-- Price comes from the recorded packet's original paid expression, retaining the four source branches. -/
def candidatePrice (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) : ℂ :=
  reader c (OriginalKCombCofinalPaAction.Q
    (materialWhole observation nontrivial half depth (epoch start count actor offset)
      (paidCandidate observation nontrivial half depth start count actor offset)) : BurnolL2)

theorem actual_candidate_price (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    candidatePrice observation nontrivial half depth start count actor offset =
      sourcePrices observation nontrivial half depth start actor.val (time start count offset) := by
  let ordinal := epoch start count actor offset
  let read (v : BurnolL2) := reader c (OriginalKCombCofinalPaAction.Q v : BurnolL2)
  have field :=
    (material_whole_is_target observation nontrivial half depth ordinal).trans
      (Native.calculated_target_raw_successor observation nontrivial half depth ordinal)
  unfold candidatePrice
  rw [paid_candidate_eq]
  have index : ordinal+1=start+actor.val+time start count offset := by
    have positive := candidate_time_pos observation nontrivial half depth start count offset
    unfold ordinal candidateEpoch
    omega
  exact (congrArg read field).trans
    (congrArg (FixedFourierKFeedback.price observation nontrivial half depth) index)

private def segmentLengthAt (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) : Nat :=
  1+Tape.distance factory initial cfg language (before start count actor offset+1)

private theorem actual_candidate_segment_end (start count : Nat) (actor : Fin (count+1))
    (offset : Offsets start count) :
    before start count actor offset+segmentLengthAt observation nontrivial half depth start count actor offset =
      after start count actor offset :=
  Tape.history_end_index factory initial cfg language (epoch start count actor offset+1)

/-- Candidate acquisition also retains the complete paid native segment. -/
def candidatePaidSegment (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :=
  (boundedNativeRun observation nontrivial half depth start count).window
    (before start count actor offset) (segmentLengthAt observation nontrivial half depth start count actor offset)
    (by
      rw [actual_candidate_segment_end]
      exact (candidate_end_within observation nontrivial half depth start count actor offset).trans (Nat.le_succ _))

theorem actual_candidate_paid_segment (start count : Nat) (actor : Fin (count+1))
    (offset : Offsets start count) :
    candidatePaidSegment observation nontrivial half depth start count actor offset =
      ⟨(runtime).stateAt (before start count actor offset),
        Tape.historyAt factory initial cfg language (epoch start count actor offset+1)⟩ :=
  window_run (runtime) _ _ _ _

def candidateSuccessor (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    ActivatedAt runtime :=
  boundedToken observation nontrivial half depth start count (after start count actor offset)
    (candidate_end_within observation nontrivial half depth start count actor offset)

theorem actual_candidate_generated_current (start count : Nat) (actor : Fin (count+1))
    (offset : Offsets start count) :
    (candidateSuccessor observation nontrivial half depth start count actor offset).1.engine.node.erase =
      ActualCofinalRootResidualConsumer.generatedCurrent factory initial cfg language
        (epoch start count actor offset+1) := by
  unfold candidateSuccessor
  rw [bounded_token_at]
  exact ActualCofinalRootResidualConsumer.actual_generated_current factory initial cfg language _

theorem actual_candidate_whole (start count : Nat) (actor : Fin (count+1)) (offset : Offsets start count) :
    type_of% ((candidateOccurrence observation nontrivial half depth start count actor offset).2.next_preservesGeneratedLivingLaw) :=
  (candidateOccurrence observation nontrivial half depth start count actor offset).2.next_preservesGeneratedLivingLaw

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
