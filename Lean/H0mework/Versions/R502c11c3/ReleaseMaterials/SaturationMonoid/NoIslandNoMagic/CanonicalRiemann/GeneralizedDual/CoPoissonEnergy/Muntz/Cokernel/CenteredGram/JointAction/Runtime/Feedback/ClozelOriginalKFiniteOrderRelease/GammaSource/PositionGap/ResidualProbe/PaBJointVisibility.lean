import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.OutsideHistory.ResolventTimeMoments
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SourceLaunched
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierKFeedback

set_option autoImplicit false

noncomputable section
universe v

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PaBJointVisibility

open BurnolPhysicalState RootInquiryCompletion SourceNativeInquiryRuntime
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace

open private betaRead vector_ne from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.AdjointCofinalReturn
open private column_ne_zero from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FixedFourierKFeedback
open private literal_split from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private nativeLanguage from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private packet_whole_at from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.PacketFit
open private generated_at from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedNativeHistory

namespace Time
export BurnolPhysicalState.OriginalRSourceJointContact.OutsideHistory.ResolventTimeMoments
  (profile decay profile_continuous profile_norm moment_zero)
export SaturationMonoid.PositiveTimeJointMoments (moment joint_tail)
end Time

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "R" => burnolDirectRightResolventCLM c
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "V" => OriginalKDirectRCofinalReentrySourceAction.sourceReentryVector c
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "β" => betaRead observation half
local notation "fee" => ReentryDifferenceClock.fee observation nontrivial half depth
local notation "price" => FixedFourierKFeedback.price observation nontrivial half depth
local notation "feedback" => FixedFourierKFeedback.feedback observation nontrivial half depth

private def fixedReader : BurnolL2 →L[ℂ] ℂ :=
  innerSL ℂ (fourierL2 (burnolCompletedMellinRieszVector c : BurnolL2))

local notation "γ" => fixedReader observation half
local notation "a" => Time.profile β (raw 0) (BurnolCompletedMellinCoordinate.value c)
local notation "b" => Time.profile γ (raw 0) (BurnolCompletedMellinCoordinate.value c)

private theorem original_powers (ordinal : Nat) :
    raw ordinal = (R^ordinal) (raw 0) := by
  have same : OriginalKCombPhysicalAction.R observation nontrivial half = R :=
    ContinuousLinearMap.ext (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half)
  rw [OriginalKCombFirstFullSourceDynamics.raw_source_iterate, same, ← ContinuousLinearMap.toLinearMap_pow]
  rfl

private theorem pa_moment_zero (degree : Nat) : Time.moment a degree = 0 ↔ fee (degree+1) = 0 := by
  rw [ReentryDifferenceClock.literal_fee,
    original_powers observation nontrivial half depth (degree+1)]
  exact Time.moment_zero β (raw 0) c degree

private theorem outside_moment_zero (degree : Nat) : Time.moment b degree = 0 ↔ price (degree+1) = 0 := by
  rw [← FixedFourierKFeedback.actual_whole_price,
    original_powers observation nontrivial half depth (degree+1)]
  exact Time.moment_zero γ (raw 0) c degree

private theorem pa_moment_live : ∃ degree, Time.moment a degree ≠ 0 := by
  obtain ⟨index, after, live, _, _⟩ :=
    CountedNativeReentry.literal_return_cofinal observation nontrivial half depth 1
  cases index with
  | zero => omega
  | succ degree =>
    exact ⟨degree, fun erased => live ((pa_moment_zero observation nontrivial half depth degree).mp erased)⟩

private theorem outside_moment_live : ∃ degree, Time.moment b degree ≠ 0 := by
  obtain ⟨index, after, live, _⟩ :=
    FixedFourierKFeedback.actual_feedback_visible_from_each_tail observation nontrivial half depth 0
  rw [Nat.zero_add] at live
  cases index with
  | zero => omega
  | succ degree =>
    exact ⟨degree, fun erased => live ((outside_moment_zero observation nontrivial half depth degree).mp erased)⟩

/-- The same literal original R write returns Pa and changes its fixed-K outside field in every tail. -/
theorem joint_fee_tail (cutoff : Nat) :
    ∃ ordinal ≥ cutoff, fee ordinal ≠ 0 ∧ price ordinal ≠ 0 := by
  have decayPos : 0 < Time.decay (c).value := by
    have right := (c).rightHalf
    unfold Time.decay
    linarith
  obtain ⟨degree, after, pa, outside⟩ := Time.joint_tail a b
    (Time.profile_continuous β (raw 0) (c).value) (Time.profile_continuous γ (raw 0) (c).value)
    (Time.decay (c).value) (‖β‖*‖raw 0‖) (‖γ‖*‖raw 0‖) decayPos (by positivity) (by positivity)
    (fun t _ => Time.profile_norm β (raw 0) (c).value t)
    (fun t _ => Time.profile_norm γ (raw 0) (c).value t)
    (pa_moment_live observation nontrivial half depth)
    (outside_moment_live observation nontrivial half depth) cutoff
  exact ⟨degree+1, by omega,
    fun erased => pa ((pa_moment_zero observation nontrivial half depth degree).mpr erased),
    fun erased => outside ((outside_moment_zero observation nontrivial half depth degree).mpr erased)⟩

/-- Choose the first jointly visible literal write after the given cofinal address. -/
def selected (cutoff : Nat) : Nat := open Classical in
  Nat.find (joint_fee_tail observation nontrivial half depth (cutoff+1))

local notation "index" => selected observation nontrivial half depth

private theorem selected_live (cutoff : Nat) :
    cutoff+1 ≤ index cutoff ∧ fee (index cutoff) ≠ 0 ∧ price (index cutoff) ≠ 0 :=
  open Classical in Nat.find_spec (joint_fee_tail observation nontrivial half depth (cutoff+1))

local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "packetAt" => PacketFit.Table.packetAt factory initial cfg language
local notation "Packet" => PacketFit.Packet
local notation "whole" => PacketFit.packetWhole

def actualPair (cutoff : Nat) : Packet × Packet :=
  let table := PacketFit.Table.acquire factory initial cfg language (index cutoff) 1
  (table.get 0, table.get 1)

local notation "pair" => actualPair observation nontrivial half depth

private theorem exact_pair (cutoff : Nat) :
    pair cutoff = (packetAt (index cutoff), packetAt (index cutoff+1)) := by
  apply Prod.ext
  · change (PacketFit.Table.acquire factory initial cfg language (index cutoff) 1).get (0 : Fin 2) = _
    simpa only [Fin.val_zero, Nat.add_zero] using
      PacketFit.Table.acquire_at factory initial cfg language (index cutoff) 1 (0 : Fin 2)
  · change (PacketFit.Table.acquire factory initial cfg language (index cutoff) 1).get (1 : Fin 2) = _
    exact PacketFit.Table.acquire_at factory initial cfg language (index cutoff) 1 (1 : Fin 2)

private theorem packet_raw (ordinal : Nat) : whole (packetAt (ordinal+1)) = raw (ordinal+1) :=
  (packet_whole_at observation nontrivial half depth ordinal).trans
    (Native.calculated_target_raw_successor observation nontrivial half depth ordinal)

private theorem pair_fields (cutoff : Nat) :
    (whole (pair cutoff).1, whole (pair cutoff).2) = (raw (index cutoff), raw (index cutoff+1)) := by
  have positive := (Nat.zero_lt_succ cutoff).trans_le (selected_live observation nontrivial half depth cutoff).1
  have prior : index cutoff - 1 + 1 = index cutoff :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt positive)
  rw [exact_pair observation nontrivial half depth cutoff]
  exact Prod.ext
    ((congrArg whole (congrArg packetAt prior.symm)).trans
      ((packet_raw observation nontrivial half depth (index cutoff-1)).trans (congrArg raw prior)))
    (packet_raw observation nontrivial half depth (index cutoff))

def paEffect (packets : Packet × Packet) : BurnolPaAmbientCarrier :=
  E (whole packets.2) - E (R (E (whole packets.1) : BurnolL2))

def outsideEffect (packets : Packet × Packet) : BurnolL2 :=
  O (whole packets.2) - O (R (O (whole packets.1)))

/-- Both complete effect fields are computed on this same pair of actual dependent packets. -/
theorem pair_effects (cutoff : Nat) :
    paEffect observation half (pair cutoff) = fee (index cutoff) • V ∧
    outsideEffect observation half (pair cutoff) = feedback (index cutoff) := by
  have fields := pair_fields observation nontrivial half depth cutoff
  have first : whole (pair cutoff).1 = raw (index cutoff) := congrArg Prod.fst fields
  have second : whole (pair cutoff).2 = raw (index cutoff+1) := congrArg Prod.snd fields
  constructor
  · unfold paEffect
    rw [first, second]
    exact ReentryDifferenceClock.literal_write observation nontrivial half depth (index cutoff)
  · unfold outsideEffect FixedFourierKFeedback.feedback
    rw [first, second]
    have old := congrArg Prod.snd (literal_split observation nontrivial half depth (index cutoff))
    have next := congrArg Prod.snd (literal_split observation nontrivial half depth (index cutoff+1))
    exact congrArg₂ (fun old next : BurnolL2 => next - O (R old)) old next

private theorem visible (cutoff : Nat) :
    (∃ height : Nat, PhysicalPriceCountable.price
      (DenseDivisionPrice.height observation nontrivial half depth height)
      (paEffect observation half (pair cutoff)) ≠ 0) ∧
    outsideEffect observation half (pair cutoff) ≠ 0 := by
  have written := pair_effects observation nontrivial half depth cutoff
  have live := selected_live observation nontrivial half depth cutoff
  constructor
  · by_contra! silent
    have erased := DenseDivisionPrice.separates observation nontrivial half depth _ silent
    rw [written.1] at erased
    exact (smul_ne_zero live.2.1 (vector_ne observation nontrivial half)) erased
  · rw [written.2, FixedFourierKFeedback.actual_outside_feedback]
    exact smul_ne_zero (mul_ne_zero (by norm_num) live.2.2) (column_ne_zero observation nontrivial half)

namespace RootRead
export ActualCofinalRootResidualConsumer (consume)
end RootRead

/-- Keep both physical effects on the one literal packet pair and consume its original whole and next. -/
def consumeJoint {Result : Sort v} (cutoff : Nat)
    (consumer : (packets : Packet × Packet) →
      packets = (packetAt (index cutoff), packetAt (index cutoff+1)) →
      (∃ height : Nat, PhysicalPriceCountable.price
        (DenseDivisionPrice.height observation nontrivial half depth height)
        (paEffect observation half packets) ≠ 0) →
      outsideEffect observation half packets ≠ 0 →
      (type_of% (RootRead.consume factory initial cfg language (index cutoff+1))) →
      (type_of% (generated_at observation nontrivial half depth (index cutoff))) → Result) : Result :=
  let packets := pair cutoff
  let paid := visible observation nontrivial half depth cutoff
  consumer packets (exact_pair observation nontrivial half depth cutoff) paid.1 paid.2
    (RootRead.consume factory initial cfg language (index cutoff+1))
    (generated_at observation nontrivial half depth (index cutoff))

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.PaBJointVisibility
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
