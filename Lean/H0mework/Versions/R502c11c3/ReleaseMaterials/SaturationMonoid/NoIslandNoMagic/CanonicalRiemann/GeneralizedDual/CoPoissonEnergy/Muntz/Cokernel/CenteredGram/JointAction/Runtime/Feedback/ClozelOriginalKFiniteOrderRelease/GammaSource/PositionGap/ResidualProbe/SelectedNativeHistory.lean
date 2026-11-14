import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.NativeHistoryContinuation
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.RetainedLiveWindows

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SelectedNativeHistory

open BurnolPhysicalState RootInquiryCompletion SourceNativeInquiryRuntime
open SourceOperationScalarInventoryLift

open private nativeLanguage from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue OriginalKDirectRCofinalMaterial.C.Value) grade

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "runtime" => acquisitionRuntime observation nontrivial half depth
local notation "tapeIndex" => Tape.index factory initial cfg language
local notation "nativeAt" => PacketFit.Table.packetAt factory initial cfg language

variable (origin last : Nat) (table : Vector PacketFit.Packet (last + 1)) (cursor : Fin (last + 1))
variable (owned : RetainedLiveWindows.recorded observation nontrivial half depth origin last table)
variable (live : ReentryDifferenceClock.fee observation nontrivial half depth (origin + cursor.val + 1) ≠ 0)

local notation "moved" => RetainedLiveWindows.advance observation nontrivial half depth origin last table cursor owned live

private def writeSize (ordinal : Nat) : Nat :=
  1 + Tape.distance factory initial cfg language (tapeIndex (ordinal + 1) + 1)

private theorem end_address (ordinal : Nat) :
    tapeIndex (ordinal + 1) + writeSize observation nontrivial half depth ordinal =
      tapeIndex (ordinal + 2) :=
  Tape.history_end_index factory initial cfg language (ordinal + 1)

/-- Keep the paid prefix and reach the selected write's next activation. -/
def horizon (ordinal paid : Nat) : Nat := max paid (tapeIndex (ordinal + 2) + 1)

local notation "horizonAt" => horizon observation nontrivial half depth

private theorem finish_bounded (ordinal paid : Nat) : tapeIndex (ordinal + 2) < horizonAt ordinal paid :=
  (Nat.lt_succ_self _).trans_le (le_max_right _ _)

private theorem segment_bounded (ordinal paid : Nat) :
    tapeIndex (ordinal + 1) + writeSize observation nontrivial half depth ordinal ≤ horizonAt ordinal paid :=
  (end_address observation nontrivial half depth ordinal).trans_le
    (finish_bounded observation nontrivial half depth ordinal paid).le

private abbrev WriteAt (ordinal paid : Nat) :=
  HistoryAt runtime (horizonAt ordinal paid) (runtime).initialState ×
    ((ActivatedAt runtime × ActivatedAt runtime) ×
      (Σ state : (runtime).State, HistoryAt runtime (writeSize observation nontrivial half depth ordinal) state))

private def readAt (ordinal : Nat) {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    WriteAt observation nontrivial half depth ordinal paid :=
  let start := tapeIndex (ordinal + 1)
  let finish := tapeIndex (ordinal + 2)
  let retained := history.extendTo (horizonAt ordinal paid) (le_max_left _ _)
  let within := finish_bounded observation nontrivial half depth ordinal paid
  let earlier : start < finish :=
    Tape.strictMono factory initial cfg language (Nat.lt_succ_self (ordinal + 1))
  let ends := (retained.storedOccurrenceAt ⟨start, earlier.trans within⟩,
    retained.storedOccurrenceAt ⟨finish, within⟩)
  let segment := retained.window start (writeSize observation nontrivial half depth ordinal)
    (segment_bounded observation nontrivial half depth ordinal paid)
  (retained, ends, segment)

/-- Continue the table and the sealed history once. Return the selected write's original
    input and output activations, its whole microstep segment, and the retained prefixes. -/
def selectedWrite {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    Σ next : (type_of% moved), WriteAt observation nontrivial half depth (origin + 1 + next.2.1.val) paid :=
  let next := moved
  ⟨next, readAt observation nontrivial half depth (origin + 1 + next.2.1.val) history⟩

local notation "read" => selectedWrite observation nontrivial half depth origin last table cursor owned live
local notation "ordinal" => (origin + 1 + Fin.val (Prod.fst (Prod.snd moved)))
local notation "sourceTick" => tapeIndex (ordinal + 1)
local notation "nextTick" => tapeIndex (ordinal + 2)

private theorem selected_packet_actual :
    (moved).2.2.2 = nativeAt (ordinal + 1) := by
  have received := RetainedLiveWindows.advanced_cursor_packet
    observation nontrivial half depth origin last table cursor owned live
  have recorded := (RetainedLiveWindows.ready_again
    observation nontrivial half depth origin last table cursor owned live).1
  have stored : (moved).1.get (moved).2.1 = nativeAt (origin + 2 + (moved).2.1.val) :=
    recorded (moved).2.1
  have index : origin + 2 + (moved).2.1.val = ordinal + 1 := by omega
  exact (received.trans stored).trans (congrArg nativeAt index)

theorem retained_history {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (read history).2.1.prefix paid (le_max_left _ _) = history :=
  history.extendTo_prefix (horizonAt ordinal paid) (le_max_left _ _)

private theorem actual_stored {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState)
    (address : Fin (horizonAt ordinal paid)) :
    (read history).2.1.storedOccurrenceAt address =
      ⟨(runtime).stateAt address.val, ((runtime).stateAt address.val).tick⟩ := by
  let rows := (read history).2.1
  have run : rows = (runtime).run (horizonAt ordinal paid) := rows.eq_runFrom
  have actual := congrArg
    (fun rows : HistoryAt runtime (horizonAt ordinal paid) (runtime).initialState => rows.occurrenceAt address) run
  exact ((rows.stored_occurrence_eq address).trans actual).trans (occurrenceAt_run runtime _ address)

private theorem source_token_actual {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (read history).2.2.1.1 = ⟨(runtime).stateAt sourceTick, ((runtime).stateAt sourceTick).tick⟩ :=
  actual_stored observation nontrivial half depth origin last table cursor owned live history
    ⟨sourceTick, (Tape.strictMono factory initial cfg language (Nat.lt_succ_self (ordinal + 1))).trans
      (finish_bounded observation nontrivial half depth ordinal paid)⟩

theorem selected_source_token {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (read history).2.2.1.1.1.engine.node = .active (Tape.admissionPresentation factory (read history).1.2.2.2) := by
  have token := source_token_actual observation nontrivial half depth origin last table cursor owned live history
  have found := Tape.actual_index factory initial cfg language (ordinal + 1)
  have packet := selected_packet_actual observation nontrivial half depth origin last table cursor owned live
  change (read history).2.2.1.1.1.engine.node = .active (Tape.admissionPresentation factory (moved).2.2.2)
  rw [packet]
  exact (congrArg (fun a : ActivatedAt runtime => a.1.engine.node) token).trans found

/-- Read the dependent source receipt from the stored activation of the selected packet. -/
theorem selected_receipt {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    HEq (read history).2.2.1.1.2.receipt (Tape.actual_branch_receipt factory initial cfg language sourceTick) := by
  rw [source_token_actual observation nontrivial half depth origin last table cursor owned live history]
  rfl

theorem selected_segment_actual {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (read history).2.2.2 =
      ⟨(runtime).stateAt sourceTick, Tape.historyAt factory initial cfg language (ordinal + 1)⟩ := by
  let rows := (read history).2.1
  let size := writeSize observation nontrivial half depth ordinal
  let bounded := segment_bounded observation nontrivial half depth ordinal paid
  have run : rows = (runtime).run (horizonAt ordinal paid) := rows.eq_runFrom
  have transport := congrArg
    (fun rows : HistoryAt runtime (horizonAt ordinal paid) (runtime).initialState =>
      rows.window sourceTick size bounded) run
  exact transport.trans (window_run runtime _ sourceTick size bounded)

private theorem generated_at (n : Nat) :
    ((runtime).stateAt (tapeIndex (n + 2))).engine.node.erase =
      ActualCofinalRootResidualConsumer.generatedCurrent factory initial cfg language (n + 1) :=
  ActualCofinalRootResidualConsumer.actual_generated_current factory initial cfg language (n + 1)

/-- The exit token has the next current generated by this selected original whole write. -/
theorem selected_generated_current {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (read history).2.2.1.2.1.engine.node.erase =
      ActualCofinalRootResidualConsumer.generatedCurrent factory initial cfg language (ordinal + 1) := by
  have token : (read history).2.2.1.2 = ⟨(runtime).stateAt nextTick, ((runtime).stateAt nextTick).tick⟩ :=
    actual_stored observation nontrivial half depth origin last table cursor owned live history
      ⟨nextTick, finish_bounded observation nontrivial half depth ordinal paid⟩
  rw [token]
  exact generated_at observation nontrivial half depth ordinal

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SelectedNativeHistory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
