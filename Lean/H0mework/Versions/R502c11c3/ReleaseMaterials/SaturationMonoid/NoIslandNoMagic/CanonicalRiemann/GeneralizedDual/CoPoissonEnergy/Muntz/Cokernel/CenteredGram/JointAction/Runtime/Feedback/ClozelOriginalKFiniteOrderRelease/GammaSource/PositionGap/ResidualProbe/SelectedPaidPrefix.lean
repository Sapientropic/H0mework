import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.UnitPortEnergy
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.PaidPrefix

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SelectedPaidPrefix

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

open private selected_packet_actual writeSize from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedNativeHistory
open private native_length_positive from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.PaidPrefix

namespace Admission
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (nativeAfterAdmission nativePresentation admission_native_full admission_native_distance)
end Admission
namespace Address
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (startAt index_eq_stop)
end Address
namespace Paid
export ActualNativePaidPrefix (length current paidMacro macro_target)
end Paid

local notation "index" => Tape.index factory initial cfg language
local notation "startAt" => Address.startAt factory initial cfg language
local notation "nativeOf" => Admission.nativeAfterAdmission factory
local notation "originalNative" =>
  OriginalKCofinalFullBranchFibre.KernelWrite.originalNative observation nontrivial half depth
local notation "width" => writeSize observation nontrivial half depth
local notation "Packet" => PacketFit.Packet

private theorem native_distance (n : Nat) :
    Tape.distance factory initial cfg language (index n + 1) = Paid.length (originalNative n) + 1 := by
  have actual := Admission.admission_native_distance factory initial cfg language (startAt n)
  rw [← Address.index_eq_stop factory initial cfg language n] at actual
  exact actual

private theorem native_node (n offset : Nat) (within : offset ≤ Paid.length (originalNative n)) :
    ((runtime).stateAt (index n + 1 + offset)).engine.node =
      .active (Admission.nativePresentation (originalNative n) offset) := by
  have full := Admission.admission_native_full factory initial cfg language (startAt n) offset within
  rw [← Address.index_eq_stop factory initial cfg language n] at full
  exact (Tape.actual_node factory initial cfg language (index n + 1 + offset)).trans
    (congrArg RootInquiryProcessNode.active full)

variable (origin last : Nat) (table : Vector Packet (last + 1)) (cursor : Fin (last + 1))
variable (owned : RetainedLiveWindows.recorded observation nontrivial half depth origin last table)
variable (live : ReentryDifferenceClock.fee observation nontrivial half depth (origin + cursor.val + 1) ≠ 0)

local notation "moved" => RetainedLiveWindows.advance observation nontrivial half depth origin last table cursor owned live
local notation "ordinal" => (origin + 1 + Fin.val (Prod.fst (Prod.snd moved)))
local notation "sourceTick" => index (ordinal + 1)
local notation "native" => nativeOf (Prod.snd (Prod.snd (Prod.snd moved)))
local notation "read" => JointFeeInverse.readSelected observation nontrivial half depth origin last table cursor owned live

private theorem selected_native :
    native = originalNative (ordinal + 1) :=
  congrArg nativeOf (selected_packet_actual observation nontrivial half depth origin last table cursor owned live)

private theorem offset_within (offset : Fin (Paid.length native + 1)) : offset.val + 1 < width ordinal := by
  have size := congrArg (fun p : Packet => Paid.length p + 1)
    (selected_native observation nontrivial half depth origin last table cursor owned live)
  have inside : offset.val < Paid.length (originalNative (ordinal + 1)) + 1 :=
    offset.isLt.trans_le (le_of_eq size)
  change offset.val + 1 < 1 + Tape.distance factory initial cfg language (sourceTick + 1)
  rw [native_distance observation nontrivial half depth (ordinal + 1)]
  omega

/-- Keep the selected sealed write and both physical fees, then consume its original paid prefix.
    The offset reader accesses that write's stored segment, including its own settlement slot. -/
def consumeSelected {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    Σ written : (type_of% (read history)),
      SourceNativePaidRootDebtMacroContinuationAt (Paid.current (nativeOf written.1.1.2.2.2) 0) ×
        (Fin (Paid.length (nativeOf written.1.1.2.2.2) + 1) → ActivatedAt runtime) :=
  let written := read history
  let receiver := nativeOf written.1.1.2.2.2
  let first : Fin (Paid.length receiver) := ⟨0, native_length_positive factory written.1.1.2.2.2⟩
  let segment := written.1.2.2.2
  ⟨written, Paid.paidMacro receiver first, fun offset =>
    segment.2.storedOccurrenceAt ⟨offset.val + 1,
      offset_within observation nontrivial half depth origin last table cursor owned live offset⟩⟩

local notation "consumed" => consumeSelected observation nontrivial half depth origin last table cursor owned live

theorem selected_macro_target {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (consumed history).2.1.target = Paid.current native (Paid.length native) :=
  Paid.macro_target native ⟨0, native_length_positive factory (moved).2.2.2⟩

/-- This is the strict debit of the original registered row at this selected write. -/
theorem selected_strict_debit {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (consumed history).2.1.target.budget < (Paid.current native 0).budget :=
  (consumed history).2.1.strictDebit

private theorem stored_segment_at (n : Nat) (slot : Fin (width n)) :
    (Tape.historyAt factory initial cfg language (n + 1)).storedOccurrenceAt slot =
      ⟨(runtime).stateAt (index (n + 1) + slot.val),
        ((runtime).stateAt (index (n + 1) + slot.val)).tick⟩ :=
  ((Tape.historyAt factory initial cfg language (n + 1)).stored_occurrence_eq slot).trans
    (occurrenceAt_runFrom runtime (index (n + 1)) (width n) slot)

private theorem offset_actual {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState)
    (offset : Fin (Paid.length native + 1)) :
    (consumed history).2.2 offset =
      ⟨(runtime).stateAt (sourceTick + 1 + offset.val),
        ((runtime).stateAt (sourceTick + 1 + offset.val)).tick⟩ := by
  let relative : Fin (width ordinal) := ⟨offset.val + 1,
    offset_within observation nontrivial half depth origin last table cursor owned live offset⟩
  have segment := SelectedNativeHistory.selected_segment_actual
    observation nontrivial half depth origin last table cursor owned live history
  let lookup (rows : Σ state : (runtime).State, HistoryAt runtime (width ordinal) state) :
      ActivatedAt runtime := rows.2.storedOccurrenceAt relative
  have same := congrArg lookup segment
  have found := stored_segment_at observation nontrivial half depth ordinal relative
  have address : sourceTick + relative.val = sourceTick + 1 + offset.val := by
    change sourceTick + (offset.val + 1) = _
    omega
  rw [address] at found
  dsimp only [consumeSelected, JointFeeInverse.readSelected]
  exact same.trans found

/-- Every stored paid offset is the original dependent native occurrence, including the stop. -/
theorem selected_offset_node {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState)
    (offset : Fin (Paid.length native + 1)) :
    ((consumed history).2.2 offset).1.engine.node =
      .active (Admission.nativePresentation native offset.val) := by
  have actual := offset_actual observation nontrivial half depth origin last table cursor owned live history offset
  have original := selected_native observation nontrivial half depth origin last table cursor owned live
  have within : offset.val ≤ Paid.length (originalNative (ordinal + 1)) :=
    (Nat.le_of_lt_succ offset.isLt).trans (le_of_eq (congrArg (fun p : Packet => Paid.length p) original))
  have nodeAt :=  native_node observation nontrivial half depth (ordinal + 1) offset.val within
  have received := congrArg (fun p : Packet => RootInquiryProcessNode.active
    (Admission.nativePresentation p offset.val)) original.symm
  exact (congrArg (fun token : ActivatedAt runtime => token.1.engine.node) actual).trans (nodeAt.trans received)

theorem selected_offset_receipt {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState)
    (offset : Fin (Paid.length native + 1)) :
    HEq ((consumed history).2.2 offset).2.receipt
      (Tape.actual_branch_receipt factory initial cfg language (sourceTick + 1 + offset.val)) := by
  rw [offset_actual observation nontrivial half depth origin last table cursor owned live history offset]
  rfl

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SelectedPaidPrefix
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
