import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedCompletion

set_option autoImplicit false
noncomputable section
universe u v

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SelectedBornRequest

open BurnolPhysicalState RootInquiryCompletion SourceNativeInquiryRuntime
open SourceOperationScalarInventoryLift

open private nativeLanguage from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledNativeTape
open private selected_packet_actual from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedNativeHistory

namespace C
export OriginalKDirectRCofinalMaterial.C (Value Var)
end C
namespace A
export ActualCofinalSourceAction (nativePacket packetTransport native_packet_actual actual_next_packet)
export ActualCofinalSourceAction.AS (AdmissionPacket nativeAfterAdmission bornAfterNative stockCfg)
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (answeredState request programme nextBorn)
end S
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (sourceAction_eq)
end J
namespace D
export RootGeneratedDebtActivationJointSource (initialEvent mathTarget mathAction)
end D
namespace RC
export ActualCofinalRootResidualConsumer
  (native born rootedMaterial rooted_material_source consume originalOldRow originalBornRow)
end RC

local instance sourceGroups (grade : Nat) : ∀ target, AddCommGroup
    (OriginalKDirectRCofinalMaterial.L.Value (PairValue C.Value) grade target) :=
  OriginalKDirectRCofinalMaterial.L.groups (PairValue C.Value) grade

private abbrev PacketIn (X : Unit → Type) := A.AdmissionPacket (W := PairValue C.Value) (X := X) (s := ())
local notation "Packet" => PacketFit.Packet
local notation "frame" => ActualSourceSegmentBornEffect.selected
private abbrev stock {X : Unit → Type} (native : PacketIn X) := A.stockCfg native.2.2.1

private def resolution {X : Unit → Type} (native : PacketIn X) :=
  let p := SelectedCompletion.Target.presentation (frame native) (stock native)
  let q := SelectedCompletion.Query.query (frame native) (stock native)
  let event := (SelectedCompletion.Observed.root (frame native) (stock native))
    |>.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
      (SelectedCompletion.Observed.visit (frame native) (stock native))
  let action := (SelectedCompletion.Target.birthProgram (frame native) (stock native)).generate event
  InternalInquiryResolutionAt.debtAdmission (state := p) (query := q) action

private def Receipt {X : Unit → Type} (native : PacketIn X) := (resolution native).ReceiptAt

private def receipt_transport {X Y : Unit → Type} (same : X = Y) (native : PacketIn X) :
    Receipt (A.packetTransport same native) → Receipt native := by
  cases same
  change Receipt native → Receipt native
  exact id

private theorem state_transport {X Y : Unit → Type} (same : X = Y) (packet : PacketIn X) :
    HEq (A.packetTransport same packet).2.1.1.event.state packet.2.1.1.event.state := by
  cases same
  rfl

private theorem state_eq {X : Unit → Type} {first second : PacketIn X} (same : first = second) :
    HEq first.2.1.1.event.state second.2.1.1.event.state := by
  cases same
  rfl

private def payment {X : Unit → Type} (native : PacketIn X) (receipt : Receipt native) :=
  (show (resolution native).ReceiptAt from receipt).2.down.1

private theorem frame_first_state {Sorts : Type u} {Value Var : Sorts → Type u}
    [∀ target, AddCommGroup (Value target)] {sort : Sorts}
    (born : RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame
      (Value := Value) (Var := Var) (sort := sort)) (first : born.depth = 0) :
    born.event.state = D.mathTarget (D.initialEvent born.registered) := by
  unfold RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation.Frame.event
  rw [first]
  rfl

/-- The receipt's first paid step generates the full state of the born registration. -/
private theorem paid_born_state {X : Unit → Type} (native : PacketIn X) (receipt : Receipt native) :
    (payment native receipt).1 = (A.bornAfterNative native).2.1.1.event.state := by
  let born := (A.bornAfterNative native).2.1.1
  have paid := (show (resolution native).ReceiptAt from receipt).2.down.2.down.1
  have generated : D.mathAction (D.initialEvent born.registered) = .inr (payment native receipt) := by
    dsimp only [born, A.bornAfterNative, S.nextBorn]
    exact (J.sourceAction_eq (S.answeredState (frame native) (stock native))
      (S.request (frame native)) (S.programme (frame native))).symm.trans paid
  have wrote : D.mathTarget (D.initialEvent born.registered) = (payment native receipt).1 := by
    unfold D.mathTarget
    rw [generated]
  exact wrote.symm.trans (frame_first_state born rfl).symm

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2 * (j + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "language" => nativeLanguage observation nontrivial half depth
local notation "runtime" => acquisitionRuntime observation nontrivial half depth
local notation "packetAt" => PacketFit.Table.packetAt factory initial cfg language
local notation "nativeAt" => RC.native factory initial cfg language
local notation "bornAt" => RC.born factory initial cfg language
local notation "materialAt" => RC.rootedMaterial factory initial cfg language

private def native_receipt (packet : Packet) (receipt : Receipt (A.nativeAfterAdmission factory packet)) :
    Receipt (A.nativePacket factory packet) :=
  receipt_transport packet.2.2.2.down (A.nativePacket factory packet)
    (Eq.mp (congrArg (fun receiver : Packet => Receipt receiver)
      (A.native_packet_actual factory packet)) receipt)

private def PaidNextAt (n : Nat) (receipt : Receipt (nativeAt n)) : Prop :=
  HEq (payment (nativeAt n) receipt).1 (materialAt n).state

private theorem first_paid_next (n : Nat) (receipt : Receipt (nativeAt n)) : PaidNextAt observation nontrivial half depth n receipt := by
  have step := heq_of_eq (paid_born_state (nativeAt n) receipt)
  have transport := state_transport (packetAt n).2.2.2.down (bornAt n)
  have same := state_eq (A.actual_next_packet factory initial cfg language n)
  have rooted := (RC.rooted_material_source factory initial cfg language n).2.2.1
  unfold PaidNextAt
  exact step.trans (transport.symm.trans (same.symm.trans rooted.symm))

variable (origin last : Nat) (table : Vector Packet (last + 1)) (cursor : Fin (last + 1))
variable (owned : RetainedLiveWindows.recorded observation nontrivial half depth origin last table)
variable (live : ReentryDifferenceClock.fee observation nontrivial half depth (origin + cursor.val + 1) ≠ 0)

local notation "moved" => RetainedLiveWindows.advance observation nontrivial half depth origin last table cursor owned live
local notation "n" => (origin + 1 + Fin.val (Prod.fst (Prod.snd moved)) + 1)
local notation "packet" => (Prod.snd (Prod.snd (Prod.snd moved)))
local notation "finish" => SelectedCompletion.finishSelected observation nontrivial half depth origin last table cursor owned live

private def selectedReceipt (receipt : Receipt (A.nativeAfterAdmission factory packet)) :
    Receipt (nativeAt n) :=
  let received := native_receipt observation nontrivial half packet receipt
  Eq.mp (congrArg (fun p : Packet => Receipt (A.nativePacket factory p))
    (selected_packet_actual observation nontrivial half depth origin last table cursor owned live)) received

/-- The same completed segment's first born payment reaches the material used by the next ledger consumer. -/
def consumeSelectedBirth {Result : Sort v} {paid : Nat}
    (history : HistoryAt runtime paid (runtime).initialState)
    (consume :
      (completed : type_of% (finish history)) →
      PaidNextAt observation nontrivial half depth n
        (selectedReceipt observation nontrivial half depth origin last table cursor owned live completed.2) →
      (type_of% (RC.consume factory initial cfg language n)) →
      (type_of% (RC.originalOldRow factory initial cfg language n)) →
      (type_of% (RC.originalBornRow factory initial cfg language n)) → Result) : Result :=
  let completed := finish history
  let receipt := selectedReceipt observation nontrivial half depth origin last table cursor owned live completed.2
  consume completed (first_paid_next observation nontrivial half depth n receipt)
    (RC.consume factory initial cfg language n)
    (RC.originalOldRow factory initial cfg language n)
    (RC.originalBornRow factory initial cfg language n)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SelectedBornRequest
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
