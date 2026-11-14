import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedPaidPrefix

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SelectedCompletion

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


open private offset_actual selected_native native_distance from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedPaidPrefix
open private actual_stored finish_bounded from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.SelectedNativeHistory
open private SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion.RootInquiryProcessNode.resolve from
  H0mework.Versions.Rdf421ff6.Foundation.Inquiry.Engine

namespace Admission
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (nativeAfterAdmission)
end Admission
namespace Target
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockTarget
  (presentation birthProgram)
end Target
namespace Observed
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.StockObservation
  (root visit)
end Observed
namespace Query
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry
  (query)
end Query
namespace Shared
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared (query_unique)
end Shared

local notation "Packet" => PacketFit.Packet
local notation "nativeOf" => Admission.nativeAfterAdmission factory
local notation "length" => ActualNativePaidPrefix.length
local notation "tapeIndex" => Tape.index factory initial cfg language
local notation "nativeAt" => PacketFit.Table.packetAt factory initial cfg language

private abbrev frame (native : Packet) := ActualSourceSegmentBornEffect.selected native
private abbrev stock (native : Packet) := ActualSourceSegmentBornEffect.AS.stockCfg native.2.2.1
private abbrev presentation (native : Packet) := Target.presentation (frame native) (stock native)
private abbrev request (native : Packet) := Query.query (frame native) (stock native)

private abbrev event (native : Packet) :=
  (Observed.root (frame native) (stock native)).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
    (Observed.visit (frame native) (stock native))

private def action (native : Packet) :=
  (Target.birthProgram (frame native) (stock native)).generate (event native)

private abbrev terminalResolution (native : Packet) :=
  InternalInquiryResolutionAt.debtAdmission (state := presentation native)
    (query := request native) (action native)

private theorem resolves (native : Packet) :
    (RootInquiryProcessNode.active (presentation native)).resolve (request native) =
      terminalResolution native :=
  @RootInquiryProcessNode.active_debtAdmission_resolution_eq
    (presentation native) (request native) (Target.birthProgram (frame native) (stock native))
    (event native) (action native) (ActualSourceSegmentBornEffect.selected_settled native)

private def readReceipt (native : Packet) {node : RootInquiryProcessNode}
    (atSource : node = .active (presentation native)) (q : node.Query)
    (resolved : node.ResolutionAt q) (actual : resolved = node.resolve q)
    (receipt : RootInquiryProcessNode.ReceiptAt resolved) : (terminalResolution native).ReceiptAt := by
  cases atSource
  cases Shared.query_unique (frame native) (stock native) q
  exact Eq.mp (congrArg RootInquiryProcessNode.ReceiptAt (actual.trans (resolves native))) receipt

private def BornRootAt (native : Packet) (target : RootInquiryStatePresentation) : Prop :=
  (terminalResolution native).PreservesTargetLivingRootAt target

private theorem bornRoot (native : Packet) {node targetNode : RootInquiryProcessNode}
    (atSource : node = .active (presentation native)) (target : RootInquiryStatePresentation)
    (atTarget : targetNode = .active target) (q : node.Query)
    (whole : node.PreservesGeneratedLivingLawAt q targetNode) :
    BornRootAt native target := by
  cases atSource
  cases atTarget
  cases Shared.query_unique (frame native) (stock native) q
  change ((RootInquiryProcessNode.active (presentation native)).resolve
    (request native)).PreservesTargetLivingRootAt target at whole
  unfold BornRootAt
  exact Eq.mp (congrArg (fun resolution => resolution.PreservesTargetLivingRootAt target)
    (resolves native)) whole

private theorem bornFromToken (receiver : Packet) (token : ActivatedAt runtime)
    (atSource : token.1.engine.node = .active (presentation receiver))
    (target : RootInquiryStatePresentation) (atTarget : token.2.nextState.engine.node = .active target) :
    BornRootAt receiver target :=
  bornRoot receiver (node := token.1.engine.node) (targetNode := token.2.next.node)
    atSource target atTarget token.1.activation.query token.2.next_preservesGeneratedLivingLaw

variable (origin last : Nat) (table : Vector Packet (last + 1)) (cursor : Fin (last + 1))
variable (owned : RetainedLiveWindows.recorded observation nontrivial half depth origin last table)
variable (live : ReentryDifferenceClock.fee observation nontrivial half depth (origin + cursor.val + 1) ≠ 0)

local notation "moved" => RetainedLiveWindows.advance observation nontrivial half depth origin last table cursor owned live
local notation "ordinal" => (origin + 1 + Fin.val (Prod.fst (Prod.snd moved)))
local notation "packet" => (Prod.snd (Prod.snd (Prod.snd moved)))
local notation "native" => nativeOf packet
local notation "sourceTick" => tapeIndex (ordinal + 1)
local notation "endTick" => tapeIndex (ordinal + 1 + 1)
local notation "consumed" => SelectedPaidPrefix.consumeSelected observation nontrivial half depth origin last table cursor owned live
local notation "atStop" => Fin.last (length native)

private def stopToken {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState)
    (source : (type_of% (consumed history))) : ActivatedAt runtime :=
  source.2.2 (Fin.last (length (nativeOf source.1.1.1.2.2.2)))

local notation "stopAt" => stopToken observation nontrivial half depth origin last cursor

private theorem stop_presentation {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (stopAt history (consumed history)).1.engine.node = .active (presentation native) := by
  change ((consumed history).2.2 atStop).1.engine.node = _
  exact SelectedPaidPrefix.selected_offset_node
    observation nontrivial half depth origin last table cursor owned live history atStop

private def CompletionReceipt (receiver : Packet) := (terminalResolution receiver).ReceiptAt

private def receiptOf (receiver : Packet) (token : ActivatedAt runtime)
    (atSource : token.1.engine.node = .active (presentation receiver)) :
    CompletionReceipt receiver :=
  readReceipt receiver (node := token.1.engine.node) atSource token.1.activation.query
    token.2.resolution token.2.resolution_eq_generated token.2.receipt

/-- Consume the complete branch receipt read from the sealed settlement activation. -/
def finishSelected {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (type_of% (consumed history)) × CompletionReceipt native :=
  let source := consumed history
  (source, receiptOf observation nontrivial half depth native (stopAt history source)
    (stop_presentation observation nontrivial half depth origin last table cursor owned live history))

local notation "sealed" => SelectedNativeHistory.selectedWrite observation nontrivial half depth origin last table cursor owned live

private theorem stop_address :
    sourceTick + 1 + length native + 1 = endTick := by
  have final := Tape.history_end_index factory initial cfg language (ordinal + 1)
  have distance := native_distance observation nontrivial half depth (ordinal + 1)
  have same := congrArg (fun p : Packet => length p)
    (selected_native observation nontrivial half depth origin last table cursor owned live)
  rw [distance, ← same] at final
  omega

private theorem exit_actual {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (sealed history).2.2.1.2 = ⟨(runtime).stateAt endTick, ((runtime).stateAt endTick).tick⟩ :=
  actual_stored observation nontrivial half depth origin last table cursor owned live history
    ⟨endTick, finish_bounded observation nontrivial half depth ordinal paid⟩

/-- The next state of the same stored settlement token is the already retained exit activation. -/
theorem same_exit_activation {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (stopAt history (consumed history)).2.nextState = (sealed history).2.2.1.2.1 := by
  change ((consumed history).2.2 atStop).2.nextState = _
  have stop := offset_actual observation nontrivial half depth origin last table cursor owned live history atStop
  have reached := exit_actual observation nontrivial half depth origin last table cursor owned live history
  rw [stop, reached]
  exact congrArg (runtime).stateAt
    (stop_address observation nontrivial half depth origin last table cursor owned live)

private def bornTarget (n : Nat) : RootInquiryStatePresentation :=
  Tape.admissionPresentation factory (nativeAt n)

local notation "targetAt" => bornTarget observation nontrivial half depth

private theorem exit_node {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (sealed history).2.2.1.2.1.engine.node =
      .active (targetAt (ordinal + 2)) :=
  (congrArg (fun t : ActivatedAt runtime => t.1.engine.node)
    (exit_actual observation nontrivial half depth origin last table cursor owned live history)).trans
    (Tape.actual_index factory initial cfg language (ordinal + 2))

private theorem stop_next_node {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    (stopAt history (consumed history)).2.nextState.engine.node = .active (targetAt (ordinal + 2)) :=
  (congrArg (fun s : (runtime).State => s.engine.node)
    (same_exit_activation observation nontrivial half depth origin last table cursor owned live history)).trans
    (exit_node observation nontrivial half depth origin last table cursor owned live history)

/-- The full next root of the stored branch is the original born presentation. -/
theorem exact_born_root {paid : Nat} (history : HistoryAt runtime paid (runtime).initialState) :
    BornRootAt native (targetAt (ordinal + 2)) :=
  bornFromToken observation nontrivial half depth native (stopAt history (consumed history))
    (stop_presentation observation nontrivial half depth origin last table cursor owned live history)
    (targetAt (ordinal + 2))
    (stop_next_node observation nontrivial half depth origin last table cursor owned live history)

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.SelectedCompletion
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
