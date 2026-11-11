import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.NativeHistoryLookup
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ScheduledPriceMatrix

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects
open SourceNativeInquiryRuntime

namespace Tape
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
  (sourceRuntime index strictMono actual_index distance historyAt history_end_index)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions.AS
  (admissionPresentation)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily
  (actual_branch_receipt actual_node)
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Actual
  (erasure_injective)
end Tape

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "factory" => Native.factory observation nontrivial half
local notation "initial" => Native.initial observation nontrivial half depth
local notation "cfg" => Native.firstCfg observation nontrivial half depth
local notation "schedule" => priceSchedule observation nontrivial half depth
local notation "packet" => Native.packet observation nontrivial half depth

private theorem nativeLanguage : (cfg).LowVar = OriginalKCombReceiptFeedback.Var := rfl
local notation "language" => nativeLanguage observation nontrivial half depth

def acquisitionRuntime := Tape.sourceRuntime factory initial cfg language

local notation "runtime" => acquisitionRuntime observation nontrivial half depth

def sampleSourceOrdinal (start count : Nat) (actor row : Fin (count+1)) : Nat :=
  (scheduledMaterial observation nontrivial half depth start (count+1) (start+actor.val) row).1

def sampleAdmissionTick (start count : Nat) (actor row : Fin (count+1)) : Nat :=
  Tape.index factory initial cfg language (sampleSourceOrdinal observation nontrivial half depth start count actor row+1)

private def sampleEnd (start count : Nat) (actor row : Fin (count+1)) : Nat :=
  Tape.index factory initial cfg language (sampleSourceOrdinal observation nontrivial half depth start count actor row+2)

local notation "ending" => sampleEnd observation nontrivial half depth
local notation "epoch" => sampleSourceOrdinal observation nontrivial half depth
local notation "address" => sampleAdmissionTick observation nontrivial half depth

private theorem row_time_le_last (start count : Nat) (row : Fin (count+1)) :
    (schedule start (count+1)).val row ≤ (schedule start (count+1)).val (Fin.last count) := by
  refine Fin.lastCases le_rfl (fun i => ?_) row
  have retained : (schedule start (count+1)).val i.castSucc = (schedule start count).val i := by
    simp only [priceSchedule, Record.schedule_prior]
  rw [retained]
  exact (actual_price_record_fresh observation nontrivial half depth start count i).le

private theorem epoch_le_last (start count : Nat) (actor row : Fin (count+1)) :
    epoch start count actor row ≤ epoch start count (Fin.last count) (Fin.last count) := by
  have earlierActor : actor.val ≤ count := Nat.le_of_lt_succ actor.isLt
  have earlierRow := row_time_le_last observation nontrivial half depth start count row
  change start+actor.val+(schedule start (count+1)).val row-1 ≤
    start+count+(schedule start (count+1)).val (Fin.last count)-1
  omega

private theorem sample_end_le_last (start count : Nat) (actor row : Fin (count+1)) :
    ending start count actor row ≤ ending start count (Fin.last count) (Fin.last count) :=
  (Tape.strictMono factory initial cfg language).monotone
    (Nat.add_le_add_right (epoch_le_last observation nontrivial half depth start count actor row) 2)

private theorem sample_tick_le_end (start count : Nat) (actor row : Fin (count+1)) :
    address start count actor row ≤ ending start count actor row :=
  (Tape.strictMono factory initial cfg language).monotone (Nat.le_succ _)

theorem actual_tape_endpoint_strict (start count : Nat) :
    ending start count (Fin.last count) (Fin.last count) <
      ending start (count+1) (Fin.last (count+1)) (Fin.last (count+1)) := by
  unfold sampleEnd
  apply Tape.strictMono factory initial cfg language
  have later : (schedule start (count+1)).val (Fin.last count) <
      (schedule start (count+2)).val (Fin.last (count+1)) :=
    actual_price_record_fresh observation nontrivial half depth start (count+1) (Fin.last count)
  change (start+count+(schedule start (count+1)).val (Fin.last count)-1)+2 <
    (start+(count+1)+(schedule start (count+2)).val (Fin.last (count+1))-1)+2
  omega

/-- The original runtime runs through the next admission of every sampled action. -/
def scheduledNativeRun (start count : Nat) :=
  (runtime).run (ending start count (Fin.last count) (Fin.last count)+1)

def tapeOccurrence (start count : Nat) (actor row : Fin (count+1)) : ActivatedAt runtime :=
  (scheduledNativeRun observation nontrivial half depth start count).occurrenceAt
    ⟨address start count actor row,
      Nat.lt_succ_of_le ((sample_tick_le_end observation nontrivial half depth start count actor row).trans
        (sample_end_le_last observation nontrivial half depth start count actor row))⟩

theorem actual_tape_occurrence (start count : Nat) (actor row : Fin (count+1)) :
    tapeOccurrence observation nontrivial half depth start count actor row =
      ⟨(runtime).stateAt (address start count actor row),((runtime).stateAt (address start count actor row)).tick⟩ :=
  occurrenceAt_run runtime _ _

/-- Cells share the full activation exactly when they address the same original source ordinal. -/
theorem actual_tape_occurrence_iff (start count start' count' : Nat)
    (actor row : Fin (count+1)) (actor' row' : Fin (count'+1)) :
    tapeOccurrence observation nontrivial half depth start count actor row =
        tapeOccurrence observation nontrivial half depth start' count' actor' row' ↔
      epoch start count actor row = epoch start' count' actor' row' := by
  rw [actual_tape_occurrence,actual_tape_occurrence]
  constructor
  · intro same
    have nodes := congrArg (fun token : ActivatedAt runtime => token.1.engine.node.erase) same
    change ((runtime).stateAt (address start count actor row)).engine.node.erase =
      ((runtime).stateAt (address start' count' actor' row')).engine.node.erase at nodes
    have first := congrArg RootInquiryProcessNode.erase
      (Tape.actual_node factory initial cfg language (address start count actor row))
    have second := congrArg RootInquiryProcessNode.erase
      (Tape.actual_node factory initial cfg language (address start' count' actor' row'))
    have equalTick := Tape.erasure_injective factory initial cfg language ((first.symm.trans nodes).trans second)
    exact Nat.succ.inj ((Tape.strictMono factory initial cfg language).injective equalTick)
  · intro same
    unfold sampleAdmissionTick
    rw [same]

/-- Lookup exposes the precise native packet of the sampled material, with its original activation. -/
theorem actual_tape_packet (start count : Nat) (actor row : Fin (count+1)) :
    (tapeOccurrence observation nontrivial half depth start count actor row).1.engine.node =
      .active (Tape.admissionPresentation factory (packet (epoch start count actor row))) := by
  rw [actual_tape_occurrence]
  exact Tape.actual_index factory initial cfg language (epoch start count actor row+1)

def tapeReceipt (start count : Nat) (actor row : Fin (count+1)) :=
  (tapeOccurrence observation nontrivial half depth start count actor row).2.receipt

theorem actual_tape_receipt (start count : Nat) (actor row : Fin (count+1)) :
    HEq (tapeReceipt observation nontrivial half depth start count actor row)
      (Tape.actual_branch_receipt factory initial cfg language (address start count actor row)) := by
  unfold tapeReceipt
  rw [actual_tape_occurrence]
  rfl

private def segmentLength (start count : Nat) (actor row : Fin (count+1)) : Nat :=
  1+Tape.distance factory initial cfg language (address start count actor row+1)

private theorem sample_segment_end (start count : Nat) (actor row : Fin (count+1)) :
    address start count actor row+segmentLength observation nontrivial half depth start count actor row =
      ending start count actor row :=
  Tape.history_end_index factory initial cfg language (epoch start count actor row+1)

/-- Read the entire original paid action directly from the stored execution. -/
def tapePaidSegment (start count : Nat) (actor row : Fin (count+1)) :=
  (scheduledNativeRun observation nontrivial half depth start count).window
    (address start count actor row) (segmentLength observation nontrivial half depth start count actor row)
    (by
      rw [sample_segment_end]
      exact (sample_end_le_last observation nontrivial half depth start count actor row).trans (Nat.le_succ _))

theorem actual_tape_paid_segment (start count : Nat) (actor row : Fin (count+1)) :
    tapePaidSegment observation nontrivial half depth start count actor row =
      ⟨(runtime).stateAt (address start count actor row),
        Tape.historyAt factory initial cfg language (epoch start count actor row+1)⟩ :=
  window_run runtime _ _ _ _

/-- The next cofinal current is read from the same stored execution as the paid segment. -/
def tapeEndOccurrence (start count : Nat) (actor row : Fin (count+1)) : ActivatedAt runtime :=
  (scheduledNativeRun observation nontrivial half depth start count).occurrenceAt
    ⟨ending start count actor row,
      Nat.lt_succ_of_le (sample_end_le_last observation nontrivial half depth start count actor row)⟩

theorem actual_tape_generated_current (start count : Nat) (actor row : Fin (count+1)) :
    (tapeEndOccurrence observation nontrivial half depth start count actor row).1.engine.node.erase =
      ActualCofinalRootResidualConsumer.generatedCurrent factory initial cfg language
        (epoch start count actor row+1) := by
  unfold tapeEndOccurrence scheduledNativeRun
  rw [occurrenceAt_run]
  exact ActualCofinalRootResidualConsumer.actual_generated_current factory initial cfg language
    (epoch start count actor row+1)

/-- Adding a scheduled birth preserves the complete earlier canonical execution. -/
theorem actual_tape_prefix (start count : Nat) :
    (scheduledNativeRun observation nontrivial half depth start (count+1)).prefix
      (ending start count (Fin.last count) (Fin.last count)+1)
      (Nat.succ_le_succ (actual_tape_endpoint_strict observation nontrivial half depth start count).le) =
      scheduledNativeRun observation nontrivial half depth start count :=
  prefix_runFrom runtime (runtime).initialState _ _ _

theorem actual_tape_retains_prior (start count : Nat) (actor row : Fin (count+1)) :
    tapeOccurrence observation nontrivial half depth start (count+1) actor.castSucc row.castSucc =
      tapeOccurrence observation nontrivial half depth start count actor row := by
  apply (actual_tape_occurrence_iff observation nontrivial half depth start (count+1) start count
    actor.castSucc row.castSucc actor row).2
  exact congrArg Sigma.fst (actual_scheduled_material_prior observation nontrivial half depth
    start (count+1) (start+actor.val) row)

/-- The selected macro occurrence carries its own generated whole ledger. -/
theorem actual_tape_whole (start count : Nat) (actor row : Fin (count+1)) :
    type_of% ((tapeOccurrence observation nontrivial half depth start count actor row).2.next_preservesGeneratedLivingLaw) :=
  (tapeOccurrence observation nontrivial half depth start count actor row).2.next_preservesGeneratedLivingLaw

theorem actual_tape_next (start count : Nat) (actor row : Fin (count+1)) :
    (tapeOccurrence observation nontrivial half depth start count actor row).2.nextState =
      (runtime).stateAt (address start count actor row+1) := by
  rw [actual_tape_occurrence]
  rfl

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
