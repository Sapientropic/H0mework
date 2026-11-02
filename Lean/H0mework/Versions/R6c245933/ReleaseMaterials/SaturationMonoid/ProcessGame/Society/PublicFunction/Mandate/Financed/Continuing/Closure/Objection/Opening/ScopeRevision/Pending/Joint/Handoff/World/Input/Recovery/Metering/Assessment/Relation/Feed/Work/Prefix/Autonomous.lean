import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Actual
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment.Autonomous

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Autonomous
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
noncomputable section

variable (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)) {epoch : Epoch} (inventory : Inventory epoch)
  (past : List (Rule prior.model.source.code))
  (reference : Whole.Program prior.model.source.code (horizon prior.domain))
  (original : Work.Batch prior.model prior.domain prior.original prior.futureRequests inventory prior.recoveryPricing)
  (rebuilt : Work.Reconstruction.Batch prior inventory original)
  (origin : FutureOrigin (⟨epoch,inventory⟩ : Packet))

abbrev Old := Actual.Candidate prior inventory past reference original rebuilt
abbrev Baseline {atPacket : Packet} (basis : FutureOrigin atPacket) :=
  TaskSource.Commitment.Autonomous.Produced basis.first

structure Rejection {first : Packet}
    (baseline trial : TaskSource.Commitment.Autonomous.Produced first) where
  intent : Input.Intent
  generated : intent ∈ ScopeForecast.intents
  broken : ¬ (ScopeForecast.PortNoWorse (trial.forecast.read intent) (baseline.forecast.read intent) ∧
    Window.NoWorse (ScopeForecast.taskWindow (trial.forecast.read intent))
      (ScopeForecast.taskWindow (baseline.forecast.read intent)) ∧
    TaskSource.Admission.NoWorse (trial.forecast.taskAdmission intent) (baseline.forecast.taskAdmission intent))

def rejectionFrom {first : Packet}
    (baseline trial : TaskSource.Commitment.Autonomous.Produced first)
    (failed : ¬ trial.Accepts baseline) :
    Rejection baseline trial :=
  match Distributed.inspect (fun intent =>
      ScopeForecast.PortNoWorse (trial.forecast.read intent) (baseline.forecast.read intent) ∧
      Window.NoWorse (ScopeForecast.taskWindow (trial.forecast.read intent))
        (ScopeForecast.taskWindow (baseline.forecast.read intent)) ∧
      TaskSource.Admission.NoWorse (trial.forecast.taskAdmission intent) (baseline.forecast.taskAdmission intent))
      ScopeForecast.intents with
  | .rejected intent generated broken => ⟨intent,generated,broken⟩
  | .accepted kept => False.elim (failed kept)

abbrev History := List (TaskSource.Commitment.Autonomous.HistoryComparison (⟨epoch,inventory⟩ : Packet))

def AllAccepted (baseline trial : Baseline origin) (history : History inventory) : Prop :=
  trial.Accepts baseline ∧ TaskSource.Commitment.Autonomous.HistoryAccepts history

instance (baseline trial : Baseline origin) (history : History inventory) :
    Decidable (AllAccepted inventory origin baseline trial history) := by
  unfold AllAccepted;infer_instance

structure HistoryRejection (history : History inventory) where
  entry : TaskSource.Commitment.Autonomous.HistoryComparison (⟨epoch,inventory⟩ : Packet)
  generated : entry ∈ history
  fault : Rejection entry.previous entry.trial

inductive CompleteRejection (baseline trial : Baseline origin) (history : History inventory) where
  | current (fault : Rejection baseline trial)
  | ancestor (fault : HistoryRejection inventory history)

def completeRejectionFrom (baseline trial : Baseline origin) (history : History inventory)
    (failed : ¬ AllAccepted inventory origin baseline trial history) :
    CompleteRejection inventory origin baseline trial history :=
  if kept : trial.Accepts baseline then
    match Distributed.inspect (fun (entry : TaskSource.Commitment.Autonomous.HistoryComparison (⟨epoch,inventory⟩ : Packet)) => entry.Accepts) history with
    | .rejected entry generated broken => .ancestor ⟨entry,generated,rejectionFrom _ _ broken⟩
    | .accepted allKept => False.elim (failed ⟨kept,allKept⟩)
  else .current (rejectionFrom baseline trial kept)

structure Evaluation where
  previous : Old prior inventory past reference original rebuilt
  trial : TaskSource.Commitment.Autonomous.Produced origin.first
  generated : trial = TaskSource.Commitment.Autonomous.generate prior inventory past origin previous.previous.previous.protocol
  history : History inventory
  history_generated : history = TaskSource.Commitment.Autonomous.generateHistory prior inventory past origin previous.previous.previous.protocol

def evaluate (bound : prior.worldCurrent.isSome = true) :
    List (Evaluation prior inventory past reference original rebuilt origin) :=
  (Actual.candidates prior inventory past reference original rebuilt bound).map fun previous =>
    ⟨previous,TaskSource.Commitment.Autonomous.generate prior inventory past origin previous.previous.previous.protocol,rfl,
      TaskSource.Commitment.Autonomous.generateHistory prior inventory past origin previous.previous.previous.protocol,rfl⟩

theorem evaluated_pool_is_reserved (bound : prior.worldCurrent.isSome = true) :
    (evaluate prior inventory past reference original rebuilt origin bound).length ≤
      TaskSource.Commitment.Autonomous.programmeBudget prior := by
  apply Nat.le_trans (m := (Prefix.Global.tailPool prior.model prior.domain past).length)
  · unfold evaluate Actual.candidates Actual.originalPool Reconstruction.candidates Reconstruction.originalPool
      Work.Prefix.candidates Prefix.Global.candidates
    rw [List.length_map]
    exact (List.length_filterMap_le _ _).trans
      ((List.length_filterMap_le _ _).trans
        ((List.length_filterMap_le _ _).trans (List.length_filterMap_le _ _)))
  · exact TaskSource.Commitment.Autonomous.reserves_the_actual_suffix_pool prior past

def evaluatedUnits (basisCount count : Nat) :=
  basisCount * (1 + ScopeForecast.services + count * TaskSource.Commitment.Autonomous.perProgrammeUnits prior)

theorem evaluated_services_are_reserved (bound : prior.worldCurrent.isSome = true) :
    evaluatedUnits prior (origin.ancestors.length+1) (evaluate prior inventory past reference original rebuilt origin bound).length ≤
      TaskSource.Commitment.Autonomous.units prior (origin.ancestors.length+1) := by
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (evaluated_pool_is_reserved prior inventory past reference original rebuilt origin bound)) _

structure Candidate (baseline : Baseline origin) where
  previous : Old prior inventory past reference original rebuilt
  trial : TaskSource.Commitment.Autonomous.Produced origin.first
  generated : trial = TaskSource.Commitment.Autonomous.generate prior inventory past origin previous.previous.previous.protocol
  history : History inventory
  history_generated : history = TaskSource.Commitment.Autonomous.generateHistory prior inventory past origin previous.previous.previous.protocol
  accepted : AllAccepted inventory origin baseline trial history

def refine (baseline : Baseline origin)
    (evaluated : Evaluation prior inventory past reference original rebuilt origin) :
    Option (Candidate prior inventory past reference original rebuilt origin baseline) :=
  if kept : AllAccepted inventory origin baseline evaluated.trial evaluated.history then
    some ⟨evaluated.previous,evaluated.trial,evaluated.generated,evaluated.history,evaluated.history_generated,kept⟩ else none

def candidates (baseline : Baseline origin)
    (evaluated : List (Evaluation prior inventory past reference original rebuilt origin)) :=
  evaluated.filterMap (refine prior inventory past reference original rebuilt origin baseline)

inductive Outcome where
  | unbound (missing : prior.worldCurrent = none)
  | selected (baseline : Baseline origin)
      (generated : baseline = TaskSource.Commitment.Autonomous.baseline origin)
      (candidate : Candidate prior inventory past reference original rebuilt origin baseline)
  | blocked (baseline : Baseline origin)
      (generated : baseline = TaskSource.Commitment.Autonomous.baseline origin)
      (bound : prior.worldCurrent.isSome = true)
      (evaluated : List (Evaluation prior inventory past reference original rebuilt origin))
      (evaluated_exact : evaluated = evaluate prior inventory past reference original rebuilt origin bound)
      (failed : ∀ entry ∈ evaluated,
        CompleteRejection inventory origin baseline entry.trial entry.history)

def compile : Outcome prior inventory past reference original rebuilt origin :=
  match bound : prior.worldCurrent with
  | none => .unbound bound
  | some _ =>
      let present : prior.worldCurrent.isSome = true := by rw [bound];rfl
      let baseline := TaskSource.Commitment.Autonomous.baseline origin
      let evaluated := evaluate prior inventory past reference original rebuilt origin present
      match found : (candidates prior inventory past reference original rebuilt origin baseline evaluated).head? with
      | some candidate => .selected baseline rfl candidate
      | none => .blocked baseline rfl present evaluated rfl
          (fun entry member => completeRejectionFrom inventory origin baseline entry.trial entry.history (by
              intro accepted
              let included : Candidate prior inventory past reference original rebuilt origin baseline :=
                ⟨entry.previous,entry.trial,entry.generated,entry.history,entry.history_generated,accepted⟩
              have has : included ∈ candidates prior inventory past reference original rebuilt origin baseline evaluated :=
                List.mem_filterMap.mpr ⟨entry,member,by simp only [refine,dif_pos accepted]; rfl⟩
              rw [List.head?_eq_none_iff.mp found] at has
              exact List.not_mem_nil has))

variable {prior inventory past reference original rebuilt origin}
def candidate? : Outcome prior inventory past reference original rebuilt origin →
    Option (Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
  | .selected _ _ candidate => some candidate.previous.previous.previous.previous
  | .unbound _ | .blocked .. => none

def Reviewed (outcome : Outcome prior inventory past reference original rebuilt origin) : Prop :=
  match outcome with
  | .unbound _ => prior.worldCurrent = none
  | .selected baseline _ candidate =>
      Actual.Reviewed (.selected candidate.previous) ∧ AllAccepted inventory origin baseline candidate.trial candidate.history
  | .blocked baseline _ _ evaluated _ _ =>
      ∀ entry ∈ evaluated,¬ AllAccepted inventory origin baseline entry.trial entry.history

theorem reviewed (outcome : Outcome prior inventory past reference original rebuilt origin) : Reviewed outcome := by
  cases outcome with
  | unbound missing => exact missing
  | selected baseline generated candidate => exact ⟨Actual.reviewed _,candidate.accepted⟩
  | blocked baseline generated bound evaluated exact failed =>
      intro entry member kept
      cases failed entry member with
      | current fault => exact fault.broken (kept.1 fault.intent fault.generated)
      | ancestor fault => exact fault.fault.broken ((kept.2 fault.entry fault.generated) fault.fault.intent fault.fault.generated)

theorem selected_old_protection (outcome : Outcome prior inventory past reference original rebuilt origin)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
    (chosen : candidate? outcome = some candidate) :
    prior.worldCurrent.isSome = true ∧
      TaskSource.Commitment.NoWorse prior inventory past reference candidate.protocol := by
  cases outcome with
  | unbound missing => cases chosen
  | blocked baseline generated bound evaluated exact failed => cases chosen
  | selected baseline generated selected =>
      apply Actual.selected_has_its_actual_protection (.selected selected.previous) candidate
      exact chosen

theorem selected_queries (outcome : Outcome prior inventory past reference original rebuilt origin)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
    (chosen : candidate? outcome = some candidate) :
    TaskSource.Commitment.Requests.Accepts prior inventory past original reference candidate.protocol
      (TaskSource.Commitment.Requests.execute prior inventory past candidate.protocol) := by
  cases outcome with
  | unbound missing => cases chosen
  | blocked baseline generated bound evaluated exact failed => cases chosen
  | selected baseline generated selected =>
      apply Actual.selected_keeps_the_original_queries (.selected selected.previous) candidate
      exact chosen

theorem selected_future (outcome : Outcome prior inventory past reference original rebuilt origin)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
    (chosen : candidate? outcome = some candidate) :
    ScopeForecast.NoWorse
      (TaskSource.Commitment.Autonomous.generate prior inventory past origin candidate.protocol).forecast
      (TaskSource.Commitment.Autonomous.baseline origin).forecast := by
  cases outcome with
  | unbound missing => cases chosen
  | blocked baseline generated bound evaluated exact failed => cases chosen
  | selected baseline generated selected =>
      cases Option.some.inj chosen
      rw [←generated,←selected.generated]
      exact selected.accepted.1

theorem selected_ancestors (outcome : Outcome prior inventory past reference original rebuilt origin)
    (candidate : Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global.Candidate
      (tariff := prior.recoveryPricing) (requested := prior.futureRequests)
      prior.model prior.domain prior.original past reference)
    (chosen : candidate? outcome = some candidate) :
    TaskSource.Commitment.Autonomous.HistoryAccepts
      (TaskSource.Commitment.Autonomous.generateHistory prior inventory past origin candidate.protocol) := by
  cases outcome with
  | unbound missing => cases chosen
  | blocked baseline generated bound evaluated exact failed => cases chosen
  | selected baseline generated selected =>
      cases Option.some.inj chosen
      rw [←selected.history_generated]
      exact selected.accepted.2

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.Input.Recovery.Metering.Assessment.Relation.Feed.Work.Prefix.Autonomous
