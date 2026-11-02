import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment.Requests

import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole.Prefix.Global

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 600000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment.Autonomous
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Budget.Programme.Debt Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole
open Computation.Search.Segmented.Publication.Learning.Paid
open Input.Recovery.Metering.Assessment.Relation
noncomputable section

structure Produced (first : Packet) where
  private mk ::
  seed : Window first
  pending : List Action
  forecast : ScopeForecast.Forecast seed pending
  generated : forecast = ScopeForecast.generate seed pending

def produce {first : Packet} (seed : Window first) (pending : List Action) : Produced first :=
  ⟨seed,pending,ScopeForecast.generate seed pending,rfl⟩

def Produced.Accepts {first : Packet} (made previous : Produced first) : Prop :=
  ScopeForecast.NoWorse made.forecast previous.forecast

instance {first : Packet} (made previous : Produced first) : Decidable (made.Accepts previous) := by
  unfold Produced.Accepts;infer_instance

def baselineWindow {atPacket : Packet} (origin : FutureOrigin atPacket) : Window origin.first :=
  ⟨origin.first,.same _⟩
def baseline {atPacket : Packet} (origin : FutureOrigin atPacket) :=
  produce (baselineWindow origin) origin.pending

variable (prior : Owned.Task (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)
  (Technology := Unit) (Instrument := Unit)) {epoch : Epoch} (inventory : Inventory epoch)
  (past : List (Rule prior.model.source.code))
  (origin : FutureOrigin (⟨epoch,inventory⟩ : Packet))

abbrev Program := Commitment.Program prior


def actualWindow (program : Program prior) : Window origin.first :=
  let actual := Commitment.Requests.window prior inventory past program
  ⟨actual.packet,.append origin.native actual.native⟩

def generate (program : Program prior) : Produced origin.first :=
  produce (actualWindow prior inventory past origin program)
    (Commitment.Requests.cursor prior inventory past program).pending

theorem received_residual_is_the_only_old_input (intent : Input.Intent) :
    Input.Challenge.Redress.Shared.Iteration.Requests.submitted
      (ScopeForecast.cursor (baseline origin).seed (baseline origin).pending)
      (ScopeForecast.word (baseline origin).seed intent) =
        origin.pending ++ Input.emit origin.first.2 intent := rfl

theorem every_actual_port_uses_the_candidate_endpoint (program : Program prior) (intent : Input.Intent) :
    (generate prior inventory past origin program).forecast.read intent =
      Input.Challenge.Redress.Shared.Iteration.Requests.produce
        (ScopeForecast.cursor (actualWindow prior inventory past origin program)
          (Commitment.Requests.cursor prior inventory past program).pending)
        (Input.emit (actualWindow prior inventory past origin program).packet.2 intent) :=
  ScopeForecast.each_port_is_generated_at_its_actual_scope _ _ _

theorem actual_window_is_the_received_candidate_cut (program : Program prior) :
    (actualWindow prior inventory past origin program).packet =
      (Commitment.Requests.cursor prior inventory past program).saved := rfl

def basisBaseline {atPacket : Packet} (basis : ReceivedBasis atPacket) : Produced basis.first :=
  produce ⟨basis.first,.same _⟩ basis.pending

def generateBasis (basis : ReceivedBasis (⟨epoch,inventory⟩ : Packet)) (program : Program prior) :
    Produced basis.first :=
  let actual := Commitment.Requests.window prior inventory past program
  produce ⟨actual.packet,.append basis.native actual.native⟩
    (Commitment.Requests.cursor prior inventory past program).pending

structure HistoryComparison (atPacket : Packet) where
  basis : ReceivedBasis atPacket
  previous : Produced basis.first
  trial : Produced basis.first

def HistoryComparison.Accepts {atPacket : Packet} (entry : HistoryComparison atPacket) : Prop :=
  entry.trial.Accepts entry.previous

instance {atPacket : Packet} (entry : HistoryComparison atPacket) : Decidable entry.Accepts := by
  unfold HistoryComparison.Accepts;infer_instance

def generateHistory (program : Program prior) : List (HistoryComparison (⟨epoch,inventory⟩ : Packet)) :=
  origin.ancestors.map fun basis =>
    ⟨basis,basisBaseline basis,generateBasis prior inventory past basis program⟩

def HistoryAccepts {atPacket : Packet} (entries : List (HistoryComparison atPacket)) : Prop :=
  ∀ entry ∈ entries,entry.Accepts

instance {atPacket : Packet} (entries : List (HistoryComparison atPacket)) : Decidable (HistoryAccepts entries) := by
  unfold HistoryAccepts;infer_instance

theorem every_retained_basis_has_its_own_actual_comparison (program : Program prior)
    (basis : ReceivedBasis (⟨epoch,inventory⟩ : Packet)) (member : basis ∈ origin.ancestors) :
    (⟨basis,basisBaseline basis,generateBasis prior inventory past basis program⟩ :
      HistoryComparison (⟨epoch,inventory⟩ : Packet)) ∈ generateHistory prior inventory past origin program :=
  List.mem_map.mpr ⟨basis,member,rfl⟩

/-- Quote every possible remaining suffix size without evaluating any Forecast. -/
def programmeBudget : Nat :=
  ((List.range (horizon prior.domain+1)).map fun room =>
    (Whole.programs prior.model.source.code room).length).sum

def perProgrammeUnits : Nat :=
  1 + horizon prior.domain + Prefix.Runtime.actualHorizon prior.point.point +
    Feed.Work.Reconstruction.snapshotServices prior + 2 * ScopeForecast.services +
    (1 + 3 * ScopeForecast.intents.length)

/-- Every ancestor/candidate pair generates both its baseline and its trial. -/
theorem both_generated_forecasts_are_reserved :
    2 * ScopeForecast.services ≤ perProgrammeUnits prior := by
  unfold perProgrammeUnits
  omega

def units (basisCount : Nat) : Nat :=
  basisCount * (1 + ScopeForecast.services + programmeBudget prior * perProgrammeUnits prior)

theorem reserves_the_actual_suffix_pool (past : List (Rule prior.model.source.code)) :
    (Prefix.Global.tailPool prior.model prior.domain past).length ≤ programmeBudget prior := by
  rw [Prefix.Global.tailPool,List.length_map]
  have inside : horizon prior.domain - past.length ∈ List.range (horizon prior.domain+1) :=
    List.mem_range.mpr (by omega)
  exact List.single_le_sum (fun _ _ => Nat.zero_le _) _
    (List.mem_map.mpr ⟨_,inside,rfl⟩)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.World.TaskSource.Commitment.Autonomous
