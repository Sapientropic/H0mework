import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ActualRoundNetworkConsumer
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.DonorRegenerationConsumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentrySource
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Distributed.Recall.Information.Agency.Protocol Continuation
open ActualRoundNetworkSource

structure Attempt where
  private mk ::
  network : Network
  callbacks : Nat → Opponent (code network)
  trace : Node network
  trace_exact : trace = ActualRoundNetworkConsumer.finished network callbacks

def execute (net : Network) (callbacks : Nat → Opponent (code net)) : Attempt :=
  ⟨net,callbacks,ActualRoundNetworkConsumer.finished net callbacks,rfl⟩

abbrev model (attempt : Attempt) : MaterialRoundSource.Bound :=
  ⟨attempt.network.entry.bound.base,attempt.network.entry.bound.scope,attempt.trace.cursor.source,
    attempt.network.entry.bound.law_exact,attempt.network.entry.bound.task_exact⟩
abbrev decision (attempt : Attempt) := result attempt.network attempt.trace
abbrev depth (attempt : Attempt) := MaterialRoundSource.depth (model attempt) attempt.trace.cursor.cut
-- Archive the completed last occurrence; the next supply owns the still-open input position.
abbrev completedOrdinal (attempt : Attempt) := depth attempt-1
abbrev disposition (attempt : Attempt) := Native.Authority.fullGenerate (model attempt) (completedOrdinal attempt)

def after (attempt : Attempt) : RoundEpisodeSource.State :=
  ⟨model attempt,attempt.trace.cursor.cut,
    attempt.network.state.archive ++ RoundEpisodeSource.nativeArchive attempt.network.state
      (RoundEpisodeSource.normal attempt.network.state attempt.network.raw) ++
    [.native (model attempt) (completedOrdinal attempt) (disposition attempt)]⟩

structure State where
  episode : RoundEpisodeSource.State
  evidence : List Attempt := []

abbrev prepared (state : State) (produce feed : Bool) :=
  UpstreamFeedSource.arrived (DonorRegenerationSource.generated state.episode produce) feed
abbrev incoming (state : State) (produce feed : Bool) := UpstreamProductionSource.incoming (prepared state produce feed)
abbrev inspect (state : State) (produce feed : Bool) (settings : Settings := {}) :=
  ActualRoundNetworkSource.inspect (prepared state produce feed) (incoming state produce feed) settings
abbrev Callbacks := (net : Network) → Nat → Opponent (code net)

def next (state : State) (produce feed : Bool) (settings : Settings) (callbacks : Callbacks) : State :=
  match inspect state produce feed settings with
  | none => ⟨RoundEpisodeSource.next (prepared state produce feed)
      (RoundEpisodeSource.normal (prepared state produce feed) (incoming state produce feed)),state.evidence⟩
  | some net => let attempt := execute net (callbacks net)
    ⟨after attempt,state.evidence ++ [attempt]⟩

abbrev latest : Callbacks := fun net _ => QueueScheduler.opponent (code net) (OriginQueue.baseline (start net))
abbrev automatic (state : State) := next state true true {} latest

def run (initial : State) (produce feed : State → Bool) (settings : State → Settings)
    (callbacks : State → Callbacks) : Nat → State :=
  Nat.rec initial fun _ state => next state (produce state) (feed state) (settings state) (callbacks state)

abbrev current (state : State) := RoundEpisodeSource.current state.episode

theorem trace_is_the_actual_fold (attempt : Attempt) : Valid attempt.network attempt.trace := by
  rw [attempt.trace_exact]
  exact actual_valid attempt.network attempt.callbacks (window attempt.network)

theorem successor_retains_the_literal_actual_source_and_cut (attempt : Attempt) :
    (after attempt).model.source = attempt.trace.cursor.source ∧
      (after attempt).cut = attempt.trace.cursor.cut ∧
      RoundEpisodeSource.boundary (after attempt) = EventStep.boundary attempt.trace.cursor := ⟨rfl,rfl,rfl⟩

theorem successor_current_is_the_actual_final_feedback_state (attempt : Attempt) :
    RoundEpisodeSource.current (after attempt) = attempt.trace.state.current := by
  have actual := attempt.trace.cursor.source.feedback_current_is_actual attempt.trace.cursor.entry rfl rfl attempt.trace.cursor.cut
  change attempt.trace.cursor.source.currentAt (attempt.trace.cursor.source.history.length+1+attempt.trace.cursor.cut+1) = _
  rw [show attempt.trace.cursor.source.history.length+1+attempt.trace.cursor.cut+1 =
    attempt.trace.cursor.source.history.length+2+attempt.trace.cursor.cut by omega,actual]
  exact (congrArg (fun state : Feedback.State (code attempt.network) => state.current)
    (trace_is_the_actual_fold attempt).2.1).symm

theorem the_completed_native_next_is_the_reentry_current (attempt : Attempt) :
    RoundEpisodeSource.current (after attempt) =
      (code attempt.network).law.next
        ((model attempt).source.actualExecution (completedOrdinal attempt)).before
        ((model attempt).source.actualExecution (completedOrdinal attempt)).submitted := by
  have positive : 0 < depth attempt := by
    dsimp [depth,MaterialRoundSource.depth,Machine.Continuation.depth]
    omega
  have next := (model attempt).source.next_is_actual (completedOrdinal attempt)
  change (model attempt).source.currentAt (depth attempt+1) = _
  rw [show depth attempt+1 = completedOrdinal attempt+2 by dsimp [completedOrdinal];omega]
  exact next

-- Readiness reads primitive balances of each generated actual endpoint, never a future Ready/certificate.
def replenishable (net : Network) : Bool :=
  (generate net (window net)).all fun node => decide
    (WorkerInputSource.Needed node.state.current ∧ DonorRegenerationLaw.Inputs node.state.current)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NetworkReentrySource
