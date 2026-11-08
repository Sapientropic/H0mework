import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReservedTransitSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.QuorumObservation
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.SourceReceiptRows

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReservedTransitDomain
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open ReservedTransitSource

abbrev Related (left right : Node) := EnvelopeObservation.Compatible start left.stages right.stages

theorem related_states (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : left.state = right.state := by
  have seeds : EventStep.seed left.cursor = EventStep.seed right.cursor := by
    rw [one.1,two.1]
    exact same.1.state
  exact one.2.1.trans (seeds.trans two.2.1.symm)

theorem related_protocols (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : protocol left = protocol right := by
  have states := related_states left right one two same
  simp only [protocol,needs,due,states]
  rfl

theorem related_choices (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : choices left = choices right := by
  change envelope left = envelope right
  rw [envelope_is_the_original_source_envelope left one,envelope_is_the_original_source_envelope right two]
  exact EnvelopeObservation.choices_equal start _ _ same allowance

def chosen (left right : Node) (rival : Opponent code) : Move code :=
  CausalLocalDomain.chosen (EventHistory.execute start left.stages) (EventHistory.execute start right.stages) rival

theorem chosen_is_actual (left right : Node) (two : Valid right) (same : Related left right)
    (rival : Opponent code) : chosen left right rival = intake right rival := by
  unfold chosen intake
  rw [EnvelopeObservation.chosen_is_the_actual_intake start _ _ same,← two.1]

theorem compact_step (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) (rival : Opponent code) :
    Related (step left (EventStep.fixed (chosen left right rival))) (step right rival) := by
  have protocols := related_protocols left right one two same
  change EnvelopeObservation.Compatible start
    (left.stages ++ [(protocol left,EventStep.fixed (chosen left right rival))])
    (right.stages ++ [(protocol right,rival)])
  rw [← protocols]
  exact EnvelopeObservation.compact_extension start _ _ same (protocol left) rival

-- Callbacks may inspect their entire actual history. Their admitted next effect is covered, not their function table.
theorem every_compliant_actual_callback_has_a_generated_source_branch
    (external : Nat → Opponent code) (count : Nat) (within : Within external count) :
    ∃ node ∈ generate count, Related node (actual external count) := by
  induction count with
  | zero => exact ⟨initial,List.mem_singleton_self _,EventStep.matches_self _,EnvelopeObservation.reflexive _⟩
  | succ count ih =>
    have prior : Within external count := fun index bounded => within index (by omega)
    obtain ⟨node,member,same⟩ := ih prior
    have one := every_generated_node_keeps_the_original_source count node member
    have two := actual_is_source_generated external count
    let rival := external (actual external count).cursor.cut
    let move := chosen node (actual external count) rival
    have allowed : move ∈ choices node := by
      dsimp only [move]
      rw [related_choices node _ one two same,chosen_is_actual node _ two same]
      exact within count (by omega)
    refine ⟨step node (EventStep.fixed move),?_,compact_step node _ one two same rival⟩
    exact List.mem_flatMap.mpr ⟨node,member,List.mem_map.mpr ⟨move,allowed,rfl⟩⟩

def reception : StageReception.Law code := DemandTransitSource.reception deliveryBound
abbrev vocabulary := RenewedQuorumSource.vocabulary
abbrev encoding := DemandTransitSource.encoding DemandScheduleConsumer.quiet
abbrev observed (node : Node) := StageReception.run vocabulary encoding reception start node.stages 2 node.stages.length
def result (node : Node) := InterfaceQuorum.produce start vocabulary encoding reception node.stages 2
  (RenewedQuorumSource.slot true) 2

abbrev cached (node : Node) := SourceReceiptRows.run vocabulary encoding node.rows reception 2 node.rows.length

theorem cached_is_the_actual_receiver (node : Node) (valid : Valid node) : cached node = observed node := by
  unfold cached observed
  rw [valid.2.2,StageTrace.record_count]
  exact SourceReceiptRows.run_actual vocabulary encoding start node.stages reception 2 node.stages.length

def calculated (node : Node) : ProspectiveQuorum.Result :=
  if ¬ code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary (RenewedQuorumSource.slot true) < 2+2 then
    .blocked .unsafeSourceBudget
  else match StageQuorum.readout (cached node) (RenewedQuorumSource.slot true) 2 with
    | .blocked => .blocked .missingQuorum
    | .decided value => .decided value

theorem calculated_is_the_original_producer (node : Node) (valid : Valid node) : calculated node = result node := by
  unfold calculated result InterfaceQuorum.produce
  rw [cached_is_the_actual_receiver node valid]
  rfl

theorem related_observations (left right : Node) (same : Related left right) :
    observed left = observed right := by
  unfold observed
  rw [QuorumObservation.count_equal start _ _ same.2]
  exact CommunicationObservation.run_equal vocabulary encoding start start _ _
    (EnvelopeObservation.communication same.2) reception _ _

theorem related_results (left right : Node) (same : Related left right) : result left = result right := by
  have received := related_observations left right same
  unfold result InterfaceQuorum.produce
  change (if ¬ code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary (RenewedQuorumSource.slot true) < 2+2 then _
    else match StageQuorum.readout (observed left) (RenewedQuorumSource.slot true) 2 with | .blocked => _ | .decided value => _) = _
  rw [received]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ReservedTransitDomain
