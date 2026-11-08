import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumSource

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumDomain
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation
open RenewedQuorumConsumer (code)
open OwnedQuorumSource

abbrev Related (left right : Node) :=
  ReservedTransitDomain.Related left.toNode right.toNode ∧ left.omissions = right.omissions

theorem related_states (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : left.state = right.state :=
  ReservedTransitDomain.related_states left.toNode right.toNode one two same.1

theorem related_owners (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : owner left = owner right := by
  have states := related_states left right one two same
  have owners : left.cursor.ownerStart = right.cursor.ownerStart := by
    rw [one.1,two.1];exact same.1.1.ownerStart
  simp only [owner,states,owners]

theorem related_ballots (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : ballots left = ballots right := by
  have rows := EnvelopeObservation.communication same.1.2
  rw [← one.2.2,← two.2.2] at rows
  unfold ballots
  generalize left.rows = a at rows ⊢
  generalize right.rows = b at rows ⊢
  induction rows with
  | nil => rfl
  | @cons a b _ _ item rest ih =>
    simp only [List.flatMap_cons,CommunicationObservation.ballots_equal vocabulary item,ih]

theorem related_encodings (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : encoding left = encoding right := by
  funext signal
  simp only [encoding,related_ballots left right one two same]

theorem related_bases (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : base left = base right := by
  have states := related_states left right one two same
  have encoded := related_encodings left right one two same
  simp only [base,ReservedTransitSource.needs,ReservedTransitSource.due,states,encoded]
  rfl

theorem related_opportunities (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : opportunity left = opportunity right := by
  simp only [opportunity,related_states left right one two same,related_owners left right one two same,
    related_bases left right one two same]

theorem related_protocols (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) (requested : Bool) : protocol left requested = protocol right requested := by
  simp only [protocol,related_bases left right one two same,withhold,
    related_opportunities left right one two same,same.2]
  rfl

def normalized (node : Node) (requested : Bool) : Bool :=
  if opportunity node && decide (node.omissions.length < controlCapacity) then requested else false

theorem normalized_is_generated (node : Node) (requested : Bool) : normalized node requested ∈ controls node := by
  unfold normalized controls
  split <;> cases requested <;> simp_all

theorem normalization_preserves_actual_control (node : Node) (requested : Bool) :
    withhold node (normalized node requested) = withhold node requested := by
  unfold withhold normalized
  split <;> simp_all

theorem normalization_preserves_actual_protocol (node : Node) (requested : Bool) :
    protocol node (normalized node requested) = protocol node requested := by
  simp only [protocol,normalization_preserves_actual_control]

def chosen (left right : Node) (rival : Opponent code) : Move code :=
  ReservedTransitDomain.chosen left.toNode right.toNode rival

theorem compact_step (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) (requested : Bool) (rival : Opponent code) :
    Related (step left (normalized left requested) (EventStep.fixed (chosen left right rival)))
      (step right requested rival) := by
  have protocols := (normalization_preserves_actual_protocol left requested).trans
    (related_protocols left right one two same requested)
  have control : withhold left (normalized left requested) = withhold right requested := by
    rw [normalization_preserves_actual_control]
    simp only [withhold,related_opportunities left right one two same,same.2]
  refine ⟨?_,?_⟩
  · change EnvelopeObservation.Compatible start
      (left.stages ++ [(protocol left (normalized left requested),EventStep.fixed (chosen left right rival))])
      (right.stages ++ [(protocol right requested,rival)])
    rw [← protocols]
    exact EnvelopeObservation.compact_extension start _ _ same.1 _ rival
  · change (if withhold left (normalized left requested) then left.omissions ++ [(left.cursor.cut,(owner left).getD 0)] else left.omissions) =
      (if withhold right requested then right.omissions ++ [(right.cursor.cut,(owner right).getD 0)] else right.omissions)
    have cuts : left.cursor.cut = right.cursor.cut := by rw [one.1,two.1];exact same.1.1.cut
    rw [control,same.2,cuts,related_owners left right one two same]

-- The domain covers next effects of arbitrary full actual-state controllers and network callbacks.
theorem every_actual_local_and_network_controller_has_a_generated_branch
    (control : Controller) (external : Nat → Opponent code) (count : Nat) (within : Within control external count) :
    ∃ node ∈ generate count, Related node (actual control external count) := by
  induction count with
  | zero => exact ⟨initial,List.mem_singleton_self _,⟨EventStep.matches_self _,EnvelopeObservation.reflexive _⟩,rfl⟩
  | succ count ih =>
    obtain ⟨node,member,same⟩ := ih (fun index bounded => within index (by omega))
    have one := every_generated_node_is_source_generated count node member
    have two := every_actual_cut_is_source_generated control external count
    let right := actual control external count
    let requested := control right.cursor.cut right.state
    let rival := external right.cursor.cut
    let move := chosen node right rival
    have allowed : move ∈ choices node := by
      change ReservedTransitDomain.chosen node.toNode right.toNode rival ∈ ReservedTransitSource.choices node.toNode
      rw [ReservedTransitDomain.related_choices node.toNode right.toNode one two same.1,
        ReservedTransitDomain.chosen_is_actual node.toNode right.toNode two same.1]
      exact within count (by omega)
    refine ⟨step node (normalized node requested) (EventStep.fixed move),?_,compact_step node right one two same requested rival⟩
    exact List.mem_flatMap.mpr ⟨node,member,List.mem_flatMap.mpr
      ⟨normalized node requested,normalized_is_generated node requested,List.mem_map.mpr ⟨move,allowed,rfl⟩⟩⟩

abbrev reception := ReservedTransitDomain.reception
abbrev observed (node : Node) := StageReception.run vocabulary (encoding node) reception start node.stages 2 node.stages.length
def result (node : Node) := InterfaceQuorum.produce start vocabulary (encoding node) reception node.stages 2
  (RenewedQuorumSource.slot true) 2
abbrev cached (node : Node) := SourceReceiptRows.run vocabulary (encoding node) node.rows reception 2 node.rows.length

theorem cached_is_the_actual_receiver (node : Node) (valid : Valid node) : cached node = observed node := by
  unfold cached observed
  rw [valid.2.2,StageTrace.record_count]
  exact SourceReceiptRows.run_actual vocabulary (encoding node) start node.stages reception 2 node.stages.length

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

theorem related_observations (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : observed left = observed right := by
  unfold observed
  rw [related_encodings left right one two same,QuorumObservation.count_equal start _ _ same.1.2]
  exact CommunicationObservation.run_equal vocabulary (encoding right) start start _ _
    (EnvelopeObservation.communication same.1.2) reception _ _

theorem related_results (left right : Node) (one : Valid left) (two : Valid right)
    (same : Related left right) : result left = result right := by
  have received := related_observations left right one two same
  unfold result InterfaceQuorum.produce
  change (if ¬ code.sites + InterfaceDeviationEnvelope.budget start.source vocabulary (RenewedQuorumSource.slot true) < 2+2 then _
    else match StageQuorum.readout (observed left) (RenewedQuorumSource.slot true) 2 with | .blocked => _ | .decided value => _) = _
  rw [received]
  rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.OwnedQuorumDomain
