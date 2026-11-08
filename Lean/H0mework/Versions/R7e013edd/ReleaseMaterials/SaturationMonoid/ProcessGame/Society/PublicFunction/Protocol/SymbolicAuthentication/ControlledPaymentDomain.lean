import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlledPaymentSource
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.FinancedNetworkDomain

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlledPaymentDomain
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program
open Distributed.Recall.Information.Agency.Protocol Continuation
open FinancedNetworkSource (code start window)
open ControlledPaymentSource

abbrev Related (left right : Node) := EnvelopeObservation.Compatible start left.stages right.stages ∧ left.omissions = right.omissions

theorem related_states (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    left.state = right.state := FinancedNetworkDomain.related_states left.toNode right.toNode one two same.1

theorem related_owners (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    owner left = owner right := by
  have owners : left.cursor.ownerStart = right.cursor.ownerStart := by rw [one.1,two.1];exact same.1.1.ownerStart
  simp only [owner,related_states left right one two same,owners]
theorem related_opportunities (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    opportunity left = opportunity right := by
  simp only [opportunity,related_states left right one two same,related_owners left right one two same]
theorem related_protocols (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) (requested : Bool) :
    protocol left requested = protocol right requested := by
  simp only [protocol,withhold,related_opportunities left right one two same,same.2]
  rfl
theorem related_choices (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    choices left = choices right := by
  rw [choices_are_the_original_source_envelope left one,choices_are_the_original_source_envelope right two]
  have equal : allowance left = allowance right := by simp only [allowance,same.2]
  rw [equal]
  exact EnvelopeObservation.choices_equal start _ _ same.1 (allowance right)

def normalized (node : Node) (requested : Bool) : Bool :=
  if opportunity node && decide (node.omissions.length < capacity) then requested else false

theorem normalized_is_generated (node : Node) (requested : Bool) : normalized node requested ∈ controls node := by
  unfold normalized controls
  split <;> cases requested <;> simp_all

theorem normalization_preserves_protocol (node : Node) (requested : Bool) : protocol node (normalized node requested) = protocol node requested := by
  have hold : withhold node (normalized node requested) = withhold node requested := by
    unfold normalized withhold
    split <;> simp_all
  simp only [protocol,hold]

def chosen (left right : Node) (rival : Opponent code) : Move code := FinancedNetworkDomain.chosen left.toNode right.toNode rival

theorem compact_step (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right)
    (requested : Bool) (rival : Opponent code) :
    Related (step left (normalized left requested) (EventStep.fixed (chosen left right rival))) (step right requested rival) := by
  have protocols := (normalization_preserves_protocol left requested).trans (related_protocols left right one two same requested)
  have hold : withhold left (normalized left requested) = withhold right requested := by
    have norm : withhold left (normalized left requested) = withhold left requested := by
      unfold withhold normalized
      split <;> simp_all
    rw [norm]
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
    rw [hold,same.2,cuts,related_owners left right one two same]

theorem every_actual_joint_controller_has_a_generated_source_branch
    (control : Controller) (rivals : Nat → Opponent code) (count : Nat) (within : Within control rivals count) :
    ∃ node ∈ generate count, Related node (actual control rivals count) := by
  induction count with
  | zero => exact ⟨initial,List.mem_singleton_self _,⟨EventStep.matches_self _,EnvelopeObservation.reflexive _⟩,rfl⟩
  | succ count ih =>
    obtain ⟨node,member,same⟩ := ih (fun index bounded => within index (by omega))
    have one := generated_valid count node member
    have two := actual_valid control rivals count
    let right := actual control rivals count
    let requested := control right.cursor.cut right.state
    let rival := rivals right.cursor.cut
    let move := chosen node right rival
    have allowed : move ∈ choices node := by
      change FinancedNetworkDomain.chosen node.toNode right.toNode rival ∈ choices node
      rw [related_choices node right one two same,
        FinancedNetworkDomain.chosen_is_actual node.toNode right.toNode two same.1]
      exact within count (by omega)
    exact ⟨step node (normalized node requested) (EventStep.fixed move),
      List.mem_flatMap.mpr ⟨node,member,List.mem_flatMap.mpr ⟨normalized node requested,normalized_is_generated node requested,
        List.mem_map.mpr ⟨move,allowed,rfl⟩⟩⟩,compact_step node right one two same requested rival⟩

theorem related_rows (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    CommunicationObservation.Related left.rows right.rows := by
  rw [one.2.2,two.2.2]
  exact EnvelopeObservation.communication same.1.2

theorem related_scopes (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) : scope left = scope right := by
  have rows := related_rows left right one two same
  unfold scope originRow
  generalize left.rows = a at rows ⊢
  generalize right.rows = b at rows ⊢
  induction rows with
  | nil => rfl
  | @cons a b _ _ head tail ih =>
    have paid : paymentAt a = paymentAt b := by simp only [paymentAt,head.before,head.submitted]
    simp only [List.find?_cons,paid]
    split
    · simp only [Option.bind_some,paid]
    · exact ih

theorem related_original_subjects (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) :
    originSubject left = originSubject right := by
  have rows := related_rows left right one two same
  unfold originSubject originRow
  generalize left.rows = a at rows ⊢
  generalize right.rows = b at rows ⊢
  induction rows with
  | nil => rfl
  | @cons a b _ _ head tail ih =>
    have paid : paymentAt a = paymentAt b := by simp only [paymentAt,head.before,head.submitted]
    simp only [List.find?_cons,paid]
    split
    · simp only [Option.bind_some,paid]
      cases paymentAt b with
      | none => rfl
      | some payment => exact StagePaymentQuorum.at_equal (vocabulary payment.scope) head payment.scope
    · exact ih

theorem related_encodings (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) (name : Scope) :
    encoding left name = encoding right name := by
  have rows := related_rows left right one two same
  have bodies : ballots left name = ballots right name := by
    unfold ballots
    generalize left.rows = a at rows ⊢
    generalize right.rows = b at rows ⊢
    induction rows with
    | nil => rfl
    | @cons a b _ _ head tail ih => simp only [List.flatMap_cons,CommunicationObservation.ballots_equal (vocabulary name) head,ih]
  funext signal
  simp only [encoding,bodies]

theorem related_results (left right : Node) (one : Valid left) (two : Valid right) (same : Related left right) : result left = result right := by
  unfold result
  rw [related_scopes left right one two same,related_original_subjects left right one two same]
  split <;> try rfl
  rename_i name original _ _
  have counts := QuorumObservation.count_equal start _ _ same.1.2
  have bodies := related_encodings left right one two same name
  have resolved := StagePaymentQuorum.resolve_equal (vocabulary name) (EnvelopeObservation.communication same.1.2) name
  have receivers := CommunicationObservation.run_equal (vocabulary name) (encoding right name) start start _ _
    (EnvelopeObservation.communication same.1.2) (reception name) 0 right.stages.length
  have produced : StagePaymentQuorum.produce (vocabulary name) start (encoding left name) (reception name) left.stages 0 name 1 =
      StagePaymentQuorum.produce (vocabulary name) start (encoding right name) (reception name) right.stages 0 name 1 := by
    unfold StagePaymentQuorum.produce StagePaymentQuorum.resolve
    rw [bodies,resolved]
    split <;> try rfl
    split <;> try rfl
    unfold StagePaymentQuorum.received
    rw [counts,receivers]
  rw [produced]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ControlledPaymentDomain
